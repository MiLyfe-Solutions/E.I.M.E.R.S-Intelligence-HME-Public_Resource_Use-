import V185TrunkScan23Chunk1195

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7086191 : List Nat := [1, 1, 2, 1, 3, 6, 2, 2, 5]
def baseStart_7086191 : Nat := 118140960795 + 7086191 * 2 ^ 59
def prefixEnd_7086191 : Nat := 4983230072969 + 3 ^ 40 * 7086191 * 2
def baseEnd_7086191 : Nat := 404291332507154442091523

theorem tailTrace_7086191 : CollatzResearch.WordTrace tailWord_7086191 prefixEnd_7086191 404291332507154442091523 := by
  unfold tailWord_7086191
  simp only [CollatzResearch.WordTrace]
  refine ⟨258454618670947706916970427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172303079113965137944646951 258454618670947706916970427)
  ·
    refine ⟨387681928006421560375455641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258454618670947706916970427 387681928006421560375455641)
    ·
      refine ⟨290761446004816170281591731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387681928006421560375455641 290761446004816170281591731)
      ·
        refine ⟨436142169007224255422387597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290761446004816170281591731 436142169007224255422387597)
        ·
          refine ⟨163553313377709095783395349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436142169007224255422387597 163553313377709095783395349)
          ·
            refine ⟨7666561564580113864846657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163553313377709095783395349 7666561564580113864846657)
            ·
              refine ⟨5749921173435085398634993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7666561564580113864846657 5749921173435085398634993)
              ·
                refine ⟨4312440880076314048976245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5749921173435085398634993 4312440880076314048976245)
                ·
                  refine ⟨404291332507154442091523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4312440880076314048976245 404291332507154442091523)
                  ·
                    rfl

theorem cell23_7086191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 5].length) (baseStart_7086191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086191 prefixEnd_7086191 := by exact prefixLift 7086191
  have htrace : WordTrace (prefixWord ++ tailWord_7086191) baseStart_7086191 baseEnd_7086191 := by
    simpa [prefixWord, tailWord_7086191, baseEnd_7086191] using wordTrace_append hprefix tailTrace_7086191
  have hstable : (prefixWord ++ tailWord_7086191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086191).length < 2 ^ (prefixWord ++ tailWord_7086191).sum := by decide
  have hdescent : baseEnd_7086191 < baseStart_7086191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086194 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 2, 5, 2]
def baseStart_7086194 : Nat := 118140960795 + 7086194 * 2 ^ 59
def prefixEnd_7086194 : Nat := 4983230072969 + 3 ^ 40 * 7086194 * 2
def baseEnd_7086194 : Nat := 3638623533006353467086193

theorem tailTrace_7086194 : CollatzResearch.WordTrace tailWord_7086194 prefixEnd_7086194 3638623533006353467086193 := by
  unfold tailWord_7086194
  simp only [CollatzResearch.WordTrace]
  refine ⟨64613682022484209607332409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172303152059957892286219757 64613682022484209607332409)
  ·
    refine ⟨48460261516863157205499307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64613682022484209607332409 48460261516863157205499307)
    ·
      refine ⟨72690392275294735808248961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48460261516863157205499307 72690392275294735808248961)
      ·
        refine ⟨54517794206471051856186721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72690392275294735808248961 54517794206471051856186721)
        ·
          refine ⟨40888345654853288892140041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54517794206471051856186721 40888345654853288892140041)
          ·
            refine ⟨30666259241139966669105031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40888345654853288892140041 30666259241139966669105031)
            ·
              refine ⟨45999388861709950003657547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30666259241139966669105031 45999388861709950003657547)
              ·
                refine ⟨68999083292564925005486321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45999388861709950003657547 68999083292564925005486321)
                ·
                  refine ⟨51749312469423693754114741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68999083292564925005486321 51749312469423693754114741)
                  ·
                    refine ⟨4851498044008471289448257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51749312469423693754114741 4851498044008471289448257)
                    ·
                      refine ⟨3638623533006353467086193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4851498044008471289448257 3638623533006353467086193)
                      ·
                        rfl

theorem cell23_7086194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_7086194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086194 prefixEnd_7086194 := by exact prefixLift 7086194
  have htrace : WordTrace (prefixWord ++ tailWord_7086194) baseStart_7086194 baseEnd_7086194 := by
    simpa [prefixWord, tailWord_7086194, baseEnd_7086194] using wordTrace_append hprefix tailTrace_7086194
  have hstable : (prefixWord ++ tailWord_7086194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086194).length < 2 ^ (prefixWord ++ tailWord_7086194).sum := by decide
  have hdescent : baseEnd_7086194 < baseStart_7086194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086200 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 2, 8]
def baseStart_7086200 : Nat := 118140960795 + 7086200 * 2 ^ 59
def prefixEnd_7086200 : Nat := 4983230072969 + 3 ^ 40 * 7086200 * 2
def baseEnd_7086200 : Nat := 1212875537963426814537055

theorem tailTrace_7086200 : CollatzResearch.WordTrace tailWord_7086200 prefixEnd_7086200 1212875537963426814537055 := by
  unfold tailWord_7086200
  simp only [CollatzResearch.WordTrace]
  refine ⟨129227473463957550727024027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172303297951943400969365369 129227473463957550727024027)
  ·
    refine ⟨193841210195936326090536041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129227473463957550727024027 193841210195936326090536041)
    ·
      refine ⟨145380907646952244567902031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193841210195936326090536041 145380907646952244567902031)
      ·
        refine ⟨218071361470428366851853047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145380907646952244567902031 218071361470428366851853047)
        ·
          refine ⟨327107042205642550277779571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218071361470428366851853047 327107042205642550277779571)
          ·
            refine ⟨490660563308463825416669357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327107042205642550277779571 490660563308463825416669357)
            ·
              refine ⟨183997711240673934531251009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 490660563308463825416669357 183997711240673934531251009)
              ·
                refine ⟨137998283430505450898438257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183997711240673934531251009 137998283430505450898438257)
                ·
                  refine ⟨103498712572879088173828693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137998283430505450898438257 103498712572879088173828693)
                  ·
                    refine ⟨1212875537963426814537055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103498712572879088173828693 1212875537963426814537055)
                    ·
                      rfl

theorem cell23_7086200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_7086200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086200 prefixEnd_7086200 := by exact prefixLift 7086200
  have htrace : WordTrace (prefixWord ++ tailWord_7086200) baseStart_7086200 baseEnd_7086200 := by
    simpa [prefixWord, tailWord_7086200, baseEnd_7086200] using wordTrace_append hprefix tailTrace_7086200
  have hstable : (prefixWord ++ tailWord_7086200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086200).length < 2 ^ (prefixWord ++ tailWord_7086200).sum := by decide
  have hdescent : baseEnd_7086200 < baseStart_7086200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086237 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_7086237 : Nat := 118140960795 + 7086237 * 2 ^ 59
def prefixEnd_7086237 : Nat := 4983230072969 + 3 ^ 40 * 7086237 * 2
def baseEnd_7086237 : Nat := 3638645612674496798848495

theorem tailTrace_7086237 : CollatzResearch.WordTrace tailWord_7086237 prefixEnd_7086237 3638645612674496798848495 := by
  unfold tailWord_7086237
  simp only [CollatzResearch.WordTrace]
  refine ⟨258456296428781056773144965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172304197619187371182096643 258456296428781056773144965)
  ·
    refine ⟨48460555580396448144964681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258456296428781056773144965 48460555580396448144964681)
    ·
      refine ⟨36345416685297336108723511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48460555580396448144964681 36345416685297336108723511)
      ·
        refine ⟨54518125027946004163085267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36345416685297336108723511 54518125027946004163085267)
        ·
          refine ⟨81777187541919006244627901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54518125027946004163085267 81777187541919006244627901)
          ·
            refine ⟨30666445328219627341735463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81777187541919006244627901 30666445328219627341735463)
            ·
              refine ⟨45999667992329441012603195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30666445328219627341735463 45999667992329441012603195)
              ·
                refine ⟨68999501988494161518904793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45999667992329441012603195 68999501988494161518904793)
                ·
                  refine ⟨51749626491370621139178595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68999501988494161518904793 51749626491370621139178595)
                  ·
                    refine ⟨77624439737055931708767893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51749626491370621139178595 77624439737055931708767893)
                    ·
                      refine ⟨3638645612674496798848495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77624439737055931708767893 3638645612674496798848495)
                      ·
                        rfl

theorem cell23_7086237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_7086237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086237 prefixEnd_7086237 := by exact prefixLift 7086237
  have htrace : WordTrace (prefixWord ++ tailWord_7086237) baseStart_7086237 baseEnd_7086237 := by
    simpa [prefixWord, tailWord_7086237, baseEnd_7086237] using wordTrace_append hprefix tailTrace_7086237
  have hstable : (prefixWord ++ tailWord_7086237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086237).length < 2 ^ (prefixWord ++ tailWord_7086237).sum := by decide
  have hdescent : baseEnd_7086237 < baseStart_7086237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086264 : List Nat := [2, 1, 2, 1, 2, 1, 7, 1, 6]
def baseStart_7086264 : Nat := 118140960795 + 7086264 * 2 ^ 59
def prefixEnd_7086264 : Nat := 4983230072969 + 3 ^ 40 * 7086264 * 2
def baseEnd_7086264 : Nat := 404295497405796465912319

theorem tailTrace_7086264 : CollatzResearch.WordTrace tailWord_7086264 prefixEnd_7086264 404295497405796465912319 := by
  unfold tailWord_7086264
  simp only [CollatzResearch.WordTrace]
  refine ⟨129228640599841620192188923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172304854133122160256251897 129228640599841620192188923)
  ·
    refine ⟨193842960899762430288283385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129228640599841620192188923 193842960899762430288283385)
    ·
      refine ⟨145382220674821822716212539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193842960899762430288283385 145382220674821822716212539)
      ·
        refine ⟨218073331012232734074318809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145382220674821822716212539 218073331012232734074318809)
        ·
          refine ⟨163554998259174550555739107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218073331012232734074318809 163554998259174550555739107)
          ·
            refine ⟨245332497388761825833608661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163554998259174550555739107 245332497388761825833608661)
            ·
              refine ⟨5749980407549105292975203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 245332497388761825833608661 5749980407549105292975203)
              ·
                refine ⟨8624970611323657939462805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5749980407549105292975203 8624970611323657939462805)
                ·
                  refine ⟨404295497405796465912319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8624970611323657939462805 404295497405796465912319)
                  ·
                    rfl

theorem cell23_7086264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 6].length) (baseStart_7086264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086264 prefixEnd_7086264 := by exact prefixLift 7086264
  have htrace : WordTrace (prefixWord ++ tailWord_7086264) baseStart_7086264 baseEnd_7086264 := by
    simpa [prefixWord, tailWord_7086264, baseEnd_7086264] using wordTrace_append hprefix tailTrace_7086264
  have hstable : (prefixWord ++ tailWord_7086264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086264).length < 2 ^ (prefixWord ++ tailWord_7086264).sum := by decide
  have hdescent : baseEnd_7086264 < baseStart_7086264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086277 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 3, 5]
def baseStart_7086277 : Nat := 118140960795 + 7086277 * 2 ^ 59
def prefixEnd_7086277 : Nat := 4983230072969 + 3 ^ 40 * 7086277 * 2
def baseEnd_7086277 : Nat := 1212888717300225547449437

theorem tailTrace_7086277 : CollatzResearch.WordTrace tailWord_7086277 prefixEnd_7086277 1212888717300225547449437 := by
  unfold tailWord_7086277
  simp only [CollatzResearch.WordTrace]
  refine ⟨258457755348636143604601085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172305170232424095736400723 258457755348636143604601085)
  ·
    refine ⟨96921658255738553851725407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258457755348636143604601085 96921658255738553851725407)
    ·
      refine ⟨145382487383607830777588111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96921658255738553851725407 145382487383607830777588111)
      ·
        refine ⟨218073731075411746166382167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145382487383607830777588111 218073731075411746166382167)
        ·
          refine ⟨327110596613117619249573251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218073731075411746166382167 327110596613117619249573251)
          ·
            refine ⟨490665894919676428874359877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327110596613117619249573251 490665894919676428874359877)
            ·
              refine ⟨91999855297439330413942477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 490665894919676428874359877 91999855297439330413942477)
              ·
                refine ⟨34499945736539748905228429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91999855297439330413942477 34499945736539748905228429)
                ·
                  refine ⟨12937479651202405839460661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34499945736539748905228429 12937479651202405839460661)
                  ·
                    refine ⟨1212888717300225547449437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12937479651202405839460661 1212888717300225547449437)
                    ·
                      rfl

theorem cell23_7086277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_7086277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086277 prefixEnd_7086277 := by exact prefixLift 7086277
  have htrace : WordTrace (prefixWord ++ tailWord_7086277) baseStart_7086277 baseEnd_7086277 := by
    simpa [prefixWord, tailWord_7086277, baseEnd_7086277] using wordTrace_append hprefix tailTrace_7086277
  have hstable : (prefixWord ++ tailWord_7086277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086277).length < 2 ^ (prefixWord ++ tailWord_7086277).sum := by decide
  have hdescent : baseEnd_7086277 < baseStart_7086277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086314 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_7086314 : Nat := 118140960795 + 7086314 * 2 ^ 59
def prefixEnd_7086314 : Nat := 4983230072969 + 3 ^ 40 * 7086314 * 2
def baseEnd_7086314 : Nat := 3638685150684892997585641

theorem tailTrace_7086314 : CollatzResearch.WordTrace tailWord_7086314 prefixEnd_7086314 3638685150684892997585641 := by
  unfold tailWord_7086314
  simp only [CollatzResearch.WordTrace]
  refine ⟨64614776212375524730924499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172306069899668065949131997 64614776212375524730924499)
  ·
    refine ⟨96922164318563287096386749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64614776212375524730924499 96922164318563287096386749)
    ·
      refine ⟨36345811619461232661145031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96922164318563287096386749 36345811619461232661145031)
      ·
        refine ⟨54518717429191848991717547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36345811619461232661145031 54518717429191848991717547)
        ·
          refine ⟨81778076143787773487576321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54518717429191848991717547 81778076143787773487576321)
          ·
            refine ⟨61333557107840830115682241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81778076143787773487576321 61333557107840830115682241)
            ·
              refine ⟨46000167830880622586761681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61333557107840830115682241 46000167830880622586761681)
              ·
                refine ⟨34500125873160466940071261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46000167830880622586761681 34500125873160466940071261)
                ·
                  refine ⟨12937547202435175102526723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34500125873160466940071261 12937547202435175102526723)
                  ·
                    refine ⟨19406320803652762653790085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12937547202435175102526723 19406320803652762653790085)
                    ·
                      refine ⟨3638685150684892997585641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19406320803652762653790085 3638685150684892997585641)
                      ·
                        rfl

theorem cell23_7086314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_7086314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086314 prefixEnd_7086314 := by exact prefixLift 7086314
  have htrace : WordTrace (prefixWord ++ tailWord_7086314) baseStart_7086314 baseEnd_7086314 := by
    simpa [prefixWord, tailWord_7086314, baseEnd_7086314] using wordTrace_append hprefix tailTrace_7086314
  have hstable : (prefixWord ++ tailWord_7086314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086314).length < 2 ^ (prefixWord ++ tailWord_7086314).sum := by decide
  have hdescent : baseEnd_7086314 < baseStart_7086314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086337 : List Nat := [1, 2, 4, 1, 1, 2, 1, 11]
def baseStart_7086337 : Nat := 118140960795 + 7086337 * 2 ^ 59
def prefixEnd_7086337 : Nat := 4983230072969 + 3 ^ 40 * 7086337 * 2
def baseEnd_7086337 : Nat := 134766554101479496577705

theorem tailTrace_7086337 : CollatzResearch.WordTrace tailWord_7086337 prefixEnd_7086337 134766554101479496577705 := by
  unfold tailWord_7086337
  simp only [CollatzResearch.WordTrace]
  refine ⟨258459943728418773851785265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172306629152279182567856843 258459943728418773851785265)
  ·
    refine ⟨193844957796314080388838949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258459943728418773851785265 193844957796314080388838949)
    ·
      refine ⟨36345929586808890072907303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193844957796314080388838949 36345929586808890072907303)
      ·
        refine ⟨54518894380213335109360955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36345929586808890072907303 54518894380213335109360955)
        ·
          refine ⟨81778341570320002664041433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54518894380213335109360955 81778341570320002664041433)
          ·
            refine ⟨61333756177740001998031075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81778341570320002664041433 61333756177740001998031075)
            ·
              refine ⟨92000634266610002997046613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61333756177740001998031075 92000634266610002997046613)
              ·
                refine ⟨134766554101479496577705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 92000634266610002997046613 134766554101479496577705)
                ·
                  rfl

theorem cell23_7086337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 11].length) (baseStart_7086337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086337 prefixEnd_7086337 := by exact prefixLift 7086337
  have htrace : WordTrace (prefixWord ++ tailWord_7086337) baseStart_7086337 baseEnd_7086337 := by
    simpa [prefixWord, tailWord_7086337, baseEnd_7086337] using wordTrace_append hprefix tailTrace_7086337
  have hstable : (prefixWord ++ tailWord_7086337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086337).length < 2 ^ (prefixWord ++ tailWord_7086337).sum := by decide
  have hdescent : baseEnd_7086337 < baseStart_7086337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086344 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_7086344 : Nat := 118140960795 + 7086344 * 2 ^ 59
def prefixEnd_7086344 : Nat := 4983230072969 + 3 ^ 40 * 7086344 * 2
def baseEnd_7086344 : Nat := 3638700555104527880210503

theorem tailTrace_7086344 : CollatzResearch.WordTrace tailWord_7086344 prefixEnd_7086344 3638700555104527880210503 := by
  unfold tailWord_7086344
  simp only [CollatzResearch.WordTrace]
  refine ⟨129230099519696707023645043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172306799359595609364860057 129230099519696707023645043)
  ·
    refine ⟨193845149279545060535467565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129230099519696707023645043 193845149279545060535467565)
    ·
      refine ⟨72691930979829397700800337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193845149279545060535467565 72691930979829397700800337)
      ·
        refine ⟨54518948234872048275600253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72691930979829397700800337 54518948234872048275600253)
        ·
          refine ⟨20444605588077018103350095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54518948234872048275600253 20444605588077018103350095)
          ·
            refine ⟨30666908382115527155025143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20444605588077018103350095 30666908382115527155025143)
            ·
              refine ⟨46000362573173290732537715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30666908382115527155025143 46000362573173290732537715)
              ·
                refine ⟨69000543859759936098806573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46000362573173290732537715 69000543859759936098806573)
                ·
                  refine ⟨25875203947409976037052465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69000543859759936098806573 25875203947409976037052465)
                  ·
                    refine ⟨19406402960557482027789349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25875203947409976037052465 19406402960557482027789349)
                    ·
                      refine ⟨3638700555104527880210503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19406402960557482027789349 3638700555104527880210503)
                      ·
                        rfl

theorem cell23_7086344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_7086344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086344 prefixEnd_7086344 := by exact prefixLift 7086344
  have htrace : WordTrace (prefixWord ++ tailWord_7086344) baseStart_7086344 baseEnd_7086344 := by
    simpa [prefixWord, tailWord_7086344, baseEnd_7086344] using wordTrace_append hprefix tailTrace_7086344
  have hstable : (prefixWord ++ tailWord_7086344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086344).length < 2 ^ (prefixWord ++ tailWord_7086344).sum := by decide
  have hdescent : baseEnd_7086344 < baseStart_7086344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086364 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_7086364 : Nat := 118140960795 + 7086364 * 2 ^ 59
def prefixEnd_7086364 : Nat := 4983230072969 + 3 ^ 40 * 7086364 * 2
def baseEnd_7086364 : Nat := 3638710824717617801960411

theorem tailTrace_7086364 : CollatzResearch.WordTrace tailWord_7086364 prefixEnd_7086364 3638710824717617801960411 := by
  unfold tailWord_7086364
  simp only [CollatzResearch.WordTrace]
  refine ⟨129230464249660478731509073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172307285666213971642012097 129230464249660478731509073)
  ·
    refine ⟨96922848187245359048631805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129230464249660478731509073 96922848187245359048631805)
    ·
      refine ⟨36346068070217009643236927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96922848187245359048631805 36346068070217009643236927)
      ·
        refine ⟨54519102105325514464855391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36346068070217009643236927 54519102105325514464855391)
        ·
          refine ⟨81778653157988271697283087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54519102105325514464855391 81778653157988271697283087)
          ·
            refine ⟨122667979736982407545924631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81778653157988271697283087 122667979736982407545924631)
            ·
              refine ⟨184001969605473611318886947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122667979736982407545924631 184001969605473611318886947)
              ·
                refine ⟨276002954408210416978330421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184001969605473611318886947 276002954408210416978330421)
                ·
                  refine ⟨25875276975769726591718477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 276002954408210416978330421 25875276975769726591718477)
                  ·
                    refine ⟨9703228865913647471894429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25875276975769726591718477 9703228865913647471894429)
                    ·
                      refine ⟨3638710824717617801960411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9703228865913647471894429 3638710824717617801960411)
                      ·
                        rfl

theorem cell23_7086364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_7086364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086364 prefixEnd_7086364 := by exact prefixLift 7086364
  have htrace : WordTrace (prefixWord ++ tailWord_7086364) baseStart_7086364 baseEnd_7086364 := by
    simpa [prefixWord, tailWord_7086364, baseEnd_7086364] using wordTrace_append hprefix tailTrace_7086364
  have hstable : (prefixWord ++ tailWord_7086364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086364).length < 2 ^ (prefixWord ++ tailWord_7086364).sum := by decide
  have hdescent : baseEnd_7086364 < baseStart_7086364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086375 : List Nat := [1, 1, 8, 1, 1, 1, 2, 1, 1, 6]
def baseStart_7086375 : Nat := 118140960795 + 7086375 * 2 ^ 59
def prefixEnd_7086375 : Nat := 4983230072969 + 3 ^ 40 * 7086375 * 2
def baseEnd_7086375 : Nat := 1212905491001605752974287

theorem tailTrace_7086375 : CollatzResearch.WordTrace tailWord_7086375 prefixEnd_7086375 1212905491001605752974287 := by
  unfold tailWord_7086375
  simp only [CollatzResearch.WordTrace]
  refine ⟨258461329702281106341668579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172307553134854070894445719 258461329702281106341668579)
  ·
    refine ⟨387691994553421659512502869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258461329702281106341668579 387691994553421659512502869)
    ·
      refine ⟨4543265561172910072412143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 387691994553421659512502869 4543265561172910072412143)
      ·
        refine ⟨6814898341759365108618215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4543265561172910072412143 6814898341759365108618215)
        ·
          refine ⟨10222347512639047662927323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6814898341759365108618215 10222347512639047662927323)
          ·
            refine ⟨15333521268958571494390985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10222347512639047662927323 15333521268958571494390985)
            ·
              refine ⟨11500140951718928620793239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15333521268958571494390985 11500140951718928620793239)
              ·
                refine ⟨17250211427578392931189859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11500140951718928620793239 17250211427578392931189859)
                ·
                  refine ⟨25875317141367589396784789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17250211427578392931189859 25875317141367589396784789)
                  ·
                    refine ⟨1212905491001605752974287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25875317141367589396784789 1212905491001605752974287)
                    ·
                      rfl

theorem cell23_7086375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_7086375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086375 prefixEnd_7086375 := by exact prefixLift 7086375
  have htrace : WordTrace (prefixWord ++ tailWord_7086375) baseStart_7086375 baseEnd_7086375 := by
    simpa [prefixWord, tailWord_7086375, baseEnd_7086375] using wordTrace_append hprefix tailTrace_7086375
  have hstable : (prefixWord ++ tailWord_7086375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086375).length < 2 ^ (prefixWord ++ tailWord_7086375).sum := by decide
  have hdescent : baseEnd_7086375 < baseStart_7086375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086378 : List Nat := [3, 1, 4, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_7086378 : Nat := 118140960795 + 7086378 * 2 ^ 59
def prefixEnd_7086378 : Nat := 4983230072969 + 3 ^ 40 * 7086378 * 2
def baseEnd_7086378 : Nat := 3638718013446780747185347

theorem tailTrace_7086378 : CollatzResearch.WordTrace tailWord_7086378 prefixEnd_7086378 3638718013446780747185347 := by
  unfold tailWord_7086378
  simp only [CollatzResearch.WordTrace]
  refine ⟨64615359780317559463506947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172307626080846825236018525 64615359780317559463506947)
  ·
    refine ⟨96923039670476339195260421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64615359780317559463506947 96923039670476339195260421)
    ·
      refine ⟨18173069938214313599111329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96923039670476339195260421 18173069938214313599111329)
      ·
        refine ⟨13629802453660735199333497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18173069938214313599111329 13629802453660735199333497)
        ·
          refine ⟨10222351840245551399500123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13629802453660735199333497 10222351840245551399500123)
          ·
            refine ⟨15333527760368327099250185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10222351840245551399500123 15333527760368327099250185)
            ·
              refine ⟨11500145820276245324437639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15333527760368327099250185 11500145820276245324437639)
              ·
                refine ⟨17250218730414367986656459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11500145820276245324437639 17250218730414367986656459)
                ·
                  refine ⟨25875328095621551979984689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17250218730414367986656459 25875328095621551979984689)
                  ·
                    refine ⟨19406496071716163984988517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25875328095621551979984689 19406496071716163984988517)
                    ·
                      refine ⟨3638718013446780747185347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19406496071716163984988517 3638718013446780747185347)
                      ·
                        rfl

theorem cell23_7086378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_7086378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086378 prefixEnd_7086378 := by exact prefixLift 7086378
  have htrace : WordTrace (prefixWord ++ tailWord_7086378) baseStart_7086378 baseEnd_7086378 := by
    simpa [prefixWord, tailWord_7086378, baseEnd_7086378] using wordTrace_append hprefix tailTrace_7086378
  have hstable : (prefixWord ++ tailWord_7086378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086378).length < 2 ^ (prefixWord ++ tailWord_7086378).sum := by decide
  have hdescent : baseEnd_7086378 < baseStart_7086378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086382 : List Nat := [4, 1, 3, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_7086382 : Nat := 118140960795 + 7086382 * 2 ^ 59
def prefixEnd_7086382 : Nat := 4983230072969 + 3 ^ 40 * 7086382 * 2
def baseEnd_7086382 : Nat := 3638720067369398731535329

theorem tailTrace_7086382 : CollatzResearch.WordTrace tailWord_7086382 prefixEnd_7086382 3638720067369398731535329 := by
  unfold tailWord_7086382
  simp only [CollatzResearch.WordTrace]
  refine ⟨32307698126656968317146675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172307723342170497691448933 32307698126656968317146675)
  ·
    refine ⟨48461547189985452475720013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32307698126656968317146675 48461547189985452475720013)
    ·
      refine ⟨18173080196244544678395005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48461547189985452475720013 18173080196244544678395005)
      ·
        refine ⟨6814905073591704254398127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18173080196244544678395005 6814905073591704254398127)
        ·
          refine ⟨10222357610387556381597191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6814905073591704254398127 10222357610387556381597191)
          ·
            refine ⟨15333536415581334572395787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10222357610387556381597191 15333536415581334572395787)
            ·
              refine ⟨23000304623372001858593681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15333536415581334572395787 23000304623372001858593681)
              ·
                refine ⟨17250228467529001393945261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23000304623372001858593681 17250228467529001393945261)
                ·
                  refine ⟨6468835675323375522729473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17250228467529001393945261 6468835675323375522729473)
                  ·
                    refine ⟨4851626756492531642047105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6468835675323375522729473 4851626756492531642047105)
                    ·
                      refine ⟨3638720067369398731535329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4851626756492531642047105 3638720067369398731535329)
                      ·
                        rfl

theorem cell23_7086382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_7086382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086382 prefixEnd_7086382 := by exact prefixLift 7086382
  have htrace : WordTrace (prefixWord ++ tailWord_7086382) baseStart_7086382 baseEnd_7086382 := by
    simpa [prefixWord, tailWord_7086382, baseEnd_7086382] using wordTrace_append hprefix tailTrace_7086382
  have hstable : (prefixWord ++ tailWord_7086382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086382).length < 2 ^ (prefixWord ++ tailWord_7086382).sum := by decide
  have hdescent : baseEnd_7086382 < baseStart_7086382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086424 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 2, 4, 3]
def baseStart_7086424 : Nat := 118140960795 + 7086424 * 2 ^ 59
def prefixEnd_7086424 : Nat := 4983230072969 + 3 ^ 40 * 7086424 * 2
def baseEnd_7086424 : Nat := 3638741633556887567210135

theorem tailTrace_7086424 : CollatzResearch.WordTrace tailWord_7086424 prefixEnd_7086424 3638741633556887567210135 := by
  unfold tailWord_7086424
  simp only [CollatzResearch.WordTrace]
  refine ⟨129231558439551793855101163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172308744586069058473468217 129231558439551793855101163)
  ·
    refine ⟨193847337659327690782651745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129231558439551793855101163 193847337659327690782651745)
    ·
      refine ⟨145385503244495768086988809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193847337659327690782651745 145385503244495768086988809)
      ·
        refine ⟨109039127433371826065241607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145385503244495768086988809 109039127433371826065241607)
        ·
          refine ⟨163558691150057739097862411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109039127433371826065241607 163558691150057739097862411)
          ·
            refine ⟨245338036725086608646793617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163558691150057739097862411 245338036725086608646793617)
            ·
              refine ⟨184003527543814956485095213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245338036725086608646793617 184003527543814956485095213)
              ·
                refine ⟨69001322828930608681910705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184003527543814956485095213 69001322828930608681910705)
                ·
                  refine ⟨51750992121697956511433029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69001322828930608681910705 51750992121697956511433029)
                  ·
                    refine ⟨9703311022818366845893693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51750992121697956511433029 9703311022818366845893693)
                    ·
                      refine ⟨3638741633556887567210135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9703311022818366845893693 3638741633556887567210135)
                      ·
                        rfl

theorem cell23_7086424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_7086424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086424 prefixEnd_7086424 := by exact prefixLift 7086424
  have htrace : WordTrace (prefixWord ++ tailWord_7086424) baseStart_7086424 baseEnd_7086424 := by
    simpa [prefixWord, tailWord_7086424, baseEnd_7086424] using wordTrace_append hprefix tailTrace_7086424
  have hstable : (prefixWord ++ tailWord_7086424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086424).length < 2 ^ (prefixWord ++ tailWord_7086424).sum := by decide
  have hdescent : baseEnd_7086424 < baseStart_7086424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086478 : List Nat := [4, 1, 1, 4, 1, 3, 1, 1, 7]
def baseStart_7086478 : Nat := 118140960795 + 7086478 * 2 ^ 59
def prefixEnd_7086478 : Nat := 4983230072969 + 3 ^ 40 * 7086478 * 2
def baseEnd_7086478 : Nat := 404307706834692261770543

theorem tailTrace_7086478 : CollatzResearch.WordTrace tailWord_7086478 prefixEnd_7086478 404307706834692261770543 := by
  unfold tailWord_7086478
  simp only [CollatzResearch.WordTrace]
  refine ⟨32308135802613494366583511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172310057613938636621778725 32308135802613494366583511)
  ·
    refine ⟨48462203703920241549875267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32308135802613494366583511 48462203703920241549875267)
    ·
      refine ⟨72693305555880362324812901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48462203703920241549875267 72693305555880362324812901)
      ·
        refine ⟨13629994791727567935902419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72693305555880362324812901 13629994791727567935902419)
        ·
          refine ⟨20444992187591351903853629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13629994791727567935902419 20444992187591351903853629)
          ·
            refine ⟨7666872070346756963945111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20444992187591351903853629 7666872070346756963945111)
            ·
              refine ⟨11500308105520135445917667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7666872070346756963945111 11500308105520135445917667)
              ·
                refine ⟨17250462158280203168876501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11500308105520135445917667 17250462158280203168876501)
                ·
                  refine ⟨404307706834692261770543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17250462158280203168876501 404307706834692261770543)
                  ·
                    rfl

theorem cell23_7086478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_7086478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086478 prefixEnd_7086478 := by exact prefixLift 7086478
  have htrace : WordTrace (prefixWord ++ tailWord_7086478) baseStart_7086478 baseEnd_7086478 := by
    simpa [prefixWord, tailWord_7086478, baseEnd_7086478] using wordTrace_append hprefix tailTrace_7086478
  have hstable : (prefixWord ++ tailWord_7086478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086478).length < 2 ^ (prefixWord ++ tailWord_7086478).sum := by decide
  have hdescent : baseEnd_7086478 < baseStart_7086478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086511 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 6, 4, 2]
def baseStart_7086511 : Nat := 118140960795 + 7086511 * 2 ^ 59
def prefixEnd_7086511 : Nat := 4983230072969 + 3 ^ 40 * 7086511 * 2
def baseEnd_7086511 : Nat := 3638786306373828726822235

theorem tailTrace_7086511 : CollatzResearch.WordTrace tailWord_7086511 prefixEnd_7086511 3638786306373828726822235 := by
  unfold tailWord_7086511
  simp only [CollatzResearch.WordTrace]
  refine ⟨258466290029788401568619387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172310860019858934379079591 258466290029788401568619387)
  ·
    refine ⟨387699435044682602352929081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258466290029788401568619387 387699435044682602352929081)
    ·
      refine ⟨290774576283511951764696811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387699435044682602352929081 290774576283511951764696811)
      ·
        refine ⟨436161864425267927647045217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290774576283511951764696811 436161864425267927647045217)
        ·
          refine ⟨327121398318950945735283913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436161864425267927647045217 327121398318950945735283913)
          ·
            refine ⟨245341048739213209301462935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327121398318950945735283913 245341048739213209301462935)
            ·
              refine ⟨368011573108819813952194403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245341048739213209301462935 368011573108819813952194403)
              ·
                refine ⟨552017359663229720928291605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368011573108819813952194403 552017359663229720928291605)
                ·
                  refine ⟨25875813734213893168513669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 552017359663229720928291605 25875813734213893168513669)
                  ·
                    refine ⟨4851715075165104969096313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25875813734213893168513669 4851715075165104969096313)
                    ·
                      refine ⟨3638786306373828726822235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4851715075165104969096313 3638786306373828726822235)
                      ·
                        rfl

theorem cell23_7086511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 4, 2].length) (baseStart_7086511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086511 prefixEnd_7086511 := by exact prefixLift 7086511
  have htrace : WordTrace (prefixWord ++ tailWord_7086511) baseStart_7086511 baseEnd_7086511 := by
    simpa [prefixWord, tailWord_7086511, baseEnd_7086511] using wordTrace_append hprefix tailTrace_7086511
  have hstable : (prefixWord ++ tailWord_7086511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086511).length < 2 ^ (prefixWord ++ tailWord_7086511).sum := by decide
  have hdescent : baseEnd_7086511 < baseStart_7086511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086588 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 4, 3, 2]
def baseStart_7086588 : Nat := 118140960795 + 7086588 * 2 ^ 59
def prefixEnd_7086588 : Nat := 4983230072969 + 3 ^ 40 * 7086588 * 2
def baseEnd_7086588 : Nat := 3638825844384224925559381

theorem tailTrace_7086588 : CollatzResearch.WordTrace tailWord_7086588 prefixEnd_7086588 3638825844384224925559381 := by
  unfold tailWord_7086588
  simp only [CollatzResearch.WordTrace]
  refine ⟨129234549225254721859586209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172312732300339629146114945 129234549225254721859586209)
  ·
    refine ⟨96925911918941041394689657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129234549225254721859586209 96925911918941041394689657)
    ·
      refine ⟨72694433939205781046017243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96925911918941041394689657 72694433939205781046017243)
      ·
        refine ⟨109041650908808671569025865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72694433939205781046017243 109041650908808671569025865)
        ·
          refine ⟨81781238181606503676769399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109041650908808671569025865 81781238181606503676769399)
          ·
            refine ⟨122671857272409755515154099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81781238181606503676769399 122671857272409755515154099)
            ·
              refine ⟨184007785908614633272731149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122671857272409755515154099 184007785908614633272731149)
              ·
                refine ⟨69002919715730487477274181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184007785908614633272731149 69002919715730487477274181)
                ·
                  refine ⟨12938047446699466401988909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69002919715730487477274181 12938047446699466401988909)
                  ·
                    refine ⟨4851767792512299900745841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12938047446699466401988909 4851767792512299900745841)
                    ·
                      refine ⟨3638825844384224925559381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4851767792512299900745841 3638825844384224925559381)
                      ·
                        rfl

theorem cell23_7086588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_7086588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086588 prefixEnd_7086588 := by exact prefixLift 7086588
  have htrace : WordTrace (prefixWord ++ tailWord_7086588) baseStart_7086588 baseEnd_7086588 := by
    simpa [prefixWord, tailWord_7086588, baseEnd_7086588] using wordTrace_append hprefix tailTrace_7086588
  have hstable : (prefixWord ++ tailWord_7086588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086588).length < 2 ^ (prefixWord ++ tailWord_7086588).sum := by decide
  have hdescent : baseEnd_7086588 < baseStart_7086588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086595 : List Nat := [1, 1, 1, 3, 2, 1, 3, 6, 1, 1, 3]
def baseStart_7086595 : Nat := 118140960795 + 7086595 * 2 ^ 59
def prefixEnd_7086595 : Nat := 4983230072969 + 3 ^ 40 * 7086595 * 2
def baseEnd_7086595 : Nat := 3638829438748806398171849

theorem tailTrace_7086595 : CollatzResearch.WordTrace tailWord_7086595 prefixEnd_7086595 3638829438748806398171849 := by
  unfold tailWord_7086595
  simp only [CollatzResearch.WordTrace]
  refine ⟨258469353761484083914677239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172312902507656055943118159 258469353761484083914677239)
  ·
    refine ⟨387704030642226125872015859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258469353761484083914677239 387704030642226125872015859)
    ·
      refine ⟨581556045963339188808023789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387704030642226125872015859 581556045963339188808023789)
      ·
        refine ⟨218083517236252195803008921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 581556045963339188808023789 218083517236252195803008921)
        ·
          refine ⟨163562637927189146852256691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218083517236252195803008921 163562637927189146852256691)
          ·
            refine ⟨245343956890783720278385037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163562637927189146852256691 245343956890783720278385037)
            ·
              refine ⟨92003983834043895104394389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245343956890783720278385037 92003983834043895104394389)
              ·
                refine ⟨4312686742220807583018487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92003983834043895104394389 4312686742220807583018487)
                ·
                  refine ⟨6469030113331211374527731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4312686742220807583018487 6469030113331211374527731)
                  ·
                    refine ⟨9703545169996817061791597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6469030113331211374527731 9703545169996817061791597)
                    ·
                      refine ⟨3638829438748806398171849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9703545169996817061791597 3638829438748806398171849)
                      ·
                        rfl

theorem cell23_7086595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 1, 1, 3].length) (baseStart_7086595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086595 prefixEnd_7086595 := by exact prefixLift 7086595
  have htrace : WordTrace (prefixWord ++ tailWord_7086595) baseStart_7086595 baseEnd_7086595 := by
    simpa [prefixWord, tailWord_7086595, baseEnd_7086595] using wordTrace_append hprefix tailTrace_7086595
  have hstable : (prefixWord ++ tailWord_7086595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086595).length < 2 ^ (prefixWord ++ tailWord_7086595).sum := by decide
  have hdescent : baseEnd_7086595 < baseStart_7086595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086601 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 3, 1, 4]
def baseStart_7086601 : Nat := 118140960795 + 7086601 * 2 ^ 59
def prefixEnd_7086601 : Nat := 4983230072969 + 3 ^ 40 * 7086601 * 2
def baseEnd_7086601 : Nat := 3638832519632733374696821

theorem tailTrace_7086601 : CollatzResearch.WordTrace tailWord_7086601 prefixEnd_7086601 3638832519632733374696821 := by
  unfold tailWord_7086601
  simp only [CollatzResearch.WordTrace]
  refine ⟨258469572599462346939395657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172313048399641564626263771 258469572599462346939395657)
  ·
    refine ⟨193852179449596760204546743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258469572599462346939395657 193852179449596760204546743)
    ·
      refine ⟨290778269174395140306820115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193852179449596760204546743 290778269174395140306820115)
      ·
        refine ⟨436167403761592710460230173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290778269174395140306820115 436167403761592710460230173)
        ·
          refine ⟨163562776410597266422586315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436167403761592710460230173 163562776410597266422586315)
          ·
            refine ⟨245344164615895899633879473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163562776410597266422586315 245344164615895899633879473)
            ·
              refine ⟨184008123461921924725409605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245344164615895899633879473 184008123461921924725409605)
              ·
                refine ⟨34501523149110360886014301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184008123461921924725409605 34501523149110360886014301)
                ·
                  refine ⟨12938071180916385332255363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34501523149110360886014301 12938071180916385332255363)
                  ·
                    refine ⟨19407106771374577998383045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12938071180916385332255363 19407106771374577998383045)
                    ·
                      refine ⟨3638832519632733374696821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19407106771374577998383045 3638832519632733374696821)
                      ·
                        rfl

theorem cell23_7086601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 1, 4].length) (baseStart_7086601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086601 prefixEnd_7086601 := by exact prefixLift 7086601
  have htrace : WordTrace (prefixWord ++ tailWord_7086601) baseStart_7086601 baseEnd_7086601 := by
    simpa [prefixWord, tailWord_7086601, baseEnd_7086601] using wordTrace_append hprefix tailTrace_7086601
  have hstable : (prefixWord ++ tailWord_7086601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086601).length < 2 ^ (prefixWord ++ tailWord_7086601).sum := by decide
  have hdescent : baseEnd_7086601 < baseStart_7086601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086612 : List Nat := [2, 4, 3, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_7086612 : Nat := 118140960795 + 7086612 * 2 ^ 59
def prefixEnd_7086612 : Nat := 4983230072969 + 3 ^ 40 * 7086612 * 2
def baseEnd_7086612 : Nat := 3638838167919932831659271

theorem tailTrace_7086612 : CollatzResearch.WordTrace tailWord_7086612 prefixEnd_7086612 3638838167919932831659271 := by
  unfold tailWord_7086612
  simp only [CollatzResearch.WordTrace]
  refine ⟨129234986901211247909023045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172313315868281663878697393 129234986901211247909023045)
  ·
    refine ⟨24231560043977108982941821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129234986901211247909023045 24231560043977108982941821)
    ·
      refine ⟨9086835016491415868603183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24231560043977108982941821 9086835016491415868603183)
      ·
        refine ⟨13630252524737123802904775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9086835016491415868603183 13630252524737123802904775)
        ·
          refine ⟨20445378787105685704357163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13630252524737123802904775 20445378787105685704357163)
          ·
            refine ⟨30668068180658528556535745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20445378787105685704357163 30668068180658528556535745)
            ·
              refine ⟨23001051135493896417401809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30668068180658528556535745 23001051135493896417401809)
              ·
                refine ⟨17250788351620422313051357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23001051135493896417401809 17250788351620422313051357)
                ·
                  refine ⟨6469045631857658367394259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17250788351620422313051357 6469045631857658367394259)
                  ·
                    refine ⟨9703568447786487551091389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6469045631857658367394259 9703568447786487551091389)
                    ·
                      refine ⟨3638838167919932831659271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9703568447786487551091389 3638838167919932831659271)
                      ·
                        rfl

theorem cell23_7086612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_7086612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086612 prefixEnd_7086612 := by exact prefixLift 7086612
  have htrace : WordTrace (prefixWord ++ tailWord_7086612) baseStart_7086612 baseEnd_7086612 := by
    simpa [prefixWord, tailWord_7086612, baseEnd_7086612] using wordTrace_append hprefix tailTrace_7086612
  have hstable : (prefixWord ++ tailWord_7086612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086612).length < 2 ^ (prefixWord ++ tailWord_7086612).sum := by decide
  have hdescent : baseEnd_7086612 < baseStart_7086612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086618 : List Nat := [3, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4]
def baseStart_7086618 : Nat := 118140960795 + 7086618 * 2 ^ 59
def prefixEnd_7086618 : Nat := 4983230072969 + 3 ^ 40 * 7086618 * 2
def baseEnd_7086618 : Nat := 3638841248803859808184243

theorem tailTrace_7086618 : CollatzResearch.WordTrace tailWord_7086618 prefixEnd_7086618 3638841248803859808184243 := by
  unfold tailWord_7086618
  simp only [CollatzResearch.WordTrace]
  refine ⟨64617548160100189710691127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172313461760267172561843005 64617548160100189710691127)
  ·
    refine ⟨96926322240150284566036691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64617548160100189710691127 96926322240150284566036691)
    ·
      refine ⟨145389483360225426849055037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96926322240150284566036691 145389483360225426849055037)
      ·
        refine ⟨54521056260084535068395639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145389483360225426849055037 54521056260084535068395639)
        ·
          refine ⟨81781584390126802602593459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54521056260084535068395639 81781584390126802602593459)
          ·
            refine ⟨122672376585190203903890189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81781584390126802602593459 122672376585190203903890189)
            ·
              refine ⟨46002141219446326463958821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122672376585190203903890189 46002141219446326463958821)
              ·
                refine ⟨8625401478646186211992279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46002141219446326463958821 8625401478646186211992279)
                ·
                  refine ⟨12938102217969279317988419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8625401478646186211992279 12938102217969279317988419)
                  ·
                    refine ⟨19407153326953918976982629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12938102217969279317988419 19407153326953918976982629)
                    ·
                      refine ⟨3638841248803859808184243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19407153326953918976982629 3638841248803859808184243)
                      ·
                        rfl

theorem cell23_7086618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_7086618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086618 prefixEnd_7086618 := by exact prefixLift 7086618
  have htrace : WordTrace (prefixWord ++ tailWord_7086618) baseStart_7086618 baseEnd_7086618 := by
    simpa [prefixWord, tailWord_7086618, baseEnd_7086618] using wordTrace_append hprefix tailTrace_7086618
  have hstable : (prefixWord ++ tailWord_7086618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086618).length < 2 ^ (prefixWord ++ tailWord_7086618).sum := by decide
  have hdescent : baseEnd_7086618 < baseStart_7086618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086646 : List Nat := [5, 1, 2, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_7086646 : Nat := 118140960795 + 7086646 * 2 ^ 59
def prefixEnd_7086646 : Nat := 4983230072969 + 3 ^ 40 * 7086646 * 2
def baseEnd_7086646 : Nat := 3638855626262185698634115

theorem tailTrace_7086646 : CollatzResearch.WordTrace tailWord_7086646 prefixEnd_7086646 3638855626262185698634115 := by
  unfold tailWord_7086646
  simp only [CollatzResearch.WordTrace]
  refine ⟨16154450867768707476548987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172314142589532879749855861 16154450867768707476548987)
  ·
    refine ⟨24231676301653061214823481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16154450867768707476548987 24231676301653061214823481)
    ·
      refine ⟨18173757226239795911117611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24231676301653061214823481 18173757226239795911117611)
      ·
        refine ⟨27260635839359693866676417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18173757226239795911117611 27260635839359693866676417)
        ·
          refine ⟨20445476879519770400007313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27260635839359693866676417 20445476879519770400007313)
          ·
            refine ⟨15334107659639827800005485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20445476879519770400007313 15334107659639827800005485)
            ·
              refine ⟨5750290372364935425002057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15334107659639827800005485 5750290372364935425002057)
              ·
                refine ⟨4312717779273701568751543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5750290372364935425002057 4312717779273701568751543)
                ·
                  refine ⟨6469076668910552353127315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4312717779273701568751543 6469076668910552353127315)
                  ·
                    refine ⟨9703615003365828529690973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6469076668910552353127315 9703615003365828529690973)
                    ·
                      refine ⟨3638855626262185698634115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9703615003365828529690973 3638855626262185698634115)
                      ·
                        rfl

theorem cell23_7086646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_7086646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086646 prefixEnd_7086646 := by exact prefixLift 7086646
  have htrace : WordTrace (prefixWord ++ tailWord_7086646) baseStart_7086646 baseEnd_7086646 := by
    simpa [prefixWord, tailWord_7086646, baseEnd_7086646] using wordTrace_append hprefix tailTrace_7086646
  have hstable : (prefixWord ++ tailWord_7086646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086646).length < 2 ^ (prefixWord ++ tailWord_7086646).sum := by decide
  have hdescent : baseEnd_7086646 < baseStart_7086646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086652 : List Nat := [2, 2, 2, 2, 3, 1, 3, 1, 3, 2, 2]
def baseStart_7086652 : Nat := 118140960795 + 7086652 * 2 ^ 59
def prefixEnd_7086652 : Nat := 4983230072969 + 3 ^ 40 * 7086652 * 2
def baseEnd_7086652 : Nat := 3638858707146112675159087

theorem tailTrace_7086652 : CollatzResearch.WordTrace tailWord_7086652 prefixEnd_7086652 3638858707146112675159087 := by
  unfold tailWord_7086652
  simp only [CollatzResearch.WordTrace]
  refine ⟨129235716361138791324751105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172314288481518388433001473 129235716361138791324751105)
  ·
    refine ⟨96926787270854093493563329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129235716361138791324751105 96926787270854093493563329)
    ·
      refine ⟨72695090453140570120172497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96926787270854093493563329 72695090453140570120172497)
      ·
        refine ⟨54521317839855427590129373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72695090453140570120172497 54521317839855427590129373)
        ·
          refine ⟨20445494189945785346298515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54521317839855427590129373 20445494189945785346298515)
          ·
            refine ⟨30668241284918678019447773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20445494189945785346298515 30668241284918678019447773)
            ·
              refine ⟨11500590481844504257292915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30668241284918678019447773 11500590481844504257292915)
              ·
                refine ⟨17250885722766756385939373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11500590481844504257292915 17250885722766756385939373)
                ·
                  refine ⟨6469082146037533644727265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17250885722766756385939373 6469082146037533644727265)
                  ·
                    refine ⟨4851811609528150233545449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6469082146037533644727265 4851811609528150233545449)
                    ·
                      refine ⟨3638858707146112675159087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4851811609528150233545449 3638858707146112675159087)
                      ·
                        rfl

theorem cell23_7086652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_7086652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086652 prefixEnd_7086652 := by exact prefixLift 7086652
  have htrace : WordTrace (prefixWord ++ tailWord_7086652) baseStart_7086652 baseEnd_7086652 := by
    simpa [prefixWord, tailWord_7086652, baseEnd_7086652] using wordTrace_append hprefix tailTrace_7086652
  have hstable : (prefixWord ++ tailWord_7086652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086652).length < 2 ^ (prefixWord ++ tailWord_7086652).sum := by decide
  have hdescent : baseEnd_7086652 < baseStart_7086652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086668 : List Nat := [2, 2, 1, 3, 1, 2, 2, 3, 1, 3, 3]
def baseStart_7086668 : Nat := 118140960795 + 7086668 * 2 ^ 59
def prefixEnd_7086668 : Nat := 4983230072969 + 3 ^ 40 * 7086668 * 2
def baseEnd_7086668 : Nat := 3638866922836584612559013

theorem tailTrace_7086668 : CollatzResearch.WordTrace tailWord_7086668 prefixEnd_7086668 3638866922836584612559013 := by
  unfold tailWord_7086668
  simp only [CollatzResearch.WordTrace]
  refine ⟨129236008145109808691042329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172314677526813078254723105 129236008145109808691042329)
  ·
    refine ⟨96927006108832356518281747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129236008145109808691042329 96927006108832356518281747)
    ·
      refine ⟨145390509163248534777422621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96927006108832356518281747 145390509163248534777422621)
      ·
        refine ⟨54521440936218200541533483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145390509163248534777422621 54521440936218200541533483)
        ·
          refine ⟨81782161404327300812300225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54521440936218200541533483 81782161404327300812300225)
          ·
            refine ⟨61336621053245475609225169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81782161404327300812300225 61336621053245475609225169)
            ·
              refine ⟨46002465789934106706918877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61336621053245475609225169 46002465789934106706918877)
              ·
                refine ⟨17250924671225290015094579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46002465789934106706918877 17250924671225290015094579)
                ·
                  refine ⟨25876387006837935022641869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17250924671225290015094579 25876387006837935022641869)
                  ·
                    refine ⟨9703645127564225633490701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25876387006837935022641869 9703645127564225633490701)
                    ·
                      refine ⟨3638866922836584612559013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9703645127564225633490701 3638866922836584612559013)
                      ·
                        rfl

theorem cell23_7086668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_7086668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086668 prefixEnd_7086668 := by exact prefixLift 7086668
  have htrace : WordTrace (prefixWord ++ tailWord_7086668) baseStart_7086668 baseEnd_7086668 := by
    simpa [prefixWord, tailWord_7086668, baseEnd_7086668] using wordTrace_append hprefix tailTrace_7086668
  have hstable : (prefixWord ++ tailWord_7086668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086668).length < 2 ^ (prefixWord ++ tailWord_7086668).sum := by decide
  have hdescent : baseEnd_7086668 < baseStart_7086668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086702 : List Nat := [4, 1, 2, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_7086702 : Nat := 118140960795 + 7086702 * 2 ^ 59
def prefixEnd_7086702 : Nat := 4983230072969 + 3 ^ 40 * 7086702 * 2
def baseEnd_7086702 : Nat := 3638884381178837479533857

theorem tailTrace_7086702 : CollatzResearch.WordTrace tailWord_7086702 prefixEnd_7086702 3638884381178837479533857 := by
  unfold tailWord_7086702
  simp only [CollatzResearch.WordTrace]
  refine ⟨32309157046512055148602795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172315504248064294125881573 32309157046512055148602795)
  ·
    refine ⟨48463735569768082722904193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32309157046512055148602795 48463735569768082722904193)
    ·
      refine ⟨36347801677326062042178145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48463735569768082722904193 36347801677326062042178145)
      ·
        refine ⟨27260851257994546531633609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36347801677326062042178145 27260851257994546531633609)
        ·
          refine ⟨20445638443495909898725207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27260851257994546531633609 20445638443495909898725207)
          ·
            refine ⟨30668457665243864848087811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20445638443495909898725207 30668457665243864848087811)
            ·
              refine ⟨46002686497865797272131717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30668457665243864848087811 46002686497865797272131717)
              ·
                refine ⟨8625503718349836988524697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46002686497865797272131717 8625503718349836988524697)
                ·
                  refine ⟨6469127788762377741393523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8625503718349836988524697 6469127788762377741393523)
                  ·
                    refine ⟨9703691683143566612090285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6469127788762377741393523 9703691683143566612090285)
                    ·
                      refine ⟨3638884381178837479533857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9703691683143566612090285 3638884381178837479533857)
                      ·
                        rfl

theorem cell23_7086702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_7086702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086702 prefixEnd_7086702 := by exact prefixLift 7086702
  have htrace : WordTrace (prefixWord ++ tailWord_7086702) baseStart_7086702 baseEnd_7086702 := by
    simpa [prefixWord, tailWord_7086702, baseEnd_7086702] using wordTrace_append hprefix tailTrace_7086702
  have hstable : (prefixWord ++ tailWord_7086702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086702).length < 2 ^ (prefixWord ++ tailWord_7086702).sum := by decide
  have hdescent : baseEnd_7086702 < baseStart_7086702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086711 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 5]
def baseStart_7086711 : Nat := 118140960795 + 7086711 * 2 ^ 59
def prefixEnd_7086711 : Nat := 4983230072969 + 3 ^ 40 * 7086711 * 2
def baseEnd_7086711 : Nat := 3638889002504727944321315

theorem tailTrace_7086711 : CollatzResearch.WordTrace tailWord_7086711 prefixEnd_7086711 3638889002504727944321315 := by
  unfold tailWord_7086711
  simp only [CollatzResearch.WordTrace]
  refine ⟨258473584629063835725899987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172315723086042557150599991 258473584629063835725899987)
  ·
    refine ⟨387710376943595753588849981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258473584629063835725899987 387710376943595753588849981)
    ·
      refine ⟨145391391353848407595818743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387710376943595753588849981 145391391353848407595818743)
      ·
        refine ⟨218087087030772611393728115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145391391353848407595818743 218087087030772611393728115)
        ·
          refine ⟨327130630546158917090592173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218087087030772611393728115 327130630546158917090592173)
          ·
            refine ⟨122673986454809593908972065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327130630546158917090592173 122673986454809593908972065)
            ·
              refine ⟨92005489841107195431729049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122673986454809593908972065 92005489841107195431729049)
              ·
                refine ⟨69004117380830396573796787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92005489841107195431729049 69004117380830396573796787)
                ·
                  refine ⟨103506176071245594860695181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69004117380830396573796787 103506176071245594860695181)
                  ·
                    refine ⟨38814816026717098072760693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103506176071245594860695181 38814816026717098072760693)
                    ·
                      refine ⟨3638889002504727944321315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38814816026717098072760693 3638889002504727944321315)
                      ·
                        rfl

theorem cell23_7086711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_7086711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086711 prefixEnd_7086711 := by exact prefixLift 7086711
  have htrace : WordTrace (prefixWord ++ tailWord_7086711) baseStart_7086711 baseEnd_7086711 := by
    simpa [prefixWord, tailWord_7086711, baseEnd_7086711] using wordTrace_append hprefix tailTrace_7086711
  have hstable : (prefixWord ++ tailWord_7086711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086711).length < 2 ^ (prefixWord ++ tailWord_7086711).sum := by decide
  have hdescent : baseEnd_7086711 < baseStart_7086711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086725 : List Nat := [1, 3, 1, 1, 4, 2, 1, 3, 1, 4, 2]
def baseStart_7086725 : Nat := 118140960795 + 7086725 * 2 ^ 59
def prefixEnd_7086725 : Nat := 4983230072969 + 3 ^ 40 * 7086725 * 2
def baseEnd_7086725 : Nat := 3638896191233890889546251

theorem tailTrace_7086725 : CollatzResearch.WordTrace tailWord_7086725 prefixEnd_7086725 3638896191233890889546251 := by
  unfold tailWord_7086725
  simp only [CollatzResearch.WordTrace]
  refine ⟨258474095251013116116909629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172316063500675410744606419 258474095251013116116909629)
  ·
    refine ⟨96927785719129918543841111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258474095251013116116909629 96927785719129918543841111)
    ·
      refine ⟨145391678578694877815761667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96927785719129918543841111 145391678578694877815761667)
      ·
        refine ⟨218087517868042316723642501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145391678578694877815761667 218087517868042316723642501)
        ·
          refine ⟨40891409600257934385682969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218087517868042316723642501 40891409600257934385682969)
          ·
            refine ⟨30668557200193450789262227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40891409600257934385682969 30668557200193450789262227)
            ·
              refine ⟨46002835800290176183893341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30668557200193450789262227 46002835800290176183893341)
              ·
                refine ⟨17251063425108816068960003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46002835800290176183893341 17251063425108816068960003)
                ·
                  refine ⟨25876595137663224103440005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17251063425108816068960003 25876595137663224103440005)
                  ·
                    refine ⟨4851861588311854519395001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25876595137663224103440005 4851861588311854519395001)
                    ·
                      refine ⟨3638896191233890889546251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4851861588311854519395001 3638896191233890889546251)
                      ·
                        rfl

theorem cell23_7086725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 4, 2].length) (baseStart_7086725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086725 prefixEnd_7086725 := by exact prefixLift 7086725
  have htrace : WordTrace (prefixWord ++ tailWord_7086725) baseStart_7086725 baseEnd_7086725 := by
    simpa [prefixWord, tailWord_7086725, baseEnd_7086725] using wordTrace_append hprefix tailTrace_7086725
  have hstable : (prefixWord ++ tailWord_7086725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086725).length < 2 ^ (prefixWord ++ tailWord_7086725).sum := by decide
  have hdescent : baseEnd_7086725 < baseStart_7086725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086741 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_7086741 : Nat := 118140960795 + 7086741 * 2 ^ 59
def prefixEnd_7086741 : Nat := 4983230072969 + 3 ^ 40 * 7086741 * 2
def baseEnd_7086741 : Nat := 3638904406924362826946177

theorem tailTrace_7086741 : CollatzResearch.WordTrace tailWord_7086741 prefixEnd_7086741 3638904406924362826946177 := by
  unfold tailWord_7086741
  simp only [CollatzResearch.WordTrace]
  refine ⟨258474678818955150849492077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172316452545970100566328051 258474678818955150849492077)
  ·
    refine ⟨96928004557108181568559529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258474678818955150849492077 96928004557108181568559529)
    ·
      refine ⟨72696003417831136176419647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96928004557108181568559529 72696003417831136176419647)
      ·
        refine ⟨109044005126746704264629471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72696003417831136176419647 109044005126746704264629471)
        ·
          refine ⟨163566007690120056396944207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109044005126746704264629471 163566007690120056396944207)
          ·
            refine ⟨245349011535180084595416311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163566007690120056396944207 245349011535180084595416311)
            ·
              refine ⟨368023517302770126893124467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245349011535180084595416311 368023517302770126893124467)
              ·
                refine ⟨552035275954155190339686701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368023517302770126893124467 552035275954155190339686701)
                ·
                  refine ⟨207013228482808196377382513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552035275954155190339686701 207013228482808196377382513)
                  ·
                    refine ⟨155259921362106147283036885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 207013228482808196377382513 155259921362106147283036885)
                    ·
                      refine ⟨3638904406924362826946177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155259921362106147283036885 3638904406924362826946177)
                      ·
                        rfl

theorem cell23_7086741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_7086741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086741 prefixEnd_7086741 := by exact prefixLift 7086741
  have htrace : WordTrace (prefixWord ++ tailWord_7086741) baseStart_7086741 baseEnd_7086741 := by
    simpa [prefixWord, tailWord_7086741, baseEnd_7086741] using wordTrace_append hprefix tailTrace_7086741
  have hstable : (prefixWord ++ tailWord_7086741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086741).length < 2 ^ (prefixWord ++ tailWord_7086741).sum := by decide
  have hdescent : baseEnd_7086741 < baseStart_7086741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086761 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 3, 7]
def baseStart_7086761 : Nat := 118140960795 + 7086761 * 2 ^ 59
def prefixEnd_7086761 : Nat := 4983230072969 + 3 ^ 40 * 7086761 * 2
def baseEnd_7086761 : Nat := 1212971558845817582898695

theorem tailTrace_7086761 : CollatzResearch.WordTrace tailWord_7086761 prefixEnd_7086761 1212971558845817582898695 := by
  unfold tailWord_7086761
  simp only [CollatzResearch.WordTrace]
  refine ⟨258475408278882694265220137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172316938852588462843480091 258475408278882694265220137)
  ·
    refine ⟨193856556209162020698915103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258475408278882694265220137 193856556209162020698915103)
    ·
      refine ⟨290784834313743031048372655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193856556209162020698915103 290784834313743031048372655)
      ·
        refine ⟨436177251470614546572558983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290784834313743031048372655 436177251470614546572558983)
        ·
          refine ⟨654265877205921819858838475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436177251470614546572558983 654265877205921819858838475)
          ·
            refine ⟨981398815808882729788257713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654265877205921819858838475 981398815808882729788257713)
            ·
              refine ⟨736049111856662047341193285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 981398815808882729788257713 736049111856662047341193285)
              ·
                refine ⟨138009208473124133876473741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 736049111856662047341193285 138009208473124133876473741)
                ·
                  refine ⟨51753453177421550203677653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138009208473124133876473741 51753453177421550203677653)
                  ·
                    refine ⟨1212971558845817582898695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51753453177421550203677653 1212971558845817582898695)
                    ·
                      rfl

theorem cell23_7086761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 7].length) (baseStart_7086761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086761 prefixEnd_7086761 := by exact prefixLift 7086761
  have htrace : WordTrace (prefixWord ++ tailWord_7086761) baseStart_7086761 baseEnd_7086761 := by
    simpa [prefixWord, tailWord_7086761, baseEnd_7086761] using wordTrace_append hprefix tailTrace_7086761
  have hstable : (prefixWord ++ tailWord_7086761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086761).length < 2 ^ (prefixWord ++ tailWord_7086761).sum := by decide
  have hdescent : baseEnd_7086761 < baseStart_7086761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086765 : List Nat := [1, 5, 2, 1, 1, 3, 2, 1, 7]
def baseStart_7086765 : Nat := 118140960795 + 7086765 * 2 ^ 59
def prefixEnd_7086765 : Nat := 4983230072969 + 3 ^ 40 * 7086765 * 2
def baseEnd_7086765 : Nat := 404324081162230081449563

theorem tailTrace_7086765 : CollatzResearch.WordTrace tailWord_7086765 prefixEnd_7086765 404324081162230081449563 := by
  unfold tailWord_7086765
  simp only [CollatzResearch.WordTrace]
  refine ⟨258475554170868202948365749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172317036113912135298910499 258475554170868202948365749)
  ·
    refine ⟨24232083203518894026409289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258475554170868202948365749 24232083203518894026409289)
    ·
      refine ⟨18174062402639170519806967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24232083203518894026409289 18174062402639170519806967)
      ·
        refine ⟨27261093603958755779710451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18174062402639170519806967 27261093603958755779710451)
        ·
          refine ⟨40891640405938133669565677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27261093603958755779710451 40891640405938133669565677)
          ·
            refine ⟨15334365152226800126087129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40891640405938133669565677 15334365152226800126087129)
            ·
              refine ⟨11500773864170100094565347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15334365152226800126087129 11500773864170100094565347)
              ·
                refine ⟨17251160796255150141848021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11500773864170100094565347 17251160796255150141848021)
                ·
                  refine ⟨404324081162230081449563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17251160796255150141848021 404324081162230081449563)
                  ·
                    rfl

theorem cell23_7086765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_7086765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086765 prefixEnd_7086765 := by exact prefixLift 7086765
  have htrace : WordTrace (prefixWord ++ tailWord_7086765) baseStart_7086765 baseEnd_7086765 := by
    simpa [prefixWord, tailWord_7086765, baseEnd_7086765] using wordTrace_append hprefix tailTrace_7086765
  have hstable : (prefixWord ++ tailWord_7086765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086765).length < 2 ^ (prefixWord ++ tailWord_7086765).sum := by decide
  have hdescent : baseEnd_7086765 < baseStart_7086765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086812 : List Nat := [2, 2, 5, 1, 1, 2, 1, 2, 2, 5]
def baseStart_7086812 : Nat := 118140960795 + 7086812 * 2 ^ 59
def prefixEnd_7086812 : Nat := 4983230072969 + 3 ^ 40 * 7086812 * 2
def baseEnd_7086812 : Nat := 1212980288016944016386117

theorem tailTrace_7086812 : CollatzResearch.WordTrace tailWord_7086812 prefixEnd_7086812 1212980288016944016386117 := by
  unfold tailWord_7086812
  simp only [CollatzResearch.WordTrace]
  refine ⟨129238634200848964987663345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172318178934465286650217793 129238634200848964987663345)
  ·
    refine ⟨96928975650636723740747509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129238634200848964987663345 96928975650636723740747509)
    ·
      refine ⟨9087091467247192850695079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96928975650636723740747509 9087091467247192850695079)
      ·
        refine ⟨13630637200870789276042619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9087091467247192850695079 13630637200870789276042619)
        ·
          refine ⟨20445955801306183914063929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13630637200870789276042619 20445955801306183914063929)
          ·
            refine ⟨15334466850979637935547947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20445955801306183914063929 15334466850979637935547947)
            ·
              refine ⟨23001700276469456903321921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15334466850979637935547947 23001700276469456903321921)
              ·
                refine ⟨17251275207352092677491441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23001700276469456903321921 17251275207352092677491441)
                ·
                  refine ⟨12938456405514069508118581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17251275207352092677491441 12938456405514069508118581)
                  ·
                    refine ⟨1212980288016944016386117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12938456405514069508118581 1212980288016944016386117)
                    ·
                      rfl

theorem cell23_7086812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_7086812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086812 prefixEnd_7086812 := by exact prefixLift 7086812
  have htrace : WordTrace (prefixWord ++ tailWord_7086812) baseStart_7086812 baseEnd_7086812 := by
    simpa [prefixWord, tailWord_7086812, baseEnd_7086812] using wordTrace_append hprefix tailTrace_7086812
  have hstable : (prefixWord ++ tailWord_7086812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086812).length < 2 ^ (prefixWord ++ tailWord_7086812).sum := by decide
  have hdescent : baseEnd_7086812 < baseStart_7086812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086815 : List Nat := [1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 4]
def baseStart_7086815 : Nat := 118140960795 + 7086815 * 2 ^ 59
def prefixEnd_7086815 : Nat := 4983230072969 + 3 ^ 40 * 7086815 * 2
def baseEnd_7086815 : Nat := 3638942404492795537420837

theorem tailTrace_7086815 : CollatzResearch.WordTrace tailWord_7086815 prefixEnd_7086815 3638942404492795537420837 := by
  unfold tailWord_7086815
  simp only [CollatzResearch.WordTrace]
  refine ⟨258477377820687061487685899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172318251880458040991790599 258477377820687061487685899)
  ·
    refine ⟨387716066731030592231528849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258477377820687061487685899 387716066731030592231528849)
    ·
      refine ⟨290787050048272944173646637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387716066731030592231528849 290787050048272944173646637)
      ·
        refine ⟨109045143768102354065117489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290787050048272944173646637 109045143768102354065117489)
        ·
          refine ⟨81783857826076765548838117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109045143768102354065117489 81783857826076765548838117)
          ·
            refine ⟨15334473342389393540407147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81783857826076765548838117 15334473342389393540407147)
            ·
              refine ⟨23001710013584090310610721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15334473342389393540407147 23001710013584090310610721)
              ·
                refine ⟨17251282510188067732958041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23001710013584090310610721 17251282510188067732958041)
                ·
                  refine ⟨12938461882641050799718531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17251282510188067732958041 12938461882641050799718531)
                  ·
                    refine ⟨19407692823961576199577797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12938461882641050799718531 19407692823961576199577797)
                    ·
                      refine ⟨3638942404492795537420837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19407692823961576199577797 3638942404492795537420837)
                      ·
                        rfl

theorem cell23_7086815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_7086815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086815 prefixEnd_7086815 := by exact prefixLift 7086815
  have htrace : WordTrace (prefixWord ++ tailWord_7086815) baseStart_7086815 baseEnd_7086815 := by
    simpa [prefixWord, tailWord_7086815, baseEnd_7086815] using wordTrace_append hprefix tailTrace_7086815
  have hstable : (prefixWord ++ tailWord_7086815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086815).length < 2 ^ (prefixWord ++ tailWord_7086815).sum := by decide
  have hdescent : baseEnd_7086815 < baseStart_7086815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086825 : List Nat := [1, 2, 1, 1, 1, 2, 7, 1, 3, 4]
def baseStart_7086825 : Nat := 118140960795 + 7086825 * 2 ^ 59
def prefixEnd_7086825 : Nat := 4983230072969 + 3 ^ 40 * 7086825 * 2
def baseEnd_7086825 : Nat := 1212982513099780166098597

theorem tailTrace_7086825 : CollatzResearch.WordTrace tailWord_7086825 prefixEnd_7086825 1212982513099780166098597 := by
  unfold tailWord_7086825
  simp only [CollatzResearch.WordTrace]
  refine ⟨258477742550650833195549929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172318495033767222130366619 258477742550650833195549929)
  ·
    refine ⟨193858306912988124896662447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258477742550650833195549929 193858306912988124896662447)
    ·
      refine ⟨290787460369482187344993671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193858306912988124896662447 290787460369482187344993671)
      ·
        refine ⟨436181190554223281017490507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290787460369482187344993671 436181190554223281017490507)
        ·
          refine ⟨654271785831334921526235761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436181190554223281017490507 654271785831334921526235761)
          ·
            refine ⟨490703839373501191144676821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654271785831334921526235761 490703839373501191144676821)
            ·
              refine ⟨11500871235316434167453363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 490703839373501191144676821 11500871235316434167453363)
              ·
                refine ⟨17251306852974651251180045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11500871235316434167453363 17251306852974651251180045)
                ·
                  refine ⟨6469240069865494219192517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17251306852974651251180045 6469240069865494219192517)
                  ·
                    refine ⟨1212982513099780166098597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6469240069865494219192517 1212982513099780166098597)
                    ·
                      rfl

theorem cell23_7086825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 4].length) (baseStart_7086825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086825 prefixEnd_7086825 := by exact prefixLift 7086825
  have htrace : WordTrace (prefixWord ++ tailWord_7086825) baseStart_7086825 baseEnd_7086825 := by
    simpa [prefixWord, tailWord_7086825, baseEnd_7086825] using wordTrace_append hprefix tailTrace_7086825
  have hstable : (prefixWord ++ tailWord_7086825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086825).length < 2 ^ (prefixWord ++ tailWord_7086825).sum := by decide
  have hdescent : baseEnd_7086825 < baseStart_7086825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086852 : List Nat := [2, 3, 2, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_7086852 : Nat := 118140960795 + 7086852 * 2 ^ 59
def prefixEnd_7086852 : Nat := 4983230072969 + 3 ^ 40 * 7086852 * 2
def baseEnd_7086852 : Nat := 3638961403277011892658167

theorem tailTrace_7086852 : CollatzResearch.WordTrace tailWord_7086852 prefixEnd_7086852 3638961403277011892658167 := by
  unfold tailWord_7086852
  simp only [CollatzResearch.WordTrace]
  refine ⟨129239363660776508403391405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172319151547702011204521873 129239363660776508403391405)
  ·
    refine ⟨48464761372791190651271777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129239363660776508403391405 48464761372791190651271777)
    ·
      refine ⟨36348571029593392988453833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48464761372791190651271777 36348571029593392988453833)
      ·
        refine ⟨27261428272195044741340375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36348571029593392988453833 27261428272195044741340375)
        ·
          refine ⟨40892142408292567112010563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27261428272195044741340375 40892142408292567112010563)
          ·
            refine ⟨61338213612438850668015845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40892142408292567112010563 61338213612438850668015845)
            ·
              refine ⟨11500915052332284500252971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61338213612438850668015845 11500915052332284500252971)
              ·
                refine ⟨17251372578498426750379457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11500915052332284500252971 17251372578498426750379457)
                ·
                  refine ⟨12938529433873820062784593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17251372578498426750379457 12938529433873820062784593)
                  ·
                    refine ⟨9703897075405365047088445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12938529433873820062784593 9703897075405365047088445)
                    ·
                      refine ⟨3638961403277011892658167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9703897075405365047088445 3638961403277011892658167)
                      ·
                        rfl

theorem cell23_7086852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_7086852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086852 prefixEnd_7086852 := by exact prefixLift 7086852
  have htrace : WordTrace (prefixWord ++ tailWord_7086852) baseStart_7086852 baseEnd_7086852 := by
    simpa [prefixWord, tailWord_7086852, baseEnd_7086852] using wordTrace_append hprefix tailTrace_7086852
  have hstable : (prefixWord ++ tailWord_7086852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086852).length < 2 ^ (prefixWord ++ tailWord_7086852).sum := by decide
  have hdescent : baseEnd_7086852 < baseStart_7086852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086876 : List Nat := [2, 2, 3, 1, 1, 5, 2, 2, 1, 4]
def baseStart_7086876 : Nat := 118140960795 + 7086876 * 2 ^ 59
def prefixEnd_7086876 : Nat := 4983230072969 + 3 ^ 40 * 7086876 * 2
def baseEnd_7086876 : Nat := 1212991242270906599586019

theorem tailTrace_7086876 : CollatzResearch.WordTrace tailWord_7086876 prefixEnd_7086876 1212991242270906599586019 := by
  unfold tailWord_7086876
  simp only [CollatzResearch.WordTrace]
  refine ⟨129239801336733034452828241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172319735115644045937104321 129239801336733034452828241)
  ·
    refine ⟨96929851002549775839621181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129239801336733034452828241 96929851002549775839621181)
    ·
      refine ⟨36348694125956165939857943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96929851002549775839621181 36348694125956165939857943)
      ·
        refine ⟨54523041188934248909786915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36348694125956165939857943 54523041188934248909786915)
        ·
          refine ⟨81784561783401373364680373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54523041188934248909786915 81784561783401373364680373)
          ·
            refine ⟨7667302667193878752938785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81784561783401373364680373 7667302667193878752938785)
            ·
              refine ⟨5750477000395409064704089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7667302667193878752938785 5750477000395409064704089)
              ·
                refine ⟨4312857750296556798528067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5750477000395409064704089 4312857750296556798528067)
                ·
                  refine ⟨6469286625444835197792101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4312857750296556798528067 6469286625444835197792101)
                  ·
                    refine ⟨1212991242270906599586019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6469286625444835197792101 1212991242270906599586019)
                    ·
                      rfl

theorem cell23_7086876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_7086876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086876 prefixEnd_7086876 := by exact prefixLift 7086876
  have htrace : WordTrace (prefixWord ++ tailWord_7086876) baseStart_7086876 baseEnd_7086876 := by
    simpa [prefixWord, tailWord_7086876, baseEnd_7086876] using wordTrace_append hprefix tailTrace_7086876
  have hstable : (prefixWord ++ tailWord_7086876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086876).length < 2 ^ (prefixWord ++ tailWord_7086876).sum := by decide
  have hdescent : baseEnd_7086876 < baseStart_7086876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086909 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 1, 5, 2]
def baseStart_7086909 : Nat := 118140960795 + 7086909 * 2 ^ 59
def prefixEnd_7086909 : Nat := 4983230072969 + 3 ^ 40 * 7086909 * 2
def baseEnd_7086909 : Nat := 3638990671674318169645405

theorem tailTrace_7086909 : CollatzResearch.WordTrace tailWord_7086909 prefixEnd_7086909 3638990671674318169645405 := by
  unfold tailWord_7086909
  simp only [CollatzResearch.WordTrace]
  refine ⟨258480806282346515541607781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172320537521564343694405187 258480806282346515541607781)
  ·
    refine ⟨48465151177939971664051459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258480806282346515541607781 48465151177939971664051459)
    ·
      refine ⟨72697726766909957496077189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48465151177939971664051459 72697726766909957496077189)
      ·
        refine ⟨13630823768795617030514473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72697726766909957496077189 13630823768795617030514473)
        ·
          refine ⟨10223117826596712772885855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13630823768795617030514473 10223117826596712772885855)
          ·
            refine ⟨15334676739895069159328783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10223117826596712772885855 15334676739895069159328783)
            ·
              refine ⟨23002015109842603738993175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15334676739895069159328783 23002015109842603738993175)
              ·
                refine ⟨34503022664763905608489763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23002015109842603738993175 34503022664763905608489763)
                ·
                  refine ⟨51754533997145858412734645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34503022664763905608489763 51754533997145858412734645)
                  ·
                    refine ⟨4851987562232424226193873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51754533997145858412734645 4851987562232424226193873)
                    ·
                      refine ⟨3638990671674318169645405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4851987562232424226193873 3638990671674318169645405)
                      ·
                        rfl

theorem cell23_7086909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_7086909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086909 prefixEnd_7086909 := by exact prefixLift 7086909
  have htrace : WordTrace (prefixWord ++ tailWord_7086909) baseStart_7086909 baseEnd_7086909 := by
    simpa [prefixWord, tailWord_7086909, baseEnd_7086909] using wordTrace_append hprefix tailTrace_7086909
  have hstable : (prefixWord ++ tailWord_7086909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086909).length < 2 ^ (prefixWord ++ tailWord_7086909).sum := by decide
  have hdescent : baseEnd_7086909 < baseStart_7086909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086915 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 4, 4]
def baseStart_7086915 : Nat := 118140960795 + 7086915 * 2 ^ 59
def prefixEnd_7086915 : Nat := 4983230072969 + 3 ^ 40 * 7086915 * 2
def baseEnd_7086915 : Nat := 1212997917519415048723459

theorem tailTrace_7086915 : CollatzResearch.WordTrace tailWord_7086915 prefixEnd_7086915 1212997917519415048723459 := by
  unfold tailWord_7086915
  simp only [CollatzResearch.WordTrace]
  refine ⟨258481025120324778566326199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172320683413549852377550799 258481025120324778566326199)
  ·
    refine ⟨387721537680487167849489299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258481025120324778566326199 387721537680487167849489299)
    ·
      refine ⟨581582306520730751774233949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387721537680487167849489299 581582306520730751774233949)
      ·
        refine ⟨218093364945274031915337731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 581582306520730751774233949 218093364945274031915337731)
        ·
          refine ⟨327140047417911047873006597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218093364945274031915337731 327140047417911047873006597)
          ·
            refine ⟨61338758890858321476188737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 327140047417911047873006597 61338758890858321476188737)
            ·
              refine ⟨46004069168143741107141553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61338758890858321476188737 46004069168143741107141553)
              ·
                refine ⟨34503051876107805830356165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46004069168143741107141553 34503051876107805830356165)
                ·
                  refine ⟨6469322226770213593191781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34503051876107805830356165 6469322226770213593191781)
                  ·
                    refine ⟨1212997917519415048723459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6469322226770213593191781 1212997917519415048723459)
                    ·
                      rfl

theorem cell23_7086915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 4].length) (baseStart_7086915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086915 prefixEnd_7086915 := by exact prefixLift 7086915
  have htrace : WordTrace (prefixWord ++ tailWord_7086915) baseStart_7086915 baseEnd_7086915 := by
    simpa [prefixWord, tailWord_7086915, baseEnd_7086915] using wordTrace_append hprefix tailTrace_7086915
  have hstable : (prefixWord ++ tailWord_7086915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086915).length < 2 ^ (prefixWord ++ tailWord_7086915).sum := by decide
  have hdescent : baseEnd_7086915 < baseStart_7086915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7086952 : List Nat := [2, 1, 4, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_7086952 : Nat := 118140960795 + 7086952 * 2 ^ 59
def prefixEnd_7086952 : Nat := 4983230072969 + 3 ^ 40 * 7086952 * 2
def baseEnd_7086952 : Nat := 3639012751342461501407707

theorem tailTrace_7086952 : CollatzResearch.WordTrace tailWord_7086952 prefixEnd_7086952 3639012751342461501407707 := by
  unfold tailWord_7086952
  simp only [CollatzResearch.WordTrace]
  refine ⟨129241187310595366942711555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172321583080793822590282073 129241187310595366942711555)
  ·
    refine ⟨193861780965893050414067333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129241187310595366942711555 193861780965893050414067333)
    ·
      refine ⟨36349083931104946952637625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193861780965893050414067333 36349083931104946952637625)
      ·
        refine ⟨27261812948328710214478219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36349083931104946952637625 27261812948328710214478219)
        ·
          refine ⟨40892719422493065321717329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27261812948328710214478219 40892719422493065321717329)
          ·
            refine ⟨30669539566869798991287997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40892719422493065321717329 30669539566869798991287997)
            ·
              refine ⟨11501077337576174621732999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30669539566869798991287997 11501077337576174621732999)
              ·
                refine ⟨17251616006364261932599499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11501077337576174621732999 17251616006364261932599499)
                ·
                  refine ⟨25877424009546392898899249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17251616006364261932599499 25877424009546392898899249)
                  ·
                    refine ⟨19408068007159794674174437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25877424009546392898899249 19408068007159794674174437)
                    ·
                      refine ⟨3639012751342461501407707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19408068007159794674174437 3639012751342461501407707)
                      ·
                        rfl

theorem cell23_7086952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_7086952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7086952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7086952 prefixEnd_7086952 := by exact prefixLift 7086952
  have htrace : WordTrace (prefixWord ++ tailWord_7086952) baseStart_7086952 baseEnd_7086952 := by
    simpa [prefixWord, tailWord_7086952, baseEnd_7086952] using wordTrace_append hprefix tailTrace_7086952
  have hstable : (prefixWord ++ tailWord_7086952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7086952).length < 2 ^ (prefixWord ++ tailWord_7086952).sum := by decide
  have hdescent : baseEnd_7086952 < baseStart_7086952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7086952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087005 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 1, 8]
def baseStart_7087005 : Nat := 118140960795 + 7087005 * 2 ^ 59
def prefixEnd_7087005 : Nat := 4983230072969 + 3 ^ 40 * 7087005 * 2
def baseEnd_7087005 : Nat := 1213013321939049931348321

theorem tailTrace_7087005 : CollatzResearch.WordTrace tailWord_7087005 prefixEnd_7087005 1213013321939049931348321 := by
  unfold tailWord_7087005
  simp only [CollatzResearch.WordTrace]
  refine ⟨258484307689998723937102469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172322871793332482624734979 258484307689998723937102469)
  ·
    refine ⟨48465807691874760738206713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258484307689998723937102469 48465807691874760738206713)
    ·
      refine ⟨36349355768906070553655035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48465807691874760738206713 36349355768906070553655035)
      ·
        refine ⟨54524033653359105830482553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36349355768906070553655035 54524033653359105830482553)
        ·
          refine ⟨40893025240019329372861915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54524033653359105830482553 40893025240019329372861915)
          ·
            refine ⟨61339537860028994059292873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40893025240019329372861915 61339537860028994059292873)
            ·
              refine ⟨46004653395021745544469655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61339537860028994059292873 46004653395021745544469655)
              ·
                refine ⟨69006980092532618316704483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46004653395021745544469655 69006980092532618316704483)
                ·
                  refine ⟨103510470138798927475056725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69006980092532618316704483 103510470138798927475056725)
                  ·
                    refine ⟨1213013321939049931348321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103510470138798927475056725 1213013321939049931348321)
                    ·
                      rfl

theorem cell23_7087005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_7087005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087005 prefixEnd_7087005 := by exact prefixLift 7087005
  have htrace : WordTrace (prefixWord ++ tailWord_7087005) baseStart_7087005 baseEnd_7087005 := by
    simpa [prefixWord, tailWord_7087005, baseEnd_7087005] using wordTrace_append hprefix tailTrace_7087005
  have hstable : (prefixWord ++ tailWord_7087005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087005).length < 2 ^ (prefixWord ++ tailWord_7087005).sum := by decide
  have hdescent : baseEnd_7087005 < baseStart_7087005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087029 : List Nat := [1, 3, 3, 2, 1, 1, 3, 2, 1, 4, 2]
def baseStart_7087029 : Nat := 118140960795 + 7087029 * 2 ^ 59
def prefixEnd_7087029 : Nat := 4983230072969 + 3 ^ 40 * 7087029 * 2
def baseEnd_7087029 : Nat := 3639052289352857700144853

theorem tailTrace_7087029 : CollatzResearch.WordTrace tailWord_7087029 prefixEnd_7087029 3639052289352857700144853 := by
  unfold tailWord_7087029
  simp only [CollatzResearch.WordTrace]
  refine ⟨258485183041911776035976141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172323455361274517357317427 258485183041911776035976141)
  ·
    refine ⟨96931943640716916013491053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258485183041911776035976141 96931943640716916013491053)
    ·
      refine ⟨36349478865268843505059145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96931943640716916013491053 36349478865268843505059145)
      ·
        refine ⟨27262109148951632628794359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36349478865268843505059145 27262109148951632628794359)
        ·
          refine ⟨40893163723427448943191539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27262109148951632628794359 40893163723427448943191539)
          ·
            refine ⟨61339745585141173414787309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40893163723427448943191539 61339745585141173414787309)
            ·
              refine ⟨23002404594427940030545241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61339745585141173414787309 23002404594427940030545241)
              ·
                refine ⟨17251803445820955022908931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23002404594427940030545241 17251803445820955022908931)
                ·
                  refine ⟨25877705168731432534363397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17251803445820955022908931 25877705168731432534363397)
                  ·
                    refine ⟨4852069719137143600193137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25877705168731432534363397 4852069719137143600193137)
                    ·
                      refine ⟨3639052289352857700144853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4852069719137143600193137 3639052289352857700144853)
                      ·
                        rfl

theorem cell23_7087029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_7087029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087029 prefixEnd_7087029 := by exact prefixLift 7087029
  have htrace : WordTrace (prefixWord ++ tailWord_7087029) baseStart_7087029 baseEnd_7087029 := by
    simpa [prefixWord, tailWord_7087029, baseEnd_7087029] using wordTrace_append hprefix tailTrace_7087029
  have hstable : (prefixWord ++ tailWord_7087029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087029).length < 2 ^ (prefixWord ++ tailWord_7087029).sum := by decide
  have hdescent : baseEnd_7087029 < baseStart_7087029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087082 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 1, 7]
def baseStart_7087082 : Nat := 118140960795 + 7087082 * 2 ^ 59
def prefixEnd_7087082 : Nat := 4983230072969 + 3 ^ 40 * 7087082 * 2
def baseEnd_7087082 : Nat := 1213026501275848664260703

theorem tailTrace_7087082 : CollatzResearch.WordTrace tailWord_7087082 prefixEnd_7087082 1213026501275848664260703 := by
  unfold tailWord_7087082
  simp only [CollatzResearch.WordTrace]
  refine ⟨64621779027679941521913875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172324744073813177391770333 64621779027679941521913875)
  ·
    refine ⟨96932668541519912282870813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64621779027679941521913875 96932668541519912282870813)
    ·
      refine ⟨36349750703069967106076555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96932668541519912282870813 36349750703069967106076555)
      ·
        refine ⟨54524626054604950659114833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36349750703069967106076555 54524626054604950659114833)
        ·
          refine ⟨40893469540953712994336125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54524626054604950659114833 40893469540953712994336125)
          ·
            refine ⟨15335051077857642372876047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40893469540953712994336125 15335051077857642372876047)
            ·
              refine ⟨23002576616786463559314071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15335051077857642372876047 23002576616786463559314071)
              ·
                refine ⟨34503864925179695338971107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23002576616786463559314071 34503864925179695338971107)
                ·
                  refine ⟨51755797387769543008456661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34503864925179695338971107 51755797387769543008456661)
                  ·
                    refine ⟨1213026501275848664260703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51755797387769543008456661 1213026501275848664260703)
                    ·
                      rfl

theorem cell23_7087082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_7087082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087082 prefixEnd_7087082 := by exact prefixLift 7087082
  have htrace : WordTrace (prefixWord ++ tailWord_7087082) baseStart_7087082 baseEnd_7087082 := by
    simpa [prefixWord, tailWord_7087082, baseEnd_7087082] using wordTrace_append hprefix tailTrace_7087082
  have hstable : (prefixWord ++ tailWord_7087082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087082).length < 2 ^ (prefixWord ++ tailWord_7087082).sum := by decide
  have hdescent : baseEnd_7087082 < baseStart_7087082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087086 : List Nat := [4, 1, 2, 1, 4, 1, 2, 3, 5]
def baseStart_7087086 : Nat := 118140960795 + 7087086 * 2 ^ 59
def prefixEnd_7087086 : Nat := 4983230072969 + 3 ^ 40 * 7087086 * 2
def baseEnd_7087086 : Nat := 404342395305573775236899

theorem tailTrace_7087086 : CollatzResearch.WordTrace tailWord_7087086 prefixEnd_7087086 404342395305573775236899 := by
  unfold tailWord_7087086
  simp only [CollatzResearch.WordTrace]
  refine ⟨32310907750338159346350139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172324841335136849847200741 32310907750338159346350139)
  ·
    refine ⟨48466361625507239019525209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32310907750338159346350139 48466361625507239019525209)
    ·
      refine ⟨36349771219130429264643907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48466361625507239019525209 36349771219130429264643907)
      ·
        refine ⟨54524656828695643896965861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36349771219130429264643907 54524656828695643896965861)
        ·
          refine ⟨10223373155380433230681099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54524656828695643896965861 10223373155380433230681099)
          ·
            refine ⟨15335059733070649846021649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10223373155380433230681099 15335059733070649846021649)
            ·
              refine ⟨11501294799802987384516237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15335059733070649846021649 11501294799802987384516237)
              ·
                refine ⟨4312985549926120269193589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11501294799802987384516237 4312985549926120269193589)
                ·
                  refine ⟨404342395305573775236899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4312985549926120269193589 404342395305573775236899)
                  ·
                    rfl

theorem cell23_7087086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_7087086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087086 prefixEnd_7087086 := by exact prefixLift 7087086
  have htrace : WordTrace (prefixWord ++ tailWord_7087086) baseStart_7087086 baseEnd_7087086 := by
    simpa [prefixWord, tailWord_7087086, baseEnd_7087086] using wordTrace_append hprefix tailTrace_7087086
  have hstable : (prefixWord ++ tailWord_7087086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087086).length < 2 ^ (prefixWord ++ tailWord_7087086).sum := by decide
  have hdescent : baseEnd_7087086 < baseStart_7087086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087145 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 2, 6, 6]
def baseStart_7087145 : Nat := 118140960795 + 7087145 * 2 ^ 59
def prefixEnd_7087145 : Nat := 4983230072969 + 3 ^ 40 * 7087145 * 2
def baseEnd_7087145 : Nat := 3639111853108779246294319

theorem tailTrace_7087145 : CollatzResearch.WordTrace tailWord_7087145 prefixEnd_7087145 3639111853108779246294319 := by
  unfold tailWord_7087145
  simp only [CollatzResearch.WordTrace]
  refine ⟨258489413909491527847198889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172326275939661018564799259 258489413909491527847198889)
  ·
    refine ⟨193867060432118645885399167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258489413909491527847198889 193867060432118645885399167)
    ·
      refine ⟨290800590648177968828098751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193867060432118645885399167 290800590648177968828098751)
      ·
        refine ⟨436200885972266953242148127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290800590648177968828098751 436200885972266953242148127)
        ·
          refine ⟨654301328958400429863222191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436200885972266953242148127 654301328958400429863222191)
          ·
            refine ⟨981451993437600644794833287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654301328958400429863222191 981451993437600644794833287)
            ·
              refine ⟨1472177990156400967192249931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981451993437600644794833287 1472177990156400967192249931)
              ·
                refine ⟨2208266985234601450788374897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1472177990156400967192249931 2208266985234601450788374897)
                ·
                  refine ⟨1656200238925951088091281173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2208266985234601450788374897 1656200238925951088091281173)
                  ·
                    refine ⟨77634386199653957254278805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1656200238925951088091281173 77634386199653957254278805)
                    ·
                      refine ⟨3639111853108779246294319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77634386199653957254278805 3639111853108779246294319)
                      ·
                        rfl

theorem cell23_7087145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_7087145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087145 prefixEnd_7087145 := by exact prefixLift 7087145
  have htrace : WordTrace (prefixWord ++ tailWord_7087145) baseStart_7087145 baseEnd_7087145 := by
    simpa [prefixWord, tailWord_7087145, baseEnd_7087145] using wordTrace_append hprefix tailTrace_7087145
  have hstable : (prefixWord ++ tailWord_7087145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087145).length < 2 ^ (prefixWord ++ tailWord_7087145).sum := by decide
  have hdescent : baseEnd_7087145 < baseStart_7087145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087156 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_7087156 : Nat := 118140960795 + 7087156 * 2 ^ 59
def prefixEnd_7087156 : Nat := 4983230072969 + 3 ^ 40 * 7087156 * 2
def baseEnd_7087156 : Nat := 3639117501395978703256769

theorem tailTrace_7087156 : CollatzResearch.WordTrace tailWord_7087156 prefixEnd_7087156 3639117501395978703256769 := by
  unfold tailWord_7087156
  simp only [CollatzResearch.WordTrace]
  refine ⟨129244907556225838362924661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172326543408301117817232881 129244907556225838362924661)
  ·
    refine ⟨12116710083396172346524187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129244907556225838362924661 12116710083396172346524187)
    ·
      refine ⟨18175065125094258519786281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12116710083396172346524187 18175065125094258519786281)
      ·
        refine ⟨13631298843820693889839711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18175065125094258519786281 13631298843820693889839711)
        ·
          refine ⟨20446948265731040834759567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13631298843820693889839711 20446948265731040834759567)
          ·
            refine ⟨30670422398596561252139351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20446948265731040834759567 30670422398596561252139351)
            ·
              refine ⟨46005633597894841878209027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30670422398596561252139351 46005633597894841878209027)
              ·
                refine ⟨69008450396842262817313541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46005633597894841878209027 69008450396842262817313541)
                ·
                  refine ⟨12939084449407924278246289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69008450396842262817313541 12939084449407924278246289)
                  ·
                    refine ⟨9704313337055943208684717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12939084449407924278246289 9704313337055943208684717)
                    ·
                      refine ⟨3639117501395978703256769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9704313337055943208684717 3639117501395978703256769)
                      ·
                        rfl

theorem cell23_7087156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_7087156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087156 prefixEnd_7087156 := by exact prefixLift 7087156
  have htrace : WordTrace (prefixWord ++ tailWord_7087156) baseStart_7087156 baseEnd_7087156 := by
    simpa [prefixWord, tailWord_7087156, baseEnd_7087156] using wordTrace_append hprefix tailTrace_7087156
  have hstable : (prefixWord ++ tailWord_7087156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087156).length < 2 ^ (prefixWord ++ tailWord_7087156).sum := by decide
  have hdescent : baseEnd_7087156 < baseStart_7087156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087190 : List Nat := [5, 2, 2, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_7087190 : Nat := 118140960795 + 7087190 * 2 ^ 59
def prefixEnd_7087190 : Nat := 4983230072969 + 3 ^ 40 * 7087190 * 2
def baseEnd_7087190 : Nat := 3639134959738231570231613

theorem tailTrace_7087190 : CollatzResearch.WordTrace tailWord_7087190 prefixEnd_7087190 3639134959738231570231613 := by
  unfold tailWord_7087190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16155690949645531283286689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172327370129552333688391349 16155690949645531283286689)
  ·
    refine ⟨12116768212234148462465017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16155690949645531283286689 12116768212234148462465017)
    ·
      refine ⟨9087576159175611346848763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12116768212234148462465017 9087576159175611346848763)
      ·
        refine ⟨13631364238763417020273145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9087576159175611346848763 13631364238763417020273145)
        ·
          refine ⟨10223523179072562765204859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13631364238763417020273145 10223523179072562765204859)
          ·
            refine ⟨15335284768608844147807289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10223523179072562765204859 15335284768608844147807289)
            ·
              refine ⟨11501463576456633110855467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15335284768608844147807289 11501463576456633110855467)
              ·
                refine ⟨17252195364684949666283201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11501463576456633110855467 17252195364684949666283201)
                ·
                  refine ⟨12939146523513712249712401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17252195364684949666283201 12939146523513712249712401)
                  ·
                    refine ⟨9704359892635284187284301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12939146523513712249712401 9704359892635284187284301)
                    ·
                      refine ⟨3639134959738231570231613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9704359892635284187284301 3639134959738231570231613)
                      ·
                        rfl

theorem cell23_7087190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_7087190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087190 prefixEnd_7087190 := by exact prefixLift 7087190
  have htrace : WordTrace (prefixWord ++ tailWord_7087190) baseStart_7087190 baseEnd_7087190 := by
    simpa [prefixWord, tailWord_7087190, baseEnd_7087190] using wordTrace_append hprefix tailTrace_7087190
  have hstable : (prefixWord ++ tailWord_7087190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087190).length < 2 ^ (prefixWord ++ tailWord_7087190).sum := by decide
  have hdescent : baseEnd_7087190 < baseStart_7087190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087229 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 5, 2, 3]
def baseStart_7087229 : Nat := 118140960795 + 7087229 * 2 ^ 59
def prefixEnd_7087229 : Nat := 4983230072969 + 3 ^ 40 * 7087229 * 2
def baseEnd_7087229 : Nat := 3639154985483756917643933

theorem tailTrace_7087229 : CollatzResearch.WordTrace tailWord_7087229 prefixEnd_7087229 3639154985483756917643933 := by
  unfold tailWord_7087229
  simp only [CollatzResearch.WordTrace]
  refine ⟨258492477641187210193256741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172328318427458140128837827 258492477641187210193256741)
  ·
    refine ⟨48467339557722601911235639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258492477641187210193256741 48467339557722601911235639)
    ·
      refine ⟨72701009336583902866853459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48467339557722601911235639 72701009336583902866853459)
      ·
        refine ⟨109051514004875854300280189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72701009336583902866853459 109051514004875854300280189)
        ·
          refine ⟨40894317751828445362605071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109051514004875854300280189 40894317751828445362605071)
          ·
            refine ⟨61341476627742668043907607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40894317751828445362605071 61341476627742668043907607)
            ·
              refine ⟨92012214941614002065861411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61341476627742668043907607 92012214941614002065861411)
              ·
                refine ⟨138018322412421003098792117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92012214941614002065861411 138018322412421003098792117)
                ·
                  refine ⟨12939217726164469040511761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138018322412421003098792117 12939217726164469040511761)
                  ·
                    refine ⟨9704413294623351780383821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12939217726164469040511761 9704413294623351780383821)
                    ·
                      refine ⟨3639154985483756917643933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9704413294623351780383821 3639154985483756917643933)
                      ·
                        rfl

theorem cell23_7087229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_7087229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087229 prefixEnd_7087229 := by exact prefixLift 7087229
  have htrace : WordTrace (prefixWord ++ tailWord_7087229) baseStart_7087229 baseEnd_7087229 := by
    simpa [prefixWord, tailWord_7087229, baseEnd_7087229] using wordTrace_append hprefix tailTrace_7087229
  have hstable : (prefixWord ++ tailWord_7087229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087229).length < 2 ^ (prefixWord ++ tailWord_7087229).sum := by decide
  have hdescent : baseEnd_7087229 < baseStart_7087229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087232 : List Nat := [2, 1, 1, 2, 1, 3, 5, 8]
def baseStart_7087232 : Nat := 118140960795 + 7087232 * 2 ^ 59
def prefixEnd_7087232 : Nat := 4983230072969 + 3 ^ 40 * 7087232 * 2
def baseEnd_7087232 : Nat := 134783575034285940959497

theorem tailTrace_7087232 : CollatzResearch.WordTrace tailWord_7087232 prefixEnd_7087232 134783575034285940959497 := by
  unfold tailWord_7087232
  simp only [CollatzResearch.WordTrace]
  refine ⟨129246293530088170852807975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172328391373450894470410633 129246293530088170852807975)
  ·
    refine ⟨193869440295132256279211963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129246293530088170852807975 193869440295132256279211963)
    ·
      refine ⟨290804160442698384418817945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193869440295132256279211963 290804160442698384418817945)
      ·
        refine ⟨218103120332023788314113459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290804160442698384418817945 218103120332023788314113459)
        ·
          refine ⟨327154680498035682471170189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218103120332023788314113459 327154680498035682471170189)
          ·
            refine ⟨122683005186763380926688821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327154680498035682471170189 122683005186763380926688821)
            ·
              refine ⟨11501531736259066961877077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122683005186763380926688821 11501531736259066961877077)
              ·
                refine ⟨134783575034285940959497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11501531736259066961877077 134783575034285940959497)
                ·
                  rfl

theorem cell23_7087232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 8].length) (baseStart_7087232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087232 prefixEnd_7087232 := by exact prefixLift 7087232
  have htrace : WordTrace (prefixWord ++ tailWord_7087232) baseStart_7087232 baseEnd_7087232 := by
    simpa [prefixWord, tailWord_7087232, baseEnd_7087232] using wordTrace_append hprefix tailTrace_7087232
  have hstable : (prefixWord ++ tailWord_7087232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087232).length < 2 ^ (prefixWord ++ tailWord_7087232).sum := by decide
  have hdescent : baseEnd_7087232 < baseStart_7087232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087236 : List Nat := [2, 3, 2, 1, 2, 2, 2, 3, 2, 4]
def baseStart_7087236 : Nat := 118140960795 + 7087236 * 2 ^ 59
def prefixEnd_7087236 : Nat := 4983230072969 + 3 ^ 40 * 7087236 * 2
def baseEnd_7087236 : Nat := 1213052859949446130085467

theorem tailTrace_7087236 : CollatzResearch.WordTrace tailWord_7087236 prefixEnd_7087236 1213052859949446130085467 := by
  unfold tailWord_7087236
  simp only [CollatzResearch.WordTrace]
  refine ⟨129246366476080925194380781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172328488634774566925841041 129246366476080925194380781)
  ·
    refine ⟨48467387428530346947892793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129246366476080925194380781 48467387428530346947892793)
    ·
      refine ⟨36350540571397760210919595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48467387428530346947892793 36350540571397760210919595)
      ·
        refine ⟨54525810857096640316379393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36350540571397760210919595 54525810857096640316379393)
        ·
          refine ⟨40894358142822480237284545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54525810857096640316379393 40894358142822480237284545)
          ·
            refine ⟨30670768607116860177963409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40894358142822480237284545 30670768607116860177963409)
            ·
              refine ⟨23003076455337645133472557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30670768607116860177963409 23003076455337645133472557)
              ·
                refine ⟨8626153670751616925052209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23003076455337645133472557 8626153670751616925052209)
                ·
                  refine ⟨6469615253063712693789157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8626153670751616925052209 6469615253063712693789157)
                  ·
                    refine ⟨1213052859949446130085467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6469615253063712693789157 1213052859949446130085467)
                    ·
                      rfl

theorem cell23_7087236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_7087236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087236 prefixEnd_7087236 := by exact prefixLift 7087236
  have htrace : WordTrace (prefixWord ++ tailWord_7087236) baseStart_7087236 baseEnd_7087236 := by
    simpa [prefixWord, tailWord_7087236, baseEnd_7087236] using wordTrace_append hprefix tailTrace_7087236
  have hstable : (prefixWord ++ tailWord_7087236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087236).length < 2 ^ (prefixWord ++ tailWord_7087236).sum := by decide
  have hdescent : baseEnd_7087236 < baseStart_7087236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087246 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3]
def baseStart_7087246 : Nat := 118140960795 + 7087246 * 2 ^ 59
def prefixEnd_7087246 : Nat := 4983230072969 + 3 ^ 40 * 7087246 * 2
def baseEnd_7087246 : Nat := 3639163714654883351131355

theorem tailTrace_7087246 : CollatzResearch.WordTrace tailWord_7087246 prefixEnd_7087246 3639163714654883351131355 := by
  unfold tailWord_7087246
  simp only [CollatzResearch.WordTrace]
  refine ⟨32311637210265702762078199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172328731788083748064417061 32311637210265702762078199)
  ·
    refine ⟨48467455815398554143117299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32311637210265702762078199 48467455815398554143117299)
    ·
      refine ⟨72701183723097831214675949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48467455815398554143117299 72701183723097831214675949)
      ·
        refine ⟨27262943896161686705503481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72701183723097831214675949 27262943896161686705503481)
        ·
          refine ⟨20447207922121265029127611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27262943896161686705503481 20447207922121265029127611)
          ·
            refine ⟨30670811883181897543691417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20447207922121265029127611 30670811883181897543691417)
            ·
              refine ⟨23003108912386423157768563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30670811883181897543691417 23003108912386423157768563)
              ·
                refine ⟨34504663368579634736652845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23003108912386423157768563 34504663368579634736652845)
                ·
                  refine ⟨12939248763217363026244817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34504663368579634736652845 12939248763217363026244817)
                  ·
                    refine ⟨9704436572413022269683613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12939248763217363026244817 9704436572413022269683613)
                    ·
                      refine ⟨3639163714654883351131355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9704436572413022269683613 3639163714654883351131355)
                      ·
                        rfl

theorem cell23_7087246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_7087246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087246 prefixEnd_7087246 := by exact prefixLift 7087246
  have htrace : WordTrace (prefixWord ++ tailWord_7087246) baseStart_7087246 baseEnd_7087246 := by
    simpa [prefixWord, tailWord_7087246, baseEnd_7087246] using wordTrace_append hprefix tailTrace_7087246
  have hstable : (prefixWord ++ tailWord_7087246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087246).length < 2 ^ (prefixWord ++ tailWord_7087246).sum := by decide
  have hdescent : baseEnd_7087246 < baseStart_7087246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087260 : List Nat := [2, 2, 3, 2, 1, 2, 1, 5, 1, 2, 2]
def baseStart_7087260 : Nat := 118140960795 + 7087260 * 2 ^ 59
def prefixEnd_7087260 : Nat := 4983230072969 + 3 ^ 40 * 7087260 * 2
def baseEnd_7087260 : Nat := 3639170903384046296356291

theorem tailTrace_7087260 : CollatzResearch.WordTrace tailWord_7087260 prefixEnd_7087260 3639170903384046296356291 := by
  unfold tailWord_7087260
  simp only [CollatzResearch.WordTrace]
  refine ⟨129246804152037451243817617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172329072202716601658423489 129246804152037451243817617)
  ·
    refine ⟨96935103114028088432863213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129246804152037451243817617 96935103114028088432863213)
    ·
      refine ⟨36350663667760533162323705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96935103114028088432863213 36350663667760533162323705)
      ·
        refine ⟨27262997750820399871742779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36350663667760533162323705 27262997750820399871742779)
        ·
          refine ⟨40894496626230599807614169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27262997750820399871742779 40894496626230599807614169)
          ·
            refine ⟨30670872469672949855710627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40894496626230599807614169 30670872469672949855710627)
            ·
              refine ⟨46006308704509424783565941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30670872469672949855710627 46006308704509424783565941)
              ·
                refine ⟨4313091441047758573459307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46006308704509424783565941 4313091441047758573459307)
                ·
                  refine ⟨6469637161571637860188961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4313091441047758573459307 6469637161571637860188961)
                  ·
                    refine ⟨4852227871178728395141721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6469637161571637860188961 4852227871178728395141721)
                    ·
                      refine ⟨3639170903384046296356291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4852227871178728395141721 3639170903384046296356291)
                      ·
                        rfl

theorem cell23_7087260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_7087260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087260 prefixEnd_7087260 := by exact prefixLift 7087260
  have htrace : WordTrace (prefixWord ++ tailWord_7087260) baseStart_7087260 baseEnd_7087260 := by
    simpa [prefixWord, tailWord_7087260, baseEnd_7087260] using wordTrace_append hprefix tailTrace_7087260
  have hstable : (prefixWord ++ tailWord_7087260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087260).length < 2 ^ (prefixWord ++ tailWord_7087260).sum := by decide
  have hdescent : baseEnd_7087260 < baseStart_7087260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087263 : List Nat := [1, 1, 2, 6, 2, 1, 1, 3, 1, 2, 3]
def baseStart_7087263 : Nat := 118140960795 + 7087263 * 2 ^ 59
def prefixEnd_7087263 : Nat := 4983230072969 + 3 ^ 40 * 7087263 * 2
def baseEnd_7087263 : Nat := 3639172443826009784618777

theorem tailTrace_7087263 : CollatzResearch.WordTrace tailWord_7087263 prefixEnd_7087263 3639172443826009784618777 := by
  unfold tailWord_7087263
  simp only [CollatzResearch.WordTrace]
  refine ⟨258493717723064033999994443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172329145148709355999996295 258493717723064033999994443)
  ·
    refine ⟨387740576584596050999991665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258493717723064033999994443 387740576584596050999991665)
    ·
      refine ⟨290805432438447038249993749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387740576584596050999991665 290805432438447038249993749)
      ·
        refine ⟨13631504645552204917968457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 290805432438447038249993749 13631504645552204917968457)
        ·
          refine ⟨10223628484164153688476343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13631504645552204917968457 10223628484164153688476343)
          ·
            refine ⟨15335442726246230532714515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10223628484164153688476343 15335442726246230532714515)
            ·
              refine ⟨23003164089369345799071773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15335442726246230532714515 23003164089369345799071773)
              ·
                refine ⟨8626186533513504674651915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23003164089369345799071773 8626186533513504674651915)
                ·
                  refine ⟨12939279800270257011977873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8626186533513504674651915 12939279800270257011977873)
                  ·
                    refine ⟨9704459850202692758983405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12939279800270257011977873 9704459850202692758983405)
                    ·
                      refine ⟨3639172443826009784618777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9704459850202692758983405 3639172443826009784618777)
                      ·
                        rfl

theorem cell23_7087263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_7087263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087263 prefixEnd_7087263 := by exact prefixLift 7087263
  have htrace : WordTrace (prefixWord ++ tailWord_7087263) baseStart_7087263 baseEnd_7087263 := by
    simpa [prefixWord, tailWord_7087263, baseEnd_7087263] using wordTrace_append hprefix tailTrace_7087263
  have hstable : (prefixWord ++ tailWord_7087263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087263).length < 2 ^ (prefixWord ++ tailWord_7087263).sum := by decide
  have hdescent : baseEnd_7087263 < baseStart_7087263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087276 : List Nat := [2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 3]
def baseStart_7087276 : Nat := 118140960795 + 7087276 * 2 ^ 59
def prefixEnd_7087276 : Nat := 4983230072969 + 3 ^ 40 * 7087276 * 2
def baseEnd_7087276 : Nat := 3639179119074518233756217

theorem tailTrace_7087276 : CollatzResearch.WordTrace tailWord_7087276 prefixEnd_7087276 3639179119074518233756217 := by
  unfold tailWord_7087276
  simp only [CollatzResearch.WordTrace]
  refine ⟨129247095936008468610108841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172329461248011291480145121 129247095936008468610108841)
  ·
    refine ⟨96935321952006351457581631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129247095936008468610108841 96935321952006351457581631)
    ·
      refine ⟨145402982928009527186372447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96935321952006351457581631 145402982928009527186372447)
      ·
        refine ⟨218104474392014290779558671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145402982928009527186372447 218104474392014290779558671)
        ·
          refine ⟨327156711588021436169338007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218104474392014290779558671 327156711588021436169338007)
          ·
            refine ⟨490735067382032154254007011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327156711588021436169338007 490735067382032154254007011)
            ·
              refine ⟨736102601073048231381010517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490735067382032154254007011 736102601073048231381010517)
              ·
                refine ⟨8626202356324783961496217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 736102601073048231381010517 8626202356324783961496217)
                ·
                  refine ⟨6469651767243587971122163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8626202356324783961496217 6469651767243587971122163)
                  ·
                    refine ⟨9704477650865381956683245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6469651767243587971122163 9704477650865381956683245)
                    ·
                      refine ⟨3639179119074518233756217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9704477650865381956683245 3639179119074518233756217)
                      ·
                        rfl

theorem cell23_7087276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 3].length) (baseStart_7087276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087276 prefixEnd_7087276 := by exact prefixLift 7087276
  have htrace : WordTrace (prefixWord ++ tailWord_7087276) baseStart_7087276 baseEnd_7087276 := by
    simpa [prefixWord, tailWord_7087276, baseEnd_7087276] using wordTrace_append hprefix tailTrace_7087276
  have hstable : (prefixWord ++ tailWord_7087276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087276).length < 2 ^ (prefixWord ++ tailWord_7087276).sum := by decide
  have hdescent : baseEnd_7087276 < baseStart_7087276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087339 : List Nat := [1, 1, 1, 1, 2, 6, 3, 1, 7]
def baseStart_7087339 : Nat := 118140960795 + 7087339 * 2 ^ 59
def prefixEnd_7087339 : Nat := 4983230072969 + 3 ^ 40 * 7087339 * 2
def baseEnd_7087339 : Nat := 404356829817305720807603

theorem tailTrace_7087339 : CollatzResearch.WordTrace tailWord_7087339 prefixEnd_7087339 404356829817305720807603 := by
  unfold tailWord_7087339
  simp only [CollatzResearch.WordTrace]
  refine ⟨258496489670788698979761071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172330993113859132653174047 258496489670788698979761071)
  ·
    refine ⟨387744734506183048469641607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258496489670788698979761071 387744734506183048469641607)
    ·
      refine ⟨581617101759274572704462411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387744734506183048469641607 581617101759274572704462411)
      ·
        refine ⟨872425652638911859056693617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581617101759274572704462411 872425652638911859056693617)
        ·
          refine ⟨654319239479183894292520213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 872425652638911859056693617 654319239479183894292520213)
          ·
            refine ⟨30671214350586745044961885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 654319239479183894292520213 30671214350586745044961885)
            ·
              refine ⟨11501705381470029391860707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30671214350586745044961885 11501705381470029391860707)
              ·
                refine ⟨17252558072205044087791061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11501705381470029391860707 17252558072205044087791061)
                ·
                  refine ⟨404356829817305720807603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17252558072205044087791061 404356829817305720807603)
                  ·
                    rfl

theorem cell23_7087339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 7].length) (baseStart_7087339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087339 prefixEnd_7087339 := by exact prefixLift 7087339
  have htrace : WordTrace (prefixWord ++ tailWord_7087339) baseStart_7087339 baseEnd_7087339 := by
    simpa [prefixWord, tailWord_7087339, baseEnd_7087339] using wordTrace_append hprefix tailTrace_7087339
  have hstable : (prefixWord ++ tailWord_7087339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087339).length < 2 ^ (prefixWord ++ tailWord_7087339).sum := by decide
  have hdescent : baseEnd_7087339 < baseStart_7087339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087386 : List Nat := [3, 1, 1, 3, 3, 1, 2, 2, 2, 5]
def baseStart_7087386 : Nat := 118140960795 + 7087386 * 2 ^ 59
def prefixEnd_7087386 : Nat := 4983230072969 + 3 ^ 40 * 7087386 * 2
def baseEnd_7087386 : Nat := 1213078533982170934460237

theorem tailTrace_7087386 : CollatzResearch.WordTrace tailWord_7087386 prefixEnd_7087386 1213078533982170934460237 := by
  unfold tailWord_7087386
  simp only [CollatzResearch.WordTrace]
  refine ⟨64624550975404606501680503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172332135934412284004481341 64624550975404606501680503)
  ·
    refine ⟨96936826463106909752520755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64624550975404606501680503 96936826463106909752520755)
    ·
      refine ⟨145405239694660364628781133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96936826463106909752520755 145405239694660364628781133)
      ·
        refine ⟨54526964885497636735792925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145405239694660364628781133 54526964885497636735792925)
        ·
          refine ⟨20447611832061613775922347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54526964885497636735792925 20447611832061613775922347)
          ·
            refine ⟨30671417748092420663883521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20447611832061613775922347 30671417748092420663883521)
            ·
              refine ⟨23003563311069315497912641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30671417748092420663883521 23003563311069315497912641)
              ·
                refine ⟨17252672483301986623434481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23003563311069315497912641 17252672483301986623434481)
                ·
                  refine ⟨12939504362476489967575861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17252672483301986623434481 12939504362476489967575861)
                  ·
                    refine ⟨1213078533982170934460237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12939504362476489967575861 1213078533982170934460237)
                    ·
                      rfl

theorem cell23_7087386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_7087386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087386 prefixEnd_7087386 := by exact prefixLift 7087386
  have htrace : WordTrace (prefixWord ++ tailWord_7087386) baseStart_7087386 baseEnd_7087386 := by
    simpa [prefixWord, tailWord_7087386, baseEnd_7087386] using wordTrace_append hprefix tailTrace_7087386
  have hstable : (prefixWord ++ tailWord_7087386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087386).length < 2 ^ (prefixWord ++ tailWord_7087386).sum := by decide
  have hdescent : baseEnd_7087386 < baseStart_7087386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087423 : List Nat := [1, 1, 2, 2, 4, 4, 1, 1, 2, 1, 4]
def baseStart_7087423 : Nat := 118140960795 + 7087423 * 2 ^ 59
def prefixEnd_7087423 : Nat := 4983230072969 + 3 ^ 40 * 7087423 * 2
def baseEnd_7087423 : Nat := 3639254600730729158618041

theorem tailTrace_7087423 : CollatzResearch.WordTrace tailWord_7087423 prefixEnd_7087423 3639254600730729158618041 := by
  unfold tailWord_7087423
  simp only [CollatzResearch.WordTrace]
  refine ⟨258499553402484381325818923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172333035601656254217212615 258499553402484381325818923)
  ·
    refine ⟨387749330103726571988728385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258499553402484381325818923 387749330103726571988728385)
    ·
      refine ⟨290811997577794928991546289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387749330103726571988728385 290811997577794928991546289)
      ·
        refine ⟨218108998183346196743659717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290811997577794928991546289 218108998183346196743659717)
        ·
          refine ⟨40895437159377411889436197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218108998183346196743659717 40895437159377411889436197)
          ·
            refine ⟨7667894467383264729269287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40895437159377411889436197 7667894467383264729269287)
            ·
              refine ⟨11501841701074897093903931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7667894467383264729269287 11501841701074897093903931)
              ·
                refine ⟨17252762551612345640855897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11501841701074897093903931 17252762551612345640855897)
                ·
                  refine ⟨12939571913709259230641923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17252762551612345640855897 12939571913709259230641923)
                  ·
                    refine ⟨19409357870563888845962885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12939571913709259230641923 19409357870563888845962885)
                    ·
                      refine ⟨3639254600730729158618041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19409357870563888845962885 3639254600730729158618041)
                      ·
                        rfl

theorem cell23_7087423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 1, 4].length) (baseStart_7087423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087423 prefixEnd_7087423 := by exact prefixLift 7087423
  have htrace : WordTrace (prefixWord ++ tailWord_7087423) baseStart_7087423 baseEnd_7087423 := by
    simpa [prefixWord, tailWord_7087423, baseEnd_7087423] using wordTrace_append hprefix tailTrace_7087423
  have hstable : (prefixWord ++ tailWord_7087423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087423).length < 2 ^ (prefixWord ++ tailWord_7087423).sum := by decide
  have hdescent : baseEnd_7087423 < baseStart_7087423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087433 : List Nat := [1, 2, 1, 1, 2, 3, 3, 5, 1, 4]
def baseStart_7087433 : Nat := 118140960795 + 7087433 * 2 ^ 59
def prefixEnd_7087433 : Nat := 4983230072969 + 3 ^ 40 * 7087433 * 2
def baseEnd_7087433 : Nat := 1213086578512424706497665

theorem tailTrace_7087433 : CollatzResearch.WordTrace tailWord_7087433 prefixEnd_7087433 1213086578512424706497665 := by
  unfold tailWord_7087433
  simp only [CollatzResearch.WordTrace]
  refine ⟨258499918132448153033682953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172333278754965435355788635 258499918132448153033682953)
  ·
    refine ⟨193874938599336114775262215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258499918132448153033682953 193874938599336114775262215)
    ·
      refine ⟨290812407899004172162893323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193874938599336114775262215 290812407899004172162893323)
      ·
        refine ⟨436218611848506258244339985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290812407899004172162893323 436218611848506258244339985)
        ·
          refine ⟨327163958886379693683254989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436218611848506258244339985 327163958886379693683254989)
          ·
            refine ⟨122686484582392385131220621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327163958886379693683254989 122686484582392385131220621)
            ·
              refine ⟨46007431718397144424207733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122686484582392385131220621 46007431718397144424207733)
              ·
                refine ⟨4313196723599732289769475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46007431718397144424207733 4313196723599732289769475)
                ·
                  refine ⟨6469795085399598434654213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4313196723599732289769475 6469795085399598434654213)
                  ·
                    refine ⟨1213086578512424706497665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6469795085399598434654213 1213086578512424706497665)
                    ·
                      rfl

theorem cell23_7087433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 1, 4].length) (baseStart_7087433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087433 prefixEnd_7087433 := by exact prefixLift 7087433
  have htrace : WordTrace (prefixWord ++ tailWord_7087433) baseStart_7087433 baseEnd_7087433 := by
    simpa [prefixWord, tailWord_7087433, baseEnd_7087433] using wordTrace_append hprefix tailTrace_7087433
  have hstable : (prefixWord ++ tailWord_7087433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087433).length < 2 ^ (prefixWord ++ tailWord_7087433).sum := by decide
  have hdescent : baseEnd_7087433 < baseStart_7087433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087449 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 1, 2, 6]
def baseStart_7087449 : Nat := 118140960795 + 7087449 * 2 ^ 59
def prefixEnd_7087449 : Nat := 4983230072969 + 3 ^ 40 * 7087449 * 2
def baseEnd_7087449 : Nat := 3639267951227746056892921

theorem tailTrace_7087449 : CollatzResearch.WordTrace tailWord_7087449 prefixEnd_7087449 3639267951227746056892921 := by
  unfold tailWord_7087449
  simp only [CollatzResearch.WordTrace]
  refine ⟨258500501700390187766265401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172333667800260125177510267 258500501700390187766265401)
  ·
    refine ⟨193875376275292640824699051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258500501700390187766265401 193875376275292640824699051)
    ·
      refine ⟨290813064412938961237048577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193875376275292640824699051 290813064412938961237048577)
      ·
        refine ⟨218109798309704220927786433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290813064412938961237048577 218109798309704220927786433)
        ·
          refine ⟨163582348732278165695839825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218109798309704220927786433 163582348732278165695839825)
          ·
            refine ⟨122686761549208624271879869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163582348732278165695839825 122686761549208624271879869)
            ·
              refine ⟨46007535580953234101954951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122686761549208624271879869 46007535580953234101954951)
              ·
                refine ⟨69011303371429851152932427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46007535580953234101954951 69011303371429851152932427)
                ·
                  refine ⟨103516955057144776729398641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69011303371429851152932427 103516955057144776729398641)
                  ·
                    refine ⟨77637716292858582547048981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103516955057144776729398641 77637716292858582547048981)
                    ·
                      refine ⟨3639267951227746056892921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77637716292858582547048981 3639267951227746056892921)
                      ·
                        rfl

theorem cell23_7087449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_7087449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087449 prefixEnd_7087449 := by exact prefixLift 7087449
  have htrace : WordTrace (prefixWord ++ tailWord_7087449) baseStart_7087449 baseEnd_7087449 := by
    simpa [prefixWord, tailWord_7087449, baseEnd_7087449] using wordTrace_append hprefix tailTrace_7087449
  have hstable : (prefixWord ++ tailWord_7087449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087449).length < 2 ^ (prefixWord ++ tailWord_7087449).sum := by decide
  have hdescent : baseEnd_7087449 < baseStart_7087449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087473 : List Nat := [1, 2, 2, 2, 1, 2, 4, 2, 3, 1, 3]
def baseStart_7087473 : Nat := 118140960795 + 7087473 * 2 ^ 59
def prefixEnd_7087473 : Nat := 4983230072969 + 3 ^ 40 * 7087473 * 2
def baseEnd_7087473 : Nat := 3639280274763453962992811

theorem tailTrace_7087473 : CollatzResearch.WordTrace tailWord_7087473 prefixEnd_7087473 3639280274763453962992811 := by
  unfold tailWord_7087473
  simp only [CollatzResearch.WordTrace]
  refine ⟨258501377052303239865139073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172334251368202159910092715 258501377052303239865139073)
  ·
    refine ⟨193876032789227429898854305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258501377052303239865139073 193876032789227429898854305)
    ·
      refine ⟨145407024591920572424140729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193876032789227429898854305 145407024591920572424140729)
      ·
        refine ⟨109055268443940429318105547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145407024591920572424140729 109055268443940429318105547)
        ·
          refine ⟨163582902665910643977158321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109055268443940429318105547 163582902665910643977158321)
          ·
            refine ⟨122687176999432982982868741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163582902665910643977158321 122687176999432982982868741)
            ·
              refine ⟨23003845687393684309287889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122687176999432982982868741 23003845687393684309287889)
              ·
                refine ⟨17252884265545263231965917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23003845687393684309287889 17252884265545263231965917)
                ·
                  refine ⟨6469831599579473711987219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17252884265545263231965917 6469831599579473711987219)
                  ·
                    refine ⟨9704747399369210567980829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6469831599579473711987219 9704747399369210567980829)
                    ·
                      refine ⟨3639280274763453962992811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9704747399369210567980829 3639280274763453962992811)
                      ·
                        rfl

theorem cell23_7087473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_7087473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087473 prefixEnd_7087473 := by exact prefixLift 7087473
  have htrace : WordTrace (prefixWord ++ tailWord_7087473) baseStart_7087473 baseEnd_7087473 := by
    simpa [prefixWord, tailWord_7087473, baseEnd_7087473] using wordTrace_append hprefix tailTrace_7087473
  have hstable : (prefixWord ++ tailWord_7087473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087473).length < 2 ^ (prefixWord ++ tailWord_7087473).sum := by decide
  have hdescent : baseEnd_7087473 < baseStart_7087473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087483 : List Nat := [1, 1, 1, 1, 1, 6, 2, 3, 2, 3, 2]
def baseStart_7087483 : Nat := 118140960795 + 7087483 * 2 ^ 59
def prefixEnd_7087483 : Nat := 4983230072969 + 3 ^ 40 * 7087483 * 2
def baseEnd_7087483 : Nat := 3639285409569998923867765

theorem tailTrace_7087483 : CollatzResearch.WordTrace tailWord_7087483 prefixEnd_7087483 3639285409569998923867765 := by
  unfold tailWord_7087483
  simp only [CollatzResearch.WordTrace]
  refine ⟨258501741782267011573003103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172334494521511341048668735 258501741782267011573003103)
  ·
    refine ⟨387752612673400517359504655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258501741782267011573003103 387752612673400517359504655)
    ·
      refine ⟨581628919010100776039256983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387752612673400517359504655 581628919010100776039256983)
      ·
        refine ⟨872443378515151164058885475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581628919010100776039256983 872443378515151164058885475)
        ·
          refine ⟨1308665067772726746088328213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872443378515151164058885475 1308665067772726746088328213)
          ·
            refine ⟨61343675051846566222890385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1308665067772726746088328213 61343675051846566222890385)
            ·
              refine ⟨46007756288884924667167789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61343675051846566222890385 46007756288884924667167789)
              ·
                refine ⟨17252908608331846750187921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46007756288884924667167789 17252908608331846750187921)
                ·
                  refine ⟨12939681456248885062640941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17252908608331846750187921 12939681456248885062640941)
                  ·
                    refine ⟨4852380546093331898490353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12939681456248885062640941 4852380546093331898490353)
                    ·
                      refine ⟨3639285409569998923867765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4852380546093331898490353 3639285409569998923867765)
                      ·
                        rfl

theorem cell23_7087483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 3, 2].length) (baseStart_7087483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087483 prefixEnd_7087483 := by exact prefixLift 7087483
  have htrace : WordTrace (prefixWord ++ tailWord_7087483) baseStart_7087483 baseEnd_7087483 := by
    simpa [prefixWord, tailWord_7087483, baseEnd_7087483] using wordTrace_append hprefix tailTrace_7087483
  have hstable : (prefixWord ++ tailWord_7087483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087483).length < 2 ^ (prefixWord ++ tailWord_7087483).sum := by decide
  have hdescent : baseEnd_7087483 < baseStart_7087483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087523 : List Nat := [1, 1, 1, 4, 1, 3, 3, 3, 2, 4]
def baseStart_7087523 : Nat := 118140960795 + 7087523 * 2 ^ 59
def prefixEnd_7087523 : Nat := 4983230072969 + 3 ^ 40 * 7087523 * 2
def baseEnd_7087523 : Nat := 1213101982932059589122527

theorem tailTrace_7087523 : CollatzResearch.WordTrace tailWord_7087523 prefixEnd_7087523 1213101982932059589122527 := by
  unfold tailWord_7087523
  simp only [CollatzResearch.WordTrace]
  refine ⟨258503200702122098404459223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172335467134748065602972815 258503200702122098404459223)
  ·
    refine ⟨387754801053183147606688835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258503200702122098404459223 387754801053183147606688835)
    ·
      refine ⟨581632201579774721410033253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387754801053183147606688835 581632201579774721410033253)
      ·
        refine ⟨109056037796207760264381235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 581632201579774721410033253 109056037796207760264381235)
        ·
          refine ⟨163584056694311640396571853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109056037796207760264381235 163584056694311640396571853)
          ·
            refine ⟨61344021260366865148714445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163584056694311640396571853 61344021260366865148714445)
            ·
              refine ⟨23004007972637574430767917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61344021260366865148714445 23004007972637574430767917)
              ·
                refine ⟨8626502989739090411537969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23004007972637574430767917 8626502989739090411537969)
                ·
                  refine ⟨6469877242304317808653477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8626502989739090411537969 6469877242304317808653477)
                  ·
                    refine ⟨1213101982932059589122527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6469877242304317808653477 1213101982932059589122527)
                    ·
                      rfl

theorem cell23_7087523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 4].length) (baseStart_7087523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087523 prefixEnd_7087523 := by exact prefixLift 7087523
  have htrace : WordTrace (prefixWord ++ tailWord_7087523) baseStart_7087523 baseEnd_7087523 := by
    simpa [prefixWord, tailWord_7087523, baseEnd_7087523] using wordTrace_append hprefix tailTrace_7087523
  have hstable : (prefixWord ++ tailWord_7087523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087523).length < 2 ^ (prefixWord ++ tailWord_7087523).sum := by decide
  have hdescent : baseEnd_7087523 < baseStart_7087523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087563 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 4, 1, 3]
def baseStart_7087563 : Nat := 118140960795 + 7087563 * 2 ^ 59
def prefixEnd_7087563 : Nat := 4983230072969 + 3 ^ 40 * 7087563 * 2
def baseEnd_7087563 : Nat := 3639326488022358610867397

theorem tailTrace_7087563 : CollatzResearch.WordTrace tailWord_7087563 prefixEnd_7087563 3639326488022358610867397 := by
  unfold tailWord_7087563
  simp only [CollatzResearch.WordTrace]
  refine ⟨258504659621977185235915343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172336439747984790157276895 258504659621977185235915343)
  ·
    refine ⟨387756989432965777853873015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258504659621977185235915343 387756989432965777853873015)
    ·
      refine ⟨581635484149448666780809523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387756989432965777853873015 581635484149448666780809523)
      ·
        refine ⟨872453226224173000171214285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581635484149448666780809523 872453226224173000171214285)
        ·
          refine ⟨327169959834064875064205357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 872453226224173000171214285 327169959834064875064205357)
          ·
            refine ⟨122688734937774328149077009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327169959834064875064205357 122688734937774328149077009)
            ·
              refine ⟨92016551203330746111807757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122688734937774328149077009 92016551203330746111807757)
              ·
                refine ⟨34506206701249029791927909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92016551203330746111807757 34506206701249029791927909)
                ·
                  refine ⟨6469913756484193085986483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34506206701249029791927909 6469913756484193085986483)
                  ·
                    refine ⟨9704870634726289628979725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6469913756484193085986483 9704870634726289628979725)
                    ·
                      refine ⟨3639326488022358610867397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9704870634726289628979725 3639326488022358610867397)
                      ·
                        rfl

theorem cell23_7087563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 1, 3].length) (baseStart_7087563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087563 prefixEnd_7087563 := by exact prefixLift 7087563
  have htrace : WordTrace (prefixWord ++ tailWord_7087563) baseStart_7087563 baseEnd_7087563 := by
    simpa [prefixWord, tailWord_7087563, baseEnd_7087563] using wordTrace_append hprefix tailTrace_7087563
  have hstable : (prefixWord ++ tailWord_7087563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087563).length < 2 ^ (prefixWord ++ tailWord_7087563).sum := by decide
  have hdescent : baseEnd_7087563 < baseStart_7087563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087564 : List Nat := [2, 2, 1, 4, 2, 2, 1, 4, 1, 2, 2]
def baseStart_7087564 : Nat := 118140960795 + 7087564 * 2 ^ 59
def prefixEnd_7087564 : Nat := 4983230072969 + 3 ^ 40 * 7087564 * 2
def baseEnd_7087564 : Nat := 3639327001503013106954893

theorem tailTrace_7087564 : CollatzResearch.WordTrace tailWord_7087564 prefixEnd_7087564 3639327001503013106954893 := by
  unfold tailWord_7087564
  simp only [CollatzResearch.WordTrace]
  refine ⟨129252348047486781203350873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172336464063315708271134497 129252348047486781203350873)
  ·
    refine ⟨96939261035615085902513155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129252348047486781203350873 96939261035615085902513155)
    ·
      refine ⟨145408891553422628853769733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96939261035615085902513155 145408891553422628853769733)
      ·
        refine ⟨27264167166266742910081825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145408891553422628853769733 27264167166266742910081825)
        ·
          refine ⟨20448125374700057182561369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27264167166266742910081825 20448125374700057182561369)
          ·
            refine ⟨15336094031025042886921027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20448125374700057182561369 15336094031025042886921027)
            ·
              refine ⟨23004141046537564330381541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15336094031025042886921027 23004141046537564330381541)
              ·
                refine ⟨4313276446225793311946539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23004141046537564330381541 4313276446225793311946539)
                ·
                  refine ⟨6469914669338689967919809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4313276446225793311946539 6469914669338689967919809)
                  ·
                    refine ⟨4852436002004017475939857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6469914669338689967919809 4852436002004017475939857)
                    ·
                      refine ⟨3639327001503013106954893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4852436002004017475939857 3639327001503013106954893)
                      ·
                        rfl

theorem cell23_7087564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_7087564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087564 prefixEnd_7087564 := by exact prefixLift 7087564
  have htrace : WordTrace (prefixWord ++ tailWord_7087564) baseStart_7087564 baseEnd_7087564 := by
    simpa [prefixWord, tailWord_7087564, baseEnd_7087564] using wordTrace_append hprefix tailTrace_7087564
  have hstable : (prefixWord ++ tailWord_7087564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087564).length < 2 ^ (prefixWord ++ tailWord_7087564).sum := by decide
  have hdescent : baseEnd_7087564 < baseStart_7087564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087566 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 2, 7]
def baseStart_7087566 : Nat := 118140960795 + 7087566 * 2 ^ 59
def prefixEnd_7087566 : Nat := 4983230072969 + 3 ^ 40 * 7087566 * 2
def baseEnd_7087566 : Nat := 1213109342821440699709961

theorem tailTrace_7087566 : CollatzResearch.WordTrace tailWord_7087566 prefixEnd_7087566 1213109342821440699709961 := by
  unfold tailWord_7087566
  simp only [CollatzResearch.WordTrace]
  refine ⟨32313096130120789593534319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172336512693977544498849701 32313096130120789593534319)
  ·
    refine ⟨48469644195181184390301479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32313096130120789593534319 48469644195181184390301479)
    ·
      refine ⟨72704466292771776585452219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48469644195181184390301479 72704466292771776585452219)
      ·
        refine ⟨109056699439157664878178329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72704466292771776585452219 109056699439157664878178329)
        ·
          refine ⟨81792524579368248658633747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109056699439157664878178329 81792524579368248658633747)
          ·
            refine ⟨122688786869052372987950621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81792524579368248658633747 122688786869052372987950621)
            ·
              refine ⟨46008295075894639870481483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122688786869052372987950621 46008295075894639870481483)
              ·
                refine ⟨69012442613841959805722225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46008295075894639870481483 69012442613841959805722225)
                ·
                  refine ⟨51759331960381469854291669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69012442613841959805722225 51759331960381469854291669)
                  ·
                    refine ⟨1213109342821440699709961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51759331960381469854291669 1213109342821440699709961)
                    ·
                      rfl

theorem cell23_7087566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_7087566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087566 prefixEnd_7087566 := by exact prefixLift 7087566
  have htrace : WordTrace (prefixWord ++ tailWord_7087566) baseStart_7087566 baseEnd_7087566 := by
    simpa [prefixWord, tailWord_7087566, baseEnd_7087566] using wordTrace_append hprefix tailTrace_7087566
  have hstable : (prefixWord ++ tailWord_7087566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087566).length < 2 ^ (prefixWord ++ tailWord_7087566).sum := by decide
  have hdescent : baseEnd_7087566 < baseStart_7087566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087603 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 2]
def baseStart_7087603 : Nat := 118140960795 + 7087603 * 2 ^ 59
def prefixEnd_7087603 : Nat := 4983230072969 + 3 ^ 40 * 7087603 * 2
def baseEnd_7087603 : Nat := 3639347027248538454367213

theorem tailTrace_7087603 : CollatzResearch.WordTrace tailWord_7087603 prefixEnd_7087603 3639347027248538454367213 := by
  unfold tailWord_7087603
  simp only [CollatzResearch.WordTrace]
  refine ⟨258506118541832272067371463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172337412361221514711580975 258506118541832272067371463)
  ·
    refine ⟨387759177812748408101057195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258506118541832272067371463 387759177812748408101057195)
    ·
      refine ⟨581638766719122612151585793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387759177812748408101057195 581638766719122612151585793)
      ·
        refine ⟨436229075039341959113689345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581638766719122612151585793 436229075039341959113689345)
        ·
          refine ⟨327171806279506469335267009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436229075039341959113689345 327171806279506469335267009)
          ·
            refine ⟨245378854709629852001450257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327171806279506469335267009 245378854709629852001450257)
            ·
              refine ⟨184034141032222389001087693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245378854709629852001450257 184034141032222389001087693)
              ·
                refine ⟨69012802887083395875407885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184034141032222389001087693 69012802887083395875407885)
                ·
                  refine ⟨25879801082656273453277957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69012802887083395875407885 25879801082656273453277957)
                  ·
                    refine ⟨4852462702998051272489617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25879801082656273453277957 4852462702998051272489617)
                    ·
                      refine ⟨3639347027248538454367213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4852462702998051272489617 3639347027248538454367213)
                      ·
                        rfl

theorem cell23_7087603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 2].length) (baseStart_7087603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087603 prefixEnd_7087603 := by exact prefixLift 7087603
  have htrace : WordTrace (prefixWord ++ tailWord_7087603) baseStart_7087603 baseEnd_7087603 := by
    simpa [prefixWord, tailWord_7087603, baseEnd_7087603] using wordTrace_append hprefix tailTrace_7087603
  have hstable : (prefixWord ++ tailWord_7087603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087603).length < 2 ^ (prefixWord ++ tailWord_7087603).sum := by decide
  have hdescent : baseEnd_7087603 < baseStart_7087603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087614 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_7087614 : Nat := 118140960795 + 7087614 * 2 ^ 59
def prefixEnd_7087614 : Nat := 4983230072969 + 3 ^ 40 * 7087614 * 2
def baseEnd_7087614 : Nat := 3639352675535737911329663

theorem tailTrace_7087614 : CollatzResearch.WordTrace tailWord_7087614 prefixEnd_7087614 3639352675535737911329663 := by
  unfold tailWord_7087614
  simp only [CollatzResearch.WordTrace]
  refine ⟨32313314968099052618252737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172337679829861613964014597 32313314968099052618252737)
  ·
    refine ⟨24234986226074289463689553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32313314968099052618252737 24234986226074289463689553)
    ·
      refine ⟨18176239669555717097767165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24234986226074289463689553 18176239669555717097767165)
      ·
        refine ⟨6816089876083393911662687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18176239669555717097767165 6816089876083393911662687)
        ·
          refine ⟨10224134814125090867494031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6816089876083393911662687 10224134814125090867494031)
          ·
            refine ⟨15336202221187636301241047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10224134814125090867494031 15336202221187636301241047)
            ·
              refine ⟨23004303331781454451861571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15336202221187636301241047 23004303331781454451861571)
              ·
                refine ⟨34506454997672181677792357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23004303331781454451861571 34506454997672181677792357)
                ·
                  refine ⟨6469960312063534064586067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34506454997672181677792357 6469960312063534064586067)
                  ·
                    refine ⟨9704940468095301096879101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6469960312063534064586067 9704940468095301096879101)
                    ·
                      refine ⟨3639352675535737911329663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9704940468095301096879101 3639352675535737911329663)
                      ·
                        rfl

theorem cell23_7087614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_7087614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087614 prefixEnd_7087614 := by exact prefixLift 7087614
  have htrace : WordTrace (prefixWord ++ tailWord_7087614) baseStart_7087614 baseEnd_7087614 := by
    simpa [prefixWord, tailWord_7087614, baseEnd_7087614] using wordTrace_append hprefix tailTrace_7087614
  have hstable : (prefixWord ++ tailWord_7087614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087614).length < 2 ^ (prefixWord ++ tailWord_7087614).sum := by decide
  have hdescent : baseEnd_7087614 < baseStart_7087614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087637 : List Nat := [1, 3, 2, 1, 3, 4, 1, 1, 1, 4, 2]
def baseStart_7087637 : Nat := 118140960795 + 7087637 * 2 ^ 59
def prefixEnd_7087637 : Nat := 4983230072969 + 3 ^ 40 * 7087637 * 2
def baseEnd_7087637 : Nat := 3639364485590791321342057

theorem tailTrace_7087637 : CollatzResearch.WordTrace tailWord_7087637 prefixEnd_7087637 3639364485590791321342057 := by
  unfold tailWord_7087637
  simp only [CollatzResearch.WordTrace]
  refine ⟨258507358623709095874109165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172338239082472730582739443 258507358623709095874109165)
  ·
    refine ⟨96940259483890910952790937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258507358623709095874109165 96940259483890910952790937)
    ·
      refine ⟨72705194612918183214593203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96940259483890910952790937 72705194612918183214593203)
      ·
        refine ⟨109057791919377274821889805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72705194612918183214593203 109057791919377274821889805)
        ·
          refine ⟨40896671969766478058208677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109057791919377274821889805 40896671969766478058208677)
          ·
            refine ⟨7668125994331214635914127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40896671969766478058208677 7668125994331214635914127)
            ·
              refine ⟨11502188991496821953871191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7668125994331214635914127 11502188991496821953871191)
              ·
                refine ⟨17253283487245232930806787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11502188991496821953871191 17253283487245232930806787)
                ·
                  refine ⟨25879925230867849396210181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17253283487245232930806787 25879925230867849396210181)
                  ·
                    refine ⟨4852485980787721761789409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25879925230867849396210181 4852485980787721761789409)
                    ·
                      refine ⟨3639364485590791321342057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4852485980787721761789409 3639364485590791321342057)
                      ·
                        rfl

theorem cell23_7087637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_7087637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087637 prefixEnd_7087637 := by exact prefixLift 7087637
  have htrace : WordTrace (prefixWord ++ tailWord_7087637) baseStart_7087637 baseEnd_7087637 := by
    simpa [prefixWord, tailWord_7087637, baseEnd_7087637] using wordTrace_append hprefix tailTrace_7087637
  have hstable : (prefixWord ++ tailWord_7087637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087637).length < 2 ^ (prefixWord ++ tailWord_7087637).sum := by decide
  have hdescent : baseEnd_7087637 < baseStart_7087637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087673 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 4, 5]
def baseStart_7087673 : Nat := 118140960795 + 7087673 * 2 ^ 59
def prefixEnd_7087673 : Nat := 4983230072969 + 3 ^ 40 * 7087673 * 2
def baseEnd_7087673 : Nat := 1213127656964784393497297

theorem tailTrace_7087673 : CollatzResearch.WordTrace tailWord_7087673 prefixEnd_7087673 1213127656964784393497297 := by
  unfold tailWord_7087673
  simp only [CollatzResearch.WordTrace]
  refine ⟨258508671651578674022419673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172339114434385782681613115 258508671651578674022419673)
  ·
    refine ⟨193881503738684005516814755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258508671651578674022419673 193881503738684005516814755)
    ·
      refine ⟨290822255608026008275222133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193881503738684005516814755 290822255608026008275222133)
      ·
        refine ⟨27264586463252438275802075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 290822255608026008275222133 27264586463252438275802075)
        ·
          refine ⟨40896879694878657413703113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27264586463252438275802075 40896879694878657413703113)
          ·
            refine ⟨30672659771158993060277335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40896879694878657413703113 30672659771158993060277335)
            ·
              refine ⟨46008989656738489590416003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30672659771158993060277335 46008989656738489590416003)
              ·
                refine ⟨69013484485107734385624005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46008989656738489590416003 69013484485107734385624005)
                ·
                  refine ⟨12940028340957700197304501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69013484485107734385624005 12940028340957700197304501)
                  ·
                    refine ⟨1213127656964784393497297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12940028340957700197304501 1213127656964784393497297)
                    ·
                      rfl

theorem cell23_7087673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 5].length) (baseStart_7087673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087673 prefixEnd_7087673 := by exact prefixLift 7087673
  have htrace : WordTrace (prefixWord ++ tailWord_7087673) baseStart_7087673 baseEnd_7087673 := by
    simpa [prefixWord, tailWord_7087673, baseEnd_7087673] using wordTrace_append hprefix tailTrace_7087673
  have hstable : (prefixWord ++ tailWord_7087673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087673).length < 2 ^ (prefixWord ++ tailWord_7087673).sum := by decide
  have hdescent : baseEnd_7087673 < baseStart_7087673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087677 : List Nat := [1, 4, 1, 3, 4, 1, 1, 1, 7]
def baseStart_7087677 : Nat := 118140960795 + 7087677 * 2 ^ 59
def prefixEnd_7087677 : Nat := 4983230072969 + 3 ^ 40 * 7087677 * 2
def baseEnd_7087677 : Nat := 404376113868552351649097

theorem tailTrace_7087677 : CollatzResearch.WordTrace tailWord_7087677 prefixEnd_7087677 404376113868552351649097 := by
  unfold tailWord_7087677
  simp only [CollatzResearch.WordTrace]
  refine ⟨258508817543564182705565285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172339211695709455137043523 258508817543564182705565285)
  ·
    refine ⟨48470403289418284257293491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258508817543564182705565285 48470403289418284257293491)
    ·
      refine ⟨72705604934127426385940237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48470403289418284257293491 72705604934127426385940237)
      ·
        refine ⟨27264601850297784894727589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72705604934127426385940237 27264601850297784894727589)
        ·
          refine ⟨5112112846930834667761423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27264601850297784894727589 5112112846930834667761423)
          ·
            refine ⟨7668169270396252001642135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5112112846930834667761423 7668169270396252001642135)
            ·
              refine ⟨11502253905594378002463203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7668169270396252001642135 11502253905594378002463203)
              ·
                refine ⟨17253380858391567003694805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11502253905594378002463203 17253380858391567003694805)
                ·
                  refine ⟨404376113868552351649097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17253380858391567003694805 404376113868552351649097)
                  ·
                    rfl

theorem cell23_7087677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_7087677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087677 prefixEnd_7087677 := by exact prefixLift 7087677
  have htrace : WordTrace (prefixWord ++ tailWord_7087677) baseStart_7087677 baseEnd_7087677 := by
    simpa [prefixWord, tailWord_7087677, baseEnd_7087677] using wordTrace_append hprefix tailTrace_7087677
  have hstable : (prefixWord ++ tailWord_7087677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087677).length < 2 ^ (prefixWord ++ tailWord_7087677).sum := by decide
  have hdescent : baseEnd_7087677 < baseStart_7087677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087737 : List Nat := [1, 2, 1, 3, 3, 1, 3, 4, 1, 4]
def baseStart_7087737 : Nat := 118140960795 + 7087737 * 2 ^ 59
def prefixEnd_7087737 : Nat := 4983230072969 + 3 ^ 40 * 7087737 * 2
def baseEnd_7087737 : Nat := 1213138611218746976697199

theorem tailTrace_7087737 : CollatzResearch.WordTrace tailWord_7087737 prefixEnd_7087737 1213138611218746976697199 := by
  unfold tailWord_7087737
  simp only [CollatzResearch.WordTrace]
  refine ⟨258511005923346812952749465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172340670615564541968499643 258511005923346812952749465)
  ·
    refine ⟨193883254442510109714562099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258511005923346812952749465 193883254442510109714562099)
    ·
      refine ⟨290824881663765164571843149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193883254442510109714562099 290824881663765164571843149)
      ·
        refine ⟨109059330623911936714441181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290824881663765164571843149 109059330623911936714441181)
        ·
          refine ⟨40897248983966976267915443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109059330623911936714441181 40897248983966976267915443)
          ·
            refine ⟨61345873475950464401873165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40897248983966976267915443 61345873475950464401873165)
            ·
              refine ⟨23004702553481424150702437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61345873475950464401873165 23004702553481424150702437)
              ·
                refine ⟨4313381728777767028256707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23004702553481424150702437 4313381728777767028256707)
                ·
                  refine ⟨6470072593166650542385061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4313381728777767028256707 6470072593166650542385061)
                  ·
                    refine ⟨1213138611218746976697199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6470072593166650542385061 1213138611218746976697199)
                    ·
                      rfl

theorem cell23_7087737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 1, 4].length) (baseStart_7087737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087737 prefixEnd_7087737 := by exact prefixLift 7087737
  have htrace : WordTrace (prefixWord ++ tailWord_7087737) baseStart_7087737 baseEnd_7087737 := by
    simpa [prefixWord, tailWord_7087737, baseEnd_7087737] using wordTrace_append hprefix tailTrace_7087737
  have hstable : (prefixWord ++ tailWord_7087737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087737).length < 2 ^ (prefixWord ++ tailWord_7087737).sum := by decide
  have hdescent : baseEnd_7087737 < baseStart_7087737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087773 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_7087773 : Nat := 118140960795 + 7087773 * 2 ^ 59
def prefixEnd_7087773 : Nat := 4983230072969 + 3 ^ 40 * 7087773 * 2
def baseEnd_7087773 : Nat := 3639434318959802789241431

theorem tailTrace_7087773 : CollatzResearch.WordTrace tailWord_7087773 prefixEnd_7087773 3639434318959802789241431 := by
  unfold tailWord_7087773
  simp only [CollatzResearch.WordTrace]
  refine ⟨258512318951216391101059973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172341545967477594067373315 258512318951216391101059973)
  ·
    refine ⟨48471059803353073331448745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258512318951216391101059973 48471059803353073331448745)
    ·
      refine ⟨36353294852514804998586559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48471059803353073331448745 36353294852514804998586559)
      ·
        refine ⟨54529942278772207497879839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36353294852514804998586559 54529942278772207497879839)
        ·
          refine ⟨81794913418158311246819759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54529942278772207497879839 81794913418158311246819759)
          ·
            refine ⟨122692370127237466870229639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81794913418158311246819759 122692370127237466870229639)
            ·
              refine ⟨184038555190856200305344459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122692370127237466870229639 184038555190856200305344459)
              ·
                refine ⟨276057832786284300458016689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184038555190856200305344459 276057832786284300458016689)
                ·
                  refine ⟨207043374589713225343512517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276057832786284300458016689 207043374589713225343512517)
                  ·
                    refine ⟨38820632735571229751908597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 207043374589713225343512517 38820632735571229751908597)
                    ·
                      refine ⟨3639434318959802789241431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38820632735571229751908597 3639434318959802789241431)
                      ·
                        rfl

theorem cell23_7087773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_7087773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087773 prefixEnd_7087773 := by exact prefixLift 7087773
  have htrace : WordTrace (prefixWord ++ tailWord_7087773) baseStart_7087773 baseEnd_7087773 := by
    simpa [prefixWord, tailWord_7087773, baseEnd_7087773] using wordTrace_append hprefix tailTrace_7087773
  have hstable : (prefixWord ++ tailWord_7087773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087773).length < 2 ^ (prefixWord ++ tailWord_7087773).sum := by decide
  have hdescent : baseEnd_7087773 < baseStart_7087773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087784 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 8]
def baseStart_7087784 : Nat := 118140960795 + 7087784 * 2 ^ 59
def prefixEnd_7087784 : Nat := 4983230072969 + 3 ^ 40 * 7087784 * 2
def baseEnd_7087784 : Nat := 404382218583000249578209

theorem tailTrace_7087784 : CollatzResearch.WordTrace tailWord_7087784 prefixEnd_7087784 404382218583000249578209 := by
  unfold tailWord_7087784
  simp only [CollatzResearch.WordTrace]
  refine ⟨129256360077088269989855203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172341813436117693319806937 129256360077088269989855203)
  ·
    refine ⟨193884540115632404984782805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129256360077088269989855203 193884540115632404984782805)
    ·
      refine ⟨4544168908960134491830847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 193884540115632404984782805 4544168908960134491830847)
      ·
        refine ⟨6816253363440201737746271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4544168908960134491830847 6816253363440201737746271)
        ·
          refine ⟨10224380045160302606619407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6816253363440201737746271 10224380045160302606619407)
          ·
            refine ⟨15336570067740453909929111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10224380045160302606619407 15336570067740453909929111)
            ·
              refine ⟨23004855101610680864893667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15336570067740453909929111 23004855101610680864893667)
              ·
                refine ⟨34507282652416021297340501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23004855101610680864893667 34507282652416021297340501)
                ·
                  refine ⟨404382218583000249578209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34507282652416021297340501 404382218583000249578209)
                  ·
                    rfl

theorem cell23_7087784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 8].length) (baseStart_7087784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087784 prefixEnd_7087784 := by exact prefixLift 7087784
  have htrace : WordTrace (prefixWord ++ tailWord_7087784) baseStart_7087784 baseEnd_7087784 := by
    simpa [prefixWord, tailWord_7087784, baseEnd_7087784] using wordTrace_append hprefix tailTrace_7087784
  have hstable : (prefixWord ++ tailWord_7087784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087784).length < 2 ^ (prefixWord ++ tailWord_7087784).sum := by decide
  have hdescent : baseEnd_7087784 < baseStart_7087784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087794 : List Nat := [3, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3]
def baseStart_7087794 : Nat := 118140960795 + 7087794 * 2 ^ 59
def prefixEnd_7087794 : Nat := 4983230072969 + 3 ^ 40 * 7087794 * 2
def baseEnd_7087794 : Nat := 3639445102053547207078835

theorem tailTrace_7087794 : CollatzResearch.WordTrace tailWord_7087794 prefixEnd_7087794 3639445102053547207078835 := by
  unfold tailWord_7087794
  simp only [CollatzResearch.WordTrace]
  refine ⟨64628271221035077921893609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172342056589426874458382957 64628271221035077921893609)
  ·
    refine ⟨48471203415776308441420207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64628271221035077921893609 48471203415776308441420207)
    ·
      refine ⟨72706805123664462662130311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48471203415776308441420207 72706805123664462662130311)
      ·
        refine ⟨109060207685496693993195467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72706805123664462662130311 109060207685496693993195467)
        ·
          refine ⟨163590311528245040989793201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109060207685496693993195467 163590311528245040989793201)
          ·
            refine ⟨122692733646183780742344901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163590311528245040989793201 122692733646183780742344901)
            ·
              refine ⟨23004887558659458889189669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122692733646183780742344901 23004887558659458889189669)
              ·
                refine ⟨4313416417248648541723063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23004887558659458889189669 4313416417248648541723063)
                ·
                  refine ⟨6470124625872972812584595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4313416417248648541723063 6470124625872972812584595)
                  ·
                    refine ⟨9705186938809459218876893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6470124625872972812584595 9705186938809459218876893)
                    ·
                      refine ⟨3639445102053547207078835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9705186938809459218876893 3639445102053547207078835)
                      ·
                        rfl

theorem cell23_7087794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_7087794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087794 prefixEnd_7087794 := by exact prefixLift 7087794
  have htrace : WordTrace (prefixWord ++ tailWord_7087794) baseStart_7087794 baseEnd_7087794 := by
    simpa [prefixWord, tailWord_7087794, baseEnd_7087794] using wordTrace_append hprefix tailTrace_7087794
  have hstable : (prefixWord ++ tailWord_7087794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087794).length < 2 ^ (prefixWord ++ tailWord_7087794).sum := by decide
  have hdescent : baseEnd_7087794 < baseStart_7087794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087813 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 1, 1, 6]
def baseStart_7087813 : Nat := 118140960795 + 7087813 * 2 ^ 59
def prefixEnd_7087813 : Nat := 4983230072969 + 3 ^ 40 * 7087813 * 2
def baseEnd_7087813 : Nat := 3639454858185982632741247

theorem tailTrace_7087813 : CollatzResearch.WordTrace tailWord_7087813 prefixEnd_7087813 3639454858185982632741247 := by
  unfold tailWord_7087813
  simp only [CollatzResearch.WordTrace]
  refine ⟨258513777871071477932516093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172342518580714318621677395 258513777871071477932516093)
  ·
    refine ⟨96942666701651804224693535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258513777871071477932516093 96942666701651804224693535)
    ·
      refine ⟨145414000052477706337040303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96942666701651804224693535 145414000052477706337040303)
      ·
        refine ⟨218121000078716559505560455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145414000052477706337040303 218121000078716559505560455)
        ·
          refine ⟨327181500118074839258340683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218121000078716559505560455 327181500118074839258340683)
          ·
            refine ⟨490772250177112258887511025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327181500118074839258340683 490772250177112258887511025)
            ·
              refine ⟨368079187632834194165633269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490772250177112258887511025 368079187632834194165633269)
              ·
                refine ⟨34507423840578205703028119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 368079187632834194165633269 34507423840578205703028119)
                ·
                  refine ⟨51761135760867308554542179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34507423840578205703028119 51761135760867308554542179)
                  ·
                    refine ⟨77641703641300962831813269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51761135760867308554542179 77641703641300962831813269)
                    ·
                      refine ⟨3639454858185982632741247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77641703641300962831813269 3639454858185982632741247)
                      ·
                        rfl

theorem cell23_7087813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_7087813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087813 prefixEnd_7087813 := by exact prefixLift 7087813
  have htrace : WordTrace (prefixWord ++ tailWord_7087813) baseStart_7087813 baseEnd_7087813 := by
    simpa [prefixWord, tailWord_7087813, baseEnd_7087813] using wordTrace_append hprefix tailTrace_7087813
  have hstable : (prefixWord ++ tailWord_7087813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087813).length < 2 ^ (prefixWord ++ tailWord_7087813).sum := by decide
  have hdescent : baseEnd_7087813 < baseStart_7087813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087828 : List Nat := [2, 4, 1, 3, 1, 3, 1, 3, 1, 1, 3]
def baseStart_7087828 : Nat := 118140960795 + 7087828 * 2 ^ 59
def prefixEnd_7087828 : Nat := 4983230072969 + 3 ^ 40 * 7087828 * 2
def baseEnd_7087828 : Nat := 3639462560395800074053679

theorem tailTrace_7087828 : CollatzResearch.WordTrace tailWord_7087828 prefixEnd_7087828 3639462560395800074053679 := by
  unfold tailWord_7087828
  simp only [CollatzResearch.WordTrace]
  refine ⟨129257162483008567747156069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172342883310678090329541425 129257162483008567747156069)
  ·
    refine ⟨24235717965564106452591763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129257162483008567747156069 24235717965564106452591763)
    ·
      refine ⟨36353576948346159678887645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24235717965564106452591763 36353576948346159678887645)
      ·
        refine ⟨13632591355629809879582867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36353576948346159678887645 13632591355629809879582867)
        ·
          refine ⟨20448887033444714819374301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13632591355629809879582867 20448887033444714819374301)
          ·
            refine ⟨7668332637541768057265363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20448887033444714819374301 7668332637541768057265363)
            ·
              refine ⟨11502498956312652085898045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7668332637541768057265363 11502498956312652085898045)
              ·
                refine ⟨4313437108617244532211767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11502498956312652085898045 4313437108617244532211767)
                ·
                  refine ⟨6470155662925866798317651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4313437108617244532211767 6470155662925866798317651)
                  ·
                    refine ⟨9705233494388800197476477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6470155662925866798317651 9705233494388800197476477)
                    ·
                      refine ⟨3639462560395800074053679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9705233494388800197476477 3639462560395800074053679)
                      ·
                        rfl

theorem cell23_7087828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_7087828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087828 prefixEnd_7087828 := by exact prefixLift 7087828
  have htrace : WordTrace (prefixWord ++ tailWord_7087828) baseStart_7087828 baseEnd_7087828 := by
    simpa [prefixWord, tailWord_7087828, baseEnd_7087828] using wordTrace_append hprefix tailTrace_7087828
  have hstable : (prefixWord ++ tailWord_7087828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087828).length < 2 ^ (prefixWord ++ tailWord_7087828).sum := by decide
  have hdescent : baseEnd_7087828 < baseStart_7087828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087900 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 2, 6]
def baseStart_7087900 : Nat := 118140960795 + 7087900 * 2 ^ 59
def prefixEnd_7087900 : Nat := 4983230072969 + 3 ^ 40 * 7087900 * 2
def baseEnd_7087900 : Nat := 1213166510334307930784449

theorem tailTrace_7087900 : CollatzResearch.WordTrace tailWord_7087900 prefixEnd_7087900 1213166510334307930784449 := by
  unfold tailWord_7087900
  simp only [CollatzResearch.WordTrace]
  refine ⟨129258475510878145895466577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172344634014504194527288769 129258475510878145895466577)
  ·
    refine ⟨96943856633158609421599933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129258475510878145895466577 96943856633158609421599933)
    ·
      refine ⟨36353946237434478533099975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96943856633158609421599933 36353946237434478533099975)
      ·
        refine ⟨54530919356151717799649963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36353946237434478533099975 54530919356151717799649963)
        ·
          refine ⟨81796379034227576699474945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54530919356151717799649963 81796379034227576699474945)
          ·
            refine ⟨61347284275670682524606209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81796379034227576699474945 61347284275670682524606209)
            ·
              refine ⟨46010463206753011893454657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61347284275670682524606209 46010463206753011893454657)
              ·
                refine ⟨34507847405064758920090993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46010463206753011893454657 34507847405064758920090993)
                ·
                  refine ⟨25880885553798569190068245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34507847405064758920090993 25880885553798569190068245)
                  ·
                    refine ⟨1213166510334307930784449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25880885553798569190068245 1213166510334307930784449)
                    ·
                      rfl

theorem cell23_7087900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_7087900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087900 prefixEnd_7087900 := by exact prefixLift 7087900
  have htrace : WordTrace (prefixWord ++ tailWord_7087900) baseStart_7087900 baseEnd_7087900 := by
    simpa [prefixWord, tailWord_7087900, baseEnd_7087900] using wordTrace_append hprefix tailTrace_7087900
  have hstable : (prefixWord ++ tailWord_7087900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087900).length < 2 ^ (prefixWord ++ tailWord_7087900).sum := by decide
  have hdescent : baseEnd_7087900 < baseStart_7087900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087902 : List Nat := [4, 3, 2, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_7087902 : Nat := 118140960795 + 7087902 * 2 ^ 59
def prefixEnd_7087902 : Nat := 4983230072969 + 3 ^ 40 * 7087902 * 2
def baseEnd_7087902 : Nat := 3639500557964232784528339

theorem tailTrace_7087902 : CollatzResearch.WordTrace tailWord_7087902 prefixEnd_7087902 3639500557964232784528339 := by
  unfold tailWord_7087902
  simp only [CollatzResearch.WordTrace]
  refine ⟨32314627995968630766563245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172344682645166030755003973 32314627995968630766563245)
  ·
    refine ⟨12117985498488236537461217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32314627995968630766563245 12117985498488236537461217)
    ·
      refine ⟨9088489123866177403095913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12117985498488236537461217 9088489123866177403095913)
      ·
        refine ⟨6816366842899633052321935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9088489123866177403095913 6816366842899633052321935)
        ·
          refine ⟨10224550264349449578482903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6816366842899633052321935 10224550264349449578482903)
          ·
            refine ⟨15336825396524174367724355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10224550264349449578482903 15336825396524174367724355)
            ·
              refine ⟨23005238094786261551586533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15336825396524174367724355 23005238094786261551586533)
              ·
                refine ⟨4313482142772424040922475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23005238094786261551586533 4313482142772424040922475)
                ·
                  refine ⟨6470223214158636061383713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4313482142772424040922475 6470223214158636061383713)
                  ·
                    refine ⟨4852667410618977046037785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6470223214158636061383713 4852667410618977046037785)
                    ·
                      refine ⟨3639500557964232784528339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4852667410618977046037785 3639500557964232784528339)
                      ·
                        rfl

theorem cell23_7087902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_7087902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087902 prefixEnd_7087902 := by exact prefixLift 7087902
  have htrace : WordTrace (prefixWord ++ tailWord_7087902) baseStart_7087902 baseEnd_7087902 := by
    simpa [prefixWord, tailWord_7087902, baseEnd_7087902] using wordTrace_append hprefix tailTrace_7087902
  have hstable : (prefixWord ++ tailWord_7087902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087902).length < 2 ^ (prefixWord ++ tailWord_7087902).sum := by decide
  have hdescent : baseEnd_7087902 < baseStart_7087902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087930 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 9]
def baseStart_7087930 : Nat := 118140960795 + 7087930 * 2 ^ 59
def prefixEnd_7087930 : Nat := 4983230072969 + 3 ^ 40 * 7087930 * 2
def baseEnd_7087930 : Nat := 404390548380284297219801

theorem tailTrace_7087930 : CollatzResearch.WordTrace tailWord_7087930 prefixEnd_7087930 404390548380284297219801 := by
  unfold tailWord_7087930
  simp only [CollatzResearch.WordTrace]
  refine ⟨64629511302911901728631311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172345363474431737943016829 64629511302911901728631311)
  ·
    refine ⟨96944266954367852592946967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64629511302911901728631311 96944266954367852592946967)
    ·
      refine ⟨145416400431551778889420451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96944266954367852592946967 145416400431551778889420451)
      ·
        refine ⟨218124600647327668334130677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145416400431551778889420451 218124600647327668334130677)
        ·
          refine ⟨20449181310686968906324751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 218124600647327668334130677 20449181310686968906324751)
          ·
            refine ⟨30673771966030453359487127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20449181310686968906324751 30673771966030453359487127)
            ·
              refine ⟨46010657949045680039230691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30673771966030453359487127 46010657949045680039230691)
              ·
                refine ⟨69015986923568520058846037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46010657949045680039230691 69015986923568520058846037)
                ·
                  refine ⟨404390548380284297219801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69015986923568520058846037 404390548380284297219801)
                  ·
                    rfl

theorem cell23_7087930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 9].length) (baseStart_7087930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087930 prefixEnd_7087930 := by exact prefixLift 7087930
  have htrace : WordTrace (prefixWord ++ tailWord_7087930) baseStart_7087930 baseEnd_7087930 := by
    simpa [prefixWord, tailWord_7087930, baseEnd_7087930] using wordTrace_append hprefix tailTrace_7087930
  have hstable : (prefixWord ++ tailWord_7087930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087930).length < 2 ^ (prefixWord ++ tailWord_7087930).sum := by decide
  have hdescent : baseEnd_7087930 < baseStart_7087930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087957 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 2, 3, 3]
def baseStart_7087957 : Nat := 118140960795 + 7087957 * 2 ^ 59
def prefixEnd_7087957 : Nat := 4983230072969 + 3 ^ 40 * 7087957 * 2
def baseEnd_7087957 : Nat := 3639528799400230069340585

theorem tailTrace_7087957 : CollatzResearch.WordTrace tailWord_7087957 prefixEnd_7087957 3639528799400230069340585 := by
  unfold tailWord_7087957
  simp only [CollatzResearch.WordTrace]
  refine ⟨258519029982549790525758125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172346019988366527017172083 258519029982549790525758125)
  ·
    refine ⟨96944636243456171447159297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258519029982549790525758125 96944636243456171447159297)
    ·
      refine ⟨72708477182592128585369473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96944636243456171447159297 72708477182592128585369473)
      ·
        refine ⟨54531357886944096439027105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72708477182592128585369473 54531357886944096439027105)
        ·
          refine ⟨40898518415208072329270329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54531357886944096439027105 40898518415208072329270329)
          ·
            refine ⟨30673888811406054246952747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40898518415208072329270329 30673888811406054246952747)
            ·
              refine ⟨46010833217109081370429121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30673888811406054246952747 46010833217109081370429121)
              ·
                refine ⟨34508124912831811027821841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46010833217109081370429121 34508124912831811027821841)
                ·
                  refine ⟨25881093684623858270866381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34508124912831811027821841 25881093684623858270866381)
                  ·
                    refine ⟨9705410131733946851574893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25881093684623858270866381 9705410131733946851574893)
                    ·
                      refine ⟨3639528799400230069340585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9705410131733946851574893 3639528799400230069340585)
                      ·
                        rfl

theorem cell23_7087957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_7087957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087957 prefixEnd_7087957 := by exact prefixLift 7087957
  have htrace : WordTrace (prefixWord ++ tailWord_7087957) baseStart_7087957 baseEnd_7087957 := by
    simpa [prefixWord, tailWord_7087957, baseEnd_7087957] using wordTrace_append hprefix tailTrace_7087957
  have hstable : (prefixWord ++ tailWord_7087957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087957).length < 2 ^ (prefixWord ++ tailWord_7087957).sum := by decide
  have hdescent : baseEnd_7087957 < baseStart_7087957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087964 : List Nat := [2, 2, 4, 2, 2, 1, 2, 1, 7]
def baseStart_7087964 : Nat := 118140960795 + 7087964 * 2 ^ 59
def prefixEnd_7087964 : Nat := 4983230072969 + 3 ^ 40 * 7087964 * 2
def baseEnd_7087964 : Nat := 404392488196090171328117

theorem tailTrace_7087964 : CollatzResearch.WordTrace tailWord_7087964 prefixEnd_7087964 404392488196090171328117 := by
  unfold tailWord_7087964
  simp only [CollatzResearch.WordTrace]
  refine ⟨129259642646762215360631473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172346190195682953814175297 129259642646762215360631473)
  ·
    refine ⟨96944731985071661520473605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129259642646762215360631473 96944731985071661520473605)
    ·
      refine ⟨18177137247200936535088801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96944731985071661520473605 18177137247200936535088801)
      ·
        refine ⟨13632852935400702401316601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18177137247200936535088801 13632852935400702401316601)
        ·
          refine ⟨10224639701550526800987451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13632852935400702401316601 10224639701550526800987451)
          ·
            refine ⟨15336959552325790201481177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10224639701550526800987451 15336959552325790201481177)
            ·
              refine ⟨11502719664244342651110883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15336959552325790201481177 11502719664244342651110883)
              ·
                refine ⟨17254079496366513976666325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11502719664244342651110883 17254079496366513976666325)
                ·
                  refine ⟨404392488196090171328117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17254079496366513976666325 404392488196090171328117)
                  ·
                    rfl

theorem cell23_7087964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 7].length) (baseStart_7087964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087964 prefixEnd_7087964 := by exact prefixLift 7087964
  have htrace : WordTrace (prefixWord ++ tailWord_7087964) baseStart_7087964 baseEnd_7087964 := by
    simpa [prefixWord, tailWord_7087964, baseEnd_7087964] using wordTrace_append hprefix tailTrace_7087964
  have hstable : (prefixWord ++ tailWord_7087964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087964).length < 2 ^ (prefixWord ++ tailWord_7087964).sum := by decide
  have hdescent : baseEnd_7087964 < baseStart_7087964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087997 : List Nat := [1, 4, 1, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_7087997 : Nat := 118140960795 + 7087997 * 2 ^ 59
def prefixEnd_7087997 : Nat := 4983230072969 + 3 ^ 40 * 7087997 * 2
def baseEnd_7087997 : Nat := 3639549338626409912840401

theorem tailTrace_7087997 : CollatzResearch.WordTrace tailWord_7087997 prefixEnd_7087997 3639549338626409912840401 := by
  unfold tailWord_7087997
  simp only [CollatzResearch.WordTrace]
  refine ⟨258520488902404877357214245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172346992601603251571476163 258520488902404877357214245)
  ·
    refine ⟨48472591669200914504477671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258520488902404877357214245 48472591669200914504477671)
    ·
      refine ⟨72708887503801371756716507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48472591669200914504477671 72708887503801371756716507)
      ·
        refine ⟨109063331255702057635074761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72708887503801371756716507 109063331255702057635074761)
        ·
          refine ⟨81797498441776543226306071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109063331255702057635074761 81797498441776543226306071)
          ·
            refine ⟨122696247662664814839459107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81797498441776543226306071 122696247662664814839459107)
            ·
              refine ⟨184044371493997222259188661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122696247662664814839459107 184044371493997222259188661)
              ·
                refine ⟨17254159827562239586798937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184044371493997222259188661 17254159827562239586798937)
                ·
                  refine ⟨12940619870671679690099203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17254159827562239586798937 12940619870671679690099203)
                  ·
                    refine ⟨19410929806007519535148805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12940619870671679690099203 19410929806007519535148805)
                    ·
                      refine ⟨3639549338626409912840401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19410929806007519535148805 3639549338626409912840401)
                      ·
                        rfl

theorem cell23_7087997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_7087997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087997 prefixEnd_7087997 := by exact prefixLift 7087997
  have htrace : WordTrace (prefixWord ++ tailWord_7087997) baseStart_7087997 baseEnd_7087997 := by
    simpa [prefixWord, tailWord_7087997, baseEnd_7087997] using wordTrace_append hprefix tailTrace_7087997
  have hstable : (prefixWord ++ tailWord_7087997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087997).length < 2 ^ (prefixWord ++ tailWord_7087997).sum := by decide
  have hdescent : baseEnd_7087997 < baseStart_7087997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7087998 : List Nat := [4, 2, 3, 1, 1, 3, 1, 3, 5]
def baseStart_7087998 : Nat := 118140960795 + 7087998 * 2 ^ 59
def prefixEnd_7087998 : Nat := 4983230072969 + 3 ^ 40 * 7087998 * 2
def baseEnd_7087998 : Nat := 404394428011896045436433

theorem tailTrace_7087998 : CollatzResearch.WordTrace tailWord_7087998 prefixEnd_7087998 404394428011896045436433 := by
  unfold tailWord_7087998
  simp only [CollatzResearch.WordTrace]
  refine ⟨32315065671925156816000081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172347016916934169685333765 32315065671925156816000081)
  ·
    refine ⟨24236299253943867612000061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32315065671925156816000081 24236299253943867612000061)
    ·
      refine ⟨9088612220228950354500023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24236299253943867612000061 9088612220228950354500023)
      ·
        refine ⟨13632918330343425531750035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9088612220228950354500023 13632918330343425531750035)
        ·
          refine ⟨20449377495515138297625053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13632918330343425531750035 20449377495515138297625053)
          ·
            refine ⟨7668516560818176861609395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20449377495515138297625053 7668516560818176861609395)
            ·
              refine ⟨11502774841227265292414093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7668516560818176861609395 11502774841227265292414093)
              ·
                refine ⟨4313540565460224484655285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11502774841227265292414093 4313540565460224484655285)
                ·
                  refine ⟨404394428011896045436433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4313540565460224484655285 404394428011896045436433)
                  ·
                    rfl

theorem cell23_7087998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_7087998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7087998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7087998 prefixEnd_7087998 := by exact prefixLift 7087998
  have htrace : WordTrace (prefixWord ++ tailWord_7087998) baseStart_7087998 baseEnd_7087998 := by
    simpa [prefixWord, tailWord_7087998, baseEnd_7087998] using wordTrace_append hprefix tailTrace_7087998
  have hstable : (prefixWord ++ tailWord_7087998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7087998).length < 2 ^ (prefixWord ++ tailWord_7087998).sum := by decide
  have hdescent : baseEnd_7087998 < baseStart_7087998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7087998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088017 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 3]
def baseStart_7088017 : Nat := 118140960795 + 7088017 * 2 ^ 59
def prefixEnd_7088017 : Nat := 4983230072969 + 3 ^ 40 * 7088017 * 2
def baseEnd_7088017 : Nat := 3639559608239499834590309

theorem tailTrace_7088017 : CollatzResearch.WordTrace tailWord_7088017 prefixEnd_7088017 3639559608239499834590309 := by
  unfold tailWord_7088017
  simp only [CollatzResearch.WordTrace]
  refine ⟨258521218362332420772942305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172347478908221613848628203 258521218362332420772942305)
  ·
    refine ⟨193890913771749315579706729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258521218362332420772942305 193890913771749315579706729)
    ·
      refine ⟨145418185328811986684780047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193890913771749315579706729 145418185328811986684780047)
      ·
        refine ⟨218127277993217980027170071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145418185328811986684780047 218127277993217980027170071)
        ·
          refine ⟨327190916989826970040755107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218127277993217980027170071 327190916989826970040755107)
          ·
            refine ⟨490786375484740455061132661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327190916989826970040755107 490786375484740455061132661)
            ·
              refine ⟨46011222701694417661981187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 490786375484740455061132661 46011222701694417661981187)
              ·
                refine ⟨69016834052541626492971781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46011222701694417661981187 69016834052541626492971781)
                ·
                  refine ⟨12940656384851554967432209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69016834052541626492971781 12940656384851554967432209)
                  ·
                    refine ⟨9705492288638666225574157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12940656384851554967432209 9705492288638666225574157)
                    ·
                      refine ⟨3639559608239499834590309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9705492288638666225574157 3639559608239499834590309)
                      ·
                        rfl

theorem cell23_7088017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_7088017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088017 prefixEnd_7088017 := by exact prefixLift 7088017
  have htrace : WordTrace (prefixWord ++ tailWord_7088017) baseStart_7088017 baseEnd_7088017 := by
    simpa [prefixWord, tailWord_7088017, baseEnd_7088017] using wordTrace_append hprefix tailTrace_7088017
  have hstable : (prefixWord ++ tailWord_7088017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088017).length < 2 ^ (prefixWord ++ tailWord_7088017).sum := by decide
  have hdescent : baseEnd_7088017 < baseStart_7088017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088087 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 4]
def baseStart_7088087 : Nat := 118140960795 + 7088087 * 2 ^ 59
def prefixEnd_7088087 : Nat := 4983230072969 + 3 ^ 40 * 7088087 * 2
def baseEnd_7088087 : Nat := 3639595551885314560714987

theorem tailTrace_7088087 : CollatzResearch.WordTrace tailWord_7088087 prefixEnd_7088087 3639595551885314560714987 := by
  unfold tailWord_7088087
  simp only [CollatzResearch.WordTrace]
  refine ⟨258523771472078822727990515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172349180981385881818660343 258523771472078822727990515)
  ·
    refine ⟨387785657208118234091985773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258523771472078822727990515 387785657208118234091985773)
    ·
      refine ⟨145419621453044337784494665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387785657208118234091985773 145419621453044337784494665)
      ·
        refine ⟨109064716089783253338370999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145419621453044337784494665 109064716089783253338370999)
        ·
          refine ⟨163597074134674880007556499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109064716089783253338370999 163597074134674880007556499)
          ·
            refine ⟨245395611202012320011334749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163597074134674880007556499 245395611202012320011334749)
            ·
              refine ⟨92023354200754620004250531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245395611202012320011334749 92023354200754620004250531)
              ·
                refine ⟨138035031301131930006375797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92023354200754620004250531 138035031301131930006375797)
                ·
                  refine ⟨12940784184481118438097731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138035031301131930006375797 12940784184481118438097731)
                  ·
                    refine ⟨19411176276721677657146597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12940784184481118438097731 19411176276721677657146597)
                    ·
                      refine ⟨3639595551885314560714987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19411176276721677657146597 3639595551885314560714987)
                      ·
                        rfl

theorem cell23_7088087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_7088087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088087 prefixEnd_7088087 := by exact prefixLift 7088087
  have htrace : WordTrace (prefixWord ++ tailWord_7088087) baseStart_7088087 baseEnd_7088087 := by
    simpa [prefixWord, tailWord_7088087, baseEnd_7088087] using wordTrace_append hprefix tailTrace_7088087
  have hstable : (prefixWord ++ tailWord_7088087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088087).length < 2 ^ (prefixWord ++ tailWord_7088087).sum := by decide
  have hdescent : baseEnd_7088087 < baseStart_7088087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088097 : List Nat := [1, 2, 3, 1, 2, 1, 3, 3, 1, 6]
def baseStart_7088097 : Nat := 118140960795 + 7088097 * 2 ^ 59
def prefixEnd_7088097 : Nat := 4983230072969 + 3 ^ 40 * 7088097 * 2
def baseEnd_7088097 : Nat := 1213200228897286507196647

theorem tailTrace_7088097 : CollatzResearch.WordTrace tailWord_7088097 prefixEnd_7088097 1213200228897286507196647 := by
  unfold tailWord_7088097
  simp only [CollatzResearch.WordTrace]
  refine ⟨258524136202042594435854545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172349424134695062957236363 258524136202042594435854545)
  ·
    refine ⟨193893102151531945826890909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258524136202042594435854545 193893102151531945826890909)
    ·
      refine ⟨72709913306824479685084091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193893102151531945826890909 72709913306824479685084091)
      ·
        refine ⟨109064869960236719527626137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72709913306824479685084091 109064869960236719527626137)
        ·
          refine ⟨81798652470177539645719603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109064869960236719527626137 81798652470177539645719603)
          ·
            refine ⟨122697978705266309468579405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81798652470177539645719603 122697978705266309468579405)
            ·
              refine ⟨46011742014474866050717277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122697978705266309468579405 46011742014474866050717277)
              ·
                refine ⟨17254403255428074769018979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46011742014474866050717277 17254403255428074769018979)
                ·
                  refine ⟨25881604883142112153528469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17254403255428074769018979 25881604883142112153528469)
                  ·
                    refine ⟨1213200228897286507196647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25881604883142112153528469 1213200228897286507196647)
                    ·
                      rfl

theorem cell23_7088097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_7088097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088097 prefixEnd_7088097 := by exact prefixLift 7088097
  have htrace : WordTrace (prefixWord ++ tailWord_7088097) baseStart_7088097 baseEnd_7088097 := by
    simpa [prefixWord, tailWord_7088097, baseEnd_7088097] using wordTrace_append hprefix tailTrace_7088097
  have hstable : (prefixWord ++ tailWord_7088097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088097).length < 2 ^ (prefixWord ++ tailWord_7088097).sum := by decide
  have hdescent : baseEnd_7088097 < baseStart_7088097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088104 : List Nat := [2, 1, 4, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_7088104 : Nat := 118140960795 + 7088104 * 2 ^ 59
def prefixEnd_7088104 : Nat := 4983230072969 + 3 ^ 40 * 7088104 * 2
def baseEnd_7088104 : Nat := 3639604281056440994202409

theorem tailTrace_7088104 : CollatzResearch.WordTrace tailWord_7088104 prefixEnd_7088104 3639604281056440994202409 := by
  unfold tailWord_7088104
  simp only [CollatzResearch.WordTrace]
  refine ⟨129262195756508617315679683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172349594342011489754239577 129262195756508617315679683)
  ·
    refine ⟨193893293634762925973519525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129262195756508617315679683 193893293634762925973519525)
    ·
      refine ⟨36354992556518048620034911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193893293634762925973519525 36354992556518048620034911)
      ·
        refine ⟨54532488834777072930052367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36354992556518048620034911 54532488834777072930052367)
        ·
          refine ⟨81798733252165609395078551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54532488834777072930052367 81798733252165609395078551)
          ·
            refine ⟨122698099878248414092617827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81798733252165609395078551 122698099878248414092617827)
            ·
              refine ⟨184047149817372621138926741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122698099878248414092617827 184047149817372621138926741)
              ·
                refine ⟨8627210147689341615887191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 184047149817372621138926741 8627210147689341615887191)
                ·
                  refine ⟨12940815221534012423830787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8627210147689341615887191 12940815221534012423830787)
                  ·
                    refine ⟨19411222832301018635746181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12940815221534012423830787 19411222832301018635746181)
                    ·
                      refine ⟨3639604281056440994202409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19411222832301018635746181 3639604281056440994202409)
                      ·
                        rfl

theorem cell23_7088104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_7088104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088104 prefixEnd_7088104 := by exact prefixLift 7088104
  have htrace : WordTrace (prefixWord ++ tailWord_7088104) baseStart_7088104 baseEnd_7088104 := by
    simpa [prefixWord, tailWord_7088104, baseEnd_7088104] using wordTrace_append hprefix tailTrace_7088104
  have hstable : (prefixWord ++ tailWord_7088104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088104).length < 2 ^ (prefixWord ++ tailWord_7088104).sum := by decide
  have hdescent : baseEnd_7088104 < baseStart_7088104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088121 : List Nat := [1, 2, 1, 3, 1, 4, 4, 1, 1, 1, 4]
def baseStart_7088121 : Nat := 118140960795 + 7088121 * 2 ^ 59
def prefixEnd_7088121 : Nat := 4983230072969 + 3 ^ 40 * 7088121 * 2
def baseEnd_7088121 : Nat := 3639613010227567427689831

theorem tailTrace_7088121 : CollatzResearch.WordTrace tailWord_7088121 prefixEnd_7088121 3639613010227567427689831 := by
  unfold tailWord_7088121
  simp only [CollatzResearch.WordTrace]
  refine ⟨258525011553955646534728217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172350007702637097689818811 258525011553955646534728217)
  ·
    refine ⟨193893758665466734901046163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258525011553955646534728217 193893758665466734901046163)
    ·
      refine ⟨290840637998200102351569245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193893758665466734901046163 290840637998200102351569245)
      ·
        refine ⟨109065239249325038381838467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290840637998200102351569245 109065239249325038381838467)
        ·
          refine ⟨163597858873987557572757701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109065239249325038381838467 163597858873987557572757701)
          ·
            refine ⟨30674598538872667044892069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163597858873987557572757701 30674598538872667044892069)
            ·
              refine ⟨5751487226038625070917263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30674598538872667044892069 5751487226038625070917263)
              ·
                refine ⟨8627230839057937606375895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5751487226038625070917263 8627230839057937606375895)
                ·
                  refine ⟨12940846258586906409563843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8627230839057937606375895 12940846258586906409563843)
                  ·
                    refine ⟨19411269387880359614345765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12940846258586906409563843 19411269387880359614345765)
                    ·
                      refine ⟨3639613010227567427689831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19411269387880359614345765 3639613010227567427689831)
                      ·
                        rfl

theorem cell23_7088121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_7088121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088121 prefixEnd_7088121 := by exact prefixLift 7088121
  have htrace : WordTrace (prefixWord ++ tailWord_7088121) baseStart_7088121 baseEnd_7088121 := by
    simpa [prefixWord, tailWord_7088121, baseEnd_7088121] using wordTrace_append hprefix tailTrace_7088121
  have hstable : (prefixWord ++ tailWord_7088121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088121).length < 2 ^ (prefixWord ++ tailWord_7088121).sum := by decide
  have hdescent : baseEnd_7088121 < baseStart_7088121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088137 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 2, 7, 3]
def baseStart_7088137 : Nat := 118140960795 + 7088137 * 2 ^ 59
def prefixEnd_7088137 : Nat := 4983230072969 + 3 ^ 40 * 7088137 * 2
def baseEnd_7088137 : Nat := 3639621225918039365089757

theorem tailTrace_7088137 : CollatzResearch.WordTrace tailWord_7088137 prefixEnd_7088137 3639621225918039365089757 := by
  unfold tailWord_7088137
  simp only [CollatzResearch.WordTrace]
  refine ⟨258525595121897681267310665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172350396747931787511540443 258525595121897681267310665)
  ·
    refine ⟨193894196341423260950482999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258525595121897681267310665 193894196341423260950482999)
    ·
      refine ⟨290841294512134891425724499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193894196341423260950482999 290841294512134891425724499)
      ·
        refine ⟨436261941768202337138586749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290841294512134891425724499 436261941768202337138586749)
        ·
          refine ⟨163598228163075876426970031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436261941768202337138586749 163598228163075876426970031)
          ·
            refine ⟨245397342244613814640455047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163598228163075876426970031 245397342244613814640455047)
            ·
              refine ⟨368096013366920721960682571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245397342244613814640455047 368096013366920721960682571)
              ·
                refine ⟨552144020050381082941023857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368096013366920721960682571 552144020050381082941023857)
                ·
                  refine ⟨414108015037785812205767893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552144020050381082941023857 414108015037785812205767893)
                  ·
                    refine ⟨9705656602448104973572685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 414108015037785812205767893 9705656602448104973572685)
                    ·
                      refine ⟨3639621225918039365089757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9705656602448104973572685 3639621225918039365089757)
                      ·
                        rfl

theorem cell23_7088137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 7, 3].length) (baseStart_7088137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088137 prefixEnd_7088137 := by exact prefixLift 7088137
  have htrace : WordTrace (prefixWord ++ tailWord_7088137) baseStart_7088137 baseEnd_7088137 := by
    simpa [prefixWord, tailWord_7088137, baseEnd_7088137] using wordTrace_append hprefix tailTrace_7088137
  have hstable : (prefixWord ++ tailWord_7088137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088137).length < 2 ^ (prefixWord ++ tailWord_7088137).sum := by decide
  have hdescent : baseEnd_7088137 < baseStart_7088137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088161 : List Nat := [1, 2, 3, 2, 4, 2, 2, 7]
def baseStart_7088161 : Nat := 118140960795 + 7088161 * 2 ^ 59
def prefixEnd_7088161 : Nat := 4983230072969 + 3 ^ 40 * 7088161 * 2
def baseEnd_7088161 : Nat := 134801242572361010044061

theorem tailTrace_7088161 : CollatzResearch.WordTrace tailWord_7088161 prefixEnd_7088161 134801242572361010044061 := by
  unfold tailWord_7088161
  simp only [CollatzResearch.WordTrace]
  refine ⟨258526470473810733366184337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172350980315873822244122891 258526470473810733366184337)
  ·
    refine ⟨193894852855358050024638253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258526470473810733366184337 193894852855358050024638253)
    ·
      refine ⟨72710569820759268759239345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193894852855358050024638253 72710569820759268759239345)
      ·
        refine ⟨54532927365569451569429509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72710569820759268759239345 54532927365569451569429509)
        ·
          refine ⟨10224923881044272169268033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54532927365569451569429509 10224923881044272169268033)
          ·
            refine ⟨7668692910783204126951025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10224923881044272169268033 7668692910783204126951025)
            ·
              refine ⟨5751519683087403095213269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7668692910783204126951025 5751519683087403095213269)
              ·
                refine ⟨134801242572361010044061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5751519683087403095213269 134801242572361010044061)
                ·
                  rfl

theorem cell23_7088161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 7].length) (baseStart_7088161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088161 prefixEnd_7088161 := by exact prefixLift 7088161
  have htrace : WordTrace (prefixWord ++ tailWord_7088161) baseStart_7088161 baseEnd_7088161 := by
    simpa [prefixWord, tailWord_7088161, baseEnd_7088161] using wordTrace_append hprefix tailTrace_7088161
  have hstable : (prefixWord ++ tailWord_7088161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088161).length < 2 ^ (prefixWord ++ tailWord_7088161).sum := by decide
  have hdescent : baseEnd_7088161 < baseStart_7088161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088197 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 3, 3, 5]
def baseStart_7088197 : Nat := 118140960795 + 7088197 * 2 ^ 59
def prefixEnd_7088197 : Nat := 4983230072969 + 3 ^ 40 * 7088197 * 2
def baseEnd_7088197 : Nat := 3639652034757309130339481

theorem tailTrace_7088197 : CollatzResearch.WordTrace tailWord_7088197 prefixEnd_7088197 3639652034757309130339481 := by
  unfold tailWord_7088197
  simp only [CollatzResearch.WordTrace]
  refine ⟨258527783501680311514494845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172351855667786874342996563 258527783501680311514494845)
  ·
    refine ⟨96947918813130116817935567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258527783501680311514494845 96947918813130116817935567)
    ·
      refine ⟨145421878219695175226903351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96947918813130116817935567 145421878219695175226903351)
      ·
        refine ⟨218132817329542762840355027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145421878219695175226903351 218132817329542762840355027)
        ·
          refine ⟨327199225994314144260532541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218132817329542762840355027 327199225994314144260532541)
          ·
            refine ⟨122699709747867804097699703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327199225994314144260532541 122699709747867804097699703)
            ·
              refine ⟨184049564621801706146549555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122699709747867804097699703 184049564621801706146549555)
              ·
                refine ⟨276074346932702559219824333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184049564621801706146549555 276074346932702559219824333)
                ·
                  refine ⟨103527880099763459707434125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276074346932702559219824333 103527880099763459707434125)
                  ·
                    refine ⟨38822955037411297390287797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103527880099763459707434125 38822955037411297390287797)
                    ·
                      refine ⟨3639652034757309130339481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38822955037411297390287797 3639652034757309130339481)
                      ·
                        rfl

theorem cell23_7088197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_7088197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088197 prefixEnd_7088197 := by exact prefixLift 7088197
  have htrace : WordTrace (prefixWord ++ tailWord_7088197) baseStart_7088197 baseEnd_7088197 := by
    simpa [prefixWord, tailWord_7088197, baseEnd_7088197] using wordTrace_append hprefix tailTrace_7088197
  have hstable : (prefixWord ++ tailWord_7088197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088197).length < 2 ^ (prefixWord ++ tailWord_7088197).sum := by decide
  have hdescent : baseEnd_7088197 < baseStart_7088197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088217 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 9]
def baseStart_7088217 : Nat := 118140960795 + 7088217 * 2 ^ 59
def prefixEnd_7088217 : Nat := 4983230072969 + 3 ^ 40 * 7088217 * 2
def baseEnd_7088217 : Nat := 404406922707822116898821

theorem tailTrace_7088217 : CollatzResearch.WordTrace tailWord_7088217 prefixEnd_7088217 404406922707822116898821 := by
  unfold tailWord_7088217
  simp only [CollatzResearch.WordTrace]
  refine ⟨258528512961607854930222905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172352341974405236620148603 258528512961607854930222905)
  ·
    refine ⟨193896384721205891197667179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258528512961607854930222905 193896384721205891197667179)
    ·
      refine ⟨290844577081808836796500769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193896384721205891197667179 290844577081808836796500769)
      ·
        refine ⟨218133432811356627597375577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290844577081808836796500769 218133432811356627597375577)
        ·
          refine ⟨163600074608517470698031683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218133432811356627597375577 163600074608517470698031683)
          ·
            refine ⟨245400111912776206047047525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163600074608517470698031683 245400111912776206047047525)
            ·
              refine ⟨46012520983645538633821411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245400111912776206047047525 46012520983645538633821411)
              ·
                refine ⟨69018781475468307950732117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46012520983645538633821411 69018781475468307950732117)
                ·
                  refine ⟨404406922707822116898821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69018781475468307950732117 404406922707822116898821)
                  ·
                    rfl

theorem cell23_7088217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 9].length) (baseStart_7088217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088217 prefixEnd_7088217 := by exact prefixLift 7088217
  have htrace : WordTrace (prefixWord ++ tailWord_7088217) baseStart_7088217 baseEnd_7088217 := by
    simpa [prefixWord, tailWord_7088217, baseEnd_7088217] using wordTrace_append hprefix tailTrace_7088217
  have hstable : (prefixWord ++ tailWord_7088217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088217).length < 2 ^ (prefixWord ++ tailWord_7088217).sum := by decide
  have hdescent : baseEnd_7088217 < baseStart_7088217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088261 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 2, 3, 3]
def baseStart_7088261 : Nat := 118140960795 + 7088261 * 2 ^ 59
def prefixEnd_7088261 : Nat := 4983230072969 + 3 ^ 40 * 7088261 * 2
def baseEnd_7088261 : Nat := 3639684897519196879939187

theorem tailTrace_7088261 : CollatzResearch.WordTrace tailWord_7088261 prefixEnd_7088261 3639684897519196879939187 := by
  unfold tailWord_7088261
  simp only [CollatzResearch.WordTrace]
  refine ⟨258530117773448450444824637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172353411848965633629883091 258530117773448450444824637)
  ·
    refine ⟨96948794165043168916809239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258530117773448450444824637 96948794165043168916809239)
    ·
      refine ⟨145423191247564753375213859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96948794165043168916809239 145423191247564753375213859)
      ·
        refine ⟨218134786871347130062820789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145423191247564753375213859 218134786871347130062820789)
        ·
          refine ⟨20450136269188793443389449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 218134786871347130062820789 20450136269188793443389449)
          ·
            refine ⟨15337602201891595082542087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20450136269188793443389449 15337602201891595082542087)
            ·
              refine ⟨23006403302837392623813131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15337602201891595082542087 23006403302837392623813131)
              ·
                refine ⟨34509604954256088935719697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23006403302837392623813131 34509604954256088935719697)
                ·
                  refine ⟨25882203715692066701789773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34509604954256088935719697 25882203715692066701789773)
                  ·
                    refine ⟨9705826393384525013171165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25882203715692066701789773 9705826393384525013171165)
                    ·
                      refine ⟨3639684897519196879939187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9705826393384525013171165 3639684897519196879939187)
                      ·
                        rfl

theorem cell23_7088261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_7088261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088261 prefixEnd_7088261 := by exact prefixLift 7088261
  have htrace : WordTrace (prefixWord ++ tailWord_7088261) baseStart_7088261 baseEnd_7088261 := by
    simpa [prefixWord, tailWord_7088261, baseEnd_7088261] using wordTrace_append hprefix tailTrace_7088261
  have hstable : (prefixWord ++ tailWord_7088261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088261).length < 2 ^ (prefixWord ++ tailWord_7088261).sum := by decide
  have hdescent : baseEnd_7088261 < baseStart_7088261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088304 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 3]
def baseStart_7088304 : Nat := 118140960795 + 7088304 * 2 ^ 59
def prefixEnd_7088304 : Nat := 4983230072969 + 3 ^ 40 * 7088304 * 2
def baseEnd_7088304 : Nat := 3639706977187340211701489

theorem tailTrace_7088304 : CollatzResearch.WordTrace tailWord_7088304 prefixEnd_7088304 3639706977187340211701489 := by
  unfold tailWord_7088304
  simp only [CollatzResearch.WordTrace]
  refine ⟨129265843056146334394319983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172354457408195112525759977 129265843056146334394319983)
  ·
    refine ⟨193898764584219501591479975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129265843056146334394319983 193898764584219501591479975)
    ·
      refine ⟨290848146876329252387219963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193898764584219501591479975 290848146876329252387219963)
      ·
        refine ⟨436272220314493878580829945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290848146876329252387219963 436272220314493878580829945)
        ·
          refine ⟨327204165235870408935622459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436272220314493878580829945 327204165235870408935622459)
          ·
            refine ⟨490806247853805613403433689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327204165235870408935622459 490806247853805613403433689)
            ·
              refine ⟨368104685890354210052575267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490806247853805613403433689 368104685890354210052575267)
              ·
                refine ⟨552157028835531315078862901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368104685890354210052575267 552157028835531315078862901)
                ·
                  refine ⟨51764721453331060788643397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 552157028835531315078862901 51764721453331060788643397)
                  ·
                    refine ⟨9705885272499573897870637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51764721453331060788643397 9705885272499573897870637)
                    ·
                      refine ⟨3639706977187340211701489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9705885272499573897870637 3639706977187340211701489)
                      ·
                        rfl

theorem cell23_7088304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 3].length) (baseStart_7088304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088304 prefixEnd_7088304 := by exact prefixLift 7088304
  have htrace : WordTrace (prefixWord ++ tailWord_7088304) baseStart_7088304 baseEnd_7088304 := by
    simpa [prefixWord, tailWord_7088304, baseEnd_7088304] using wordTrace_append hprefix tailTrace_7088304
  have hstable : (prefixWord ++ tailWord_7088304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088304).length < 2 ^ (prefixWord ++ tailWord_7088304).sum := by decide
  have hdescent : baseEnd_7088304 < baseStart_7088304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088311 : List Nat := [1, 1, 3, 1, 4, 2, 1, 3, 3, 4]
def baseStart_7088311 : Nat := 118140960795 + 7088311 * 2 ^ 59
def prefixEnd_7088311 : Nat := 4983230072969 + 3 ^ 40 * 7088311 * 2
def baseEnd_7088311 : Nat := 1213236857183973894771319

theorem tailTrace_7088311 : CollatzResearch.WordTrace tailWord_7088311 prefixEnd_7088311 1213236857183973894771319 := by
  unfold tailWord_7088311
  simp only [CollatzResearch.WordTrace]
  refine ⟨258531941423267308984144787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172354627615511539322763191 258531941423267308984144787)
  ·
    refine ⟨387797912134900963476217181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258531941423267308984144787 387797912134900963476217181)
    ·
      refine ⟨145424217050587861303581443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387797912134900963476217181 145424217050587861303581443)
      ·
        refine ⟨218136325575881791955372165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145424217050587861303581443 218136325575881791955372165)
        ·
          refine ⟨40900561045477835991632281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218136325575881791955372165 40900561045477835991632281)
          ·
            refine ⟨30675420784108376993724211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40900561045477835991632281 30675420784108376993724211)
            ·
              refine ⟨46013131176162565490586317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30675420784108376993724211 46013131176162565490586317)
              ·
                refine ⟨17254924191060962058969869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46013131176162565490586317 17254924191060962058969869)
                ·
                  refine ⟨6470596571647860772113701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17254924191060962058969869 6470596571647860772113701)
                  ·
                    refine ⟨1213236857183973894771319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6470596571647860772113701 1213236857183973894771319)
                    ·
                      rfl

theorem cell23_7088311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_7088311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088311 prefixEnd_7088311 := by exact prefixLift 7088311
  have htrace : WordTrace (prefixWord ++ tailWord_7088311) baseStart_7088311 baseEnd_7088311 := by
    simpa [prefixWord, tailWord_7088311, baseEnd_7088311] using wordTrace_append hprefix tailTrace_7088311
  have hstable : (prefixWord ++ tailWord_7088311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088311).length < 2 ^ (prefixWord ++ tailWord_7088311).sum := by decide
  have hdescent : baseEnd_7088311 < baseStart_7088311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088355 : List Nat := [1, 1, 1, 8, 1, 1, 1, 2, 2, 2, 3]
def baseStart_7088355 : Nat := 118140960795 + 7088355 * 2 ^ 59
def prefixEnd_7088355 : Nat := 4983230072969 + 3 ^ 40 * 7088355 * 2
def baseEnd_7088355 : Nat := 3639733164700719512163755

theorem tailTrace_7088355 : CollatzResearch.WordTrace tailWord_7088355 prefixEnd_7088355 3639733164700719512163755 := by
  unfold tailWord_7088355
  simp only [CollatzResearch.WordTrace]
  refine ⟨258533546235107904498746519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172355697490071936332497679 258533546235107904498746519)
  ·
    refine ⟨387800319352661856748119779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258533546235107904498746519 387800319352661856748119779)
    ·
      refine ⟨581700479028992785122179669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387800319352661856748119779 581700479028992785122179669)
      ·
        refine ⟨6816802488621009200650543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 581700479028992785122179669 6816802488621009200650543)
        ·
          refine ⟨10225203732931513800975815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6816802488621009200650543 10225203732931513800975815)
          ·
            refine ⟨15337805599397270701463723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10225203732931513800975815 15337805599397270701463723)
            ·
              refine ⟨23006708399095906052195585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15337805599397270701463723 23006708399095906052195585)
              ·
                refine ⟨17255031299321929539146689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23006708399095906052195585 17255031299321929539146689)
                ·
                  refine ⟨12941273474491447154360017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17255031299321929539146689 12941273474491447154360017)
                  ·
                    refine ⟨9705955105868585365770013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12941273474491447154360017 9705955105868585365770013)
                    ·
                      refine ⟨3639733164700719512163755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9705955105868585365770013 3639733164700719512163755)
                      ·
                        rfl

theorem cell23_7088355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_7088355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088355 prefixEnd_7088355 := by exact prefixLift 7088355
  have htrace : WordTrace (prefixWord ++ tailWord_7088355) baseStart_7088355 baseEnd_7088355 := by
    simpa [prefixWord, tailWord_7088355, baseEnd_7088355] using wordTrace_append hprefix tailTrace_7088355
  have hstable : (prefixWord ++ tailWord_7088355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088355).length < 2 ^ (prefixWord ++ tailWord_7088355).sum := by decide
  have hdescent : baseEnd_7088355 < baseStart_7088355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088388 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 3, 5]
def baseStart_7088388 : Nat := 118140960795 + 7088388 * 2 ^ 59
def prefixEnd_7088388 : Nat := 4983230072969 + 3 ^ 40 * 7088388 * 2
def baseEnd_7088388 : Nat := 1213250036520772627683701

theorem tailTrace_7088388 : CollatzResearch.WordTrace tailWord_7088388 prefixEnd_7088388 1213250036520772627683701 := by
  unfold tailWord_7088388
  simp only [CollatzResearch.WordTrace]
  refine ⟨129267374921994175567348909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172356499895992234089798545 129267374921994175567348909)
  ·
    refine ⟨48475265595747815837755841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129267374921994175567348909 48475265595747815837755841)
    ·
      refine ⟨36356449196810861878316881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48475265595747815837755841 36356449196810861878316881)
      ·
        refine ⟨27267336897608146408737661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36356449196810861878316881 27267336897608146408737661)
        ·
          refine ⟨10225251336603054903276623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27267336897608146408737661 10225251336603054903276623)
          ·
            refine ⟨15337877004904582354914935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10225251336603054903276623 15337877004904582354914935)
            ·
              refine ⟨23006815507356873532372403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15337877004904582354914935 23006815507356873532372403)
              ·
                refine ⟨34510223261035310298558605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23006815507356873532372403 34510223261035310298558605)
                ·
                  refine ⟨12941333722888241361959477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34510223261035310298558605 12941333722888241361959477)
                  ·
                    refine ⟨1213250036520772627683701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12941333722888241361959477 1213250036520772627683701)
                    ·
                      rfl

theorem cell23_7088388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_7088388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088388 prefixEnd_7088388 := by exact prefixLift 7088388
  have htrace : WordTrace (prefixWord ++ tailWord_7088388) baseStart_7088388 baseEnd_7088388 := by
    simpa [prefixWord, tailWord_7088388, baseEnd_7088388] using wordTrace_append hprefix tailTrace_7088388
  have hstable : (prefixWord ++ tailWord_7088388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088388).length < 2 ^ (prefixWord ++ tailWord_7088388).sum := by decide
  have hdescent : baseEnd_7088388 < baseStart_7088388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088401 : List Nat := [1, 2, 2, 1, 1, 6, 1, 2, 1, 6]
def baseStart_7088401 : Nat := 118140960795 + 7088401 * 2 ^ 59
def prefixEnd_7088401 : Nat := 4983230072969 + 3 ^ 40 * 7088401 * 2
def baseEnd_7088401 : Nat := 1213252261603608777396181

theorem tailTrace_7088401 : CollatzResearch.WordTrace tailWord_7088401 prefixEnd_7088401 1213252261603608777396181 := by
  unfold tailWord_7088401
  simp only [CollatzResearch.WordTrace]
  refine ⟨258535223992941254354921057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172356815995294169569947371 258535223992941254354921057)
  ·
    refine ⟨193901417994705940766190793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258535223992941254354921057 193901417994705940766190793)
    ·
      refine ⟨145426063496029455574643095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193901417994705940766190793 145426063496029455574643095)
      ·
        refine ⟨218139095244044183361964643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145426063496029455574643095 218139095244044183361964643)
        ·
          refine ⟨327208642866066275042946965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218139095244044183361964643 327208642866066275042946965)
          ·
            refine ⟨15337905134346856642638139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 327208642866066275042946965 15337905134346856642638139)
            ·
              refine ⟨23006857701520284963957209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15337905134346856642638139 23006857701520284963957209)
              ·
                refine ⟨17255143276140213722967907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23006857701520284963957209 17255143276140213722967907)
                ·
                  refine ⟨25882714914210320584451861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17255143276140213722967907 25882714914210320584451861)
                  ·
                    refine ⟨1213252261603608777396181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25882714914210320584451861 1213252261603608777396181)
                    ·
                      rfl

theorem cell23_7088401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_7088401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088401 prefixEnd_7088401 := by exact prefixLift 7088401
  have htrace : WordTrace (prefixWord ++ tailWord_7088401) baseStart_7088401 baseEnd_7088401 := by
    simpa [prefixWord, tailWord_7088401, baseEnd_7088401] using wordTrace_append hprefix tailTrace_7088401
  have hstable : (prefixWord ++ tailWord_7088401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088401).length < 2 ^ (prefixWord ++ tailWord_7088401).sum := by decide
  have hdescent : baseEnd_7088401 < baseStart_7088401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088411 : List Nat := [1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 5]
def baseStart_7088411 : Nat := 118140960795 + 7088411 * 2 ^ 59
def prefixEnd_7088411 : Nat := 4983230072969 + 3 ^ 40 * 7088411 * 2
def baseEnd_7088411 : Nat := 3639761919617371293063497

theorem tailTrace_7088411 : CollatzResearch.WordTrace tailWord_7088411 prefixEnd_7088411 3639761919617371293063497 := by
  unfold tailWord_7088411
  simp only [CollatzResearch.WordTrace]
  refine ⟨258535588722905026062785087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172357059148603350708523391 258535588722905026062785087)
  ·
    refine ⟨387803383084357539094177631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258535588722905026062785087 387803383084357539094177631)
    ·
      refine ⟨581705074626536308641266447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387803383084357539094177631 581705074626536308641266447)
      ·
        refine ⟨872557611939804462961899671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581705074626536308641266447 872557611939804462961899671)
        ·
          refine ⟨1308836417909706694442849507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872557611939804462961899671 1308836417909706694442849507)
          ·
            refine ⟨1963254626864560041664274261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1308836417909706694442849507 1963254626864560041664274261)
            ·
              refine ⟨11503445079284531494126607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1963254626864560041664274261 11503445079284531494126607)
              ·
                refine ⟨17255167618926797241189911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11503445079284531494126607 17255167618926797241189911)
                ·
                  refine ⟨25882751428390195861784867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17255167618926797241189911 25882751428390195861784867)
                  ·
                    refine ⟨38824127142585293792677301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25882751428390195861784867 38824127142585293792677301)
                    ·
                      refine ⟨3639761919617371293063497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38824127142585293792677301 3639761919617371293063497)
                      ·
                        rfl

theorem cell23_7088411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 5].length) (baseStart_7088411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088411 prefixEnd_7088411 := by exact prefixLift 7088411
  have htrace : WordTrace (prefixWord ++ tailWord_7088411) baseStart_7088411 baseEnd_7088411 := by
    simpa [prefixWord, tailWord_7088411, baseEnd_7088411] using wordTrace_append hprefix tailTrace_7088411
  have hstable : (prefixWord ++ tailWord_7088411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088411).length < 2 ^ (prefixWord ++ tailWord_7088411).sum := by decide
  have hdescent : baseEnd_7088411 < baseStart_7088411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088492 : List Nat := [2, 2, 1, 1, 7, 1, 1, 1, 1, 3, 3]
def baseStart_7088492 : Nat := 118140960795 + 7088492 * 2 ^ 59
def prefixEnd_7088492 : Nat := 4983230072969 + 3 ^ 40 * 7088492 * 2
def baseEnd_7088492 : Nat := 3639803511550385476150625

theorem tailTrace_7088492 : CollatzResearch.WordTrace tailWord_7088492 prefixEnd_7088492 3639803511550385476150625 := by
  unfold tailWord_7088492
  simp only [CollatzResearch.WordTrace]
  refine ⟨129269271517805788448241865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172359028690407717930989153 129269271517805788448241865)
  ·
    refine ⟨96951953638354341336181399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129269271517805788448241865 96951953638354341336181399)
    ·
      refine ⟨145427930457531512004272099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96951953638354341336181399 145427930457531512004272099)
      ·
        refine ⟨218141895686297268006408149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145427930457531512004272099 218141895686297268006408149)
        ·
          refine ⟨5112700680147592218900191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 218141895686297268006408149 5112700680147592218900191)
          ·
            refine ⟨7669051020221388328350287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5112700680147592218900191 7669051020221388328350287)
            ·
              refine ⟨11503576530332082492525431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7669051020221388328350287 11503576530332082492525431)
              ·
                refine ⟨17255364795498123738788147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11503576530332082492525431 17255364795498123738788147)
                ·
                  refine ⟨25883047193247185608182221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17255364795498123738788147 25883047193247185608182221)
                  ·
                    refine ⟨9706142697467694603068333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25883047193247185608182221 9706142697467694603068333)
                    ·
                      refine ⟨3639803511550385476150625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9706142697467694603068333 3639803511550385476150625)
                      ·
                        rfl

theorem cell23_7088492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 1, 3, 3].length) (baseStart_7088492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088492 prefixEnd_7088492 := by exact prefixLift 7088492
  have htrace : WordTrace (prefixWord ++ tailWord_7088492) baseStart_7088492 baseEnd_7088492 := by
    simpa [prefixWord, tailWord_7088492, baseEnd_7088492] using wordTrace_append hprefix tailTrace_7088492
  have hstable : (prefixWord ++ tailWord_7088492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088492).length < 2 ^ (prefixWord ++ tailWord_7088492).sum := by decide
  have hdescent : baseEnd_7088492 < baseStart_7088492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088538 : List Nat := [3, 1, 1, 4, 1, 2, 3, 1, 7]
def baseStart_7088538 : Nat := 118140960795 + 7088538 * 2 ^ 59
def prefixEnd_7088538 : Nat := 4983230072969 + 3 ^ 40 * 7088538 * 2
def baseEnd_7088538 : Nat := 404425236851165810686157

theorem tailTrace_7088538 : CollatzResearch.WordTrace tailWord_7088538 prefixEnd_7088538 404425236851165810686157 := by
  unfold tailWord_7088538
  simp only [CollatzResearch.WordTrace]
  refine ⟨64635055198361231688164567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172360147195629951168438845 64635055198361231688164567)
  ·
    refine ⟨96952582797541847532246851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64635055198361231688164567 96952582797541847532246851)
    ·
      refine ⟨145428874196312771298370277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96952582797541847532246851 145428874196312771298370277)
      ·
        refine ⟨27267913911808644618444427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145428874196312771298370277 27267913911808644618444427)
        ·
          refine ⟨40901870867712966927666641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27267913911808644618444427 40901870867712966927666641)
          ·
            refine ⟨30676403150784725195749981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40901870867712966927666641 30676403150784725195749981)
            ·
              refine ⟨11503651181544271948406243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30676403150784725195749981 11503651181544271948406243)
              ·
                refine ⟨17255476772316407922609365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11503651181544271948406243 17255476772316407922609365)
                ·
                  refine ⟨404425236851165810686157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17255476772316407922609365 404425236851165810686157)
                  ·
                    rfl

theorem cell23_7088538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 7].length) (baseStart_7088538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088538 prefixEnd_7088538 := by exact prefixLift 7088538
  have htrace : WordTrace (prefixWord ++ tailWord_7088538) baseStart_7088538 baseEnd_7088538 := by
    simpa [prefixWord, tailWord_7088538, baseEnd_7088538] using wordTrace_append hprefix tailTrace_7088538
  have hstable : (prefixWord ++ tailWord_7088538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088538).length < 2 ^ (prefixWord ++ tailWord_7088538).sum := by decide
  have hdescent : baseEnd_7088538 < baseStart_7088538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088548 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 2, 3, 3]
def baseStart_7088548 : Nat := 118140960795 + 7088548 * 2 ^ 59
def prefixEnd_7088548 : Nat := 4983230072969 + 3 ^ 40 * 7088548 * 2
def baseEnd_7088548 : Nat := 3639832266467037257050367

theorem tailTrace_7088548 : CollatzResearch.WordTrace tailWord_7088548 prefixEnd_7088548 3639832266467037257050367 := by
  unfold tailWord_7088548
  simp only [CollatzResearch.WordTrace]
  refine ⟨129270292761704349230261149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172360390348939132307014865 129270292761704349230261149)
  ·
    refine ⟨48476359785639130961347931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129270292761704349230261149 48476359785639130961347931)
    ·
      refine ⟨72714539678458696442021897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48476359785639130961347931 72714539678458696442021897)
      ·
        refine ⟨54535904758844022331516423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72714539678458696442021897 54535904758844022331516423)
        ·
          refine ⟨81803857138266033497274635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54535904758844022331516423 81803857138266033497274635)
          ·
            refine ⟨122705785707399050245911953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81803857138266033497274635 122705785707399050245911953)
            ·
              refine ⟨92029339280549287684433965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122705785707399050245911953 92029339280549287684433965)
              ·
                refine ⟨34511002230205982881662737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92029339280549287684433965 34511002230205982881662737)
                ·
                  refine ⟨25883251672654487161247053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34511002230205982881662737 25883251672654487161247053)
                  ·
                    refine ⟨9706219377245432685467645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25883251672654487161247053 9706219377245432685467645)
                    ·
                      refine ⟨3639832266467037257050367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9706219377245432685467645 3639832266467037257050367)
                      ·
                        rfl

theorem cell23_7088548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_7088548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088548 prefixEnd_7088548 := by exact prefixLift 7088548
  have htrace : WordTrace (prefixWord ++ tailWord_7088548) baseStart_7088548 baseEnd_7088548 := by
    simpa [prefixWord, tailWord_7088548, baseEnd_7088548] using wordTrace_append hprefix tailTrace_7088548
  have hstable : (prefixWord ++ tailWord_7088548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088548).length < 2 ^ (prefixWord ++ tailWord_7088548).sum := by decide
  have hdescent : baseEnd_7088548 < baseStart_7088548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088591 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 5]
def baseStart_7088591 : Nat := 118140960795 + 7088591 * 2 ^ 59
def prefixEnd_7088591 : Nat := 4983230072969 + 3 ^ 40 * 7088591 * 2
def baseEnd_7088591 : Nat := 3639854346135180588812669

theorem tailTrace_7088591 : CollatzResearch.WordTrace tailWord_7088591 prefixEnd_7088591 3639854346135180588812669 := by
  unfold tailWord_7088591
  simp only [CollatzResearch.WordTrace]
  refine ⟨258542153862252916804337627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172361435908168611202891751 258542153862252916804337627)
  ·
    refine ⟨387813230793379375206506441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258542153862252916804337627 387813230793379375206506441)
    ·
      refine ⟨290859923095034531404879831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387813230793379375206506441 290859923095034531404879831)
      ·
        refine ⟨436289884642551797107319747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290859923095034531404879831 436289884642551797107319747)
        ·
          refine ⟨654434826963827695660979621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436289884642551797107319747 654434826963827695660979621)
          ·
            refine ⟨122706530055717692936433679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 654434826963827695660979621 122706530055717692936433679)
            ·
              refine ⟨184059795083576539404650519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122706530055717692936433679 184059795083576539404650519)
              ·
                refine ⟨276089692625364809106975779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184059795083576539404650519 276089692625364809106975779)
                ·
                  refine ⟨414134538938047213660463669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276089692625364809106975779 414134538938047213660463669)
                  ·
                    refine ⟨38825113025441926280668469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 414134538938047213660463669 38825113025441926280668469)
                    ·
                      refine ⟨3639854346135180588812669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38825113025441926280668469 3639854346135180588812669)
                      ·
                        rfl

theorem cell23_7088591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_7088591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088591 prefixEnd_7088591 := by exact prefixLift 7088591
  have htrace : WordTrace (prefixWord ++ tailWord_7088591) baseStart_7088591 baseEnd_7088591 := by
    simpa [prefixWord, tailWord_7088591, baseEnd_7088591] using wordTrace_append hprefix tailTrace_7088591
  have hstable : (prefixWord ++ tailWord_7088591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088591).length < 2 ^ (prefixWord ++ tailWord_7088591).sum := by decide
  have hdescent : baseEnd_7088591 < baseStart_7088591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088608 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 3]
def baseStart_7088608 : Nat := 118140960795 + 7088608 * 2 ^ 59
def prefixEnd_7088608 : Nat := 4983230072969 + 3 ^ 40 * 7088608 * 2
def baseEnd_7088608 : Nat := 3639863075306307022300091

theorem tailTrace_7088608 : CollatzResearch.WordTrace tailWord_7088608 prefixEnd_7088608 3639863075306307022300091 := by
  unfold tailWord_7088608
  simp only [CollatzResearch.WordTrace]
  refine ⟨129271386951595664353853239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172361849268794219138470985 129271386951595664353853239)
  ·
    refine ⟨193907080427393496530779859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129271386951595664353853239 193907080427393496530779859)
    ·
      refine ⟨290860620641090244796169789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193907080427393496530779859 290860620641090244796169789)
      ·
        refine ⟨109072732740408841798563671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290860620641090244796169789 109072732740408841798563671)
        ·
          refine ⟨163609099110613262697845507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109072732740408841798563671 163609099110613262697845507)
          ·
            refine ⟨245413648665919894046768261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163609099110613262697845507 245413648665919894046768261)
            ·
              refine ⟨46015059124859980133769049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245413648665919894046768261 46015059124859980133769049)
              ·
                refine ⟨34511294343644985100326787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46015059124859980133769049 34511294343644985100326787)
                ·
                  refine ⟨51766941515467477650490181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34511294343644985100326787 51766941515467477650490181)
                  ·
                    refine ⟨9706301534150152059466909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51766941515467477650490181 9706301534150152059466909)
                    ·
                      refine ⟨3639863075306307022300091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9706301534150152059466909 3639863075306307022300091)
                      ·
                        rfl

theorem cell23_7088608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_7088608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088608 prefixEnd_7088608 := by exact prefixLift 7088608
  have htrace : WordTrace (prefixWord ++ tailWord_7088608) baseStart_7088608 baseEnd_7088608 := by
    simpa [prefixWord, tailWord_7088608, baseEnd_7088608] using wordTrace_append hprefix tailTrace_7088608
  have hstable : (prefixWord ++ tailWord_7088608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088608).length < 2 ^ (prefixWord ++ tailWord_7088608).sum := by decide
  have hdescent : baseEnd_7088608 < baseStart_7088608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088615 : List Nat := [1, 1, 5, 2, 1, 1, 3, 2, 3, 4]
def baseStart_7088615 : Nat := 118140960795 + 7088615 * 2 ^ 59
def prefixEnd_7088615 : Nat := 4983230072969 + 3 ^ 40 * 7088615 * 2
def baseEnd_7088615 : Nat := 1213288889890296164970853

theorem tailTrace_7088615 : CollatzResearch.WordTrace tailWord_7088615 prefixEnd_7088615 1213288889890296164970853 := by
  unfold tailWord_7088615
  simp only [CollatzResearch.WordTrace]
  refine ⟨258543029214165968903211299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172362019476110645935474199 258543029214165968903211299)
  ·
    refine ⟨387814543821248953354816949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258543029214165968903211299 387814543821248953354816949)
    ·
      refine ⟨36357613483242089377014089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 387814543821248953354816949 36357613483242089377014089)
      ·
        refine ⟨27268210112431567032760567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36357613483242089377014089 27268210112431567032760567)
        ·
          refine ⟨40902315168647350549140851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27268210112431567032760567 40902315168647350549140851)
          ·
            refine ⟨61353472752971025823711277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40902315168647350549140851 61353472752971025823711277)
            ·
              refine ⟨23007552282364134683891729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61353472752971025823711277 23007552282364134683891729)
              ·
                refine ⟨17255664211773101012918797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23007552282364134683891729 17255664211773101012918797)
                ·
                  refine ⟨6470874079414912879844549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17255664211773101012918797 6470874079414912879844549)
                  ·
                    refine ⟨1213288889890296164970853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6470874079414912879844549 1213288889890296164970853)
                    ·
                      rfl

theorem cell23_7088615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_7088615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088615 prefixEnd_7088615 := by exact prefixLift 7088615
  have htrace : WordTrace (prefixWord ++ tailWord_7088615) baseStart_7088615 baseEnd_7088615 := by
    simpa [prefixWord, tailWord_7088615, baseEnd_7088615] using wordTrace_append hprefix tailTrace_7088615
  have hstable : (prefixWord ++ tailWord_7088615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088615).length < 2 ^ (prefixWord ++ tailWord_7088615).sum := by decide
  have hdescent : baseEnd_7088615 < baseStart_7088615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088622 : List Nat := [4, 1, 2, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_7088622 : Nat := 118140960795 + 7088622 * 2 ^ 59
def prefixEnd_7088622 : Nat := 4983230072969 + 3 ^ 40 * 7088622 * 2
def baseEnd_7088622 : Nat := 3639870264035469967525027

theorem tailTrace_7088622 : CollatzResearch.WordTrace tailWord_7088622 prefixEnd_7088622 3639870264035469967525027 := by
  unfold tailWord_7088622
  simp only [CollatzResearch.WordTrace]
  refine ⟨32317910565642576137339515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172362189683427072732477413 32317910565642576137339515)
  ·
    refine ⟨48476865848463864206009273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32317910565642576137339515 48476865848463864206009273)
    ·
      refine ⟨36357649386347898154506955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48476865848463864206009273 36357649386347898154506955)
      ·
        refine ⟨54536474079521847231760433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36357649386347898154506955 54536474079521847231760433)
        ·
          refine ⟨40902355559641385423820325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54536474079521847231760433 40902355559641385423820325)
          ·
            refine ⟨7669191667432759766966311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40902355559641385423820325 7669191667432759766966311)
            ·
              refine ⟨11503787501149139650449467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7669191667432759766966311 11503787501149139650449467)
              ·
                refine ⟨17255681251723709475674201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11503787501149139650449467 17255681251723709475674201)
                ·
                  refine ⟨12941760938792782106755651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17255681251723709475674201 12941760938792782106755651)
                  ·
                    refine ⟨19412641408189173160133477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12941760938792782106755651 19412641408189173160133477)
                    ·
                      refine ⟨3639870264035469967525027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19412641408189173160133477 3639870264035469967525027)
                      ·
                        rfl

theorem cell23_7088622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_7088622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088622 prefixEnd_7088622 := by exact prefixLift 7088622
  have htrace : WordTrace (prefixWord ++ tailWord_7088622) baseStart_7088622 baseEnd_7088622 := by
    simpa [prefixWord, tailWord_7088622, baseEnd_7088622] using wordTrace_append hprefix tailTrace_7088622
  have hstable : (prefixWord ++ tailWord_7088622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088622).length < 2 ^ (prefixWord ++ tailWord_7088622).sum := by decide
  have hdescent : baseEnd_7088622 < baseStart_7088622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088632 : List Nat := [2, 1, 2, 1, 1, 4, 4, 3, 1, 4]
def baseStart_7088632 : Nat := 118140960795 + 7088632 * 2 ^ 59
def prefixEnd_7088632 : Nat := 4983230072969 + 3 ^ 40 * 7088632 * 2
def baseEnd_7088632 : Nat := 1213291799614004976133327

theorem tailTrace_7088632 : CollatzResearch.WordTrace tailWord_7088632 prefixEnd_7088632 1213291799614004976133327 := by
  unfold tailWord_7088632
  simp only [CollatzResearch.WordTrace]
  refine ⟨129271824627552190403290075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172362432836736253871053433 129271824627552190403290075)
  ·
    refine ⟨193907736941328285604935113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129271824627552190403290075 193907736941328285604935113)
    ·
      refine ⟨145430802705996214203701335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193907736941328285604935113 145430802705996214203701335)
      ·
        refine ⟨218146204058994321305552003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145430802705996214203701335 218146204058994321305552003)
        ·
          refine ⟨327219306088491481958328005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218146204058994321305552003 327219306088491481958328005)
          ·
            refine ⟨61353619891592152867186501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 327219306088491481958328005 61353619891592152867186501)
            ·
              refine ⟨11503803729673528662597469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61353619891592152867186501 11503803729673528662597469)
              ·
                refine ⟨4313926398627573248474051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11503803729673528662597469 4313926398627573248474051)
                ·
                  refine ⟨6470889597941359872711077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4313926398627573248474051 6470889597941359872711077)
                  ·
                    refine ⟨1213291799614004976133327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6470889597941359872711077 1213291799614004976133327)
                    ·
                      rfl

theorem cell23_7088632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 1, 4].length) (baseStart_7088632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088632 prefixEnd_7088632 := by exact prefixLift 7088632
  have htrace : WordTrace (prefixWord ++ tailWord_7088632) baseStart_7088632 baseEnd_7088632 := by
    simpa [prefixWord, tailWord_7088632, baseEnd_7088632] using wordTrace_append hprefix tailTrace_7088632
  have hstable : (prefixWord ++ tailWord_7088632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088632).length < 2 ^ (prefixWord ++ tailWord_7088632).sum := by decide
  have hdescent : baseEnd_7088632 < baseStart_7088632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088655 : List Nat := [1, 1, 2, 1, 1, 1, 2, 7, 3, 1, 3]
def baseStart_7088655 : Nat := 118140960795 + 7088655 * 2 ^ 59
def prefixEnd_7088655 : Nat := 4983230072969 + 3 ^ 40 * 7088655 * 2
def baseEnd_7088655 : Nat := 3639887208897068338412375

theorem tailTrace_7088655 : CollatzResearch.WordTrace tailWord_7088655 prefixEnd_7088655 3639887208897068338412375 := by
  unfold tailWord_7088655
  simp only [CollatzResearch.WordTrace]
  refine ⟨258544488134021055734667419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172362992089347370489778279 258544488134021055734667419)
  ·
    refine ⟨387816732201031583602001129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258544488134021055734667419 387816732201031583602001129)
    ·
      refine ⟨290862549150773687701500847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387816732201031583602001129 290862549150773687701500847)
      ·
        refine ⟨436293823726160531552251271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290862549150773687701500847 436293823726160531552251271)
        ·
          refine ⟨654440735589240797328376907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436293823726160531552251271 654440735589240797328376907)
          ·
            refine ⟨981661103383861195992565361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654440735589240797328376907 981661103383861195992565361)
            ·
              refine ⟨736245827537895896994424021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 981661103383861195992565361 736245827537895896994424021)
              ·
                refine ⟨17255761582919435085806813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 736245827537895896994424021 17255761582919435085806813)
                ·
                  refine ⟨6470910593594788157177555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17255761582919435085806813 6470910593594788157177555)
                  ·
                    refine ⟨9706365890392182235766333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6470910593594788157177555 9706365890392182235766333)
                    ·
                      refine ⟨3639887208897068338412375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9706365890392182235766333 3639887208897068338412375)
                      ·
                        rfl

theorem cell23_7088655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 1, 3].length) (baseStart_7088655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088655 prefixEnd_7088655 := by exact prefixLift 7088655
  have htrace : WordTrace (prefixWord ++ tailWord_7088655) baseStart_7088655 baseEnd_7088655 := by
    simpa [prefixWord, tailWord_7088655, baseEnd_7088655] using wordTrace_append hprefix tailTrace_7088655
  have hstable : (prefixWord ++ tailWord_7088655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088655).length < 2 ^ (prefixWord ++ tailWord_7088655).sum := by decide
  have hdescent : baseEnd_7088655 < baseStart_7088655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088665 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 4, 3, 2]
def baseStart_7088665 : Nat := 118140960795 + 7088665 * 2 ^ 59
def prefixEnd_7088665 : Nat := 4983230072969 + 3 ^ 40 * 7088665 * 2
def baseEnd_7088665 : Nat := 3639892343703613299287329

theorem tailTrace_7088665 : CollatzResearch.WordTrace tailWord_7088665 prefixEnd_7088665 3639892343703613299287329 := by
  unfold tailWord_7088665
  simp only [CollatzResearch.WordTrace]
  refine ⟨258544852863984827442531449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172363235242656551628354299 258544852863984827442531449)
  ·
    refine ⟨193908639647988620581898587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258544852863984827442531449 193908639647988620581898587)
    ·
      refine ⟨290862959471982930872847881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193908639647988620581898587 290862959471982930872847881)
      ·
        refine ⟨218147219603987198154635911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290862959471982930872847881 218147219603987198154635911)
        ·
          refine ⟨327220829405980797231953867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218147219603987198154635911 327220829405980797231953867)
          ·
            refine ⟨490831244108971195847930801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327220829405980797231953867 490831244108971195847930801)
            ·
              refine ⟨368123433081728396885948101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490831244108971195847930801 368123433081728396885948101)
              ·
                refine ⟨69023143702824074416115269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 368123433081728396885948101 69023143702824074416115269)
                ·
                  refine ⟨12941839444279513953021613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69023143702824074416115269 12941839444279513953021613)
                  ·
                    refine ⟨4853189791604817732383105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12941839444279513953021613 4853189791604817732383105)
                    ·
                      refine ⟨3639892343703613299287329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4853189791604817732383105 3639892343703613299287329)
                      ·
                        rfl

theorem cell23_7088665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 3, 2].length) (baseStart_7088665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088665 prefixEnd_7088665 := by exact prefixLift 7088665
  have htrace : WordTrace (prefixWord ++ tailWord_7088665) baseStart_7088665 baseEnd_7088665 := by
    simpa [prefixWord, tailWord_7088665, baseEnd_7088665] using wordTrace_append hprefix tailTrace_7088665
  have hstable : (prefixWord ++ tailWord_7088665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088665).length < 2 ^ (prefixWord ++ tailWord_7088665).sum := by decide
  have hdescent : baseEnd_7088665 < baseStart_7088665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088675 : List Nat := [1, 1, 1, 4, 4, 1, 1, 4, 1, 5]
def baseStart_7088675 : Nat := 118140960795 + 7088675 * 2 ^ 59
def prefixEnd_7088675 : Nat := 4983230072969 + 3 ^ 40 * 7088675 * 2
def baseEnd_7088675 : Nat := 1213299159503386086720761

theorem tailTrace_7088675 : CollatzResearch.WordTrace tailWord_7088675 prefixEnd_7088675 1213299159503386086720761 := by
  unfold tailWord_7088675
  simp only [CollatzResearch.WordTrace]
  refine ⟨258545217593948599150395479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172363478395965732766930319 258545217593948599150395479)
  ·
    refine ⟨387817826390922898725593219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258545217593948599150395479 387817826390922898725593219)
    ·
      refine ⟨581726739586384348088389829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387817826390922898725593219 581726739586384348088389829)
      ·
        refine ⟨109073763672447065266573093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 581726739586384348088389829 109073763672447065266573093)
        ·
          refine ⟨20451330688583824737482455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109073763672447065266573093 20451330688583824737482455)
          ·
            refine ⟨30676996032875737106223683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20451330688583824737482455 30676996032875737106223683)
            ·
              refine ⟨46015494049313605659335525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30676996032875737106223683 46015494049313605659335525)
              ·
                refine ⟨8627905134246301061125411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46015494049313605659335525 8627905134246301061125411)
                ·
                  refine ⟨12941857701369451591688117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8627905134246301061125411 12941857701369451591688117)
                  ·
                    refine ⟨1213299159503386086720761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12941857701369451591688117 1213299159503386086720761)
                    ·
                      rfl

theorem cell23_7088675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 5].length) (baseStart_7088675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088675 prefixEnd_7088675 := by exact prefixLift 7088675
  have htrace : WordTrace (prefixWord ++ tailWord_7088675) baseStart_7088675 baseEnd_7088675 := by
    simpa [prefixWord, tailWord_7088675, baseEnd_7088675] using wordTrace_append hprefix tailTrace_7088675
  have hstable : (prefixWord ++ tailWord_7088675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088675).length < 2 ^ (prefixWord ++ tailWord_7088675).sum := by decide
  have hdescent : baseEnd_7088675 < baseStart_7088675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088682 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_7088682 : Nat := 118140960795 + 7088682 * 2 ^ 59
def prefixEnd_7088682 : Nat := 4983230072969 + 3 ^ 40 * 7088682 * 2
def baseEnd_7088682 : Nat := 3639901072874739732774751

theorem tailTrace_7088682 : CollatzResearch.WordTrace tailWord_7088682 prefixEnd_7088682 3639901072874739732774751 := by
  unfold tailWord_7088682
  simp only [CollatzResearch.WordTrace]
  refine ⟨64636368226230809836475075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172363648603282159563933533 64636368226230809836475075)
  ·
    refine ⟨96954552339346214754712613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64636368226230809836475075 96954552339346214754712613)
    ·
      refine ⟨18178978563627415266508615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96954552339346214754712613 18178978563627415266508615)
      ·
        refine ⟨27268467845441122899762923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18178978563627415266508615 27268467845441122899762923)
        ·
          refine ⟨40902701768161684349644385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27268467845441122899762923 40902701768161684349644385)
          ·
            refine ⟨30677026326121263262233289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40902701768161684349644385 30677026326121263262233289)
            ·
              refine ⟨23007769744590947446674967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30677026326121263262233289 23007769744590947446674967)
              ·
                refine ⟨34511654616886421170012451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23007769744590947446674967 34511654616886421170012451)
                ·
                  refine ⟨51767481925329631755018677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34511654616886421170012451 51767481925329631755018677)
                  ·
                    refine ⟨4853201430499652977033001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51767481925329631755018677 4853201430499652977033001)
                    ·
                      refine ⟨3639901072874739732774751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4853201430499652977033001 3639901072874739732774751)
                      ·
                        rfl

theorem cell23_7088682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_7088682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088682 prefixEnd_7088682 := by exact prefixLift 7088682
  have htrace : WordTrace (prefixWord ++ tailWord_7088682) baseStart_7088682 baseEnd_7088682 := by
    simpa [prefixWord, tailWord_7088682, baseEnd_7088682] using wordTrace_append hprefix tailTrace_7088682
  have hstable : (prefixWord ++ tailWord_7088682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088682).length < 2 ^ (prefixWord ++ tailWord_7088682).sum := by decide
  have hdescent : baseEnd_7088682 < baseStart_7088682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088688 : List Nat := [2, 1, 1, 1, 2, 3, 2, 4, 1, 6]
def baseStart_7088688 : Nat := 118140960795 + 7088688 * 2 ^ 59
def prefixEnd_7088688 : Nat := 4983230072969 + 3 ^ 40 * 7088688 * 2
def baseEnd_7088688 : Nat := 1213301384586222236433241

theorem tailTrace_7088688 : CollatzResearch.WordTrace tailWord_7088688 prefixEnd_7088688 1213301384586222236433241 := by
  unfold tailWord_7088688
  simp only [CollatzResearch.WordTrace]
  refine ⟨129272845871450751185309359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172363794495267668247079145 129272845871450751185309359)
  ·
    refine ⟨193909268807176126777964039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129272845871450751185309359 193909268807176126777964039)
    ·
      refine ⟨290863903210764190166946059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193909268807176126777964039 290863903210764190166946059)
      ·
        refine ⟨436295854816146285250419089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290863903210764190166946059 436295854816146285250419089)
        ·
          refine ⟨327221891112109713937814317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436295854816146285250419089 327221891112109713937814317)
          ·
            refine ⟨122708209167041142726680369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327221891112109713937814317 122708209167041142726680369)
            ·
              refine ⟨92031156875280857045010277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122708209167041142726680369 92031156875280857045010277)
              ·
                refine ⟨17255841914115160695939427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92031156875280857045010277 17255841914115160695939427)
                ·
                  refine ⟨25883762871172741043909141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17255841914115160695939427 25883762871172741043909141)
                  ·
                    refine ⟨1213301384586222236433241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25883762871172741043909141 1213301384586222236433241)
                    ·
                      rfl

theorem cell23_7088688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 1, 6].length) (baseStart_7088688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088688 prefixEnd_7088688 := by exact prefixLift 7088688
  have htrace : WordTrace (prefixWord ++ tailWord_7088688) baseStart_7088688 baseEnd_7088688 := by
    simpa [prefixWord, tailWord_7088688, baseEnd_7088688] using wordTrace_append hprefix tailTrace_7088688
  have hstable : (prefixWord ++ tailWord_7088688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088688).length < 2 ^ (prefixWord ++ tailWord_7088688).sum := by decide
  have hdescent : baseEnd_7088688 < baseStart_7088688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088689 : List Nat := [1, 2, 2, 3, 1, 1, 5, 3, 1, 1, 3]
def baseStart_7088689 : Nat := 118140960795 + 7088689 * 2 ^ 59
def prefixEnd_7088689 : Nat := 4983230072969 + 3 ^ 40 * 7088689 * 2
def baseEnd_7088689 : Nat := 3639904667239321205387219

theorem tailTrace_7088689 : CollatzResearch.WordTrace tailWord_7088689 prefixEnd_7088689 3639904667239321205387219 := by
  unfold tailWord_7088689
  simp only [CollatzResearch.WordTrace]
  refine ⟨258545728215897879541405121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172363818810598586360936747 258545728215897879541405121)
  ·
    refine ⟨193909296161923409656053841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258545728215897879541405121 193909296161923409656053841)
    ·
      refine ⟨145431972121442557242040381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193909296161923409656053841 145431972121442557242040381)
      ·
        refine ⟨54536989545540958965765143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145431972121442557242040381 54536989545540958965765143)
        ·
          refine ⟨81805484318311438448647715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54536989545540958965765143 81805484318311438448647715)
          ·
            refine ⟨122708226477467157672971573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81805484318311438448647715 122708226477467157672971573)
            ·
              refine ⟨11503896232262546031841085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122708226477467157672971573 11503896232262546031841085)
              ·
                refine ⟨4313961087098454761940407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11503896232262546031841085 4313961087098454761940407)
                ·
                  refine ⟨6470941630647682142910611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4313961087098454761940407 6470941630647682142910611)
                  ·
                    refine ⟨9706412445971523214365917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6470941630647682142910611 9706412445971523214365917)
                    ·
                      refine ⟨3639904667239321205387219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9706412445971523214365917 3639904667239321205387219)
                      ·
                        rfl

theorem cell23_7088689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_7088689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088689 prefixEnd_7088689 := by exact prefixLift 7088689
  have htrace : WordTrace (prefixWord ++ tailWord_7088689) baseStart_7088689 baseEnd_7088689 := by
    simpa [prefixWord, tailWord_7088689, baseEnd_7088689] using wordTrace_append hprefix tailTrace_7088689
  have hstable : (prefixWord ++ tailWord_7088689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088689).length < 2 ^ (prefixWord ++ tailWord_7088689).sum := by decide
  have hdescent : baseEnd_7088689 < baseStart_7088689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088695 : List Nat := [1, 1, 3, 1, 2, 3, 1, 5, 1, 1, 4]
def baseStart_7088695 : Nat := 118140960795 + 7088695 * 2 ^ 59
def prefixEnd_7088695 : Nat := 4983230072969 + 3 ^ 40 * 7088695 * 2
def baseEnd_7088695 : Nat := 3639907748123248181912191

theorem tailTrace_7088695 : CollatzResearch.WordTrace tailWord_7088695 prefixEnd_7088695 3639907748123248181912191 := by
  unfold tailWord_7088695
  simp only [CollatzResearch.WordTrace]
  refine ⟨258545947053876142566123539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172363964702584095044082359 258545947053876142566123539)
  ·
    refine ⟨387818920580814213849185309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258545947053876142566123539 387818920580814213849185309)
    ·
      refine ⟨145432095217805330193444491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387818920580814213849185309 145432095217805330193444491)
      ·
        refine ⟨218148142826707995290166737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145432095217805330193444491 218148142826707995290166737)
        ·
          refine ⟨163611107120030996467625053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218148142826707995290166737 163611107120030996467625053)
          ·
            refine ⟨61354165170011623675359395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163611107120030996467625053 61354165170011623675359395)
            ·
              refine ⟨92031247755017435513039093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61354165170011623675359395 92031247755017435513039093)
              ·
                refine ⟨8627929477032884579347415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92031247755017435513039093 8627929477032884579347415)
                ·
                  refine ⟨12941894215549326869021123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8627929477032884579347415 12941894215549326869021123)
                  ·
                    refine ⟨19412841323323990303531685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12941894215549326869021123 19412841323323990303531685)
                    ·
                      refine ⟨3639907748123248181912191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19412841323323990303531685 3639907748123248181912191)
                      ·
                        rfl

theorem cell23_7088695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 1, 4].length) (baseStart_7088695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088695 prefixEnd_7088695 := by exact prefixLift 7088695
  have htrace : WordTrace (prefixWord ++ tailWord_7088695) baseStart_7088695 baseEnd_7088695 := by
    simpa [prefixWord, tailWord_7088695, baseEnd_7088695] using wordTrace_append hprefix tailTrace_7088695
  have hstable : (prefixWord ++ tailWord_7088695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088695).length < 2 ^ (prefixWord ++ tailWord_7088695).sum := by decide
  have hdescent : baseEnd_7088695 < baseStart_7088695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088718 : List Nat := [4, 1, 1, 1, 1, 2, 3, 10]
def baseStart_7088718 : Nat := 118140960795 + 7088718 * 2 ^ 59
def prefixEnd_7088718 : Nat := 4983230072969 + 3 ^ 40 * 7088718 * 2
def baseEnd_7088718 : Nat := 134811835488085244145355

theorem tailTrace_7088718 : CollatzResearch.WordTrace tailWord_7088718 prefixEnd_7088718 134811835488085244145355 := by
  unfold tailWord_7088718
  simp only [CollatzResearch.WordTrace]
  refine ⟨32318348241599102186776351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172364523955195211662807205 32318348241599102186776351)
  ·
    refine ⟨48477522362398653280164527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32318348241599102186776351 48477522362398653280164527)
    ·
      refine ⟨72716283543597979920246791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48477522362398653280164527 72716283543597979920246791)
      ·
        refine ⟨109074425315396969880370187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72716283543597979920246791 109074425315396969880370187)
        ·
          refine ⟨163611637973095454820555281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109074425315396969880370187 163611637973095454820555281)
          ·
            refine ⟨122708728479821591115416461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163611637973095454820555281 122708728479821591115416461)
            ·
              refine ⟨46015773179933096668281173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122708728479821591115416461 46015773179933096668281173)
              ·
                refine ⟨134811835488085244145355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46015773179933096668281173 134811835488085244145355)
                ·
                  rfl

theorem cell23_7088718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 10].length) (baseStart_7088718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088718 prefixEnd_7088718 := by exact prefixLift 7088718
  have htrace : WordTrace (prefixWord ++ tailWord_7088718) baseStart_7088718 baseEnd_7088718 := by
    simpa [prefixWord, tailWord_7088718, baseEnd_7088718] using wordTrace_append hprefix tailTrace_7088718
  have hstable : (prefixWord ++ tailWord_7088718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088718).length < 2 ^ (prefixWord ++ tailWord_7088718).sum := by decide
  have hdescent : baseEnd_7088718 < baseStart_7088718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088722 : List Nat := [3, 2, 2, 1, 2, 1, 3, 3, 2, 4]
def baseStart_7088722 : Nat := 118140960795 + 7088722 * 2 ^ 59
def prefixEnd_7088722 : Nat := 4983230072969 + 3 ^ 40 * 7088722 * 2
def baseEnd_7088722 : Nat := 1213307204033639858758189

theorem tailTrace_7088722 : CollatzResearch.WordTrace tailWord_7088722 prefixEnd_7088722 1213307204033639858758189 := by
  unfold tailWord_7088722
  simp only [CollatzResearch.WordTrace]
  refine ⟨64636732956194581544339105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172364621216518884118237613 64636732956194581544339105)
  ·
    refine ⟨48477549717145936158254329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64636732956194581544339105 48477549717145936158254329)
    ·
      refine ⟨36358162287859452118690747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48477549717145936158254329 36358162287859452118690747)
      ·
        refine ⟨54537243431789178178036121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36358162287859452118690747 54537243431789178178036121)
        ·
          refine ⟨40902932573841883633527091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54537243431789178178036121 40902932573841883633527091)
          ·
            refine ⟨61354398860762825450290637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40902932573841883633527091 61354398860762825450290637)
            ·
              refine ⟨23007899572786059543858989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61354398860762825450290637 23007899572786059543858989)
              ·
                refine ⟨8627962339794772328947121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23007899572786059543858989 8627962339794772328947121)
                ·
                  refine ⟨6470971754846079246710341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8627962339794772328947121 6470971754846079246710341)
                  ·
                    refine ⟨1213307204033639858758189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6470971754846079246710341 1213307204033639858758189)
                    ·
                      rfl

theorem cell23_7088722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_7088722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088722 prefixEnd_7088722 := by exact prefixLift 7088722
  have htrace : WordTrace (prefixWord ++ tailWord_7088722) baseStart_7088722 baseEnd_7088722 := by
    simpa [prefixWord, tailWord_7088722, baseEnd_7088722] using wordTrace_append hprefix tailTrace_7088722
  have hstable : (prefixWord ++ tailWord_7088722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088722).length < 2 ^ (prefixWord ++ tailWord_7088722).sum := by decide
  have hdescent : baseEnd_7088722 < baseStart_7088722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088746 : List Nat := [3, 1, 3, 2, 1, 1, 2, 5, 1, 2, 2]
def baseStart_7088746 : Nat := 118140960795 + 7088746 * 2 ^ 59
def prefixEnd_7088746 : Nat := 4983230072969 + 3 ^ 40 * 7088746 * 2
def baseEnd_7088746 : Nat := 3639933935636627482374457

theorem tailTrace_7088746 : CollatzResearch.WordTrace tailWord_7088746 prefixEnd_7088746 3639933935636627482374457 := by
  unfold tailWord_7088746
  simp only [CollatzResearch.WordTrace]
  refine ⟨64636951794172844569057523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172365204784460918850820061 64636951794172844569057523)
  ·
    refine ⟨96955427691259266853586285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64636951794172844569057523 96955427691259266853586285)
    ·
      refine ⟨36358285384222225070094857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96955427691259266853586285 36358285384222225070094857)
      ·
        refine ⟨27268714038166668802571143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36358285384222225070094857 27268714038166668802571143)
        ·
          refine ⟨40903071057250003203856715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27268714038166668802571143 40903071057250003203856715)
          ·
            refine ⟨61354606585875004805785073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40903071057250003203856715 61354606585875004805785073)
            ·
              refine ⟨46015954939406253604338805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61354606585875004805785073 46015954939406253604338805)
              ·
                refine ⟨4313995775569336275406763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46015954939406253604338805 4313995775569336275406763)
                ·
                  refine ⟨6470993663354004413110145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4313995775569336275406763 6470993663354004413110145)
                  ·
                    refine ⟨4853245247515503309832609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6470993663354004413110145 4853245247515503309832609)
                    ·
                      refine ⟨3639933935636627482374457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4853245247515503309832609 3639933935636627482374457)
                      ·
                        rfl

theorem cell23_7088746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_7088746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088746 prefixEnd_7088746 := by exact prefixLift 7088746
  have htrace : WordTrace (prefixWord ++ tailWord_7088746) baseStart_7088746 baseEnd_7088746 := by
    simpa [prefixWord, tailWord_7088746, baseEnd_7088746] using wordTrace_append hprefix tailTrace_7088746
  have hstable : (prefixWord ++ tailWord_7088746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088746).length < 2 ^ (prefixWord ++ tailWord_7088746).sum := by decide
  have hdescent : baseEnd_7088746 < baseStart_7088746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088815 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 4]
def baseStart_7088815 : Nat := 118140960795 + 7088815 * 2 ^ 59
def prefixEnd_7088815 : Nat := 4983230072969 + 3 ^ 40 * 7088815 * 2
def baseEnd_7088815 : Nat := 3639969365801787712411639

theorem tailTrace_7088815 : CollatzResearch.WordTrace tailWord_7088815 prefixEnd_7088815 3639969365801787712411639 := by
  unfold tailWord_7088815
  simp only [CollatzResearch.WordTrace]
  refine ⟨258550323813441403060491899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172366882542294268706994599 258550323813441403060491899)
  ·
    refine ⟨387825485720162104590737849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258550323813441403060491899 387825485720162104590737849)
    ·
      refine ⟨290869114290121578443053387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387825485720162104590737849 290869114290121578443053387)
      ·
        refine ⟨436303671435182367664580081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290869114290121578443053387 436303671435182367664580081)
        ·
          refine ⟨327227753576386775748435061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436303671435182367664580081 327227753576386775748435061)
          ·
            refine ⟨30677601897786260226415787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 327227753576386775748435061 30677601897786260226415787)
            ·
              refine ⟨46016402846679390339623681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30677601897786260226415787 46016402846679390339623681)
              ·
                refine ⟨34512302135009542754717761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46016402846679390339623681 34512302135009542754717761)
                ·
                  refine ⟨25884226601257157066038321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34512302135009542754717761 25884226601257157066038321)
                  ·
                    refine ⟨19413169950942867799528741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25884226601257157066038321 19413169950942867799528741)
                    ·
                      refine ⟨3639969365801787712411639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19413169950942867799528741 3639969365801787712411639)
                      ·
                        rfl

theorem cell23_7088815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_7088815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088815 prefixEnd_7088815 := by exact prefixLift 7088815
  have htrace : WordTrace (prefixWord ++ tailWord_7088815) baseStart_7088815 baseEnd_7088815 := by
    simpa [prefixWord, tailWord_7088815, baseEnd_7088815] using wordTrace_append hprefix tailTrace_7088815
  have hstable : (prefixWord ++ tailWord_7088815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088815).length < 2 ^ (prefixWord ++ tailWord_7088815).sum := by decide
  have hdescent : baseEnd_7088815 < baseStart_7088815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088819 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 4, 2, 2]
def baseStart_7088819 : Nat := 118140960795 + 7088819 * 2 ^ 59
def prefixEnd_7088819 : Nat := 4983230072969 + 3 ^ 40 * 7088819 * 2
def baseEnd_7088819 : Nat := 3639971419724405696761621

theorem tailTrace_7088819 : CollatzResearch.WordTrace tailWord_7088819 prefixEnd_7088819 3639971419724405696761621 := by
  unfold tailWord_7088819
  simp only [CollatzResearch.WordTrace]
  refine ⟨258550469705426911743637511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172366979803617941162425007 258550469705426911743637511)
  ·
    refine ⟨387825704558140367615456267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258550469705426911743637511 387825704558140367615456267)
    ·
      refine ⟨581738556837210551423184401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387825704558140367615456267 581738556837210551423184401)
      ·
        refine ⟨436303917627907913567388301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581738556837210551423184401 436303917627907913567388301)
        ·
          refine ⟨163613969110465467587770613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436303917627907913567388301 163613969110465467587770613)
          ·
            refine ⟨15338809604106137586353495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163613969110465467587770613 15338809604106137586353495)
            ·
              refine ⟨23008214406159206379530243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15338809604106137586353495 23008214406159206379530243)
              ·
                refine ⟨34512321609238809569295365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23008214406159206379530243 34512321609238809569295365)
                ·
                  refine ⟨6471060301732276794242881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34512321609238809569295365 6471060301732276794242881)
                  ·
                    refine ⟨4853295226299207595682161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6471060301732276794242881 4853295226299207595682161)
                    ·
                      refine ⟨3639971419724405696761621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4853295226299207595682161 3639971419724405696761621)
                      ·
                        rfl

theorem cell23_7088819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 2, 2].length) (baseStart_7088819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088819 prefixEnd_7088819 := by exact prefixLift 7088819
  have htrace : WordTrace (prefixWord ++ tailWord_7088819) baseStart_7088819 baseEnd_7088819 := by
    simpa [prefixWord, tailWord_7088819, baseEnd_7088819] using wordTrace_append hprefix tailTrace_7088819
  have hstable : (prefixWord ++ tailWord_7088819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088819).length < 2 ^ (prefixWord ++ tailWord_7088819).sum := by decide
  have hdescent : baseEnd_7088819 < baseStart_7088819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088836 : List Nat := [2, 3, 3, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_7088836 : Nat := 118140960795 + 7088836 * 2 ^ 59
def prefixEnd_7088836 : Nat := 4983230072969 + 3 ^ 40 * 7088836 * 2
def baseEnd_7088836 : Nat := 3639980148895532130249043

theorem tailTrace_7088836 : CollatzResearch.WordTrace tailWord_7088836 prefixEnd_7088836 3639980148895532130249043 := by
  unfold tailWord_7088836
  simp only [CollatzResearch.WordTrace]
  refine ⟨129275544873182661823503181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172367393164243549098004241 129275544873182661823503181)
  ·
    refine ⟨48478329327443498183813693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129275544873182661823503181 48478329327443498183813693)
    ·
      refine ⟨18179373497791311818930135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48478329327443498183813693 18179373497791311818930135)
      ·
        refine ⟨27269060246686967728395203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18179373497791311818930135 27269060246686967728395203)
        ·
          refine ⟨40903590370030451592592805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27269060246686967728395203 40903590370030451592592805)
          ·
            refine ⟨7669423194380709673611151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40903590370030451592592805 7669423194380709673611151)
            ·
              refine ⟨11504134791571064510416727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7669423194380709673611151 11504134791571064510416727)
              ·
                refine ⟨17256202187356596765625091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11504134791571064510416727 17256202187356596765625091)
                ·
                  refine ⟨25884303281034895148437637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17256202187356596765625091 25884303281034895148437637)
                  ·
                    refine ⟨4853306865194042840332057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25884303281034895148437637 4853306865194042840332057)
                    ·
                      refine ⟨3639980148895532130249043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4853306865194042840332057 3639980148895532130249043)
                      ·
                        rfl

theorem cell23_7088836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_7088836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088836 prefixEnd_7088836 := by exact prefixLift 7088836
  have htrace : WordTrace (prefixWord ++ tailWord_7088836) baseStart_7088836 baseEnd_7088836 := by
    simpa [prefixWord, tailWord_7088836, baseEnd_7088836] using wordTrace_append hprefix tailTrace_7088836
  have hstable : (prefixWord ++ tailWord_7088836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088836).length < 2 ^ (prefixWord ++ tailWord_7088836).sum := by decide
  have hdescent : baseEnd_7088836 < baseStart_7088836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088855 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 1, 7]
def baseStart_7088855 : Nat := 118140960795 + 7088855 * 2 ^ 59
def prefixEnd_7088855 : Nat := 4983230072969 + 3 ^ 40 * 7088855 * 2
def baseEnd_7088855 : Nat := 1213329968342655851970485

theorem tailTrace_7088855 : CollatzResearch.WordTrace tailWord_7088855 prefixEnd_7088855 1213329968342655851970485 := by
  unfold tailWord_7088855
  simp only [CollatzResearch.WordTrace]
  refine ⟨258551782733296489891948019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172367855155530993261298679 258551782733296489891948019)
  ·
    refine ⟨387827674099944734837922029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258551782733296489891948019 387827674099944734837922029)
    ·
      refine ⟨145435377787479275564220761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387827674099944734837922029 145435377787479275564220761)
      ·
        refine ⟨109076533340609456673165571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145435377787479275564220761 109076533340609456673165571)
        ·
          refine ⟨163614800010914185009748357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109076533340609456673165571 163614800010914185009748357)
          ·
            refine ⟨30677775002046409689327817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163614800010914185009748357 30677775002046409689327817)
            ·
              refine ⟨23008331251534807266995863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30677775002046409689327817 23008331251534807266995863)
              ·
                refine ⟨34512496877302210900493795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23008331251534807266995863 34512496877302210900493795)
                ·
                  refine ⟨51768745315953316350740693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34512496877302210900493795 51768745315953316350740693)
                  ·
                    refine ⟨1213329968342655851970485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51768745315953316350740693 1213329968342655851970485)
                    ·
                      rfl

theorem cell23_7088855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_7088855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088855 prefixEnd_7088855 := by exact prefixLift 7088855
  have htrace : WordTrace (prefixWord ++ tailWord_7088855) baseStart_7088855 baseEnd_7088855 := by
    simpa [prefixWord, tailWord_7088855, baseEnd_7088855] using wordTrace_append hprefix tailTrace_7088855
  have hstable : (prefixWord ++ tailWord_7088855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088855).length < 2 ^ (prefixWord ++ tailWord_7088855).sum := by decide
  have hdescent : baseEnd_7088855 < baseStart_7088855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088882 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_7088882 : Nat := 118140960795 + 7088882 * 2 ^ 59
def prefixEnd_7088882 : Nat := 4983230072969 + 3 ^ 40 * 7088882 * 2
def baseEnd_7088882 : Nat := 3640003769005638950273831

theorem tailTrace_7088882 : CollatzResearch.WordTrace tailWord_7088882 prefixEnd_7088882 3640003769005638950273831 := by
  unfold tailWord_7088882
  simp only [CollatzResearch.WordTrace]
  refine ⟨64638191876049668375795225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172368511669465782335453933 64638191876049668375795225)
  ·
    refine ⟨48478643907037251281846419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64638191876049668375795225 48478643907037251281846419)
    ·
      refine ⟨72717965860555876922769629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48478643907037251281846419 72717965860555876922769629)
      ·
        refine ⟨27269237197708453846038611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72717965860555876922769629 27269237197708453846038611)
        ·
          refine ⟨40903855796562680769057917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27269237197708453846038611 40903855796562680769057917)
          ·
            refine ⟨15338945923711005288396719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40903855796562680769057917 15338945923711005288396719)
            ·
              refine ⟨23008418885566507932595079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15338945923711005288396719 23008418885566507932595079)
              ·
                refine ⟨34512628328349761898892619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23008418885566507932595079 34512628328349761898892619)
                ·
                  refine ⟨51768942492524642848338929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34512628328349761898892619 51768942492524642848338929)
                  ·
                    refine ⟨38826706869393482136254197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51768942492524642848338929 38826706869393482136254197)
                    ·
                      refine ⟨3640003769005638950273831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38826706869393482136254197 3640003769005638950273831)
                      ·
                        rfl

theorem cell23_7088882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_7088882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088882 prefixEnd_7088882 := by exact prefixLift 7088882
  have htrace : WordTrace (prefixWord ++ tailWord_7088882) baseStart_7088882 baseEnd_7088882 := by
    simpa [prefixWord, tailWord_7088882, baseEnd_7088882] using wordTrace_append hprefix tailTrace_7088882
  have hstable : (prefixWord ++ tailWord_7088882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088882).length < 2 ^ (prefixWord ++ tailWord_7088882).sum := by decide
  have hdescent : baseEnd_7088882 < baseStart_7088882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088905 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 2, 4, 4]
def baseStart_7088905 : Nat := 118140960795 + 7088905 * 2 ^ 59
def prefixEnd_7088905 : Nat := 4983230072969 + 3 ^ 40 * 7088905 * 2
def baseEnd_7088905 : Nat := 3640015579060692360286225

theorem tailTrace_7088905 : CollatzResearch.WordTrace tailWord_7088905 prefixEnd_7088905 3640015579060692360286225 := by
  unfold tailWord_7088905
  simp only [CollatzResearch.WordTrace]
  refine ⟨258553606383115348431268169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172369070922076898954178779 258553606383115348431268169)
  ·
    refine ⟨193915204787336511323451127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258553606383115348431268169 193915204787336511323451127)
    ·
      refine ⟨290872807181004766985176691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193915204787336511323451127 290872807181004766985176691)
      ·
        refine ⟨436309210771507150477765037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290872807181004766985176691 436309210771507150477765037)
        ·
          refine ⟨163615954039315181429161889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436309210771507150477765037 163615954039315181429161889)
          ·
            refine ⟨122711965529486386071871417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163615954039315181429161889 122711965529486386071871417)
            ·
              refine ⟨92033974147114789553903563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122711965529486386071871417 92033974147114789553903563)
              ·
                refine ⟨138050961220672184330855345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92033974147114789553903563 138050961220672184330855345)
                ·
                  refine ⟨103538220915504138248141509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138050961220672184330855345 103538220915504138248141509)
                  ·
                    refine ⟨19413416421657025921526533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103538220915504138248141509 19413416421657025921526533)
                    ·
                      refine ⟨3640015579060692360286225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19413416421657025921526533 3640015579060692360286225)
                      ·
                        rfl

theorem cell23_7088905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_7088905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088905 prefixEnd_7088905 := by exact prefixLift 7088905
  have htrace : WordTrace (prefixWord ++ tailWord_7088905) baseStart_7088905 baseEnd_7088905 := by
    simpa [prefixWord, tailWord_7088905, baseEnd_7088905] using wordTrace_append hprefix tailTrace_7088905
  have hstable : (prefixWord ++ tailWord_7088905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088905).length < 2 ^ (prefixWord ++ tailWord_7088905).sum := by decide
  have hdescent : baseEnd_7088905 < baseStart_7088905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088936 : List Nat := [2, 1, 5, 1, 1, 1, 3, 4, 1, 4]
def baseStart_7088936 : Nat := 118140960795 + 7088936 * 2 ^ 59
def prefixEnd_7088936 : Nat := 4983230072969 + 3 ^ 40 * 7088936 * 2
def baseEnd_7088936 : Nat := 1213343832320327246332861

theorem tailTrace_7088936 : CollatzResearch.WordTrace tailWord_7088936 prefixEnd_7088936 1213343832320327246332861 := by
  unfold tailWord_7088936
  simp only [CollatzResearch.WordTrace]
  refine ⟨129277368523001520362823331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172369824697335360483764441 129277368523001520362823331)
  ·
    refine ⟨193916052784502280544234997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129277368523001520362823331 193916052784502280544234997)
    ·
      refine ⟨18179629948547088801022031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193916052784502280544234997 18179629948547088801022031)
      ·
        refine ⟨27269444922820633201533047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18179629948547088801022031 27269444922820633201533047)
        ·
          refine ⟨40904167384230949802299571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27269444922820633201533047 40904167384230949802299571)
          ·
            refine ⟨61356251076346424703449357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40904167384230949802299571 61356251076346424703449357)
            ·
              refine ⟨23008594153629909263793509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61356251076346424703449357 23008594153629909263793509)
              ·
                refine ⟨4314111403805607986961283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23008594153629909263793509 4314111403805607986961283)
                ·
                  refine ⟨6471167105708411980441925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4314111403805607986961283 6471167105708411980441925)
                  ·
                    refine ⟨1213343832320327246332861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6471167105708411980441925 1213343832320327246332861)
                    ·
                      rfl

theorem cell23_7088936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_7088936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088936 prefixEnd_7088936 := by exact prefixLift 7088936
  have htrace : WordTrace (prefixWord ++ tailWord_7088936) baseStart_7088936 baseEnd_7088936 := by
    simpa [prefixWord, tailWord_7088936, baseEnd_7088936] using wordTrace_append hprefix tailTrace_7088936
  have hstable : (prefixWord ++ tailWord_7088936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088936).length < 2 ^ (prefixWord ++ tailWord_7088936).sum := by decide
  have hdescent : baseEnd_7088936 < baseStart_7088936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088959 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 5, 1, 3]
def baseStart_7088959 : Nat := 118140960795 + 7088959 * 2 ^ 59
def prefixEnd_7088959 : Nat := 4983230072969 + 3 ^ 40 * 7088959 * 2
def baseEnd_7088959 : Nat := 3640043307016035149010977

theorem tailTrace_7088959 : CollatzResearch.WordTrace tailWord_7088959 prefixEnd_7088959 3640043307016035149010977 := by
  unfold tailWord_7088959
  simp only [CollatzResearch.WordTrace]
  refine ⟨258555575924919715653733931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172370383949946477102489287 258555575924919715653733931)
  ·
    refine ⟨387833363887379573480600897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258555575924919715653733931 387833363887379573480600897)
    ·
      refine ⟨290875022915534680110450673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387833363887379573480600897 290875022915534680110450673)
      ·
        refine ⟨218156267186651010082838005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290875022915534680110450673 218156267186651010082838005)
        ·
          refine ⟨20452150048748532195266063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 218156267186651010082838005 20452150048748532195266063)
          ·
            refine ⟨30678225073122798292899095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20452150048748532195266063 30678225073122798292899095)
            ·
              refine ⟨46017337609684197439348643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30678225073122798292899095 46017337609684197439348643)
              ·
                refine ⟨69026006414526296159022965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46017337609684197439348643 69026006414526296159022965)
                ·
                  refine ⟨6471188101361840264908403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69026006414526296159022965 6471188101361840264908403)
                  ·
                    refine ⟨9706782152042760397362605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6471188101361840264908403 9706782152042760397362605)
                    ·
                      refine ⟨3640043307016035149010977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9706782152042760397362605 3640043307016035149010977)
                      ·
                        rfl

theorem cell23_7088959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 1, 3].length) (baseStart_7088959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088959 prefixEnd_7088959 := by exact prefixLift 7088959
  have htrace : WordTrace (prefixWord ++ tailWord_7088959) baseStart_7088959 baseEnd_7088959 := by
    simpa [prefixWord, tailWord_7088959, baseEnd_7088959] using wordTrace_append hprefix tailTrace_7088959
  have hstable : (prefixWord ++ tailWord_7088959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088959).length < 2 ^ (prefixWord ++ tailWord_7088959).sum := by decide
  have hdescent : baseEnd_7088959 < baseStart_7088959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088969 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 1, 5, 2]
def baseStart_7088969 : Nat := 118140960795 + 7088969 * 2 ^ 59
def prefixEnd_7088969 : Nat := 4983230072969 + 3 ^ 40 * 7088969 * 2
def baseEnd_7088969 : Nat := 3640048441822580109885931

theorem tailTrace_7088969 : CollatzResearch.WordTrace tailWord_7088969 prefixEnd_7088969 3640048441822580109885931 := by
  unfold tailWord_7088969
  simp only [CollatzResearch.WordTrace]
  refine ⟨258555940654883487361597961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172370627103255658241065307 258555940654883487361597961)
  ·
    refine ⟨193916955491162615521198471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258555940654883487361597961 193916955491162615521198471)
    ·
      refine ⟨290875433236743923281797707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193916955491162615521198471 290875433236743923281797707)
      ·
        refine ⟨436313149855115884922696561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290875433236743923281797707 436313149855115884922696561)
        ·
          refine ⟨327234862391336913692022421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436313149855115884922696561 327234862391336913692022421)
          ·
            refine ⟨15339134174593917829313551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 327234862391336913692022421 15339134174593917829313551)
            ·
              refine ⟨23008701261890876743970327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15339134174593917829313551 23008701261890876743970327)
              ·
                refine ⟨34513051892836315115955491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23008701261890876743970327 34513051892836315115955491)
                ·
                  refine ⟨51769577839254472673933237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34513051892836315115955491 51769577839254472673933237)
                  ·
                    refine ⟨4853397922430106813181241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51769577839254472673933237 4853397922430106813181241)
                    ·
                      refine ⟨3640048441822580109885931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4853397922430106813181241 3640048441822580109885931)
                      ·
                        rfl

theorem cell23_7088969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 5, 2].length) (baseStart_7088969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088969 prefixEnd_7088969 := by exact prefixLift 7088969
  have htrace : WordTrace (prefixWord ++ tailWord_7088969) baseStart_7088969 baseEnd_7088969 := by
    simpa [prefixWord, tailWord_7088969, baseEnd_7088969] using wordTrace_append hprefix tailTrace_7088969
  have hstable : (prefixWord ++ tailWord_7088969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088969).length < 2 ^ (prefixWord ++ tailWord_7088969).sum := by decide
  have hdescent : baseEnd_7088969 < baseStart_7088969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7088976 : List Nat := [2, 1, 1, 1, 1, 4, 3, 5, 1, 1, 3]
def baseStart_7088976 : Nat := 118140960795 + 7088976 * 2 ^ 59
def prefixEnd_7088976 : Nat := 4983230072969 + 3 ^ 40 * 7088976 * 2
def baseEnd_7088976 : Nat := 3640052036187161582498399

theorem tailTrace_7088976 : CollatzResearch.WordTrace tailWord_7088976 prefixEnd_7088976 3640052036187161582498399 := by
  unfold tailWord_7088976
  simp only [CollatzResearch.WordTrace]
  refine ⟨129278097982929063778551391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172370797310572085038068521 129278097982929063778551391)
  ·
    refine ⟨193917146974393595667827087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129278097982929063778551391 193917146974393595667827087)
    ·
      refine ⟨290875720461590393501740631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193917146974393595667827087 290875720461590393501740631)
      ·
        refine ⟨436313580692385590252610947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290875720461590393501740631 436313580692385590252610947)
        ·
          refine ⟨654470371038578385378916421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436313580692385590252610947 654470371038578385378916421)
          ·
            refine ⟨122713194569733447258546829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 654470371038578385378916421 122713194569733447258546829)
            ·
              refine ⟨46017447963650042721955061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122713194569733447258546829 46017447963650042721955061)
              ·
                refine ⟨4314135746592191505183287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46017447963650042721955061 4314135746592191505183287)
                ·
                  refine ⟨6471203619888287257774931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4314135746592191505183287 6471203619888287257774931)
                  ·
                    refine ⟨9706805429832430886662397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6471203619888287257774931 9706805429832430886662397)
                    ·
                      refine ⟨3640052036187161582498399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9706805429832430886662397 3640052036187161582498399)
                      ·
                        rfl

theorem cell23_7088976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 1, 1, 3].length) (baseStart_7088976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7088976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7088976 prefixEnd_7088976 := by exact prefixLift 7088976
  have htrace : WordTrace (prefixWord ++ tailWord_7088976) baseStart_7088976 baseEnd_7088976 := by
    simpa [prefixWord, tailWord_7088976, baseEnd_7088976] using wordTrace_append hprefix tailTrace_7088976
  have hstable : (prefixWord ++ tailWord_7088976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7088976).length < 2 ^ (prefixWord ++ tailWord_7088976).sum := by decide
  have hdescent : baseEnd_7088976 < baseStart_7088976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7088976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089009 : List Nat := [1, 2, 2, 2, 1, 6, 1, 1, 1, 6]
def baseStart_7089009 : Nat := 118140960795 + 7089009 * 2 ^ 59
def prefixEnd_7089009 : Nat := 4983230072969 + 3 ^ 40 * 7089009 * 2
def baseEnd_7089009 : Nat := 1213356327016253317795249

theorem tailTrace_7089009 : CollatzResearch.WordTrace tailWord_7089009 prefixEnd_7089009 1213356327016253317795249 := by
  unfold tailWord_7089009
  simp only [CollatzResearch.WordTrace]
  refine ⟨258557399574738574193054081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172371599716492382795369387 258557399574738574193054081)
  ·
    refine ⟨193918049681053930644790561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258557399574738574193054081 193918049681053930644790561)
    ·
      refine ⟨145438537260790447983592921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193918049681053930644790561 145438537260790447983592921)
      ·
        refine ⟨109078902945592835987694691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145438537260790447983592921 109078902945592835987694691)
        ·
          refine ⟨163618354418389253981542037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109078902945592835987694691 163618354418389253981542037)
          ·
            refine ⟨7669610363361996280384783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163618354418389253981542037 7669610363361996280384783)
            ·
              refine ⟨11504415545042994420577175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7669610363361996280384783 11504415545042994420577175)
              ·
                refine ⟨17256623317564491630865763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11504415545042994420577175 17256623317564491630865763)
                ·
                  refine ⟨25884934976346737446298645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17256623317564491630865763 25884934976346737446298645)
                  ·
                    refine ⟨1213356327016253317795249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25884934976346737446298645 1213356327016253317795249)
                    ·
                      rfl

theorem cell23_7089009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_7089009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089009 prefixEnd_7089009 := by exact prefixLift 7089009
  have htrace : WordTrace (prefixWord ++ tailWord_7089009) baseStart_7089009 baseEnd_7089009 := by
    simpa [prefixWord, tailWord_7089009, baseEnd_7089009] using wordTrace_append hprefix tailTrace_7089009
  have hstable : (prefixWord ++ tailWord_7089009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089009).length < 2 ^ (prefixWord ++ tailWord_7089009).sum := by decide
  have hdescent : baseEnd_7089009 < baseStart_7089009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089019 : List Nat := [1, 1, 1, 1, 1, 5, 3, 4, 1, 2, 3]
def baseStart_7089019 : Nat := 118140960795 + 7089019 * 2 ^ 59
def prefixEnd_7089019 : Nat := 4983230072969 + 3 ^ 40 * 7089019 * 2
def baseEnd_7089019 : Nat := 3640074115855304914260701

theorem tailTrace_7089019 : CollatzResearch.WordTrace tailWord_7089019 prefixEnd_7089019 3640074115855304914260701 := by
  unfold tailWord_7089019
  simp only [CollatzResearch.WordTrace]
  refine ⟨258557764304702345900918111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172371842869801563933945407 258557764304702345900918111)
  ·
    refine ⟨387836646457053518851377167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258557764304702345900918111 387836646457053518851377167)
    ·
      refine ⟨581754969685580278277065751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387836646457053518851377167 581754969685580278277065751)
      ·
        refine ⟨872632454528370417415598627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581754969685580278277065751 872632454528370417415598627)
        ·
          refine ⟨1308948681792555626123397941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872632454528370417415598627 1308948681792555626123397941)
          ·
            refine ⟨122713938918052089949068557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1308948681792555626123397941 122713938918052089949068557)
            ·
              refine ⟨46017727094269533730900709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122713938918052089949068557 46017727094269533730900709)
              ·
                refine ⟨8628323830175537574543883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46017727094269533730900709 8628323830175537574543883)
                ·
                  refine ⟨12942485745263306361815825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8628323830175537574543883 12942485745263306361815825)
                  ·
                    refine ⟨9706864308947479771361869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12942485745263306361815825 9706864308947479771361869)
                    ·
                      refine ⟨3640074115855304914260701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9706864308947479771361869 3640074115855304914260701)
                      ·
                        rfl

theorem cell23_7089019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 2, 3].length) (baseStart_7089019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089019 prefixEnd_7089019 := by exact prefixLift 7089019
  have htrace : WordTrace (prefixWord ++ tailWord_7089019) baseStart_7089019 baseEnd_7089019 := by
    simpa [prefixWord, tailWord_7089019, baseEnd_7089019] using wordTrace_append hprefix tailTrace_7089019
  have hstable : (prefixWord ++ tailWord_7089019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089019).length < 2 ^ (prefixWord ++ tailWord_7089019).sum := by decide
  have hdescent : baseEnd_7089019 < baseStart_7089019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089050 : List Nat := [3, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2]
def baseStart_7089050 : Nat := 118140960795 + 7089050 * 2 ^ 59
def prefixEnd_7089050 : Nat := 4983230072969 + 3 ^ 40 * 7089050 * 2
def baseEnd_7089050 : Nat := 3640090033755594292973059

theorem tailTrace_7089050 : CollatzResearch.WordTrace tailWord_7089050 prefixEnd_7089050 3640090033755594292973059 := by
  unfold tailWord_7089050
  simp only [CollatzResearch.WordTrace]
  refine ⟨64639723741897509548824151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172372596645060025463531069 64639723741897509548824151)
  ·
    refine ⟨96959585612846264323236227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64639723741897509548824151 96959585612846264323236227)
    ·
      refine ⟨145439378419269396484854341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96959585612846264323236227 145439378419269396484854341)
      ·
        refine ⟨27269883453613011840910189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145439378419269396484854341 27269883453613011840910189)
        ·
          refine ⟨10226206295104879440341321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27269883453613011840910189 10226206295104879440341321)
          ·
            refine ⟨7669654721328659580255991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10226206295104879440341321 7669654721328659580255991)
            ·
              refine ⟨11504482081992989370383987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7669654721328659580255991 11504482081992989370383987)
              ·
                refine ⟨17256723122989484055575981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11504482081992989370383987 17256723122989484055575981)
                ·
                  refine ⟨6471271171121056520840993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17256723122989484055575981 6471271171121056520840993)
                  ·
                    refine ⟨4853453378340792390630745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6471271171121056520840993 4853453378340792390630745)
                    ·
                      refine ⟨3640090033755594292973059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4853453378340792390630745 3640090033755594292973059)
                      ·
                        rfl

theorem cell23_7089050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_7089050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089050 prefixEnd_7089050 := by exact prefixLift 7089050
  have htrace : WordTrace (prefixWord ++ tailWord_7089050) baseStart_7089050 baseEnd_7089050 := by
    simpa [prefixWord, tailWord_7089050, baseEnd_7089050] using wordTrace_append hprefix tailTrace_7089050
  have hstable : (prefixWord ++ tailWord_7089050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089050).length < 2 ^ (prefixWord ++ tailWord_7089050).sum := by decide
  have hdescent : baseEnd_7089050 < baseStart_7089050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089094 : List Nat := [6, 1, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_7089094 : Nat := 118140960795 + 7089094 * 2 ^ 59
def prefixEnd_7089094 : Nat := 4983230072969 + 3 ^ 40 * 7089094 * 2
def baseEnd_7089094 : Nat := 1213370875634797373607619

theorem tailTrace_7089094 : CollatzResearch.WordTrace tailWord_7089094 prefixEnd_7089094 1213370875634797373607619 := by
  unfold tailWord_7089094
  simp only [CollatzResearch.WordTrace]
  refine ⟨8080015618107207303434323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 172373666519620422473265557 8080015618107207303434323)
  ·
    refine ⟨12120023427160810955151485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8080015618107207303434323 12120023427160810955151485)
    ·
      refine ⟨4545008785185304108181807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12120023427160810955151485 4545008785185304108181807)
      ·
        refine ⟨6817513177777956162272711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4545008785185304108181807 6817513177777956162272711)
        ·
          refine ⟨10226269766666934243409067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6817513177777956162272711 10226269766666934243409067)
          ·
            refine ⟨15339404650000401365113601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10226269766666934243409067 15339404650000401365113601)
            ·
              refine ⟨11504553487500301023835201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15339404650000401365113601 11504553487500301023835201)
              ·
                refine ⟨8628415115625225767876401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11504553487500301023835201 8628415115625225767876401)
                ·
                  refine ⟨6471311336718919325907301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8628415115625225767876401 6471311336718919325907301)
                  ·
                    refine ⟨1213370875634797373607619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6471311336718919325907301 1213370875634797373607619)
                    ·
                      rfl

theorem cell23_7089094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_7089094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089094 prefixEnd_7089094 := by exact prefixLift 7089094
  have htrace : WordTrace (prefixWord ++ tailWord_7089094) baseStart_7089094 baseEnd_7089094 := by
    simpa [prefixWord, tailWord_7089094, baseEnd_7089094] using wordTrace_append hprefix tailTrace_7089094
  have hstable : (prefixWord ++ tailWord_7089094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089094).length < 2 ^ (prefixWord ++ tailWord_7089094).sum := by decide
  have hdescent : baseEnd_7089094 < baseStart_7089094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089101 : List Nat := [1, 6, 3, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_7089101 : Nat := 118140960795 + 7089101 * 2 ^ 59
def prefixEnd_7089101 : Nat := 4983230072969 + 3 ^ 40 * 7089101 * 2
def baseEnd_7089101 : Nat := 3640116221268973593435325

theorem tailTrace_7089101 : CollatzResearch.WordTrace tailWord_7089101 prefixEnd_7089101 3640116221268973593435325 := by
  unfold tailWord_7089101
  simp only [CollatzResearch.WordTrace]
  refine ⟨258560755090405273905403157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172373836726936849270268771 258560755090405273905403157)
  ·
    refine ⟨12120035394862747214315773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 258560755090405273905403157 12120035394862747214315773)
    ·
      refine ⟨4545013273073530205368415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12120035394862747214315773 4545013273073530205368415)
      ·
        refine ⟨6817519909610295308052623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4545013273073530205368415 6817519909610295308052623)
        ·
          refine ⟨10226279864415442962078935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6817519909610295308052623 10226279864415442962078935)
          ·
            refine ⟨15339419796623164443118403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10226279864415442962078935 15339419796623164443118403)
            ·
              refine ⟨23009129694934746664677605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15339419796623164443118403 23009129694934746664677605)
              ·
                refine ⟨4314211817800264999627051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23009129694934746664677605 4314211817800264999627051)
                ·
                  refine ⟨6471317726700397499440577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4314211817800264999627051 6471317726700397499440577)
                  ·
                    refine ⟨4853488295025298124580433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6471317726700397499440577 4853488295025298124580433)
                    ·
                      refine ⟨3640116221268973593435325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4853488295025298124580433 3640116221268973593435325)
                      ·
                        rfl

theorem cell23_7089101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_7089101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089101 prefixEnd_7089101 := by exact prefixLift 7089101
  have htrace : WordTrace (prefixWord ++ tailWord_7089101) baseStart_7089101 baseEnd_7089101 := by
    simpa [prefixWord, tailWord_7089101, baseEnd_7089101] using wordTrace_append hprefix tailTrace_7089101
  have hstable : (prefixWord ++ tailWord_7089101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089101).length < 2 ^ (prefixWord ++ tailWord_7089101).sum := by decide
  have hdescent : baseEnd_7089101 < baseStart_7089101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089123 : List Nat := [1, 1, 1, 6, 1, 1, 1, 5, 2, 2, 2]
def baseStart_7089123 : Nat := 118140960795 + 7089123 * 2 ^ 59
def prefixEnd_7089123 : Nat := 4983230072969 + 3 ^ 40 * 7089123 * 2
def baseEnd_7089123 : Nat := 3640127517843372507360223

theorem tailTrace_7089123 : CollatzResearch.WordTrace tailWord_7089123 prefixEnd_7089123 3640127517843372507360223 := by
  unfold tailWord_7089123
  simp only [CollatzResearch.WordTrace]
  refine ⟨258561557496325571662704023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172374371664217047775136015 258561557496325571662704023)
  ·
    refine ⟨387842336244488357494056035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258561557496325571662704023 387842336244488357494056035)
    ·
      refine ⟨581763504366732536241084053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387842336244488357494056035 581763504366732536241084053)
      ·
        refine ⟨27270164267190587636300815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 581763504366732536241084053 27270164267190587636300815)
        ·
          refine ⟨40905246400785881454451223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27270164267190587636300815 40905246400785881454451223)
          ·
            refine ⟨61357869601178822181676835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40905246400785881454451223 61357869601178822181676835)
            ·
              refine ⟨92036804401768233272515253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61357869601178822181676835 92036804401768233272515253)
              ·
                refine ⟨8628450412665771869298305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92036804401768233272515253 8628450412665771869298305)
                ·
                  refine ⟨6471337809499328901973729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8628450412665771869298305 6471337809499328901973729)
                  ·
                    refine ⟨4853503357124496676480297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6471337809499328901973729 4853503357124496676480297)
                    ·
                      refine ⟨3640127517843372507360223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4853503357124496676480297 3640127517843372507360223)
                      ·
                        rfl

theorem cell23_7089123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_7089123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089123 prefixEnd_7089123 := by exact prefixLift 7089123
  have htrace : WordTrace (prefixWord ++ tailWord_7089123) baseStart_7089123 baseEnd_7089123 := by
    simpa [prefixWord, tailWord_7089123, baseEnd_7089123] using wordTrace_append hprefix tailTrace_7089123
  have hstable : (prefixWord ++ tailWord_7089123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089123).length < 2 ^ (prefixWord ++ tailWord_7089123).sum := by decide
  have hdescent : baseEnd_7089123 < baseStart_7089123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089159 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 4, 5]
def baseStart_7089159 : Nat := 118140960795 + 7089159 * 2 ^ 59
def prefixEnd_7089159 : Nat := 4983230072969 + 3 ^ 40 * 7089159 * 2
def baseEnd_7089159 : Nat := 1213382001048978122170019

theorem tailTrace_7089159 : CollatzResearch.WordTrace tailWord_7089159 prefixEnd_7089159 1213382001048978122170019 := by
  unfold tailWord_7089159
  simp only [CollatzResearch.WordTrace]
  refine ⟨258562870524195149811014531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172375247016130099874009687 258562870524195149811014531)
  ·
    refine ⟨387844305786292724716521797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258562870524195149811014531 387844305786292724716521797)
    ·
      refine ⟨72720807334929885884347837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 387844305786292724716521797 72720807334929885884347837)
      ·
        refine ⟨27270302750598707206630439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72720807334929885884347837 27270302750598707206630439)
        ·
          refine ⟨40905454125898060809945659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27270302750598707206630439 40905454125898060809945659)
          ·
            refine ⟨61358181188847091214918489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40905454125898060809945659 61358181188847091214918489)
            ·
              refine ⟨46018635891635318411188867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61358181188847091214918489 46018635891635318411188867)
              ·
                refine ⟨69027953837452977616783301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46018635891635318411188867 69027953837452977616783301)
                ·
                  refine ⟨12942741344522433303146869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69027953837452977616783301 12942741344522433303146869)
                  ·
                    refine ⟨1213382001048978122170019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12942741344522433303146869 1213382001048978122170019)
                    ·
                      rfl

theorem cell23_7089159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_7089159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089159 prefixEnd_7089159 := by exact prefixLift 7089159
  have htrace : WordTrace (prefixWord ++ tailWord_7089159) baseStart_7089159 baseEnd_7089159 := by
    simpa [prefixWord, tailWord_7089159, baseEnd_7089159] using wordTrace_append hprefix tailTrace_7089159
  have hstable : (prefixWord ++ tailWord_7089159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089159).length < 2 ^ (prefixWord ++ tailWord_7089159).sum := by decide
  have hdescent : baseEnd_7089159 < baseStart_7089159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089216 : List Nat := [2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 3]
def baseStart_7089216 : Nat := 118140960795 + 7089216 * 2 ^ 59
def prefixEnd_7089216 : Nat := 4983230072969 + 3 ^ 40 * 7089216 * 2
def baseEnd_7089216 : Nat := 3640175271544240643497295

theorem tailTrace_7089216 : CollatzResearch.WordTrace tailWord_7089216 prefixEnd_7089216 3640175271544240643497295 := by
  unfold tailWord_7089216
  simp only [CollatzResearch.WordTrace]
  refine ⟨129282474742494324272919751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172376632989992432363893001 129282474742494324272919751)
  ·
    refine ⟨193923712113741486409379627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129282474742494324272919751 193923712113741486409379627)
    ·
      refine ⟨290885568170612229614069441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193923712113741486409379627 290885568170612229614069441)
      ·
        refine ⟨218164176127959172210552081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290885568170612229614069441 218164176127959172210552081)
        ·
          refine ⟨163623132095969379157914061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218164176127959172210552081 163623132095969379157914061)
          ·
            refine ⟨61358674535988517184217773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163623132095969379157914061 61358674535988517184217773)
            ·
              refine ⟨23009502950995693944081665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61358674535988517184217773 23009502950995693944081665)
              ·
                refine ⟨17257127213246770458061249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23009502950995693944081665 17257127213246770458061249)
                ·
                  refine ⟨12942845409935077843545937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17257127213246770458061249 12942845409935077843545937)
                  ·
                    refine ⟨9707134057451308382659453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12942845409935077843545937 9707134057451308382659453)
                    ·
                      refine ⟨3640175271544240643497295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9707134057451308382659453 3640175271544240643497295)
                      ·
                        rfl

theorem cell23_7089216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_7089216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089216 prefixEnd_7089216 := by exact prefixLift 7089216
  have htrace : WordTrace (prefixWord ++ tailWord_7089216) baseStart_7089216 baseEnd_7089216 := by
    simpa [prefixWord, tailWord_7089216, baseEnd_7089216] using wordTrace_append hprefix tailTrace_7089216
  have hstable : (prefixWord ++ tailWord_7089216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089216).length < 2 ^ (prefixWord ++ tailWord_7089216).sum := by decide
  have hdescent : baseEnd_7089216 < baseStart_7089216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089219 : List Nat := [1, 1, 1, 3, 1, 2, 4, 4, 6]
def baseStart_7089219 : Nat := 118140960795 + 7089219 * 2 ^ 59
def prefixEnd_7089219 : Nat := 4983230072969 + 3 ^ 40 * 7089219 * 2
def baseEnd_7089219 : Nat := 404464090220689347973309

theorem tailTrace_7089219 : CollatzResearch.WordTrace tailWord_7089219 prefixEnd_7089219 404464090220689347973309 := by
  unfold tailWord_7089219
  simp only [CollatzResearch.WordTrace]
  refine ⟨258565058903977780058198711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172376705935985186705465807 258565058903977780058198711)
  ·
    refine ⟨387847588355966670087298067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258565058903977780058198711 387847588355966670087298067)
    ·
      refine ⟨581771382533950005130947101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387847588355966670087298067 581771382533950005130947101)
      ·
        refine ⟨218164268450231251924105163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 581771382533950005130947101 218164268450231251924105163)
        ·
          refine ⟨327246402675346877886157745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218164268450231251924105163 327246402675346877886157745)
          ·
            refine ⟨245434802006510158414618309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327246402675346877886157745 245434802006510158414618309)
            ·
              refine ⟨46019025376220654702740933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245434802006510158414618309 46019025376220654702740933)
              ·
                refine ⟨8628567258041372756763925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46019025376220654702740933 8628567258041372756763925)
                ·
                  refine ⟨404464090220689347973309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8628567258041372756763925 404464090220689347973309)
                  ·
                    rfl

theorem cell23_7089219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 6].length) (baseStart_7089219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089219 prefixEnd_7089219 := by exact prefixLift 7089219
  have htrace : WordTrace (prefixWord ++ tailWord_7089219) baseStart_7089219 baseEnd_7089219 := by
    simpa [prefixWord, tailWord_7089219, baseEnd_7089219] using wordTrace_append hprefix tailTrace_7089219
  have hstable : (prefixWord ++ tailWord_7089219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089219).length < 2 ^ (prefixWord ++ tailWord_7089219).sum := by decide
  have hdescent : baseEnd_7089219 < baseStart_7089219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089223 : List Nat := [1, 1, 4, 1, 3, 4, 1, 1, 3, 4]
def baseStart_7089223 : Nat := 118140960795 + 7089223 * 2 ^ 59
def prefixEnd_7089223 : Nat := 4983230072969 + 3 ^ 40 * 7089223 * 2
def baseEnd_7089223 : Nat := 1213392955302940705369921

theorem tailTrace_7089223 : CollatzResearch.WordTrace tailWord_7089223 prefixEnd_7089223 1213392955302940705369921 := by
  unfold tailWord_7089223
  simp only [CollatzResearch.WordTrace]
  refine ⟨258565204795963288741344323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172376803197308859160896215 258565204795963288741344323)
  ·
    refine ⟨387847807193944933112016485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258565204795963288741344323 387847807193944933112016485)
    ·
      refine ⟨72721463848864674958503091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 387847807193944933112016485 72721463848864674958503091)
      ·
        refine ⟨109082195773297012437754637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72721463848864674958503091 109082195773297012437754637)
        ·
          refine ⟨40905823414986379664157989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109082195773297012437754637 40905823414986379664157989)
          ·
            refine ⟨7669841890309946187029623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40905823414986379664157989 7669841890309946187029623)
            ·
              refine ⟨11504762835464919280544435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7669841890309946187029623 11504762835464919280544435)
              ·
                refine ⟨17257144253197378920816653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11504762835464919280544435 17257144253197378920816653)
                ·
                  refine ⟨6471429094949017095306245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17257144253197378920816653 6471429094949017095306245)
                  ·
                    refine ⟨1213392955302940705369921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6471429094949017095306245 1213392955302940705369921)
                    ·
                      rfl

theorem cell23_7089223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_7089223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089223 prefixEnd_7089223 := by exact prefixLift 7089223
  have htrace : WordTrace (prefixWord ++ tailWord_7089223) baseStart_7089223 baseEnd_7089223 := by
    simpa [prefixWord, tailWord_7089223, baseEnd_7089223] using wordTrace_append hprefix tailTrace_7089223
  have hstable : (prefixWord ++ tailWord_7089223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089223).length < 2 ^ (prefixWord ++ tailWord_7089223).sum := by decide
  have hdescent : baseEnd_7089223 < baseStart_7089223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089250 : List Nat := [3, 3, 2, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_7089250 : Nat := 118140960795 + 7089250 * 2 ^ 59
def prefixEnd_7089250 : Nat := 4983230072969 + 3 ^ 40 * 7089250 * 2
def baseEnd_7089250 : Nat := 3640192729886493510472139

theorem tailTrace_7089250 : CollatzResearch.WordTrace tailWord_7089250 prefixEnd_7089250 3640192729886493510472139 := by
  unfold tailWord_7089250
  simp only [CollatzResearch.WordTrace]
  refine ⟨64641547391716368088144301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172377459711243648235051469 64641547391716368088144301)
  ·
    refine ⟨24240580271893638033054113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64641547391716368088144301 24240580271893638033054113)
    ·
      refine ⟨18180435203920228524790585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24240580271893638033054113 18180435203920228524790585)
      ·
        refine ⟨13635326402940171393592939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18180435203920228524790585 13635326402940171393592939)
        ·
          refine ⟨20452989604410257090389409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13635326402940171393592939 20452989604410257090389409)
          ·
            refine ⟨15339742203307692817792057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20452989604410257090389409 15339742203307692817792057)
            ·
              refine ⟨11504806652480769613344043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15339742203307692817792057 11504806652480769613344043)
              ·
                refine ⟨17257209978721154420016065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11504806652480769613344043 17257209978721154420016065)
                ·
                  refine ⟨12942907484040865815012049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17257209978721154420016065 12942907484040865815012049)
                  ·
                    refine ⟨9707180613030649361259037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12942907484040865815012049 9707180613030649361259037)
                    ·
                      refine ⟨3640192729886493510472139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9707180613030649361259037 3640192729886493510472139)
                      ·
                        rfl

theorem cell23_7089250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_7089250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089250 prefixEnd_7089250 := by exact prefixLift 7089250
  have htrace : WordTrace (prefixWord ++ tailWord_7089250) baseStart_7089250 baseEnd_7089250 := by
    simpa [prefixWord, tailWord_7089250, baseEnd_7089250] using wordTrace_append hprefix tailTrace_7089250
  have hstable : (prefixWord ++ tailWord_7089250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089250).length < 2 ^ (prefixWord ++ tailWord_7089250).sum := by decide
  have hdescent : baseEnd_7089250 < baseStart_7089250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089299 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 6]
def baseStart_7089299 : Nat := 118140960795 + 7089299 * 2 ^ 59
def prefixEnd_7089299 : Nat := 4983230072969 + 3 ^ 40 * 7089299 * 2
def baseEnd_7089299 : Nat := 3640217890438563818759413

theorem tailTrace_7089299 : CollatzResearch.WordTrace tailWord_7089299 prefixEnd_7089299 3640217890438563818759413 := by
  unfold tailWord_7089299
  simp only [CollatzResearch.WordTrace]
  refine ⟨258567976743687953721110951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172378651162458635814073967 258567976743687953721110951)
  ·
    refine ⟨387851965115531930581666427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258567976743687953721110951 387851965115531930581666427)
    ·
      refine ⟨581777947673297895872499641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387851965115531930581666427 581777947673297895872499641)
      ·
        refine ⟨436333460754973421904374731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581777947673297895872499641 436333460754973421904374731)
        ·
          refine ⟨654500191132460132856562097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436333460754973421904374731 654500191132460132856562097)
          ·
            refine ⟨490875143349345099642421573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654500191132460132856562097 490875143349345099642421573)
            ·
              refine ⟨92039089378002206182954045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 490875143349345099642421573 92039089378002206182954045)
              ·
                refine ⟨34514658516750827318607767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92039089378002206182954045 34514658516750827318607767)
                ·
                  refine ⟨51771987775126240977911651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34514658516750827318607767 51771987775126240977911651)
                  ·
                    refine ⟨77657981662689361466867477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51771987775126240977911651 77657981662689361466867477)
                    ·
                      refine ⟨3640217890438563818759413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77657981662689361466867477 3640217890438563818759413)
                      ·
                        rfl

theorem cell23_7089299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_7089299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089299 prefixEnd_7089299 := by exact prefixLift 7089299
  have htrace : WordTrace (prefixWord ++ tailWord_7089299) baseStart_7089299 baseEnd_7089299 := by
    simpa [prefixWord, tailWord_7089299, baseEnd_7089299] using wordTrace_append hprefix tailTrace_7089299
  have hstable : (prefixWord ++ tailWord_7089299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089299).length < 2 ^ (prefixWord ++ tailWord_7089299).sum := by decide
  have hdescent : baseEnd_7089299 < baseStart_7089299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089314 : List Nat := [3, 3, 1, 3, 2, 1, 2, 3, 1, 1, 3]
def baseStart_7089314 : Nat := 118140960795 + 7089314 * 2 ^ 59
def prefixEnd_7089314 : Nat := 4983230072969 + 3 ^ 40 * 7089314 * 2
def baseEnd_7089314 : Nat := 3640225592648381260071845

theorem tailTrace_7089314 : CollatzResearch.WordTrace tailWord_7089314 prefixEnd_7089314 3640225592648381260071845 := by
  unfold tailWord_7089314
  simp only [CollatzResearch.WordTrace]
  refine ⟨64642130959658402820726749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172379015892422407521937997 64642130959658402820726749)
  ·
    refine ⟨24240799109871901057772531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64642130959658402820726749 24240799109871901057772531)
    ·
      refine ⟨36361198664807851586658797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24240799109871901057772531 36361198664807851586658797)
      ·
        refine ⟨13635449499302944344997049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36361198664807851586658797 13635449499302944344997049)
        ·
          refine ⟨10226587124477208258747787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13635449499302944344997049 10226587124477208258747787)
          ·
            refine ⟨15339880686715812388121681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10226587124477208258747787 15339880686715812388121681)
            ·
              refine ⟨11504910515036859291091261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15339880686715812388121681 11504910515036859291091261)
              ·
                refine ⟨4314341443138822234159223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11504910515036859291091261 4314341443138822234159223)
                ·
                  refine ⟨6471512164708233351238835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4314341443138822234159223 6471512164708233351238835)
                  ·
                    refine ⟨9707268247062350026858253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6471512164708233351238835 9707268247062350026858253)
                    ·
                      refine ⟨3640225592648381260071845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9707268247062350026858253 3640225592648381260071845)
                      ·
                        rfl

theorem cell23_7089314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_7089314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089314 prefixEnd_7089314 := by exact prefixLift 7089314
  have htrace : WordTrace (prefixWord ++ tailWord_7089314) baseStart_7089314 baseEnd_7089314 := by
    simpa [prefixWord, tailWord_7089314, baseEnd_7089314] using wordTrace_append hprefix tailTrace_7089314
  have hstable : (prefixWord ++ tailWord_7089314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089314).length < 2 ^ (prefixWord ++ tailWord_7089314).sum := by decide
  have hdescent : baseEnd_7089314 < baseStart_7089314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089330 : List Nat := [3, 2, 1, 1, 1, 6, 1, 2, 2, 4]
def baseStart_7089330 : Nat := 118140960795 + 7089330 * 2 ^ 59
def prefixEnd_7089330 : Nat := 4983230072969 + 3 ^ 40 * 7089330 * 2
def baseEnd_7089330 : Nat := 1213411269446284399157257

theorem tailTrace_7089330 : CollatzResearch.WordTrace tailWord_7089330 prefixEnd_7089330 1213411269446284399157257 := by
  unfold tailWord_7089330
  simp only [CollatzResearch.WordTrace]
  refine ⟨64642276851643911503872361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172379404937717097343659629 64642276851643911503872361)
  ·
    refine ⟨48481707638732933627904271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64642276851643911503872361 48481707638732933627904271)
    ·
      refine ⟨72722561458099400441856407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48481707638732933627904271 72722561458099400441856407)
      ·
        refine ⟨109083842187149100662784611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72722561458099400441856407 109083842187149100662784611)
        ·
          refine ⟨163625763280723650994176917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109083842187149100662784611 163625763280723650994176917)
          ·
            refine ⟨7669957653783921140352043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163625763280723650994176917 7669957653783921140352043)
            ·
              refine ⟨11504936480675881710528065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7669957653783921140352043 11504936480675881710528065)
              ·
                refine ⟨8628702360506911282896049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11504936480675881710528065 8628702360506911282896049)
                ·
                  refine ⟨6471526770380183462172037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8628702360506911282896049 6471526770380183462172037)
                  ·
                    refine ⟨1213411269446284399157257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6471526770380183462172037 1213411269446284399157257)
                    ·
                      rfl

theorem cell23_7089330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_7089330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089330 prefixEnd_7089330 := by exact prefixLift 7089330
  have htrace : WordTrace (prefixWord ++ tailWord_7089330) baseStart_7089330 baseEnd_7089330 := by
    simpa [prefixWord, tailWord_7089330, baseEnd_7089330] using wordTrace_append hprefix tailTrace_7089330
  have hstable : (prefixWord ++ tailWord_7089330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089330).length < 2 ^ (prefixWord ++ tailWord_7089330).sum := by decide
  have hdescent : baseEnd_7089330 < baseStart_7089330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089337 : List Nat := [1, 2, 1, 4, 1, 3, 2, 4, 1, 2, 2]
def baseStart_7089337 : Nat := 118140960795 + 7089337 * 2 ^ 59
def prefixEnd_7089337 : Nat := 4983230072969 + 3 ^ 40 * 7089337 * 2
def baseEnd_7089337 : Nat := 3640237402703434670084239

theorem tailTrace_7089337 : CollatzResearch.WordTrace tailWord_7089337 prefixEnd_7089337 3640237402703434670084239 := by
  unfold tailWord_7089337
  simp only [CollatzResearch.WordTrace]
  refine ⟨258569362717550286210994265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172379575145033524140662843 258569362717550286210994265)
  ·
    refine ⟨193927022038162714658245699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258569362717550286210994265 193927022038162714658245699)
    ·
      refine ⟨290890533057244071987368549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193927022038162714658245699 290890533057244071987368549)
      ·
        refine ⟨54541974948233263497631603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290890533057244071987368549 54541974948233263497631603)
        ·
          refine ⟨81812962422349895246447405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54541974948233263497631603 81812962422349895246447405)
          ·
            refine ⟨30679860908381210717417777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81812962422349895246447405 30679860908381210717417777)
            ·
              refine ⟨23009895681285908038063333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30679860908381210717417777 23009895681285908038063333)
              ·
                refine ⟨4314355440241107757136875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23009895681285908038063333 4314355440241107757136875)
                ·
                  refine ⟨6471533160361661635705313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4314355440241107757136875 6471533160361661635705313)
                  ·
                    refine ⟨4853649870271246226778985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6471533160361661635705313 4853649870271246226778985)
                    ·
                      refine ⟨3640237402703434670084239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4853649870271246226778985 3640237402703434670084239)
                      ·
                        rfl

theorem cell23_7089337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_7089337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089337 prefixEnd_7089337 := by exact prefixLift 7089337
  have htrace : WordTrace (prefixWord ++ tailWord_7089337) baseStart_7089337 baseEnd_7089337 := by
    simpa [prefixWord, tailWord_7089337, baseEnd_7089337] using wordTrace_append hprefix tailTrace_7089337
  have hstable : (prefixWord ++ tailWord_7089337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089337).length < 2 ^ (prefixWord ++ tailWord_7089337).sum := by decide
  have hdescent : baseEnd_7089337 < baseStart_7089337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089339 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 2, 7]
def baseStart_7089339 : Nat := 118140960795 + 7089339 * 2 ^ 59
def prefixEnd_7089339 : Nat := 4983230072969 + 3 ^ 40 * 7089339 * 2
def baseEnd_7089339 : Nat := 1213412809888247887419743

theorem tailTrace_7089339 : CollatzResearch.WordTrace tailWord_7089339 prefixEnd_7089339 1213412809888247887419743 := by
  unfold tailWord_7089339
  simp only [CollatzResearch.WordTrace]
  refine ⟨258569435663543040552567071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172379623775695360368378047 258569435663543040552567071)
  ·
    refine ⟨387854153495314560828850607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258569435663543040552567071 387854153495314560828850607)
    ·
      refine ⟨581781230242971841243275911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387854153495314560828850607 581781230242971841243275911)
      ·
        refine ⟨872671845364457761864913867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581781230242971841243275911 872671845364457761864913867)
        ·
          refine ⟨1309007768046686642797370801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872671845364457761864913867 1309007768046686642797370801)
          ·
            refine ⟨981755826035014982098028101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309007768046686642797370801 981755826035014982098028101)
            ·
              refine ⟨184079217381565309143380269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 981755826035014982098028101 184079217381565309143380269)
              ·
                refine ⟨69029706518086990928767601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184079217381565309143380269 69029706518086990928767601)
                ·
                  refine ⟨51772279888565243196575701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69029706518086990928767601 51772279888565243196575701)
                  ·
                    refine ⟨1213412809888247887419743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51772279888565243196575701 1213412809888247887419743)
                    ·
                      rfl

theorem cell23_7089339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 7].length) (baseStart_7089339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089339 prefixEnd_7089339 := by exact prefixLift 7089339
  have htrace : WordTrace (prefixWord ++ tailWord_7089339) baseStart_7089339 baseEnd_7089339 := by
    simpa [prefixWord, tailWord_7089339, baseEnd_7089339] using wordTrace_append hprefix tailTrace_7089339
  have hstable : (prefixWord ++ tailWord_7089339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089339).length < 2 ^ (prefixWord ++ tailWord_7089339).sum := by decide
  have hdescent : baseEnd_7089339 < baseStart_7089339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089359 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 8]
def baseStart_7089359 : Nat := 118140960795 + 7089359 * 2 ^ 59
def prefixEnd_7089359 : Nat := 4983230072969 + 3 ^ 40 * 7089359 * 2
def baseEnd_7089359 : Nat := 3640248699277833584009137

theorem tailTrace_7089359 : CollatzResearch.WordTrace tailWord_7089359 prefixEnd_7089359 3640248699277833584009137 := by
  unfold tailWord_7089359
  simp only [CollatzResearch.WordTrace]
  refine ⟨258570165123470583968295131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172380110082313722645530087 258570165123470583968295131)
  ·
    refine ⟨387855247685205875952442697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258570165123470583968295131 387855247685205875952442697)
    ·
      refine ⟨290891435763904406964332023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387855247685205875952442697 290891435763904406964332023)
      ·
        refine ⟨436337153645856610446498035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290891435763904406964332023 436337153645856610446498035)
        ·
          refine ⟨654505730468784915669747053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436337153645856610446498035 654505730468784915669747053)
          ·
            refine ⟨245439648925794343376155145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 654505730468784915669747053 245439648925794343376155145)
            ·
              refine ⟨184079736694345757532116359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245439648925794343376155145 184079736694345757532116359)
              ·
                refine ⟨276119605041518636298174539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184079736694345757532116359 276119605041518636298174539)
                ·
                  refine ⟨414179407562277954447261809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276119605041518636298174539 414179407562277954447261809)
                  ·
                    refine ⟨310634555671708465835446357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 414179407562277954447261809 310634555671708465835446357)
                    ·
                      refine ⟨3640248699277833584009137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 310634555671708465835446357 3640248699277833584009137)
                      ·
                        rfl

theorem cell23_7089359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_7089359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089359 prefixEnd_7089359 := by exact prefixLift 7089359
  have htrace : WordTrace (prefixWord ++ tailWord_7089359) baseStart_7089359 baseEnd_7089359 := by
    simpa [prefixWord, tailWord_7089359, baseEnd_7089359] using wordTrace_append hprefix tailTrace_7089359
  have hstable : (prefixWord ++ tailWord_7089359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089359).length < 2 ^ (prefixWord ++ tailWord_7089359).sum := by decide
  have hdescent : baseEnd_7089359 < baseStart_7089359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089380 : List Nat := [2, 3, 1, 1, 1, 2, 4, 3, 1, 3, 2]
def baseStart_7089380 : Nat := 118140960795 + 7089380 * 2 ^ 59
def prefixEnd_7089380 : Nat := 4983230072969 + 3 ^ 40 * 7089380 * 2
def baseEnd_7089380 : Nat := 3640259482371578001846541

theorem tailTrace_7089380 : CollatzResearch.WordTrace tailWord_7089380 prefixEnd_7089380 3640259482371578001846541 := by
  unfold tailWord_7089380
  simp only [CollatzResearch.WordTrace]
  refine ⟨129285465528197252277404797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172380620704263003036539729 129285465528197252277404797)
  ·
    refine ⟨48482049573073969604026799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129285465528197252277404797 48482049573073969604026799)
    ·
      refine ⟨72723074359610954406040199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48482049573073969604026799 72723074359610954406040199)
      ·
        refine ⟨109084611539416431609060299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72723074359610954406040199 109084611539416431609060299)
        ·
          refine ⟨163626917309124647413590449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109084611539416431609060299 163626917309124647413590449)
          ·
            refine ⟨122720187981843485560192837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163626917309124647413590449 122720187981843485560192837)
            ·
              refine ⟨23010035246595653542536157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122720187981843485560192837 23010035246595653542536157)
              ·
                refine ⟨8628763217473370078451059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23010035246595653542536157 8628763217473370078451059)
                ·
                  refine ⟨12943144826210055117676589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8628763217473370078451059 12943144826210055117676589)
                  ·
                    refine ⟨4853679309828770669128721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12943144826210055117676589 4853679309828770669128721)
                    ·
                      refine ⟨3640259482371578001846541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4853679309828770669128721 3640259482371578001846541)
                      ·
                        rfl

theorem cell23_7089380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_7089380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089380 prefixEnd_7089380 := by exact prefixLift 7089380
  have htrace : WordTrace (prefixWord ++ tailWord_7089380) baseStart_7089380 baseEnd_7089380 := by
    simpa [prefixWord, tailWord_7089380, baseEnd_7089380] using wordTrace_append hprefix tailTrace_7089380
  have hstable : (prefixWord ++ tailWord_7089380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089380).length < 2 ^ (prefixWord ++ tailWord_7089380).sum := by decide
  have hdescent : baseEnd_7089380 < baseStart_7089380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089404 : List Nat := [2, 2, 2, 1, 5, 2, 2, 1, 2, 1, 3]
def baseStart_7089404 : Nat := 118140960795 + 7089404 * 2 ^ 59
def prefixEnd_7089404 : Nat := 4983230072969 + 3 ^ 40 * 7089404 * 2
def baseEnd_7089404 : Nat := 3640271805907285907946431

theorem tailTrace_7089404 : CollatzResearch.WordTrace tailWord_7089404 prefixEnd_7089404 3640271805907285907946431 := by
  unfold tailWord_7089404
  simp only [CollatzResearch.WordTrace]
  refine ⟨129285903204153778326841633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172381204272205037769122177 129285903204153778326841633)
  ·
    refine ⟨96964427403115333745131225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129285903204153778326841633 96964427403115333745131225)
    ·
      refine ⟨72723320552336500308848419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96964427403115333745131225 72723320552336500308848419)
      ·
        refine ⟨109084980828504750463272629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72723320552336500308848419 109084980828504750463272629)
        ·
          refine ⟨10226716952672320355931809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109084980828504750463272629 10226716952672320355931809)
          ·
            refine ⟨7670037714504240266948857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10226716952672320355931809 7670037714504240266948857)
            ·
              refine ⟨5752528285878180200211643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7670037714504240266948857 5752528285878180200211643)
              ·
                refine ⟨8628792428817270300317465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5752528285878180200211643 8628792428817270300317465)
                ·
                  refine ⟨6471594321612952725238099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8628792428817270300317465 6471594321612952725238099)
                  ·
                    refine ⟨9707391482419429087857149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6471594321612952725238099 9707391482419429087857149)
                    ·
                      refine ⟨3640271805907285907946431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9707391482419429087857149 3640271805907285907946431)
                      ·
                        rfl

theorem cell23_7089404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_7089404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089404 prefixEnd_7089404 := by exact prefixLift 7089404
  have htrace : WordTrace (prefixWord ++ tailWord_7089404) baseStart_7089404 baseEnd_7089404 := by
    simpa [prefixWord, tailWord_7089404, baseEnd_7089404] using wordTrace_append hprefix tailTrace_7089404
  have hstable : (prefixWord ++ tailWord_7089404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089404).length < 2 ^ (prefixWord ++ tailWord_7089404).sum := by decide
  have hdescent : baseEnd_7089404 < baseStart_7089404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089456 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 5]
def baseStart_7089456 : Nat := 118140960795 + 7089456 * 2 ^ 59
def prefixEnd_7089456 : Nat := 4983230072969 + 3 ^ 40 * 7089456 * 2
def baseEnd_7089456 : Nat := 3640298506901319704496191

theorem tailTrace_7089456 : CollatzResearch.WordTrace tailWord_7089456 prefixEnd_7089456 3640298506901319704496191 := by
  unfold tailWord_7089456
  simp only [CollatzResearch.WordTrace]
  refine ⟨129286851502059584767288111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172382468669412779689717481 129286851502059584767288111)
  ·
    refine ⟨193930277253089377150932167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129286851502059584767288111 193930277253089377150932167)
    ·
      refine ⟨290895415879634065726398251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193930277253089377150932167 290895415879634065726398251)
      ·
        refine ⟨436343123819451098589597377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290895415879634065726398251 436343123819451098589597377)
        ·
          refine ⟨327257342864588323942198033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436343123819451098589597377 327257342864588323942198033)
          ·
            refine ⟨245443007148441242956648525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327257342864588323942198033 245443007148441242956648525)
            ·
              refine ⟨92041127680665466108743197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245443007148441242956648525 92041127680665466108743197)
              ·
                refine ⟨34515422880249549790778699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92041127680665466108743197 34515422880249549790778699)
                ·
                  refine ⟨51773134320374324686168049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34515422880249549790778699 51773134320374324686168049)
                  ·
                    refine ⟨38829850740280743514626037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51773134320374324686168049 38829850740280743514626037)
                    ·
                      refine ⟨3640298506901319704496191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38829850740280743514626037 3640298506901319704496191)
                      ·
                        rfl

theorem cell23_7089456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_7089456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089456 prefixEnd_7089456 := by exact prefixLift 7089456
  have htrace : WordTrace (prefixWord ++ tailWord_7089456) baseStart_7089456 baseEnd_7089456 := by
    simpa [prefixWord, tailWord_7089456, baseEnd_7089456] using wordTrace_append hprefix tailTrace_7089456
  have hstable : (prefixWord ++ tailWord_7089456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089456).length < 2 ^ (prefixWord ++ tailWord_7089456).sum := by decide
  have hdescent : baseEnd_7089456 < baseStart_7089456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089460 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_7089460 : Nat := 118140960795 + 7089460 * 2 ^ 59
def prefixEnd_7089460 : Nat := 4983230072969 + 3 ^ 40 * 7089460 * 2
def baseEnd_7089460 : Nat := 3640300560823937688846173

theorem tailTrace_7089460 : CollatzResearch.WordTrace tailWord_7089460 prefixEnd_7089460 3640300560823937688846173 := by
  unfold tailWord_7089460
  simp only [CollatzResearch.WordTrace]
  refine ⟨129286924448052339108860917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172382565930736452145147889 129286924448052339108860917)
  ·
    refine ⟨12120649167004906791455711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129286924448052339108860917 12120649167004906791455711)
    ·
      refine ⟨18180973750507360187183567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12120649167004906791455711 18180973750507360187183567)
      ·
        refine ⟨27271460625761040280775351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18180973750507360187183567 27271460625761040280775351)
        ·
          refine ⟨40907190938641560421163027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27271460625761040280775351 40907190938641560421163027)
          ·
            refine ⟨61360786407962340631744541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40907190938641560421163027 61360786407962340631744541)
            ·
              refine ⟨23010294902985877736904203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61360786407962340631744541 23010294902985877736904203)
              ·
                refine ⟨34515442354478816605356305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23010294902985877736904203 34515442354478816605356305)
                ·
                  refine ⟨25886581765859112454017229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34515442354478816605356305 25886581765859112454017229)
                  ·
                    refine ⟨9707468162197167170256461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25886581765859112454017229 9707468162197167170256461)
                    ·
                      refine ⟨3640300560823937688846173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9707468162197167170256461 3640300560823937688846173)
                      ·
                        rfl

theorem cell23_7089460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_7089460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089460 prefixEnd_7089460 := by exact prefixLift 7089460
  have htrace : WordTrace (prefixWord ++ tailWord_7089460) baseStart_7089460 baseEnd_7089460 := by
    simpa [prefixWord, tailWord_7089460, baseEnd_7089460] using wordTrace_append hprefix tailTrace_7089460
  have hstable : (prefixWord ++ tailWord_7089460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089460).length < 2 ^ (prefixWord ++ tailWord_7089460).sum := by decide
  have hdescent : baseEnd_7089460 < baseStart_7089460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089470 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 2, 5, 2]
def baseStart_7089470 : Nat := 118140960795 + 7089470 * 2 ^ 59
def prefixEnd_7089470 : Nat := 4983230072969 + 3 ^ 40 * 7089470 * 2
def baseEnd_7089470 : Nat := 3640305695630482649721127

theorem tailTrace_7089470 : CollatzResearch.WordTrace tailWord_7089470 prefixEnd_7089470 3640305695630482649721127 := by
  unfold tailWord_7089470
  simp only [CollatzResearch.WordTrace]
  refine ⟨32321776703258556240698233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172382809084045633283723909 32321776703258556240698233)
  ·
    refine ⟨24241332527443917180523675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32321776703258556240698233 24241332527443917180523675)
    ·
      refine ⟨36361998791165875770785513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24241332527443917180523675 36361998791165875770785513)
      ·
        refine ⟨27271499093374406828089135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36361998791165875770785513 27271499093374406828089135)
        ·
          refine ⟨40907248640061610242133703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27271499093374406828089135 40907248640061610242133703)
          ·
            refine ⟨61360872960092415363200555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40907248640061610242133703 61360872960092415363200555)
            ·
              refine ⟨92041309440138623044800833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61360872960092415363200555 92041309440138623044800833)
              ·
                refine ⟨69030982080103967283600625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92041309440138623044800833 69030982080103967283600625)
                ·
                  refine ⟨51773236560077975462700469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69030982080103967283600625 51773236560077975462700469)
                  ·
                    refine ⟨4853740927507310199628169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51773236560077975462700469 4853740927507310199628169)
                    ·
                      refine ⟨3640305695630482649721127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4853740927507310199628169 3640305695630482649721127)
                      ·
                        rfl

theorem cell23_7089470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_7089470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089470 prefixEnd_7089470 := by exact prefixLift 7089470
  have htrace : WordTrace (prefixWord ++ tailWord_7089470) baseStart_7089470 baseEnd_7089470 := by
    simpa [prefixWord, tailWord_7089470, baseEnd_7089470] using wordTrace_append hprefix tailTrace_7089470
  have hstable : (prefixWord ++ tailWord_7089470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089470).length < 2 ^ (prefixWord ++ tailWord_7089470).sum := by decide
  have hdescent : baseEnd_7089470 < baseStart_7089470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089496 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 1, 3, 6]
def baseStart_7089496 : Nat := 118140960795 + 7089496 * 2 ^ 59
def prefixEnd_7089496 : Nat := 4983230072969 + 3 ^ 40 * 7089496 * 2
def baseEnd_7089496 : Nat := 3640319046127499547996007

theorem tailTrace_7089496 : CollatzResearch.WordTrace tailWord_7089496 prefixEnd_7089496 3640319046127499547996007 := by
  unfold tailWord_7089496
  simp only [CollatzResearch.WordTrace]
  refine ⟨129287580961987128183016171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172383441282649504244021561 129287580961987128183016171)
  ·
    refine ⟨193931371442980692274524257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129287580961987128183016171 193931371442980692274524257)
    ·
      refine ⟨145448528582235519205893193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193931371442980692274524257 145448528582235519205893193)
      ·
        refine ⟨109086396436676639404419895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145448528582235519205893193 109086396436676639404419895)
        ·
          refine ⟨163629594655014959106629843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109086396436676639404419895 163629594655014959106629843)
          ·
            refine ⟨245444391982522438659944765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163629594655014959106629843 245444391982522438659944765)
            ·
              refine ⟨92041646993445914497479287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245444391982522438659944765 92041646993445914497479287)
              ·
                refine ⟨138062470490168871746218931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92041646993445914497479287 138062470490168871746218931)
                ·
                  refine ⟨207093705735253307619328397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138062470490168871746218931 207093705735253307619328397)
                  ·
                    refine ⟨77660139650719990357248149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 207093705735253307619328397 77660139650719990357248149)
                    ·
                      refine ⟨3640319046127499547996007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77660139650719990357248149 3640319046127499547996007)
                      ·
                        rfl

theorem cell23_7089496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_7089496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089496 prefixEnd_7089496 := by exact prefixLift 7089496
  have htrace : WordTrace (prefixWord ++ tailWord_7089496) baseStart_7089496 baseEnd_7089496 := by
    simpa [prefixWord, tailWord_7089496, baseEnd_7089496] using wordTrace_append hprefix tailTrace_7089496
  have hstable : (prefixWord ++ tailWord_7089496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089496).length < 2 ^ (prefixWord ++ tailWord_7089496).sum := by decide
  have hdescent : baseEnd_7089496 < baseStart_7089496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089503 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 3]
def baseStart_7089503 : Nat := 118140960795 + 7089503 * 2 ^ 59
def prefixEnd_7089503 : Nat := 4983230072969 + 3 ^ 40 * 7089503 * 2
def baseEnd_7089503 : Nat := 3640322640492081020608475

theorem tailTrace_7089503 : CollatzResearch.WordTrace tailWord_7089503 prefixEnd_7089503 3640322640492081020608475 := by
  unfold tailWord_7089503
  simp only [CollatzResearch.WordTrace]
  refine ⟨258575417234948896561537163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172383611489965931041024775 258575417234948896561537163)
  ·
    refine ⟨387863125852423344842305745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258575417234948896561537163 387863125852423344842305745)
    ·
      refine ⟨290897344389317508631729309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387863125852423344842305745 290897344389317508631729309)
      ·
        refine ⟨109086504145994065736898491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290897344389317508631729309 109086504145994065736898491)
        ·
          refine ⟨163629756218991098605347737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109086504145994065736898491 163629756218991098605347737)
          ·
            refine ⟨122722317164243323954010803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163629756218991098605347737 122722317164243323954010803)
            ·
              refine ⟨184083475746364985931016205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122722317164243323954010803 184083475746364985931016205)
              ·
                refine ⟨69031303404886869724131077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184083475746364985931016205 69031303404886869724131077)
                ·
                  refine ⟨12943369388416288073274577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69031303404886869724131077 12943369388416288073274577)
                  ·
                    refine ⟨9707527041312216054955933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12943369388416288073274577 9707527041312216054955933)
                    ·
                      refine ⟨3640322640492081020608475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9707527041312216054955933 3640322640492081020608475)
                      ·
                        rfl

theorem cell23_7089503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_7089503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089503 prefixEnd_7089503 := by exact prefixLift 7089503
  have htrace : WordTrace (prefixWord ++ tailWord_7089503) baseStart_7089503 baseEnd_7089503 := by
    simpa [prefixWord, tailWord_7089503, baseEnd_7089503] using wordTrace_append hprefix tailTrace_7089503
  have hstable : (prefixWord ++ tailWord_7089503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089503).length < 2 ^ (prefixWord ++ tailWord_7089503).sum := by decide
  have hdescent : baseEnd_7089503 < baseStart_7089503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089533 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 2, 5, 3]
def baseStart_7089533 : Nat := 118140960795 + 7089533 * 2 ^ 59
def prefixEnd_7089533 : Nat := 4983230072969 + 3 ^ 40 * 7089533 * 2
def baseEnd_7089533 : Nat := 3640338044911715903233337

theorem tailTrace_7089533 : CollatzResearch.WordTrace tailWord_7089533 prefixEnd_7089533 3640338044911715903233337 := by
  unfold tailWord_7089533
  simp only [CollatzResearch.WordTrace]
  refine ⟨258576511424840211685129253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172384340949893474456752835 258576511424840211685129253)
  ·
    refine ⟨48483095892157539690961735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258576511424840211685129253 48483095892157539690961735)
    ·
      refine ⟨72724643838236309536442603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48483095892157539690961735 72724643838236309536442603)
      ·
        refine ⟨109086965757354464304663905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72724643838236309536442603 109086965757354464304663905)
        ·
          refine ⟨81815224318015848228497929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109086965757354464304663905 81815224318015848228497929)
          ·
            refine ⟨61361418238511886171373447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81815224318015848228497929 61361418238511886171373447)
            ·
              refine ⟨92042127357767829257060171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61361418238511886171373447 92042127357767829257060171)
              ·
                refine ⟨138063191036651743885590257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92042127357767829257060171 138063191036651743885590257)
                ·
                  refine ⟨103547393277488807914192693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138063191036651743885590257 103547393277488807914192693)
                  ·
                    refine ⟨9707568119764575741955565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103547393277488807914192693 9707568119764575741955565)
                    ·
                      refine ⟨3640338044911715903233337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9707568119764575741955565 3640338044911715903233337)
                      ·
                        rfl

theorem cell23_7089533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_7089533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089533 prefixEnd_7089533 := by exact prefixLift 7089533
  have htrace : WordTrace (prefixWord ++ tailWord_7089533) baseStart_7089533 baseEnd_7089533 := by
    simpa [prefixWord, tailWord_7089533, baseEnd_7089533] using wordTrace_append hprefix tailTrace_7089533
  have hstable : (prefixWord ++ tailWord_7089533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089533).length < 2 ^ (prefixWord ++ tailWord_7089533).sum := by decide
  have hdescent : baseEnd_7089533 < baseStart_7089533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089536 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 2, 9]
def baseStart_7089536 : Nat := 118140960795 + 7089536 * 2 ^ 59
def prefixEnd_7089536 : Nat := 4983230072969 + 3 ^ 40 * 7089536 * 2
def baseEnd_7089536 : Nat := 1213446528451226463831941

theorem tailTrace_7089536 : CollatzResearch.WordTrace tailWord_7089536 prefixEnd_7089536 1213446528451226463831941 := by
  unfold tailWord_7089536
  simp only [CollatzResearch.WordTrace]
  refine ⟨129288310421914671598744231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172384413895886228798325641 129288310421914671598744231)
  ·
    refine ⟨193932465632872007398116347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129288310421914671598744231 193932465632872007398116347)
    ·
      refine ⟨290898698449308011097174521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193932465632872007398116347 290898698449308011097174521)
      ·
        refine ⟨218174023836981008322880891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290898698449308011097174521 218174023836981008322880891)
        ·
          refine ⟨327261035755471512484321337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218174023836981008322880891 327261035755471512484321337)
          ·
            refine ⟨245445776816603634363241003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327261035755471512484321337 245445776816603634363241003)
            ·
              refine ⟨368168665224905451544861505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245445776816603634363241003 368168665224905451544861505)
              ·
                refine ⟨276126498918679088658646129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368168665224905451544861505 276126498918679088658646129)
                ·
                  refine ⟨207094874189009316493984597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276126498918679088658646129 207094874189009316493984597)
                  ·
                    refine ⟨1213446528451226463831941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 207094874189009316493984597 1213446528451226463831941)
                    ·
                      rfl

theorem cell23_7089536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 9].length) (baseStart_7089536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089536 prefixEnd_7089536 := by exact prefixLift 7089536
  have htrace : WordTrace (prefixWord ++ tailWord_7089536) baseStart_7089536 baseEnd_7089536 := by
    simpa [prefixWord, tailWord_7089536, baseEnd_7089536] using wordTrace_append hprefix tailTrace_7089536
  have hstable : (prefixWord ++ tailWord_7089536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089536).length < 2 ^ (prefixWord ++ tailWord_7089536).sum := by decide
  have hdescent : baseEnd_7089536 < baseStart_7089536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089544 : List Nat := [2, 1, 3, 3, 1, 4, 1, 3, 1, 4]
def baseStart_7089544 : Nat := 118140960795 + 7089544 * 2 ^ 59
def prefixEnd_7089544 : Nat := 4983230072969 + 3 ^ 40 * 7089544 * 2
def baseEnd_7089544 : Nat := 1213447897732971786731929

theorem tailTrace_7089544 : CollatzResearch.WordTrace tailWord_7089544 prefixEnd_7089544 1213447897732971786731929 := by
  unfold tailWord_7089544
  simp only [CollatzResearch.WordTrace]
  refine ⟨129288456313900180281889843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172384608418533573709186457 129288456313900180281889843)
  ·
    refine ⟨193932684470850270422834765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129288456313900180281889843 193932684470850270422834765)
    ·
      refine ⟨72724756676568851408563037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193932684470850270422834765 72724756676568851408563037)
      ·
        refine ⟨27271783753713319278211139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72724756676568851408563037 27271783753713319278211139)
        ·
          refine ⟨40907675630569978917316709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27271783753713319278211139 40907675630569978917316709)
          ·
            refine ⟨7670189180731871046996883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40907675630569978917316709 7670189180731871046996883)
            ·
              refine ⟨11505283771097806570495325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7670189180731871046996883 11505283771097806570495325)
              ·
                refine ⟨4314481414161677463935747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11505283771097806570495325 4314481414161677463935747)
                ·
                  refine ⟨6471722121242516195903621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4314481414161677463935747 6471722121242516195903621)
                  ·
                    refine ⟨1213447897732971786731929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6471722121242516195903621 1213447897732971786731929)
                    ·
                      rfl

theorem cell23_7089544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_7089544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089544 prefixEnd_7089544 := by exact prefixLift 7089544
  have htrace : WordTrace (prefixWord ++ tailWord_7089544) baseStart_7089544 baseEnd_7089544 := by
    simpa [prefixWord, tailWord_7089544, baseEnd_7089544] using wordTrace_append hprefix tailTrace_7089544
  have hstable : (prefixWord ++ tailWord_7089544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089544).length < 2 ^ (prefixWord ++ tailWord_7089544).sum := by decide
  have hdescent : baseEnd_7089544 < baseStart_7089544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089554 : List Nat := [3, 2, 3, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_7089554 : Nat := 118140960795 + 7089554 * 2 ^ 59
def prefixEnd_7089554 : Nat := 4983230072969 + 3 ^ 40 * 7089554 * 2
def baseEnd_7089554 : Nat := 3640348828005460321070741

theorem tailTrace_7089554 : CollatzResearch.WordTrace tailWord_7089554 prefixEnd_7089554 3640348828005460321070741 := by
  unfold tailWord_7089554
  simp only [CollatzResearch.WordTrace]
  refine ⟨64644319339441033067910929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172384851571842754847762477 64644319339441033067910929)
  ·
    refine ⟨48483239504580774800933197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64644319339441033067910929 48483239504580774800933197)
    ·
      refine ⟨18181214814217790550349949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48483239504580774800933197 18181214814217790550349949)
      ·
        refine ⟨6817955555331671456381231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18181214814217790550349949 6817955555331671456381231)
        ·
          refine ⟨10226933332997507184571847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6817955555331671456381231 10226933332997507184571847)
          ·
            refine ⟨15340399999496260776857771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10226933332997507184571847 15340399999496260776857771)
            ·
              refine ⟨23010599999244391165286657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15340399999496260776857771 23010599999244391165286657)
              ·
                refine ⟨17257949999433293373964993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23010599999244391165286657 17257949999433293373964993)
                ·
                  refine ⟨12943462499574970030473745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17257949999433293373964993 12943462499574970030473745)
                  ·
                    refine ⟨9707596874681227522855309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12943462499574970030473745 9707596874681227522855309)
                    ·
                      refine ⟨3640348828005460321070741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9707596874681227522855309 3640348828005460321070741)
                      ·
                        rfl

theorem cell23_7089554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_7089554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089554 prefixEnd_7089554 := by exact prefixLift 7089554
  have htrace : WordTrace (prefixWord ++ tailWord_7089554) baseStart_7089554 baseEnd_7089554 := by
    simpa [prefixWord, tailWord_7089554, baseEnd_7089554] using wordTrace_append hprefix tailTrace_7089554
  have hstable : (prefixWord ++ tailWord_7089554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089554).length < 2 ^ (prefixWord ++ tailWord_7089554).sum := by decide
  have hdescent : baseEnd_7089554 < baseStart_7089554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089567 : List Nat := [1, 1, 2, 5, 1, 2, 3, 1, 3, 1, 3]
def baseStart_7089567 : Nat := 118140960795 + 7089567 * 2 ^ 59
def prefixEnd_7089567 : Nat := 4983230072969 + 3 ^ 40 * 7089567 * 2
def baseEnd_7089567 : Nat := 3640355503253968770208181

theorem tailTrace_7089567 : CollatzResearch.WordTrace tailWord_7089567 prefixEnd_7089567 3640355503253968770208181 := by
  unfold tailWord_7089567
  simp only [CollatzResearch.WordTrace]
  refine ⟨258577751506717035491866955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172385167671144690327911303 258577751506717035491866955)
  ·
    refine ⟨387866627260075553237800433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258577751506717035491866955 387866627260075553237800433)
    ·
      refine ⟨290899970445056664928350325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387866627260075553237800433 290899970445056664928350325)
      ·
        refine ⟨27271872229224062337032843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 290899970445056664928350325 27271872229224062337032843)
        ·
          refine ⟨40907808343836093505549265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27271872229224062337032843 40907808343836093505549265)
          ·
            refine ⟨30680856257877070129161949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40907808343836093505549265 30680856257877070129161949)
            ·
              refine ⟨11505321096703901298435731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30680856257877070129161949 11505321096703901298435731)
              ·
                refine ⟨17257981645055851947653597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11505321096703901298435731 17257981645055851947653597)
                ·
                  refine ⟨6471743116895944480370099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17257981645055851947653597 6471743116895944480370099)
                  ·
                    refine ⟨9707614675343916720555149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6471743116895944480370099 9707614675343916720555149)
                    ·
                      refine ⟨3640355503253968770208181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9707614675343916720555149 3640355503253968770208181)
                      ·
                        rfl

theorem cell23_7089567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_7089567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089567 prefixEnd_7089567 := by exact prefixLift 7089567
  have htrace : WordTrace (prefixWord ++ tailWord_7089567) baseStart_7089567 baseEnd_7089567 := by
    simpa [prefixWord, tailWord_7089567, baseEnd_7089567] using wordTrace_append hprefix tailTrace_7089567
  have hstable : (prefixWord ++ tailWord_7089567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089567).length < 2 ^ (prefixWord ++ tailWord_7089567).sum := by decide
  have hdescent : baseEnd_7089567 < baseStart_7089567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089603 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 4]
def baseStart_7089603 : Nat := 118140960795 + 7089603 * 2 ^ 59
def prefixEnd_7089603 : Nat := 4983230072969 + 3 ^ 40 * 7089603 * 2
def baseEnd_7089603 : Nat := 3640373988557530629358015

theorem tailTrace_7089603 : CollatzResearch.WordTrace tailWord_7089603 prefixEnd_7089603 3640373988557530629358015 := by
  unfold tailWord_7089603
  simp only [CollatzResearch.WordTrace]
  refine ⟨258579064534586613640177463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172386043023057742426784975 258579064534586613640177463)
  ·
    refine ⟨387868596801879920460266195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258579064534586613640177463 387868596801879920460266195)
    ·
      refine ⟨581802895202819880690399293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387868596801879920460266195 581802895202819880690399293)
      ·
        refine ⟨218176085701057455258899735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 581802895202819880690399293 218176085701057455258899735)
        ·
          refine ⟨327264128551586182888349603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218176085701057455258899735 327264128551586182888349603)
          ·
            refine ⟨490896192827379274332524405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327264128551586182888349603 490896192827379274332524405)
            ·
              refine ⟨46021518077566806968674163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 490896192827379274332524405 46021518077566806968674163)
              ·
                refine ⟨69032277116350210453011245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46021518077566806968674163 69032277116350210453011245)
                ·
                  refine ⟨25887103918631328919879217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69032277116350210453011245 25887103918631328919879217)
                  ·
                    refine ⟨19415327938973496689909413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25887103918631328919879217 19415327938973496689909413)
                    ·
                      refine ⟨3640373988557530629358015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19415327938973496689909413 3640373988557530629358015)
                      ·
                        rfl

theorem cell23_7089603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_7089603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089603 prefixEnd_7089603 := by exact prefixLift 7089603
  have htrace : WordTrace (prefixWord ++ tailWord_7089603) baseStart_7089603 baseEnd_7089603 := by
    simpa [prefixWord, tailWord_7089603, baseEnd_7089603] using wordTrace_append hprefix tailTrace_7089603
  have hstable : (prefixWord ++ tailWord_7089603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089603).length < 2 ^ (prefixWord ++ tailWord_7089603).sum := by decide
  have hdescent : baseEnd_7089603 < baseStart_7089603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089604 : List Nat := [2, 3, 3, 2, 1, 2, 3, 1, 1, 5]
def baseStart_7089604 : Nat := 118140960795 + 7089604 * 2 ^ 59
def prefixEnd_7089604 : Nat := 4983230072969 + 3 ^ 40 * 7089604 * 2
def baseEnd_7089604 : Nat := 1213458167346061708481837

theorem tailTrace_7089604 : CollatzResearch.WordTrace tailWord_7089604 prefixEnd_7089604 1213458167346061708481837 := by
  unfold tailWord_7089604
  simp only [CollatzResearch.WordTrace]
  refine ⟨129289550503791495405481933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172386067338388660540642577 129289550503791495405481933)
  ·
    refine ⟨48483581438921810777055725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129289550503791495405481933 48483581438921810777055725)
    ·
      refine ⟨18181343039595679041395897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48483581438921810777055725 18181343039595679041395897)
      ·
        refine ⟨13636007279696759281046923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18181343039595679041395897 13636007279696759281046923)
        ·
          refine ⟨20454010919545138921570385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13636007279696759281046923 20454010919545138921570385)
          ·
            refine ⟨15340508189658854191177789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20454010919545138921570385 15340508189658854191177789)
            ·
              refine ⟨5752690571122070321691671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15340508189658854191177789 5752690571122070321691671)
              ·
                refine ⟨8629035856683105482537507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5752690571122070321691671 8629035856683105482537507)
                ·
                  refine ⟨12943553785024658223806261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8629035856683105482537507 12943553785024658223806261)
                  ·
                    refine ⟨1213458167346061708481837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12943553785024658223806261 1213458167346061708481837)
                    ·
                      rfl

theorem cell23_7089604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_7089604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089604 prefixEnd_7089604 := by exact prefixLift 7089604
  have htrace : WordTrace (prefixWord ++ tailWord_7089604) baseStart_7089604 baseEnd_7089604 := by
    simpa [prefixWord, tailWord_7089604, baseEnd_7089604] using wordTrace_append hprefix tailTrace_7089604
  have hstable : (prefixWord ++ tailWord_7089604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089604).length < 2 ^ (prefixWord ++ tailWord_7089604).sum := by decide
  have hdescent : baseEnd_7089604 < baseStart_7089604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089607 : List Nat := [1, 1, 4, 1, 1, 3, 5, 1, 1, 1, 4]
def baseStart_7089607 : Nat := 118140960795 + 7089607 * 2 ^ 59
def prefixEnd_7089607 : Nat := 4983230072969 + 3 ^ 40 * 7089607 * 2
def baseEnd_7089607 : Nat := 3640376042480148613707997

theorem tailTrace_7089607 : CollatzResearch.WordTrace tailWord_7089607 prefixEnd_7089607 3640376042480148613707997 := by
  unfold tailWord_7089607
  simp only [CollatzResearch.WordTrace]
  refine ⟨258579210426572122323323075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172386140284381414882215383 258579210426572122323323075)
  ·
    refine ⟨387868815639858183484984613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258579210426572122323323075 387868815639858183484984613)
    ·
      refine ⟨72725402932473409403434615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 387868815639858183484984613 72725402932473409403434615)
      ·
        refine ⟨109088104398710114105151923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72725402932473409403434615 109088104398710114105151923)
        ·
          refine ⟨163632156598065171157727885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109088104398710114105151923 163632156598065171157727885)
          ·
            refine ⟨61362058724274439184147957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163632156598065171157727885 61362058724274439184147957)
            ·
              refine ⟨5752693005400728673513871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61362058724274439184147957 5752693005400728673513871)
              ·
                refine ⟨8629039508101093010270807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5752693005400728673513871 8629039508101093010270807)
                ·
                  refine ⟨12943559262151639515406211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8629039508101093010270807 12943559262151639515406211)
                  ·
                    refine ⟨19415338893227459273109317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12943559262151639515406211 19415338893227459273109317)
                    ·
                      refine ⟨3640376042480148613707997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19415338893227459273109317 3640376042480148613707997)
                      ·
                        rfl

theorem cell23_7089607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_7089607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089607 prefixEnd_7089607 := by exact prefixLift 7089607
  have htrace : WordTrace (prefixWord ++ tailWord_7089607) baseStart_7089607 baseEnd_7089607 := by
    simpa [prefixWord, tailWord_7089607, baseEnd_7089607] using wordTrace_append hprefix tailTrace_7089607
  have hstable : (prefixWord ++ tailWord_7089607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089607).length < 2 ^ (prefixWord ++ tailWord_7089607).sum := by decide
  have hdescent : baseEnd_7089607 < baseStart_7089607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089610 : List Nat := [3, 1, 2, 1, 2, 3, 3, 1, 1, 1, 5]
def baseStart_7089610 : Nat := 118140960795 + 7089610 * 2 ^ 59
def prefixEnd_7089610 : Nat := 4983230072969 + 3 ^ 40 * 7089610 * 2
def baseEnd_7089610 : Nat := 3640377582922112101970483

theorem tailTrace_7089610 : CollatzResearch.WordTrace tailWord_7089610 prefixEnd_7089610 3640377582922112101970483 := by
  unfold tailWord_7089610
  simp only [CollatzResearch.WordTrace]
  refine ⟨64644829961390313458920571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172386213230374169223788189 64644829961390313458920571)
  ·
    refine ⟨96967244942085470188380857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64644829961390313458920571 96967244942085470188380857)
    ·
      refine ⟨72725433706564102641285643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96967244942085470188380857 72725433706564102641285643)
      ·
        refine ⟨109088150559846153961928465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72725433706564102641285643 109088150559846153961928465)
        ·
          refine ⟨81816112919884615471446349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109088150559846153961928465 81816112919884615471446349)
          ·
            refine ⟨30681042344956730801792381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81816112919884615471446349 30681042344956730801792381)
            ·
              refine ⟨11505390879358774050672143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30681042344956730801792381 11505390879358774050672143)
              ·
                refine ⟨17258086319038161076008215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11505390879358774050672143 17258086319038161076008215)
                ·
                  refine ⟨25887129478557241614012323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17258086319038161076008215 25887129478557241614012323)
                  ·
                    refine ⟨38830694217835862421018485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25887129478557241614012323 38830694217835862421018485)
                    ·
                      refine ⟨3640377582922112101970483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38830694217835862421018485 3640377582922112101970483)
                      ·
                        rfl

theorem cell23_7089610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_7089610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089610 prefixEnd_7089610 := by exact prefixLift 7089610
  have htrace : WordTrace (prefixWord ++ tailWord_7089610) baseStart_7089610 baseEnd_7089610 := by
    simpa [prefixWord, tailWord_7089610, baseEnd_7089610] using wordTrace_append hprefix tailTrace_7089610
  have hstable : (prefixWord ++ tailWord_7089610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089610).length < 2 ^ (prefixWord ++ tailWord_7089610).sum := by decide
  have hdescent : baseEnd_7089610 < baseStart_7089610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089637 : List Nat := [1, 3, 1, 5, 1, 2, 2, 1, 1, 2, 4]
def baseStart_7089637 : Nat := 118140960795 + 7089637 * 2 ^ 59
def prefixEnd_7089637 : Nat := 4983230072969 + 3 ^ 40 * 7089637 * 2
def baseEnd_7089637 : Nat := 3640391446899783496332859

theorem tailTrace_7089637 : CollatzResearch.WordTrace tailWord_7089637 prefixEnd_7089637 3640391446899783496332859 := by
  unfold tailWord_7089637
  simp only [CollatzResearch.WordTrace]
  refine ⟨258580304616463437446915165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172386869744308958297943443 258580304616463437446915165)
  ·
    refine ⟨96967614231173789042593187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258580304616463437446915165 96967614231173789042593187)
    ·
      refine ⟨145451421346760683563889781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96967614231173789042593187 145451421346760683563889781)
      ·
        refine ⟨13636070751258814084114667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145451421346760683563889781 13636070751258814084114667)
        ·
          refine ⟨20454106126888221126172001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13636070751258814084114667 20454106126888221126172001)
          ·
            refine ⟨15340579595166165844629001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20454106126888221126172001 15340579595166165844629001)
            ·
              refine ⟨11505434696374624383471751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15340579595166165844629001 11505434696374624383471751)
              ·
                refine ⟨17258152044561936575207627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11505434696374624383471751 17258152044561936575207627)
                ·
                  refine ⟨25887228066842904862811441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17258152044561936575207627 25887228066842904862811441)
                  ·
                    refine ⟨19415421050132178647108581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25887228066842904862811441 19415421050132178647108581)
                    ·
                      refine ⟨3640391446899783496332859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19415421050132178647108581 3640391446899783496332859)
                      ·
                        rfl

theorem cell23_7089637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_7089637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089637 prefixEnd_7089637 := by exact prefixLift 7089637
  have htrace : WordTrace (prefixWord ++ tailWord_7089637) baseStart_7089637 baseEnd_7089637 := by
    simpa [prefixWord, tailWord_7089637, baseEnd_7089637] using wordTrace_append hprefix tailTrace_7089637
  have hstable : (prefixWord ++ tailWord_7089637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089637).length < 2 ^ (prefixWord ++ tailWord_7089637).sum := by decide
  have hdescent : baseEnd_7089637 < baseStart_7089637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089663 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 4]
def baseStart_7089663 : Nat := 118140960795 + 7089663 * 2 ^ 59
def prefixEnd_7089663 : Nat := 4983230072969 + 3 ^ 40 * 7089663 * 2
def baseEnd_7089663 : Nat := 3640404797396800394607739

theorem tailTrace_7089663 : CollatzResearch.WordTrace tailWord_7089663 prefixEnd_7089663 3640404797396800394607739 := by
  unfold tailWord_7089663
  simp only [CollatzResearch.WordTrace]
  refine ⟨258581252914369243887361643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172387501942912829258241095 258581252914369243887361643)
  ·
    refine ⟨387871879371553865831042465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258581252914369243887361643 387871879371553865831042465)
    ·
      refine ⟨290903909528665399373281849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387871879371553865831042465 290903909528665399373281849)
      ·
        refine ⟨218177932146499049529961387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290903909528665399373281849 218177932146499049529961387)
        ·
          refine ⟨327266898219748574294942081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218177932146499049529961387 327266898219748574294942081)
          ·
            refine ⟨245450173664811430721206561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327266898219748574294942081 245450173664811430721206561)
            ·
              refine ⟨184087630248608573040904921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245450173664811430721206561 184087630248608573040904921)
              ·
                refine ⟨138065722686456429780678691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184087630248608573040904921 138065722686456429780678691)
                ·
                  refine ⟨207098584029684644671018037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138065722686456429780678691 207098584029684644671018037)
                  ·
                    refine ⟨19415492252782935437907941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 207098584029684644671018037 19415492252782935437907941)
                    ·
                      refine ⟨3640404797396800394607739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19415492252782935437907941 3640404797396800394607739)
                      ·
                        rfl

theorem cell23_7089663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_7089663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089663 prefixEnd_7089663 := by exact prefixLift 7089663
  have htrace : WordTrace (prefixWord ++ tailWord_7089663) baseStart_7089663 baseEnd_7089663 := by
    simpa [prefixWord, tailWord_7089663, baseEnd_7089663] using wordTrace_append hprefix tailTrace_7089663
  have hstable : (prefixWord ++ tailWord_7089663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089663).length < 2 ^ (prefixWord ++ tailWord_7089663).sum := by decide
  have hdescent : baseEnd_7089663 < baseStart_7089663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089673 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 4, 6]
def baseStart_7089673 : Nat := 118140960795 + 7089673 * 2 ^ 59
def prefixEnd_7089673 : Nat := 4983230072969 + 3 ^ 40 * 7089673 * 2
def baseEnd_7089673 : Nat := 1213469977401115118494231

theorem tailTrace_7089673 : CollatzResearch.WordTrace tailWord_7089673 prefixEnd_7089673 1213469977401115118494231 := by
  unfold tailWord_7089673
  simp only [CollatzResearch.WordTrace]
  refine ⟨258581617644333015595225673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172387745096222010396817115 258581617644333015595225673)
  ·
    refine ⟨193936213233249761696419255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258581617644333015595225673 193936213233249761696419255)
    ·
      refine ⟨290904319849874642544628883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193936213233249761696419255 290904319849874642544628883)
      ·
        refine ⟨436356479774811963816943325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290904319849874642544628883 436356479774811963816943325)
        ·
          refine ⟨163633679915554486431353747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436356479774811963816943325 163633679915554486431353747)
          ·
            refine ⟨245450519873331729647030621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163633679915554486431353747 245450519873331729647030621)
            ·
              refine ⟨92043944952499398617636483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245450519873331729647030621 92043944952499398617636483)
              ·
                refine ⟨138065917428749097926454725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92043944952499398617636483 138065917428749097926454725)
                ·
                  refine ⟨25887359517890455861210261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138065917428749097926454725 25887359517890455861210261)
                  ·
                    refine ⟨1213469977401115118494231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25887359517890455861210261 1213469977401115118494231)
                    ·
                      rfl

theorem cell23_7089673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 6].length) (baseStart_7089673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089673 prefixEnd_7089673 := by exact prefixLift 7089673
  have htrace : WordTrace (prefixWord ++ tailWord_7089673) baseStart_7089673 baseEnd_7089673 := by
    simpa [prefixWord, tailWord_7089673, baseEnd_7089673] using wordTrace_append hprefix tailTrace_7089673
  have hstable : (prefixWord ++ tailWord_7089673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089673).length < 2 ^ (prefixWord ++ tailWord_7089673).sum := by decide
  have hdescent : baseEnd_7089673 < baseStart_7089673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089674 : List Nat := [3, 1, 2, 2, 2, 2, 3, 2, 2, 1, 3]
def baseStart_7089674 : Nat := 118140960795 + 7089674 * 2 ^ 59
def prefixEnd_7089674 : Nat := 4983230072969 + 3 ^ 40 * 7089674 * 2
def baseEnd_7089674 : Nat := 3640410445683999851570189

theorem tailTrace_7089674 : CollatzResearch.WordTrace tailWord_7089674 prefixEnd_7089674 3640410445683999851570189 := by
  unfold tailWord_7089674
  simp only [CollatzResearch.WordTrace]
  refine ⟨64645413529332348191503019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172387769411552928510674717 64645413529332348191503019)
  ·
    refine ⟨96968120293998522287254529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64645413529332348191503019 96968120293998522287254529)
    ·
      refine ⟨72726090220498891715440897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96968120293998522287254529 72726090220498891715440897)
      ·
        refine ⟨54544567665374168786580673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72726090220498891715440897 54544567665374168786580673)
        ·
          refine ⟨40908425749030626589935505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54544567665374168786580673 40908425749030626589935505)
          ·
            refine ⟨30681319311772969942451629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40908425749030626589935505 30681319311772969942451629)
            ·
              refine ⟨11505494741914863728419361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30681319311772969942451629 11505494741914863728419361)
              ·
                refine ⟨8629121056436147796314521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11505494741914863728419361 8629121056436147796314521)
                ·
                  refine ⟨6471840792327110847235891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8629121056436147796314521 6471840792327110847235891)
                  ·
                    refine ⟨9707761188490666270853837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6471840792327110847235891 9707761188490666270853837)
                    ·
                      refine ⟨3640410445683999851570189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9707761188490666270853837 3640410445683999851570189)
                      ·
                        rfl

theorem cell23_7089674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_7089674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089674 prefixEnd_7089674 := by exact prefixLift 7089674
  have htrace : WordTrace (prefixWord ++ tailWord_7089674) baseStart_7089674 baseEnd_7089674 := by
    simpa [prefixWord, tailWord_7089674, baseEnd_7089674] using wordTrace_append hprefix tailTrace_7089674
  have hstable : (prefixWord ++ tailWord_7089674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089674).length < 2 ^ (prefixWord ++ tailWord_7089674).sum := by decide
  have hdescent : baseEnd_7089674 < baseStart_7089674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089787 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 2, 4, 2]
def baseStart_7089787 : Nat := 118140960795 + 7089787 * 2 ^ 59
def prefixEnd_7089787 : Nat := 4983230072969 + 3 ^ 40 * 7089787 * 2
def baseEnd_7089787 : Nat := 3640468468997957909457169

theorem tailTrace_7089787 : CollatzResearch.WordTrace tailWord_7089787 prefixEnd_7089787 3640468468997957909457169 := by
  unfold tailWord_7089787
  simp only [CollatzResearch.WordTrace]
  refine ⟨258585775565920013064875615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172390517043946675376583743 258585775565920013064875615)
  ·
    refine ⟨387878663348880019597313423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258585775565920013064875615 387878663348880019597313423)
    ·
      refine ⟨581817995023320029395970135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387878663348880019597313423 581817995023320029395970135)
      ·
        refine ⟨872726992534980044093955203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581817995023320029395970135 872726992534980044093955203)
        ·
          refine ⟨1309090488802470066140932805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872726992534980044093955203 1309090488802470066140932805)
          ·
            refine ⟨245454466650463137401424901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1309090488802470066140932805 245454466650463137401424901)
            ·
              refine ⟨46022712496961838262767169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245454466650463137401424901 46022712496961838262767169)
              ·
                refine ⟨34517034372721378697075377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46022712496961838262767169 34517034372721378697075377)
                ·
                  refine ⟨25887775779541034022806533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34517034372721378697075377 25887775779541034022806533)
                  ·
                    refine ⟨4853957958663943879276225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25887775779541034022806533 4853957958663943879276225)
                    ·
                      refine ⟨3640468468997957909457169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4853957958663943879276225 3640468468997957909457169)
                      ·
                        rfl

theorem cell23_7089787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 4, 2].length) (baseStart_7089787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089787 prefixEnd_7089787 := by exact prefixLift 7089787
  have htrace : WordTrace (prefixWord ++ tailWord_7089787) baseStart_7089787 baseEnd_7089787 := by
    simpa [prefixWord, tailWord_7089787, baseEnd_7089787] using wordTrace_append hprefix tailTrace_7089787
  have hstable : (prefixWord ++ tailWord_7089787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089787).length < 2 ^ (prefixWord ++ tailWord_7089787).sum := by decide
  have hdescent : baseEnd_7089787 < baseStart_7089787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089797 : List Nat := [1, 3, 1, 1, 4, 1, 2, 3, 3, 4]
def baseStart_7089797 : Nat := 118140960795 + 7089797 * 2 ^ 59
def prefixEnd_7089797 : Nat := 4983230072969 + 3 ^ 40 * 7089797 * 2
def baseEnd_7089797 : Nat := 1213491201268167623444041

theorem tailTrace_7089797 : CollatzResearch.WordTrace tailWord_7089797 prefixEnd_7089797 1213491201268167623444041 := by
  unfold tailWord_7089797
  simp only [CollatzResearch.WordTrace]
  refine ⟨258586140295883784772739645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172390760197255856515159763 258586140295883784772739645)
  ·
    refine ⟨96969802610956419289777367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258586140295883784772739645 96969802610956419289777367)
    ·
      refine ⟨145454703916434628934666051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96969802610956419289777367 145454703916434628934666051)
      ·
        refine ⟨218182055874651943401999077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145454703916434628934666051 218182055874651943401999077)
        ·
          refine ⟨40909135476497239387874827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218182055874651943401999077 40909135476497239387874827)
          ·
            refine ⟨61363703214745859081812241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40909135476497239387874827 61363703214745859081812241)
            ·
              refine ⟨46022777411059394311359181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61363703214745859081812241 46022777411059394311359181)
              ·
                refine ⟨17258541529147272866759693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46022777411059394311359181 17258541529147272866759693)
                ·
                  refine ⟨6471953073430227325034885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17258541529147272866759693 6471953073430227325034885)
                  ·
                    refine ⟨1213491201268167623444041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6471953073430227325034885 1213491201268167623444041)
                    ·
                      rfl

theorem cell23_7089797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_7089797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089797 prefixEnd_7089797 := by exact prefixLift 7089797
  have htrace : WordTrace (prefixWord ++ tailWord_7089797) baseStart_7089797 baseEnd_7089797 := by
    simpa [prefixWord, tailWord_7089797, baseEnd_7089797] using wordTrace_append hprefix tailTrace_7089797
  have hstable : (prefixWord ++ tailWord_7089797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089797).length < 2 ^ (prefixWord ++ tailWord_7089797).sum := by decide
  have hdescent : baseEnd_7089797 < baseStart_7089797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089824 : List Nat := [2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 3]
def baseStart_7089824 : Nat := 118140960795 + 7089824 * 2 ^ 59
def prefixEnd_7089824 : Nat := 4983230072969 + 3 ^ 40 * 7089824 * 2
def baseEnd_7089824 : Nat := 3640487467782174264694499

theorem tailTrace_7089824 : CollatzResearch.WordTrace tailWord_7089824 prefixEnd_7089824 3640487467782174264694499 := by
  unfold tailWord_7089824
  simp only [CollatzResearch.WordTrace]
  refine ⟨129293562533392984191986263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172391416711190645589315017 129293562533392984191986263)
  ·
    refine ⟨193940343800089476287979395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129293562533392984191986263 193940343800089476287979395)
    ·
      refine ⟨290910515700134214431969093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193940343800089476287979395 290910515700134214431969093)
      ·
        refine ⟨54545721693775165205994205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290910515700134214431969093 54545721693775165205994205)
        ·
          refine ⟨20454645635165686952247827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54545721693775165205994205 20454645635165686952247827)
          ·
            refine ⟨30681968452748530428371741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20454645635165686952247827 30681968452748530428371741)
            ·
              refine ⟨11505738169780698910639403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30681968452748530428371741 11505738169780698910639403)
              ·
                refine ⟨17258607254671048365959105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11505738169780698910639403 17258607254671048365959105)
                ·
                  refine ⟨12943955441003286274469329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17258607254671048365959105 12943955441003286274469329)
                  ·
                    refine ⟨9707966580752464705851997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12943955441003286274469329 9707966580752464705851997)
                    ·
                      refine ⟨3640487467782174264694499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9707966580752464705851997 3640487467782174264694499)
                      ·
                        rfl

theorem cell23_7089824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_7089824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089824 prefixEnd_7089824 := by exact prefixLift 7089824
  have htrace : WordTrace (prefixWord ++ tailWord_7089824) baseStart_7089824 baseEnd_7089824 := by
    simpa [prefixWord, tailWord_7089824, baseEnd_7089824] using wordTrace_append hprefix tailTrace_7089824
  have hstable : (prefixWord ++ tailWord_7089824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089824).length < 2 ^ (prefixWord ++ tailWord_7089824).sum := by decide
  have hdescent : baseEnd_7089824 < baseStart_7089824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089874 : List Nat := [3, 2, 2, 2, 2, 1, 1, 4, 1, 5]
def baseStart_7089874 : Nat := 118140960795 + 7089874 * 2 ^ 59
def prefixEnd_7089874 : Nat := 4983230072969 + 3 ^ 40 * 7089874 * 2
def baseEnd_7089874 : Nat := 1213504380604966356356423

theorem tailTrace_7089874 : CollatzResearch.WordTrace tailWord_7089874 prefixEnd_7089874 1213504380604966356356423 := by
  unfold tailWord_7089874
  simp only [CollatzResearch.WordTrace]
  refine ⟨64647237179151206730823169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172392632477736551282195117 64647237179151206730823169)
  ·
    refine ⟨48485427884363405048117377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64647237179151206730823169 48485427884363405048117377)
    ·
      refine ⟨36364070913272553786088033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48485427884363405048117377 36364070913272553786088033)
      ·
        refine ⟨27273053184954415339566025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36364070913272553786088033 27273053184954415339566025)
        ·
          refine ⟨20454789888715811504674519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27273053184954415339566025 20454789888715811504674519)
          ·
            refine ⟨30682184833073717257011779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20454789888715811504674519 30682184833073717257011779)
            ·
              refine ⟨46023277249610575885517669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30682184833073717257011779 46023277249610575885517669)
              ·
                refine ⟨8629364484301982978534563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46023277249610575885517669 8629364484301982978534563)
                ·
                  refine ⟨12944046726452974467801845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8629364484301982978534563 12944046726452974467801845)
                  ·
                    refine ⟨1213504380604966356356423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12944046726452974467801845 1213504380604966356356423)
                    ·
                      rfl

theorem cell23_7089874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_7089874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089874 prefixEnd_7089874 := by exact prefixLift 7089874
  have htrace : WordTrace (prefixWord ++ tailWord_7089874) baseStart_7089874 baseEnd_7089874 := by
    simpa [prefixWord, tailWord_7089874, baseEnd_7089874] using wordTrace_append hprefix tailTrace_7089874
  have hstable : (prefixWord ++ tailWord_7089874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089874).length < 2 ^ (prefixWord ++ tailWord_7089874).sum := by decide
  have hdescent : baseEnd_7089874 < baseStart_7089874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089887 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 6, 4]
def baseStart_7089887 : Nat := 118140960795 + 7089887 * 2 ^ 59
def prefixEnd_7089887 : Nat := 4983230072969 + 3 ^ 40 * 7089887 * 2
def baseEnd_7089887 : Nat := 1213506605687802506068903

theorem tailTrace_7089887 : CollatzResearch.WordTrace tailWord_7089887 prefixEnd_7089887 1213506605687802506068903 := by
  unfold tailWord_7089887
  simp only [CollatzResearch.WordTrace]
  refine ⟨258589422865557730143515915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172392948577038486762343943 258589422865557730143515915)
  ·
    refine ⟨387884134298336595215273873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258589422865557730143515915 387884134298336595215273873)
    ·
      refine ⟨290913100723752446411455405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387884134298336595215273873 290913100723752446411455405)
      ·
        refine ⟨109092412771407167404295777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290913100723752446411455405 109092412771407167404295777)
        ·
          refine ⟨81819309578555375553221833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109092412771407167404295777 81819309578555375553221833)
          ·
            refine ⟨61364482183916531664916375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81819309578555375553221833 61364482183916531664916375)
            ·
              refine ⟨92046723275874797497374563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61364482183916531664916375 92046723275874797497374563)
              ·
                refine ⟨138070084913812196246061845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92046723275874797497374563 138070084913812196246061845)
                ·
                  refine ⟨6472035230334946699034149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138070084913812196246061845 6472035230334946699034149)
                  ·
                    refine ⟨1213506605687802506068903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6472035230334946699034149 1213506605687802506068903)
                    ·
                      rfl

theorem cell23_7089887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 4].length) (baseStart_7089887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089887 prefixEnd_7089887 := by exact prefixLift 7089887
  have htrace : WordTrace (prefixWord ++ tailWord_7089887) baseStart_7089887 baseEnd_7089887 := by
    simpa [prefixWord, tailWord_7089887, baseEnd_7089887] using wordTrace_append hprefix tailTrace_7089887
  have hstable : (prefixWord ++ tailWord_7089887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089887).length < 2 ^ (prefixWord ++ tailWord_7089887).sum := by decide
  have hdescent : baseEnd_7089887 < baseStart_7089887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089897 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 5, 2, 3]
def baseStart_7089897 : Nat := 118140960795 + 7089897 * 2 ^ 59
def prefixEnd_7089897 : Nat := 4983230072969 + 3 ^ 40 * 7089897 * 2
def baseEnd_7089897 : Nat := 3640524951869952479081663

theorem tailTrace_7089897 : CollatzResearch.WordTrace tailWord_7089897 prefixEnd_7089897 3640524951869952479081663 := by
  unfold tailWord_7089897
  simp only [CollatzResearch.WordTrace]
  refine ⟨258589787595521501851379945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172393191730347667900919963 258589787595521501851379945)
  ·
    refine ⟨193942340696641126388534959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258589787595521501851379945 193942340696641126388534959)
    ·
      refine ⟨290913511044961689582802439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193942340696641126388534959 290913511044961689582802439)
      ·
        refine ⟨436370266567442534374203659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290913511044961689582802439 436370266567442534374203659)
        ·
          refine ⟨654555399851163801561305489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436370266567442534374203659 654555399851163801561305489)
          ·
            refine ⟨490916549888372851170979117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654555399851163801561305489 490916549888372851170979117)
            ·
              refine ⟨184093706208139819189117169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 490916549888372851170979117 184093706208139819189117169)
              ·
                refine ⟨138070279656104864391837877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184093706208139819189117169 138070279656104864391837877)
                ·
                  refine ⟨12944088717759831036734801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138070279656104864391837877 12944088717759831036734801)
                  ·
                    refine ⟨9708066538319873277551101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12944088717759831036734801 9708066538319873277551101)
                    ·
                      refine ⟨3640524951869952479081663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9708066538319873277551101 3640524951869952479081663)
                      ·
                        rfl

theorem cell23_7089897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 2, 3].length) (baseStart_7089897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089897 prefixEnd_7089897 := by exact prefixLift 7089897
  have htrace : WordTrace (prefixWord ++ tailWord_7089897) baseStart_7089897 baseEnd_7089897 := by
    simpa [prefixWord, tailWord_7089897, baseEnd_7089897] using wordTrace_append hprefix tailTrace_7089897
  have hstable : (prefixWord ++ tailWord_7089897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089897).length < 2 ^ (prefixWord ++ tailWord_7089897).sum := by decide
  have hdescent : baseEnd_7089897 < baseStart_7089897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089900 : List Nat := [2, 2, 1, 1, 2, 2, 13]
def baseStart_7089900 : Nat := 118140960795 + 7089900 * 2 ^ 59
def prefixEnd_7089900 : Nat := 4983230072969 + 3 ^ 40 * 7089900 * 2
def baseEnd_7089900 : Nat := 44944771510023653917829

theorem tailTrace_7089900 : CollatzResearch.WordTrace tailWord_7089900 prefixEnd_7089900 44944771510023653917829 := by
  unfold tailWord_7089900
  simp only [CollatzResearch.WordTrace]
  refine ⟨129294948507255316681869577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172393264676340422242492769 129294948507255316681869577)
  ·
    refine ⟨96971211380441487511402183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129294948507255316681869577 96971211380441487511402183)
    ·
      refine ⟨145456817070662231267103275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96971211380441487511402183 145456817070662231267103275)
      ·
        refine ⟨218185225605993346900654913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145456817070662231267103275 218185225605993346900654913)
        ·
          refine ⟨163638919204495010175491185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218185225605993346900654913 163638919204495010175491185)
          ·
            refine ⟨122729189403371257631618389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163638919204495010175491185 122729189403371257631618389)
            ·
              refine ⟨44944771510023653917829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 122729189403371257631618389 44944771510023653917829)
              ·
                rfl

theorem cell23_7089900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 13].length) (baseStart_7089900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089900 prefixEnd_7089900 := by exact prefixLift 7089900
  have htrace : WordTrace (prefixWord ++ tailWord_7089900) baseStart_7089900 baseEnd_7089900 := by
    simpa [prefixWord, tailWord_7089900, baseEnd_7089900] using wordTrace_append hprefix tailTrace_7089900
  have hstable : (prefixWord ++ tailWord_7089900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089900).length < 2 ^ (prefixWord ++ tailWord_7089900).sum := by decide
  have hdescent : baseEnd_7089900 < baseStart_7089900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089911 : List Nat := [1, 1, 3, 1, 1, 1, 7, 1, 3, 2, 2]
def baseStart_7089911 : Nat := 118140960795 + 7089911 * 2 ^ 59
def prefixEnd_7089911 : Nat := 4983230072969 + 3 ^ 40 * 7089911 * 2
def baseEnd_7089911 : Nat := 3640532140599115424306599

theorem tailTrace_7089911 : CollatzResearch.WordTrace tailWord_7089911 prefixEnd_7089911 3640532140599115424306599 := by
  unfold tailWord_7089911
  simp only [CollatzResearch.WordTrace]
  refine ⟨258590298217470782242389587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172393532144980521494926391 258590298217470782242389587)
  ·
    refine ⟨387885447326206173363584381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258590298217470782242389587 387885447326206173363584381)
    ·
      refine ⟨145457042747327315011344143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387885447326206173363584381 145457042747327315011344143)
      ·
        refine ⟨218185564120990972517016215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145457042747327315011344143 218185564120990972517016215)
        ·
          refine ⟨327278346181486458775524323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218185564120990972517016215 327278346181486458775524323)
          ·
            refine ⟨490917519272229688163286485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327278346181486458775524323 490917519272229688163286485)
            ·
              refine ⟨11505879357942883316327027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 490917519272229688163286485 11505879357942883316327027)
              ·
                refine ⟨17258819036914324974490541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11505879357942883316327027 17258819036914324974490541)
                ·
                  refine ⟨6472057138842871865433953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17258819036914324974490541 6472057138842871865433953)
                  ·
                    refine ⟨4854042854132153899075465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6472057138842871865433953 4854042854132153899075465)
                    ·
                      refine ⟨3640532140599115424306599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4854042854132153899075465 3640532140599115424306599)
                      ·
                        rfl

theorem cell23_7089911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 2, 2].length) (baseStart_7089911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089911 prefixEnd_7089911 := by exact prefixLift 7089911
  have htrace : WordTrace (prefixWord ++ tailWord_7089911) baseStart_7089911 baseEnd_7089911 := by
    simpa [prefixWord, tailWord_7089911, baseEnd_7089911] using wordTrace_append hprefix tailTrace_7089911
  have hstable : (prefixWord ++ tailWord_7089911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089911).length < 2 ^ (prefixWord ++ tailWord_7089911).sum := by decide
  have hdescent : baseEnd_7089911 < baseStart_7089911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089921 : List Nat := [1, 2, 4, 1, 1, 1, 6, 1, 2, 4]
def baseStart_7089921 : Nat := 118140960795 + 7089921 * 2 ^ 59
def prefixEnd_7089921 : Nat := 4983230072969 + 3 ^ 40 * 7089921 * 2
def baseEnd_7089921 : Nat := 1213512425135220128393851

theorem tailTrace_7089921 : CollatzResearch.WordTrace tailWord_7089921 prefixEnd_7089921 1213512425135220128393851 := by
  unfold tailWord_7089921
  simp only [CollatzResearch.WordTrace]
  refine ⟨258590662947434553950253617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172393775298289702633502411 258590662947434553950253617)
  ·
    refine ⟨193942997210575915462690213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258590662947434553950253617 193942997210575915462690213)
    ·
      refine ⟨36364311976982984149254415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193942997210575915462690213 36364311976982984149254415)
      ·
        refine ⟨54546467965474476223881623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36364311976982984149254415 54546467965474476223881623)
        ·
          refine ⟨81819701948211714335822435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54546467965474476223881623 81819701948211714335822435)
          ·
            refine ⟨122729552922317571503733653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81819701948211714335822435 122729552922317571503733653)
            ·
              refine ⟨5752947793233636164237515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122729552922317571503733653 5752947793233636164237515)
              ·
                refine ⟨8629421689850454246356273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5752947793233636164237515 8629421689850454246356273)
                ·
                  refine ⟨6472066267387840684767205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8629421689850454246356273 6472066267387840684767205)
                  ·
                    refine ⟨1213512425135220128393851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6472066267387840684767205 1213512425135220128393851)
                    ·
                      rfl

theorem cell23_7089921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_7089921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089921 prefixEnd_7089921 := by exact prefixLift 7089921
  have htrace : WordTrace (prefixWord ++ tailWord_7089921) baseStart_7089921 baseEnd_7089921 := by
    simpa [prefixWord, tailWord_7089921, baseEnd_7089921] using wordTrace_append hprefix tailTrace_7089921
  have hstable : (prefixWord ++ tailWord_7089921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089921).length < 2 ^ (prefixWord ++ tailWord_7089921).sum := by decide
  have hdescent : baseEnd_7089921 < baseStart_7089921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7089944 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 6, 1, 3]
def baseStart_7089944 : Nat := 118140960795 + 7089944 * 2 ^ 59
def prefixEnd_7089944 : Nat := 4983230072969 + 3 ^ 40 * 7089944 * 2
def baseEnd_7089944 : Nat := 3640549085460713795193947

theorem tailTrace_7089944 : CollatzResearch.WordTrace tailWord_7089944 prefixEnd_7089944 3640549085460713795193947 := by
  unfold tailWord_7089944
  simp only [CollatzResearch.WordTrace]
  refine ⟨129295750913175614439170443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172394334550900819252227257 129295750913175614439170443)
  ·
    refine ⟨193943626369763421658755665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129295750913175614439170443 193943626369763421658755665)
    ·
      refine ⟨145457719777322566244066749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193943626369763421658755665 145457719777322566244066749)
      ·
        refine ⟨54546644916495962341525031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145457719777322566244066749 54546644916495962341525031)
        ·
          refine ⟨81819967374743943512287547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54546644916495962341525031 81819967374743943512287547)
          ·
            refine ⟨122729951062115915268431321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81819967374743943512287547 122729951062115915268431321)
            ·
              refine ⟨92047463296586936451323491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122729951062115915268431321 92047463296586936451323491)
              ·
                refine ⟨138071194944880404676985237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92047463296586936451323491 138071194944880404676985237)
                ·
                  refine ⟨6472087263041268969233683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138071194944880404676985237 6472087263041268969233683)
                  ·
                    refine ⟨9708130894561903453850525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6472087263041268969233683 9708130894561903453850525)
                    ·
                      refine ⟨3640549085460713795193947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9708130894561903453850525 3640549085460713795193947)
                      ·
                        rfl

theorem cell23_7089944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_7089944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7089944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7089944 prefixEnd_7089944 := by exact prefixLift 7089944
  have htrace : WordTrace (prefixWord ++ tailWord_7089944) baseStart_7089944 baseEnd_7089944 := by
    simpa [prefixWord, tailWord_7089944, baseEnd_7089944] using wordTrace_append hprefix tailTrace_7089944
  have hstable : (prefixWord ++ tailWord_7089944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7089944).length < 2 ^ (prefixWord ++ tailWord_7089944).sum := by decide
  have hdescent : baseEnd_7089944 < baseStart_7089944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7089944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090001 : List Nat := [1, 2, 2, 1, 5, 1, 2, 2, 1, 4, 2]
def baseStart_7090001 : Nat := 118140960795 + 7090001 * 2 ^ 59
def prefixEnd_7090001 : Nat := 4983230072969 + 3 ^ 40 * 7090001 * 2
def baseEnd_7090001 : Nat := 3640578353858020072181185

theorem tailTrace_7090001 : CollatzResearch.WordTrace tailWord_7090001 prefixEnd_7090001 3640578353858020072181185 := by
  unfold tailWord_7090001
  simp only [CollatzResearch.WordTrace]
  refine ⟨258593580787144727613165857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172395720524763151742110571 258593580787144727613165857)
  ·
    refine ⟨193945185590358545709874393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258593580787144727613165857 193945185590358545709874393)
    ·
      refine ⟨145458889192768909282405795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193945185590358545709874393 145458889192768909282405795)
      ·
        refine ⟨218188333789153363923608693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145458889192768909282405795 218188333789153363923608693)
        ·
          refine ⟨20455156292733127867838315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 218188333789153363923608693 20455156292733127867838315)
          ·
            refine ⟨30682734439099691801757473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20455156292733127867838315 30682734439099691801757473)
            ·
              refine ⟨23012050829324768851318105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30682734439099691801757473 23012050829324768851318105)
              ·
                refine ⟨17259038121993576638488579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23012050829324768851318105 17259038121993576638488579)
                ·
                  refine ⟨25888557182990364957732869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17259038121993576638488579 25888557182990364957732869)
                  ·
                    refine ⟨4854104471810693429574913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25888557182990364957732869 4854104471810693429574913)
                    ·
                      refine ⟨3640578353858020072181185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4854104471810693429574913 3640578353858020072181185)
                      ·
                        rfl

theorem cell23_7090001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 4, 2].length) (baseStart_7090001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090001 prefixEnd_7090001 := by exact prefixLift 7090001
  have htrace : WordTrace (prefixWord ++ tailWord_7090001) baseStart_7090001 baseEnd_7090001 := by
    simpa [prefixWord, tailWord_7090001, baseEnd_7090001] using wordTrace_append hprefix tailTrace_7090001
  have hstable : (prefixWord ++ tailWord_7090001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090001).length < 2 ^ (prefixWord ++ tailWord_7090001).sum := by decide
  have hdescent : baseEnd_7090001 < baseStart_7090001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090005 : List Nat := [1, 3, 2, 2, 2, 4, 2, 1, 1, 3, 2]
def baseStart_7090005 : Nat := 118140960795 + 7090005 * 2 ^ 59
def prefixEnd_7090005 : Nat := 4983230072969 + 3 ^ 40 * 7090005 * 2
def baseEnd_7090005 : Nat := 3640580407780638056531167

theorem tailTrace_7090005 : CollatzResearch.WordTrace tailWord_7090005 prefixEnd_7090005 3640580407780638056531167 := by
  unfold tailWord_7090005
  simp only [CollatzResearch.WordTrace]
  refine ⟨258593726679130236296311469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172395817786086824197540979 258593726679130236296311469)
  ·
    refine ⟨96972647504673838611116801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258593726679130236296311469 96972647504673838611116801)
    ·
      refine ⟨72729485628505378958337601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96972647504673838611116801 72729485628505378958337601)
      ·
        refine ⟨54547114221379034218753201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72729485628505378958337601 54547114221379034218753201)
        ·
          refine ⟨40910335666034275664064901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54547114221379034218753201 40910335666034275664064901)
          ·
            refine ⟨7670687937381426687012169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40910335666034275664064901 7670687937381426687012169)
            ·
              refine ⟨5753015953036070015259127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7670687937381426687012169 5753015953036070015259127)
              ·
                refine ⟨8629523929554105022888691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5753015953036070015259127 8629523929554105022888691)
                ·
                  refine ⟨12944285894331157534333037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8629523929554105022888691 12944285894331157534333037)
                  ·
                    refine ⟨4854107210374184075374889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12944285894331157534333037 4854107210374184075374889)
                    ·
                      refine ⟨3640580407780638056531167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4854107210374184075374889 3640580407780638056531167)
                      ·
                        rfl

theorem cell23_7090005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_7090005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090005 prefixEnd_7090005 := by exact prefixLift 7090005
  have htrace : WordTrace (prefixWord ++ tailWord_7090005) baseStart_7090005 baseEnd_7090005 := by
    simpa [prefixWord, tailWord_7090005, baseEnd_7090005] using wordTrace_append hprefix tailTrace_7090005
  have hstable : (prefixWord ++ tailWord_7090005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090005).length < 2 ^ (prefixWord ++ tailWord_7090005).sum := by decide
  have hdescent : baseEnd_7090005 < baseStart_7090005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090012 : List Nat := [2, 2, 4, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_7090012 : Nat := 118140960795 + 7090012 * 2 ^ 59
def prefixEnd_7090012 : Nat := 4983230072969 + 3 ^ 40 * 7090012 * 2
def baseEnd_7090012 : Nat := 3640584002145219529143635

theorem tailTrace_7090012 : CollatzResearch.WordTrace tailWord_7090012 prefixEnd_7090012 3640584002145219529143635 := by
  unfold tailWord_7090012
  simp only [CollatzResearch.WordTrace]
  refine ⟨129296990995052438245908145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172395987993403250994544193 129296990995052438245908145)
  ·
    refine ⟨96972743246289328684431109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129296990995052438245908145 96972743246289328684431109)
    ·
      refine ⟨18182389358679249128330833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96972743246289328684431109 18182389358679249128330833)
      ·
        refine ⟨13636792019009436846248125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18182389358679249128330833 13636792019009436846248125)
        ·
          refine ⟨5113797007128538817343047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13636792019009436846248125 5113797007128538817343047)
          ·
            refine ⟨7670695510692808226014571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5113797007128538817343047 7670695510692808226014571)
            ·
              refine ⟨11506043266039212339021857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7670695510692808226014571 11506043266039212339021857)
              ·
                refine ⟨8629532449529409254266393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11506043266039212339021857 8629532449529409254266393)
                ·
                  refine ⟨6472149337147056940699795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8629532449529409254266393 6472149337147056940699795)
                  ·
                    refine ⟨9708224005720585411049693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6472149337147056940699795 9708224005720585411049693)
                    ·
                      refine ⟨3640584002145219529143635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9708224005720585411049693 3640584002145219529143635)
                      ·
                        rfl

theorem cell23_7090012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_7090012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090012 prefixEnd_7090012 := by exact prefixLift 7090012
  have htrace : WordTrace (prefixWord ++ tailWord_7090012) baseStart_7090012 baseEnd_7090012 := by
    simpa [prefixWord, tailWord_7090012, baseEnd_7090012] using wordTrace_append hprefix tailTrace_7090012
  have hstable : (prefixWord ++ tailWord_7090012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090012).length < 2 ^ (prefixWord ++ tailWord_7090012).sum := by decide
  have hdescent : baseEnd_7090012 < baseStart_7090012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090024 : List Nat := [2, 1, 4, 2, 1, 1, 4, 1, 7]
def baseStart_7090024 : Nat := 118140960795 + 7090024 * 2 ^ 59
def prefixEnd_7090024 : Nat := 4983230072969 + 3 ^ 40 * 7090024 * 2
def baseEnd_7090024 : Nat := 404510018212563720243731

theorem tailTrace_7090024 : CollatzResearch.WordTrace tailWord_7090024 prefixEnd_7090024 404510018212563720243731 := by
  unfold tailWord_7090024
  simp only [CollatzResearch.WordTrace]
  refine ⟨129297209833030701270626563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172396279777374268360835417 129297209833030701270626563)
  ·
    refine ⟨193945814749546051905939845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129297209833030701270626563 193945814749546051905939845)
    ·
      refine ⟨36364840265539884732363721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193945814749546051905939845 36364840265539884732363721)
      ·
        refine ⟨27273630199154913549272791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36364840265539884732363721 27273630199154913549272791)
        ·
          refine ⟨40910445298732370323909187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27273630199154913549272791 40910445298732370323909187)
          ·
            refine ⟨61365667948098555485863781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40910445298732370323909187 61365667948098555485863781)
            ·
              refine ⟨11506062740268479153599459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61365667948098555485863781 11506062740268479153599459)
              ·
                refine ⟨17259094110402718730399189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11506062740268479153599459 17259094110402718730399189)
                ·
                  refine ⟨404510018212563720243731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17259094110402718730399189 404510018212563720243731)
                  ·
                    rfl

theorem cell23_7090024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 7].length) (baseStart_7090024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090024 prefixEnd_7090024 := by exact prefixLift 7090024
  have htrace : WordTrace (prefixWord ++ tailWord_7090024) baseStart_7090024 baseEnd_7090024 := by
    simpa [prefixWord, tailWord_7090024, baseEnd_7090024] using wordTrace_append hprefix tailTrace_7090024
  have hstable : (prefixWord ++ tailWord_7090024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090024).length < 2 ^ (prefixWord ++ tailWord_7090024).sum := by decide
  have hdescent : baseEnd_7090024 < baseStart_7090024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090047 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 5]
def baseStart_7090047 : Nat := 118140960795 + 7090047 * 2 ^ 59
def prefixEnd_7090047 : Nat := 4983230072969 + 3 ^ 40 * 7090047 * 2
def baseEnd_7090047 : Nat := 3640601973968126892205973

theorem tailTrace_7090047 : CollatzResearch.WordTrace tailWord_7090047 prefixEnd_7090047 3640601973968126892205973 := by
  unfold tailWord_7090047
  simp only [CollatzResearch.WordTrace]
  refine ⟨258595258544978077469340395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172396839029985384979560263 258595258544978077469340395)
  ·
    refine ⟨387892887817467116204010593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258595258544978077469340395 387892887817467116204010593)
    ·
      refine ⟨290919665863100337153007945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387892887817467116204010593 290919665863100337153007945)
      ·
        refine ⟨218189749397325252864755959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290919665863100337153007945 218189749397325252864755959)
        ·
          refine ⟨327284624095987879297133939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218189749397325252864755959 327284624095987879297133939)
          ·
            refine ⟨490926936143981818945700909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327284624095987879297133939 490926936143981818945700909)
            ·
              refine ⟨184097601053993182104637841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 490926936143981818945700909 184097601053993182104637841)
              ·
                refine ⟨138073200790494886578478381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184097601053993182104637841 138073200790494886578478381)
                ·
                  refine ⟨51777450296435582466929393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138073200790494886578478381 51777450296435582466929393)
                  ·
                    refine ⟨38833087722326686850197045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51777450296435582466929393 38833087722326686850197045)
                    ·
                      refine ⟨3640601973968126892205973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38833087722326686850197045 3640601973968126892205973)
                      ·
                        rfl

theorem cell23_7090047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_7090047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090047 prefixEnd_7090047 := by exact prefixLift 7090047
  have htrace : WordTrace (prefixWord ++ tailWord_7090047) baseStart_7090047 baseEnd_7090047 := by
    simpa [prefixWord, tailWord_7090047, baseEnd_7090047] using wordTrace_append hprefix tailTrace_7090047
  have hstable : (prefixWord ++ tailWord_7090047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090047).length < 2 ^ (prefixWord ++ tailWord_7090047).sum := by decide
  have hdescent : baseEnd_7090047 < baseStart_7090047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090081 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 1, 2, 5]
def baseStart_7090081 : Nat := 118140960795 + 7090081 * 2 ^ 59
def prefixEnd_7090081 : Nat := 4983230072969 + 3 ^ 40 * 7090081 * 2
def baseEnd_7090081 : Nat := 3640619432310379759180817

theorem tailTrace_7090081 : CollatzResearch.WordTrace tailWord_7090081 prefixEnd_7090081 3640619432310379759180817 := by
  unfold tailWord_7090081
  simp only [CollatzResearch.WordTrace]
  refine ⟨258596498626854901276078097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172397665751236600850718731 258596498626854901276078097)
  ·
    refine ⟨193947373970141175957058573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258596498626854901276078097 193947373970141175957058573)
    ·
      refine ⟨72730265238802940983896965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193947373970141175957058573 72730265238802940983896965)
      ·
        refine ⟨13636924732275551434480681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72730265238802940983896965 13636924732275551434480681)
        ·
          refine ⟨10227693549206663575860511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13636924732275551434480681 10227693549206663575860511)
          ·
            refine ⟨15341540323809995363790767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10227693549206663575860511 15341540323809995363790767)
            ·
              refine ⟨23012310485714993045686151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15341540323809995363790767 23012310485714993045686151)
              ·
                refine ⟨34518465728572489568529227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23012310485714993045686151 34518465728572489568529227)
                ·
                  refine ⟨51777698592858734352793841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34518465728572489568529227 51777698592858734352793841)
                  ·
                    refine ⟨38833273944644050764595381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51777698592858734352793841 38833273944644050764595381)
                    ·
                      refine ⟨3640619432310379759180817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38833273944644050764595381 3640619432310379759180817)
                      ·
                        rfl

theorem cell23_7090081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_7090081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090081 prefixEnd_7090081 := by exact prefixLift 7090081
  have htrace : WordTrace (prefixWord ++ tailWord_7090081) baseStart_7090081 baseEnd_7090081 := by
    simpa [prefixWord, tailWord_7090081, baseEnd_7090081] using wordTrace_append hprefix tailTrace_7090081
  have hstable : (prefixWord ++ tailWord_7090081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090081).length < 2 ^ (prefixWord ++ tailWord_7090081).sum := by decide
  have hdescent : baseEnd_7090081 < baseStart_7090081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090111 : List Nat := [1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 3]
def baseStart_7090111 : Nat := 118140960795 + 7090111 * 2 ^ 59
def prefixEnd_7090111 : Nat := 4983230072969 + 3 ^ 40 * 7090111 * 2
def baseEnd_7090111 : Nat := 3640634836730014641805679

theorem tailTrace_7090111 : CollatzResearch.WordTrace tailWord_7090111 prefixEnd_7090111 3640634836730014641805679 := by
  unfold tailWord_7090111
  simp only [CollatzResearch.WordTrace]
  refine ⟨258597592816746216399670187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172398395211164144266446791 258597592816746216399670187)
  ·
    refine ⟨387896389225119324599505281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258597592816746216399670187 387896389225119324599505281)
    ·
      refine ⟨290922291918839493449628961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387896389225119324599505281 290922291918839493449628961)
      ·
        refine ⟨218191718939129620087221721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290922291918839493449628961 218191718939129620087221721)
        ·
          refine ⟨163643789204347215065416291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218191718939129620087221721 163643789204347215065416291)
          ·
            refine ⟨245465683806520822598124437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163643789204347215065416291 245465683806520822598124437)
            ·
              refine ⟨11506203928430663559287083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 245465683806520822598124437 11506203928430663559287083)
              ·
                refine ⟨17259305892645995338930625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11506203928430663559287083 17259305892645995338930625)
                ·
                  refine ⟨12944479419484496504197969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17259305892645995338930625 12944479419484496504197969)
                  ·
                    refine ⟨9708359564613372378148477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12944479419484496504197969 9708359564613372378148477)
                    ·
                      refine ⟨3640634836730014641805679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9708359564613372378148477 3640634836730014641805679)
                      ·
                        rfl

theorem cell23_7090111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_7090111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090111 prefixEnd_7090111 := by exact prefixLift 7090111
  have htrace : WordTrace (prefixWord ++ tailWord_7090111) baseStart_7090111 baseEnd_7090111 := by
    simpa [prefixWord, tailWord_7090111, baseEnd_7090111] using wordTrace_append hprefix tailTrace_7090111
  have hstable : (prefixWord ++ tailWord_7090111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090111).length < 2 ^ (prefixWord ++ tailWord_7090111).sum := by decide
  have hdescent : baseEnd_7090111 < baseStart_7090111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090154 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_7090154 : Nat := 118140960795 + 7090154 * 2 ^ 59
def prefixEnd_7090154 : Nat := 4983230072969 + 3 ^ 40 * 7090154 * 2
def baseEnd_7090154 : Nat := 3640656916398157973567981

theorem tailTrace_7090154 : CollatzResearch.WordTrace tailWord_7090154 prefixEnd_7090154 3640656916398157973567981 := by
  unfold tailWord_7090154
  simp only [CollatzResearch.WordTrace]
  refine ⟨64649790288897608685871379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172399440770393623162323677 64649790288897608685871379)
  ·
    refine ⟨96974685433346413028807069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64649790288897608685871379 96974685433346413028807069)
    ·
      refine ⟨36365507037504904885802651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96974685433346413028807069 36365507037504904885802651)
      ·
        refine ⟨54548260556257357328703977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36365507037504904885802651 54548260556257357328703977)
        ·
          refine ⟨40911195417193017996527983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54548260556257357328703977 40911195417193017996527983)
          ·
            refine ⟨61366793125789526994791975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40911195417193017996527983 61366793125789526994791975)
            ·
              refine ⟨92050189688684290492187963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61366793125789526994791975 92050189688684290492187963)
              ·
                refine ⟨138075284533026435738281945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92050189688684290492187963 138075284533026435738281945)
                ·
                  refine ⟨103556463399769826803711459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138075284533026435738281945 103556463399769826803711459)
                  ·
                    refine ⟨155334695099654740205567189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103556463399769826803711459 155334695099654740205567189)
                    ·
                      refine ⟨3640656916398157973567981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155334695099654740205567189 3640656916398157973567981)
                      ·
                        rfl

theorem cell23_7090154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_7090154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090154 prefixEnd_7090154 := by exact prefixLift 7090154
  have htrace : WordTrace (prefixWord ++ tailWord_7090154) baseStart_7090154 baseEnd_7090154 := by
    simpa [prefixWord, tailWord_7090154, baseEnd_7090154] using wordTrace_append hprefix tailTrace_7090154
  have hstable : (prefixWord ++ tailWord_7090154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090154).length < 2 ^ (prefixWord ++ tailWord_7090154).sum := by decide
  have hdescent : baseEnd_7090154 < baseStart_7090154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090158 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_7090158 : Nat := 118140960795 + 7090158 * 2 ^ 59
def prefixEnd_7090158 : Nat := 4983230072969 + 3 ^ 40 * 7090158 * 2
def baseEnd_7090158 : Nat := 3640658970320775957917963

theorem tailTrace_7090158 : CollatzResearch.WordTrace tailWord_7090158 prefixEnd_7090158 3640658970320775957917963 := by
  unfold tailWord_7090158
  simp only [CollatzResearch.WordTrace]
  refine ⟨32324913380946992928328891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172399538031717295617754085 32324913380946992928328891)
  ·
    refine ⟨48487370071420489392493337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32324913380946992928328891 48487370071420489392493337)
    ·
      refine ⟨36365527553565367044370003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48487370071420489392493337 36365527553565367044370003)
      ·
        refine ⟨54548291330348050566555005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36365527553565367044370003 54548291330348050566555005)
        ·
          refine ⟨20455609248880518962458127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54548291330348050566555005 20455609248880518962458127)
          ·
            refine ⟨30683413873320778443687191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20455609248880518962458127 30683413873320778443687191)
            ·
              refine ⟨46025120809981167665530787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30683413873320778443687191 46025120809981167665530787)
              ·
                refine ⟨69037681214971751498296181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46025120809981167665530787 69037681214971751498296181)
                ·
                  refine ⟨6472282613903601702965267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69037681214971751498296181 6472282613903601702965267)
                  ·
                    refine ⟨9708423920855402554447901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6472282613903601702965267 9708423920855402554447901)
                    ·
                      refine ⟨3640658970320775957917963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9708423920855402554447901 3640658970320775957917963)
                      ·
                        rfl

theorem cell23_7090158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_7090158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090158 prefixEnd_7090158 := by exact prefixLift 7090158
  have htrace : WordTrace (prefixWord ++ tailWord_7090158) baseStart_7090158 baseEnd_7090158 := by
    simpa [prefixWord, tailWord_7090158, baseEnd_7090158] using wordTrace_append hprefix tailTrace_7090158
  have hstable : (prefixWord ++ tailWord_7090158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090158).length < 2 ^ (prefixWord ++ tailWord_7090158).sum := by decide
  have hdescent : baseEnd_7090158 < baseStart_7090158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090168 : List Nat := [2, 1, 2, 1, 1, 3, 5, 1, 2, 3, 2]
def baseStart_7090168 : Nat := 118140960795 + 7090168 * 2 ^ 59
def prefixEnd_7090168 : Nat := 4983230072969 + 3 ^ 40 * 7090168 * 2
def baseEnd_7090168 : Nat := 3640664105127320918792917

theorem tailTrace_7090168 : CollatzResearch.WordTrace tailWord_7090168 prefixEnd_7090168 3640664105127320918792917 := by
  unfold tailWord_7090168
  simp only [CollatzResearch.WordTrace]
  refine ⟨129299835888769857567247579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172399781185026476756330105 129299835888769857567247579)
  ·
    refine ⟨193949753833154786350871369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129299835888769857567247579 193949753833154786350871369)
    ·
      refine ⟨145462315374866089763153527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193949753833154786350871369 145462315374866089763153527)
      ·
        refine ⟨218193473062299134644730291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145462315374866089763153527 218193473062299134644730291)
        ·
          refine ⟨327290209593448701967095437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218193473062299134644730291 327290209593448701967095437)
          ·
            refine ⟨122733828597543263237660789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327290209593448701967095437 122733828597543263237660789)
            ·
              refine ⟨11506296431019680928530699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122733828597543263237660789 11506296431019680928530699)
              ·
                refine ⟨17259444646529521392796049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11506296431019680928530699 17259444646529521392796049)
                ·
                  refine ⟨12944583484897141044597037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17259444646529521392796049 12944583484897141044597037)
                  ·
                    refine ⟨4854218806836427891723889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12944583484897141044597037 4854218806836427891723889)
                    ·
                      refine ⟨3640664105127320918792917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4854218806836427891723889 3640664105127320918792917)
                      ·
                        rfl

theorem cell23_7090168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 2, 3, 2].length) (baseStart_7090168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090168 prefixEnd_7090168 := by exact prefixLift 7090168
  have htrace : WordTrace (prefixWord ++ tailWord_7090168) baseStart_7090168 baseEnd_7090168 := by
    simpa [prefixWord, tailWord_7090168, baseEnd_7090168] using wordTrace_append hprefix tailTrace_7090168
  have hstable : (prefixWord ++ tailWord_7090168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090168).length < 2 ^ (prefixWord ++ tailWord_7090168).sum := by decide
  have hdescent : baseEnd_7090168 < baseStart_7090168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090182 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_7090182 : Nat := 118140960795 + 7090182 * 2 ^ 59
def prefixEnd_7090182 : Nat := 4983230072969 + 3 ^ 40 * 7090182 * 2
def baseEnd_7090182 : Nat := 404519032650720429335317

theorem tailTrace_7090182 : CollatzResearch.WordTrace tailWord_7090182 prefixEnd_7090182 404519032650720429335317 := by
  unfold tailWord_7090182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8081255699984031110172025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 172400121599659330350336533 8081255699984031110172025)
  ·
    refine ⟨6060941774988023332629019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8081255699984031110172025 6060941774988023332629019)
    ·
      refine ⟨9091412662482034998943529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6060941774988023332629019 9091412662482034998943529)
      ·
        refine ⟨6818559496861526249207647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9091412662482034998943529 6818559496861526249207647)
        ·
          refine ⟨10227839245292289373811471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6818559496861526249207647 10227839245292289373811471)
          ·
            refine ⟨15341758867938434060717207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10227839245292289373811471 15341758867938434060717207)
            ·
              refine ⟨23012638301907651091075811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15341758867938434060717207 23012638301907651091075811)
              ·
                refine ⟨34518957452861476636613717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23012638301907651091075811 34518957452861476636613717)
                ·
                  refine ⟨404519032650720429335317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34518957452861476636613717 404519032650720429335317)
                  ·
                    rfl

theorem cell23_7090182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_7090182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090182 prefixEnd_7090182 := by exact prefixLift 7090182
  have htrace : WordTrace (prefixWord ++ tailWord_7090182) baseStart_7090182 baseEnd_7090182 := by
    simpa [prefixWord, tailWord_7090182, baseEnd_7090182] using wordTrace_append hprefix tailTrace_7090182
  have hstable : (prefixWord ++ tailWord_7090182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090182).length < 2 ^ (prefixWord ++ tailWord_7090182).sum := by decide
  have hdescent : baseEnd_7090182 < baseStart_7090182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090231 : List Nat := [1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 3]
def baseStart_7090231 : Nat := 118140960795 + 7090231 * 2 ^ 59
def prefixEnd_7090231 : Nat := 4983230072969 + 3 ^ 40 * 7090231 * 2
def baseEnd_7090231 : Nat := 3640696454408554172305127

theorem tailTrace_7090231 : CollatzResearch.WordTrace tailWord_7090231 prefixEnd_7090231 3640696454408554172305127 := by
  unfold tailWord_7090231
  simp only [CollatzResearch.WordTrace]
  refine ⟨258601969576311476894038547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172401313050874317929359031 258601969576311476894038547)
  ·
    refine ⟨387902954364467215341057821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258601969576311476894038547 387902954364467215341057821)
    ·
      refine ⟨145463607886675205752896683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387902954364467215341057821 145463607886675205752896683)
      ·
        refine ⟨218195411830012808629345025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145463607886675205752896683 218195411830012808629345025)
        ·
          refine ⟨163646558872509606472008769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218195411830012808629345025 163646558872509606472008769)
          ·
            refine ⟨122734919154382204854006577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163646558872509606472008769 122734919154382204854006577)
            ·
              refine ⟨92051189365786653640504933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122734919154382204854006577 92051189365786653640504933)
              ·
                refine ⟨17259598006084997557594675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92051189365786653640504933 17259598006084997557594675)
                ·
                  refine ⟨25889397009127496336392013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17259598006084997557594675 25889397009127496336392013)
                  ·
                    refine ⟨9708523878422811126147005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25889397009127496336392013 9708523878422811126147005)
                    ·
                      refine ⟨3640696454408554172305127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9708523878422811126147005 3640696454408554172305127)
                      ·
                        rfl

theorem cell23_7090231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_7090231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090231 prefixEnd_7090231 := by exact prefixLift 7090231
  have htrace : WordTrace (prefixWord ++ tailWord_7090231) baseStart_7090231 baseEnd_7090231 := by
    simpa [prefixWord, tailWord_7090231, baseEnd_7090231] using wordTrace_append hprefix tailTrace_7090231
  have hstable : (prefixWord ++ tailWord_7090231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090231).length < 2 ^ (prefixWord ++ tailWord_7090231).sum := by decide
  have hdescent : baseEnd_7090231 < baseStart_7090231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090234 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 1, 9]
def baseStart_7090234 : Nat := 118140960795 + 7090234 * 2 ^ 59
def prefixEnd_7090234 : Nat := 4983230072969 + 3 ^ 40 * 7090234 * 2
def baseEnd_7090234 : Nat := 1213565998283505886855871

theorem tailTrace_7090234 : CollatzResearch.WordTrace tailWord_7090234 prefixEnd_7090234 1213565998283505886855871 := by
  unfold tailWord_7090234
  simp only [CollatzResearch.WordTrace]
  refine ⟨64650519748825152101599439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172401385996867072270931837 64650519748825152101599439)
  ·
    refine ⟨96975779623237728152399159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64650519748825152101599439 96975779623237728152399159)
    ·
      refine ⟨145463669434856592228598739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96975779623237728152399159 145463669434856592228598739)
      ·
        refine ⟨218195504152284888342898109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145463669434856592228598739 218195504152284888342898109)
        ·
          refine ⟨81823314057106833128586791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218195504152284888342898109 81823314057106833128586791)
          ·
            refine ⟨122734971085660249692880187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81823314057106833128586791 122734971085660249692880187)
            ·
              refine ⟨184102456628490374539320281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122734971085660249692880187 184102456628490374539320281)
              ·
                refine ⟨138076842471367780904490211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184102456628490374539320281 138076842471367780904490211)
                ·
                  refine ⟨207115263707051671356735317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138076842471367780904490211 207115263707051671356735317)
                  ·
                    refine ⟨1213565998283505886855871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 207115263707051671356735317 1213565998283505886855871)
                    ·
                      rfl

theorem cell23_7090234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_7090234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090234 prefixEnd_7090234 := by exact prefixLift 7090234
  have htrace : WordTrace (prefixWord ++ tailWord_7090234) baseStart_7090234 baseEnd_7090234 := by
    simpa [prefixWord, tailWord_7090234, baseEnd_7090234] using wordTrace_append hprefix tailTrace_7090234
  have hstable : (prefixWord ++ tailWord_7090234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090234).length < 2 ^ (prefixWord ++ tailWord_7090234).sum := by decide
  have hdescent : baseEnd_7090234 < baseStart_7090234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090238 : List Nat := [4, 2, 1, 3, 2, 2, 9]
def baseStart_7090238 : Nat := 118140960795 + 7090238 * 2 ^ 59
def prefixEnd_7090238 : Nat := 4983230072969 + 3 ^ 40 * 7090238 * 2
def baseEnd_7090238 : Nat := 44946914182384390677995

theorem tailTrace_7090238 : CollatzResearch.WordTrace tailWord_7090238 prefixEnd_7090238 44946914182384390677995 := by
  unfold tailWord_7090238
  simp only [CollatzResearch.WordTrace]
  refine ⟨32325278110910764636192921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172401483258190744726362245 32325278110910764636192921)
  ·
    refine ⟨24243958583183073477144691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32325278110910764636192921 24243958583183073477144691)
    ·
      refine ⟨36365937874774610215717037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24243958583183073477144691 36365937874774610215717037)
      ·
        refine ⟨13637226703040478830893889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36365937874774610215717037 13637226703040478830893889)
        ·
          refine ⟨10227920027280359123170417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13637226703040478830893889 10227920027280359123170417)
          ·
            refine ⟨7670940020460269342377813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10227920027280359123170417 7670940020460269342377813)
            ·
              refine ⟨44946914182384390677995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7670940020460269342377813 44946914182384390677995)
              ·
                rfl

theorem cell23_7090238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 9].length) (baseStart_7090238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090238 prefixEnd_7090238 := by exact prefixLift 7090238
  have htrace : WordTrace (prefixWord ++ tailWord_7090238) baseStart_7090238 baseEnd_7090238 := by
    simpa [prefixWord, tailWord_7090238, baseEnd_7090238] using wordTrace_append hprefix tailTrace_7090238
  have hstable : (prefixWord ++ tailWord_7090238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090238).length < 2 ^ (prefixWord ++ tailWord_7090238).sum := by decide
  have hdescent : baseEnd_7090238 < baseStart_7090238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090275 : List Nat := [1, 1, 1, 5, 1, 1, 5, 2, 1, 3, 2]
def baseStart_7090275 : Nat := 118140960795 + 7090275 * 2 ^ 59
def prefixEnd_7090275 : Nat := 4983230072969 + 3 ^ 40 * 7090275 * 2
def baseEnd_7090275 : Nat := 3640719047557352000154925

theorem tailTrace_7090275 : CollatzResearch.WordTrace tailWord_7090275 prefixEnd_7090275 3640719047557352000154925 := by
  unfold tailWord_7090275
  simp only [CollatzResearch.WordTrace]
  refine ⟨258603574388152072408640279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172402382925434714939093519 258603574388152072408640279)
  ·
    refine ⟨387905361582228108612960419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258603574388152072408640279 387905361582228108612960419)
    ·
      refine ⟨581858042373342162919440629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387905361582228108612960419 581858042373342162919440629)
      ·
        refine ⟨54549191472500827773697559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 581858042373342162919440629 54549191472500827773697559)
        ·
          refine ⟨81823787208751241660546339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54549191472500827773697559 81823787208751241660546339)
          ·
            refine ⟨122735680813126862490819509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81823787208751241660546339 122735680813126862490819509)
            ·
              refine ⟨11506470076230643358514329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122735680813126862490819509 11506470076230643358514329)
              ·
                refine ⟨8629852557172982518885747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11506470076230643358514329 8629852557172982518885747)
                ·
                  refine ⟨12944778835759473778328621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8629852557172982518885747 12944778835759473778328621)
                  ·
                    refine ⟨4854292063409802666873233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12944778835759473778328621 4854292063409802666873233)
                    ·
                      refine ⟨3640719047557352000154925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4854292063409802666873233 3640719047557352000154925)
                      ·
                        rfl

theorem cell23_7090275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_7090275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090275 prefixEnd_7090275 := by exact prefixLift 7090275
  have htrace : WordTrace (prefixWord ++ tailWord_7090275) baseStart_7090275 baseEnd_7090275 := by
    simpa [prefixWord, tailWord_7090275, baseEnd_7090275] using wordTrace_append hprefix tailTrace_7090275
  have hstable : (prefixWord ++ tailWord_7090275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090275).length < 2 ^ (prefixWord ++ tailWord_7090275).sum := by decide
  have hdescent : baseEnd_7090275 < baseStart_7090275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090288 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 3, 4, 2]
def baseStart_7090288 : Nat := 118140960795 + 7090288 * 2 ^ 59
def prefixEnd_7090288 : Nat := 4983230072969 + 3 ^ 40 * 7090288 * 2
def baseEnd_7090288 : Nat := 3640725722805860449292365

theorem tailTrace_7090288 : CollatzResearch.WordTrace tailWord_7090288 prefixEnd_7090288 3640725722805860449292365 := by
  unfold tailWord_7090288
  simp only [CollatzResearch.WordTrace]
  refine ⟨129302024268552487814431759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172402699024736650419242345 129302024268552487814431759)
  ·
    refine ⟨193953036402828731721647639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129302024268552487814431759 193953036402828731721647639)
    ·
      refine ⟨290929554604243097582471459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193953036402828731721647639 290929554604243097582471459)
      ·
        refine ⟨436394331906364646373707189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290929554604243097582471459 436394331906364646373707189)
        ·
          refine ⟨40911968616221685597535049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 436394331906364646373707189 40911968616221685597535049)
          ·
            refine ⟨30683976462166264198151287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40911968616221685597535049 30683976462166264198151287)
            ·
              refine ⟨46025964693249396297226931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30683976462166264198151287 46025964693249396297226931)
              ·
                refine ⟨69038947039874094445840397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46025964693249396297226931 69038947039874094445840397)
                ·
                  refine ⟨25889605139952785417190149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69038947039874094445840397 25889605139952785417190149)
                  ·
                    refine ⟨4854300963741147265723153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25889605139952785417190149 4854300963741147265723153)
                    ·
                      refine ⟨3640725722805860449292365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4854300963741147265723153 3640725722805860449292365)
                      ·
                        rfl

theorem cell23_7090288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 3, 4, 2].length) (baseStart_7090288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090288 prefixEnd_7090288 := by exact prefixLift 7090288
  have htrace : WordTrace (prefixWord ++ tailWord_7090288) baseStart_7090288 baseEnd_7090288 := by
    simpa [prefixWord, tailWord_7090288, baseEnd_7090288] using wordTrace_append hprefix tailTrace_7090288
  have hstable : (prefixWord ++ tailWord_7090288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090288).length < 2 ^ (prefixWord ++ tailWord_7090288).sum := by decide
  have hdescent : baseEnd_7090288 < baseStart_7090288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090322 : List Nat := [3, 2, 3, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_7090322 : Nat := 118140960795 + 7090322 * 2 ^ 59
def prefixEnd_7090322 : Nat := 4983230072969 + 3 ^ 40 * 7090322 * 2
def baseEnd_7090322 : Nat := 3640743181148113316267209

theorem tailTrace_7090322 : CollatzResearch.WordTrace tailWord_7090322 prefixEnd_7090322 3640743181148113316267209 := by
  unfold tailWord_7090322
  simp only [CollatzResearch.WordTrace]
  refine ⟨64651322154745449858900305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172403525745987866290400813 64651322154745449858900305)
  ·
    refine ⟨48488491616059087394175229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64651322154745449858900305 48488491616059087394175229)
    ·
      refine ⟨18183184356022157772815711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48488491616059087394175229 18183184356022157772815711)
      ·
        refine ⟨27274776534033236659223567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18183184356022157772815711 27274776534033236659223567)
        ·
          refine ⟨40912164801049854988835351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27274776534033236659223567 40912164801049854988835351)
          ·
            refine ⟨61368247201574782483253027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40912164801049854988835351 61368247201574782483253027)
            ·
              refine ⟨92052370802362173724879541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61368247201574782483253027 92052370802362173724879541)
              ·
                refine ⟨8629909762721453786707457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92052370802362173724879541 8629909762721453786707457)
                ·
                  refine ⟨6472432322041090340030593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8629909762721453786707457 6472432322041090340030593)
                  ·
                    refine ⟨4854324241530817755022945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6472432322041090340030593 4854324241530817755022945)
                    ·
                      refine ⟨3640743181148113316267209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4854324241530817755022945 3640743181148113316267209)
                      ·
                        rfl

theorem cell23_7090322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_7090322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090322 prefixEnd_7090322 := by exact prefixLift 7090322
  have htrace : WordTrace (prefixWord ++ tailWord_7090322) baseStart_7090322 baseEnd_7090322 := by
    simpa [prefixWord, tailWord_7090322, baseEnd_7090322] using wordTrace_append hprefix tailTrace_7090322
  have hstable : (prefixWord ++ tailWord_7090322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090322).length < 2 ^ (prefixWord ++ tailWord_7090322).sum := by decide
  have hdescent : baseEnd_7090322 < baseStart_7090322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090328 : List Nat := [2, 1, 2, 4, 3, 1, 1, 2, 7]
def baseStart_7090328 : Nat := 118140960795 + 7090328 * 2 ^ 59
def prefixEnd_7090328 : Nat := 4983230072969 + 3 ^ 40 * 7090328 * 2
def baseEnd_7090328 : Nat := 404527362448004476976909

theorem tailTrace_7090328 : CollatzResearch.WordTrace tailWord_7090328 prefixEnd_7090328 404527362448004476976909 := by
  unfold tailWord_7090328
  simp only [CollatzResearch.WordTrace]
  refine ⟨129302753728480031230159819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172403671637973374973546425 129302753728480031230159819)
  ·
    refine ⟨193954130592720046845239729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129302753728480031230159819 193954130592720046845239729)
    ·
      refine ⟨145465597944540035133929797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193954130592720046845239729 145465597944540035133929797)
      ·
        refine ⟨27274799614601256587611837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145465597944540035133929797 27274799614601256587611837)
        ·
          refine ⟨10228049855475471220354439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27274799614601256587611837 10228049855475471220354439)
          ·
            refine ⟨15342074783213206830531659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10228049855475471220354439 15342074783213206830531659)
            ·
              refine ⟨23013112174819810245797489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15342074783213206830531659 23013112174819810245797489)
              ·
                refine ⟨17259834131114857684348117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23013112174819810245797489 17259834131114857684348117)
                ·
                  refine ⟨404527362448004476976909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17259834131114857684348117 404527362448004476976909)
                  ·
                    rfl

theorem cell23_7090328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 7].length) (baseStart_7090328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090328 prefixEnd_7090328 := by exact prefixLift 7090328
  have htrace : WordTrace (prefixWord ++ tailWord_7090328) baseStart_7090328 baseEnd_7090328 := by
    simpa [prefixWord, tailWord_7090328, baseEnd_7090328] using wordTrace_append hprefix tailTrace_7090328
  have hstable : (prefixWord ++ tailWord_7090328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090328).length < 2 ^ (prefixWord ++ tailWord_7090328).sum := by decide
  have hdescent : baseEnd_7090328 < baseStart_7090328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090341 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 1, 7]
def baseStart_7090341 : Nat := 118140960795 + 7090341 * 2 ^ 59
def prefixEnd_7090341 : Nat := 4983230072969 + 3 ^ 40 * 7090341 * 2
def baseEnd_7090341 : Nat := 1213584312426849580643207

theorem tailTrace_7090341 : CollatzResearch.WordTrace tailWord_7090341 prefixEnd_7090341 1213584312426849580643207 := by
  unfold tailWord_7090341
  simp only [CollatzResearch.WordTrace]
  refine ⟨258605981605912965680542877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172403987737275310453695251 258605981605912965680542877)
  ·
    refine ⟨96977243102217362130203579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258605981605912965680542877 96977243102217362130203579)
    ·
      refine ⟨145465864653326043195305369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96977243102217362130203579 145465864653326043195305369)
      ·
        refine ⟨109099398489994532396479027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145465864653326043195305369 109099398489994532396479027)
        ·
          refine ⟨163649097734991798594718541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109099398489994532396479027 163649097734991798594718541)
          ·
            refine ⟨61368411650621924473019453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163649097734991798594718541 61368411650621924473019453)
            ·
              refine ⟨23013154368983221677382295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61368411650621924473019453 23013154368983221677382295)
              ·
                refine ⟨34519731553474832516073443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23013154368983221677382295 34519731553474832516073443)
                ·
                  refine ⟨51779597330212248774110165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34519731553474832516073443 51779597330212248774110165)
                  ·
                    refine ⟨1213584312426849580643207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51779597330212248774110165 1213584312426849580643207)
                    ·
                      rfl

theorem cell23_7090341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_7090341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090341 prefixEnd_7090341 := by exact prefixLift 7090341
  have htrace : WordTrace (prefixWord ++ tailWord_7090341) baseStart_7090341 baseEnd_7090341 := by
    simpa [prefixWord, tailWord_7090341, baseEnd_7090341] using wordTrace_append hprefix tailTrace_7090341
  have hstable : (prefixWord ++ tailWord_7090341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090341).length < 2 ^ (prefixWord ++ tailWord_7090341).sum := by decide
  have hdescent : baseEnd_7090341 < baseStart_7090341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090391 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 4]
def baseStart_7090391 : Nat := 118140960795 + 7090391 * 2 ^ 59
def prefixEnd_7090391 : Nat := 4983230072969 + 3 ^ 40 * 7090391 * 2
def baseEnd_7090391 : Nat := 3640778611313273546304391

theorem tailTrace_7090391 : CollatzResearch.WordTrace tailWord_7090391 prefixEnd_7090391 3640778611313273546304391 := by
  unfold tailWord_7090391
  simp only [CollatzResearch.WordTrace]
  refine ⟨258607805255731824219863027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172405203503821216146575351 258607805255731824219863027)
  ·
    refine ⟨387911707883597736329794541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258607805255731824219863027 387911707883597736329794541)
    ·
      refine ⟨145466890456349151123672953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387911707883597736329794541 145466890456349151123672953)
      ·
        refine ⟨109100167842261863342754715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145466890456349151123672953 109100167842261863342754715)
        ·
          refine ⟨163650251763392795014132073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109100167842261863342754715 163650251763392795014132073)
          ·
            refine ⟨122737688822544596260599055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163650251763392795014132073 122737688822544596260599055)
            ·
              refine ⟨184106533233816894390898583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122737688822544596260599055 184106533233816894390898583)
              ·
                refine ⟨276159799850725341586347875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184106533233816894390898583 276159799850725341586347875)
                ·
                  refine ⟨414239699776088012379521813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276159799850725341586347875 414239699776088012379521813)
                  ·
                    refine ⟨19417485927004125580290085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 414239699776088012379521813 19417485927004125580290085)
                    ·
                      refine ⟨3640778611313273546304391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19417485927004125580290085 3640778611313273546304391)
                      ·
                        rfl

theorem cell23_7090391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_7090391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090391 prefixEnd_7090391 := by exact prefixLift 7090391
  have htrace : WordTrace (prefixWord ++ tailWord_7090391) baseStart_7090391 baseEnd_7090391 := by
    simpa [prefixWord, tailWord_7090391, baseEnd_7090391] using wordTrace_append hprefix tailTrace_7090391
  have hstable : (prefixWord ++ tailWord_7090391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090391).length < 2 ^ (prefixWord ++ tailWord_7090391).sum := by decide
  have hdescent : baseEnd_7090391 < baseStart_7090391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090396 : List Nat := [2, 2, 5, 2, 2, 1, 1, 3, 5]
def baseStart_7090396 : Nat := 118140960795 + 7090396 * 2 ^ 59
def prefixEnd_7090396 : Nat := 4983230072969 + 3 ^ 40 * 7090396 * 2
def baseEnd_7090396 : Nat := 404531242079616225193541

theorem tailTrace_7090396 : CollatzResearch.WordTrace tailWord_7090396 prefixEnd_7090396 404531242079616225193541 := by
  unfold tailWord_7090396
  simp only [CollatzResearch.WordTrace]
  refine ⟨129303993810356855036897521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172405325080475806715863361 129303993810356855036897521)
  ·
    refine ⟨96977995357767641277673141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129303993810356855036897521 96977995357767641277673141)
    ·
      refine ⟨9091687064790716369781857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96977995357767641277673141 9091687064790716369781857)
      ·
        refine ⟨6818765298593037277336393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9091687064790716369781857 6818765298593037277336393)
        ·
          refine ⟨5114073973944777958002295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6818765298593037277336393 5114073973944777958002295)
          ·
            refine ⟨7671110960917166937003443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5114073973944777958002295 7671110960917166937003443)
            ·
              refine ⟨11506666441375750405505165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7671110960917166937003443 11506666441375750405505165)
              ·
                refine ⟨4314999915515906402064437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11506666441375750405505165 4314999915515906402064437)
                ·
                  refine ⟨404531242079616225193541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4314999915515906402064437 404531242079616225193541)
                  ·
                    rfl

theorem cell23_7090396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 5].length) (baseStart_7090396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090396 prefixEnd_7090396 := by exact prefixLift 7090396
  have htrace : WordTrace (prefixWord ++ tailWord_7090396) baseStart_7090396 baseEnd_7090396 := by
    simpa [prefixWord, tailWord_7090396, baseEnd_7090396] using wordTrace_append hprefix tailTrace_7090396
  have hstable : (prefixWord ++ tailWord_7090396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090396).length < 2 ^ (prefixWord ++ tailWord_7090396).sum := by decide
  have hdescent : baseEnd_7090396 < baseStart_7090396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090401 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 10]
def baseStart_7090401 : Nat := 118140960795 + 7090401 * 2 ^ 59
def prefixEnd_7090401 : Nat := 4983230072969 + 3 ^ 40 * 7090401 * 2
def baseEnd_7090401 : Nat := 404531527346646500797705

theorem tailTrace_7090401 : CollatzResearch.WordTrace tailWord_7090401 prefixEnd_7090401 404531527346646500797705 := by
  unfold tailWord_7090401
  simp only [CollatzResearch.WordTrace]
  refine ⟨258608169985695595927727057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172405446657130397285151371 258608169985695595927727057)
  ·
    refine ⟨193956127489271696945795293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258608169985695595927727057 193956127489271696945795293)
    ·
      refine ⟨72733547808476886354673235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193956127489271696945795293 72733547808476886354673235)
      ·
        refine ⟨109100321712715329532009853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72733547808476886354673235 109100321712715329532009853)
        ·
          refine ⟨40912620642268248574503695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109100321712715329532009853 40912620642268248574503695)
          ·
            refine ⟨61368930963402372861755543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40912620642268248574503695 61368930963402372861755543)
            ·
              refine ⟨92053396445103559292633315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61368930963402372861755543 92053396445103559292633315)
              ·
                refine ⟨138080094667655338938949973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92053396445103559292633315 138080094667655338938949973)
                ·
                  refine ⟨404531527346646500797705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 138080094667655338938949973 404531527346646500797705)
                  ·
                    rfl

theorem cell23_7090401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 10].length) (baseStart_7090401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090401 prefixEnd_7090401 := by exact prefixLift 7090401
  have htrace : WordTrace (prefixWord ++ tailWord_7090401) baseStart_7090401 baseEnd_7090401 := by
    simpa [prefixWord, tailWord_7090401, baseEnd_7090401] using wordTrace_append hprefix tailTrace_7090401
  have hstable : (prefixWord ++ tailWord_7090401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090401).length < 2 ^ (prefixWord ++ tailWord_7090401).sum := by decide
  have hdescent : baseEnd_7090401 < baseStart_7090401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090415 : List Nat := [1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 3]
def baseStart_7090415 : Nat := 118140960795 + 7090415 * 2 ^ 59
def prefixEnd_7090415 : Nat := 4983230072969 + 3 ^ 40 * 7090415 * 2
def baseEnd_7090415 : Nat := 3640790934848981452404281

theorem tailTrace_7090415 : CollatzResearch.WordTrace tailWord_7090415 prefixEnd_7090415 3640790934848981452404281 := by
  unfold tailWord_7090415
  simp only [CollatzResearch.WordTrace]
  refine ⟨258608680607644876318736699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172405787071763250879157799 258608680607644876318736699)
  ·
    refine ⟨387913020911467314478105049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258608680607644876318736699 387913020911467314478105049)
    ·
      refine ⟨290934765683600485858578787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387913020911467314478105049 290934765683600485858578787)
      ·
        refine ⟨436402148525400728787868181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290934765683600485858578787 436402148525400728787868181)
        ·
          refine ⟨20456350712128159161931321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 436402148525400728787868181 20456350712128159161931321)
          ·
            refine ⟨15342263034096119371448491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20456350712128159161931321 15342263034096119371448491)
            ·
              refine ⟨23013394551144179057172737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15342263034096119371448491 23013394551144179057172737)
              ·
                refine ⟨17260045913358134292879553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23013394551144179057172737 17260045913358134292879553)
                ·
                  refine ⟨12945034435018600719659665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17260045913358134292879553 12945034435018600719659665)
                  ·
                    refine ⟨9708775826263950539744749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12945034435018600719659665 9708775826263950539744749)
                    ·
                      refine ⟨3640790934848981452404281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9708775826263950539744749 3640790934848981452404281)
                      ·
                        rfl

theorem cell23_7090415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 3].length) (baseStart_7090415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090415 prefixEnd_7090415 := by exact prefixLift 7090415
  have htrace : WordTrace (prefixWord ++ tailWord_7090415) baseStart_7090415 baseEnd_7090415 := by
    simpa [prefixWord, tailWord_7090415, baseEnd_7090415] using wordTrace_append hprefix tailTrace_7090415
  have hstable : (prefixWord ++ tailWord_7090415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090415).length < 2 ^ (prefixWord ++ tailWord_7090415).sum := by decide
  have hdescent : baseEnd_7090415 < baseStart_7090415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090418 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 8]
def baseStart_7090418 : Nat := 118140960795 + 7090418 * 2 ^ 59
def prefixEnd_7090418 : Nat := 4983230072969 + 3 ^ 40 * 7090418 * 2
def baseEnd_7090418 : Nat := 404532497254549437851863

theorem tailTrace_7090418 : CollatzResearch.WordTrace tailWord_7090418 prefixEnd_7090418 404532497254549437851863 := by
  unfold tailWord_7090418
  simp only [CollatzResearch.WordTrace]
  refine ⟨64652197506658501957773977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172405860017756005220730605 64652197506658501957773977)
  ·
    refine ⟨48489148129993876468330483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64652197506658501957773977 48489148129993876468330483)
    ·
      refine ⟨72733722194990814702495725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48489148129993876468330483 72733722194990814702495725)
      ·
        refine ⟨27275145823121555513435897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72733722194990814702495725 27275145823121555513435897)
        ·
          refine ⟨20456359367341166635076923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27275145823121555513435897 20456359367341166635076923)
          ·
            refine ⟨30684539051011749952615385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20456359367341166635076923 30684539051011749952615385)
            ·
              refine ⟨23013404288258812464461539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30684539051011749952615385 23013404288258812464461539)
              ·
                refine ⟨34520106432388218696692309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23013404288258812464461539 34520106432388218696692309)
                ·
                  refine ⟨404532497254549437851863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34520106432388218696692309 404532497254549437851863)
                  ·
                    rfl

theorem cell23_7090418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_7090418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090418 prefixEnd_7090418 := by exact prefixLift 7090418
  have htrace : WordTrace (prefixWord ++ tailWord_7090418) baseStart_7090418 baseEnd_7090418 := by
    simpa [prefixWord, tailWord_7090418, baseEnd_7090418] using wordTrace_append hprefix tailTrace_7090418
  have hstable : (prefixWord ++ tailWord_7090418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090418).length < 2 ^ (prefixWord ++ tailWord_7090418).sum := by decide
  have hdescent : baseEnd_7090418 < baseStart_7090418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090422 : List Nat := [5, 1, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_7090422 : Nat := 118140960795 + 7090422 * 2 ^ 59
def prefixEnd_7090422 : Nat := 4983230072969 + 3 ^ 40 * 7090422 * 2
def baseEnd_7090422 : Nat := 1213598176404520975005583

theorem tailTrace_7090422 : CollatzResearch.WordTrace tailWord_7090422 prefixEnd_7090422 1213598176404520975005583 := by
  unfold tailWord_7090422
  simp only [CollatzResearch.WordTrace]
  refine ⟨16163058494913719782140095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172405957279079677676161013 16163058494913719782140095)
  ·
    refine ⟨24244587742370579673210143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16163058494913719782140095 24244587742370579673210143)
    ·
      refine ⟨36366881613555869509815215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24244587742370579673210143 36366881613555869509815215)
      ·
        refine ⟨54550322420333804264722823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36366881613555869509815215 54550322420333804264722823)
        ·
          refine ⟨81825483630500706397084235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54550322420333804264722823 81825483630500706397084235)
          ·
            refine ⟨122738225445751059595626353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81825483630500706397084235 122738225445751059595626353)
            ·
              refine ⟨92053669084313294696719765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122738225445751059595626353 92053669084313294696719765)
              ·
                refine ⟨4315015738327185688908739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92053669084313294696719765 4315015738327185688908739)
                ·
                  refine ⟨6472523607490778533363109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4315015738327185688908739 6472523607490778533363109)
                  ·
                    refine ⟨1213598176404520975005583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6472523607490778533363109 1213598176404520975005583)
                    ·
                      rfl

theorem cell23_7090422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_7090422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090422 prefixEnd_7090422 := by exact prefixLift 7090422
  have htrace : WordTrace (prefixWord ++ tailWord_7090422) baseStart_7090422 baseEnd_7090422 := by
    simpa [prefixWord, tailWord_7090422, baseEnd_7090422] using wordTrace_append hprefix tailTrace_7090422
  have hstable : (prefixWord ++ tailWord_7090422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090422).length < 2 ^ (prefixWord ++ tailWord_7090422).sum := by decide
  have hdescent : baseEnd_7090422 < baseStart_7090422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090479 : List Nat := [1, 1, 2, 1, 2, 1, 8, 2, 1, 1, 3]
def baseStart_7090479 : Nat := 118140960795 + 7090479 * 2 ^ 59
def prefixEnd_7090479 : Nat := 4983230072969 + 3 ^ 40 * 7090479 * 2
def baseEnd_7090479 : Nat := 3640823797610869202003987

theorem tailTrace_7090479 : CollatzResearch.WordTrace tailWord_7090479 prefixEnd_7090479 3640823797610869202003987 := by
  unfold tailWord_7090479
  simp only [CollatzResearch.WordTrace]
  refine ⟨258611014879413015249066491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172407343252942010166044327 258611014879413015249066491)
  ·
    refine ⟨387916522319119522873599737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258611014879413015249066491 387916522319119522873599737)
    ·
      refine ⟨290937391739339642155199803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387916522319119522873599737 290937391739339642155199803)
      ·
        refine ⟨436406087609009463232799705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290937391739339642155199803 436406087609009463232799705)
        ·
          refine ⟨327304565706757097424599779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436406087609009463232799705 327304565706757097424599779)
          ·
            refine ⟨490956848560135646136899669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327304565706757097424599779 490956848560135646136899669)
            ·
              refine ⟨5753400569064089603166793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 490956848560135646136899669 5753400569064089603166793)
              ·
                refine ⟨4315050426798067202375095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5753400569064089603166793 4315050426798067202375095)
                ·
                  refine ⟨6472575640197100803562643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4315050426798067202375095 6472575640197100803562643)
                  ·
                    refine ⟨9708863460295651205343965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6472575640197100803562643 9708863460295651205343965)
                    ·
                      refine ⟨3640823797610869202003987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9708863460295651205343965 3640823797610869202003987)
                      ·
                        rfl

theorem cell23_7090479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 1, 1, 3].length) (baseStart_7090479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090479 prefixEnd_7090479 := by exact prefixLift 7090479
  have htrace : WordTrace (prefixWord ++ tailWord_7090479) baseStart_7090479 baseEnd_7090479 := by
    simpa [prefixWord, tailWord_7090479, baseEnd_7090479] using wordTrace_append hprefix tailTrace_7090479
  have hstable : (prefixWord ++ tailWord_7090479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090479).length < 2 ^ (prefixWord ++ tailWord_7090479).sum := by decide
  have hdescent : baseEnd_7090479 < baseStart_7090479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090488 : List Nat := [2, 1, 2, 1, 3, 1, 2, 4, 1, 1, 5]
def baseStart_7090488 : Nat := 118140960795 + 7090488 * 2 ^ 59
def prefixEnd_7090488 : Nat := 4983230072969 + 3 ^ 40 * 7090488 * 2
def baseEnd_7090488 : Nat := 3640828418936759666791445

theorem tailTrace_7090488 : CollatzResearch.WordTrace tailWord_7090488 prefixEnd_7090488 3640828418936759666791445 := by
  unfold tailWord_7090488
  simp only [CollatzResearch.WordTrace]
  refine ⟨129305671568190204893072059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172407562090920273190762745 129305671568190204893072059)
  ·
    refine ⟨193958507352285307339608089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129305671568190204893072059 193958507352285307339608089)
    ·
      refine ⟨145468880514213980504706067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193958507352285307339608089 145468880514213980504706067)
      ·
        refine ⟨218203320771320970757059101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145468880514213980504706067 218203320771320970757059101)
        ·
          refine ⟨81826245289245364033897163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218203320771320970757059101 81826245289245364033897163)
          ·
            refine ⟨122739367933868046050845745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81826245289245364033897163 122739367933868046050845745)
            ·
              refine ⟨92054525950401034538134309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122739367933868046050845745 92054525950401034538134309)
              ·
                refine ⟨17260223615700193975900183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92054525950401034538134309 17260223615700193975900183)
                ·
                  refine ⟨25890335423550290963850275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17260223615700193975900183 25890335423550290963850275)
                  ·
                    refine ⟨38835503135325436445775413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25890335423550290963850275 38835503135325436445775413)
                    ·
                      refine ⟨3640828418936759666791445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38835503135325436445775413 3640828418936759666791445)
                      ·
                        rfl

theorem cell23_7090488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_7090488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090488 prefixEnd_7090488 := by exact prefixLift 7090488
  have htrace : WordTrace (prefixWord ++ tailWord_7090488) baseStart_7090488 baseEnd_7090488 := by
    simpa [prefixWord, tailWord_7090488, baseEnd_7090488] using wordTrace_append hprefix tailTrace_7090488
  have hstable : (prefixWord ++ tailWord_7090488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090488).length < 2 ^ (prefixWord ++ tailWord_7090488).sum := by decide
  have hdescent : baseEnd_7090488 < baseStart_7090488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090495 : List Nat := [1, 1, 2, 2, 4, 1, 1, 5, 2, 4]
def baseStart_7090495 : Nat := 118140960795 + 7090495 * 2 ^ 59
def prefixEnd_7090495 : Nat := 4983230072969 + 3 ^ 40 * 7090495 * 2
def baseEnd_7090495 : Nat := 1213610671100447046467971

theorem tailTrace_7090495 : CollatzResearch.WordTrace tailWord_7090495 prefixEnd_7090495 1213610671100447046467971 := by
  unfold tailWord_7090495
  simp only [CollatzResearch.WordTrace]
  refine ⟨258611598447355049981648939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172407732298236699987765959 258611598447355049981648939)
  ·
    refine ⟨387917397671032574972473409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258611598447355049981648939 387917397671032574972473409)
    ·
      refine ⟨290938048253274431229355057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387917397671032574972473409 290938048253274431229355057)
      ·
        refine ⟨218203536189955823422016293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290938048253274431229355057 218203536189955823422016293)
        ·
          refine ⟨40913163035616716891628055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218203536189955823422016293 40913163035616716891628055)
          ·
            refine ⟨61369744553425075337442083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40913163035616716891628055 61369744553425075337442083)
            ·
              refine ⟨92054616830137613006163125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61369744553425075337442083 92054616830137613006163125)
              ·
                refine ⟨8630120327825401219327793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92054616830137613006163125 8630120327825401219327793)
                ·
                  refine ⟨6472590245869050914495845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8630120327825401219327793 6472590245869050914495845)
                  ·
                    refine ⟨1213610671100447046467971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6472590245869050914495845 1213610671100447046467971)
                    ·
                      rfl

theorem cell23_7090495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 4].length) (baseStart_7090495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090495 prefixEnd_7090495 := by exact prefixLift 7090495
  have htrace : WordTrace (prefixWord ++ tailWord_7090495) baseStart_7090495 baseEnd_7090495 := by
    simpa [prefixWord, tailWord_7090495, baseEnd_7090495] using wordTrace_append hprefix tailTrace_7090495
  have hstable : (prefixWord ++ tailWord_7090495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090495).length < 2 ^ (prefixWord ++ tailWord_7090495).sum := by decide
  have hdescent : baseEnd_7090495 < baseStart_7090495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090505 : List Nat := [1, 2, 1, 1, 2, 3, 1, 6, 1, 2, 3]
def baseStart_7090505 : Nat := 118140960795 + 7090505 * 2 ^ 59
def prefixEnd_7090505 : Nat := 4983230072969 + 3 ^ 40 * 7090505 * 2
def baseEnd_7090505 : Nat := 3640837148107886100278867

theorem tailTrace_7090505 : CollatzResearch.WordTrace tailWord_7090505 prefixEnd_7090505 3640837148107886100278867 := by
  unfold tailWord_7090505
  simp only [CollatzResearch.WordTrace]
  refine ⟨258611963177318821689512969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172407975451545881126341979 258611963177318821689512969)
  ·
    refine ⟨193958972382989116267134727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258611963177318821689512969 193958972382989116267134727)
    ·
      refine ⟨290938458574483674400702091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193958972382989116267134727 290938458574483674400702091)
      ·
        refine ⟨436407687861725511601053137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290938458574483674400702091 436407687861725511601053137)
        ·
          refine ⟨327305765896294133700789853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436407687861725511601053137 327305765896294133700789853)
          ·
            refine ⟨122739662211110300137796195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327305765896294133700789853 122739662211110300137796195)
            ·
              refine ⟨184109493316665450206694293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122739662211110300137796195 184109493316665450206694293)
              ·
                refine ⟨8630132499218692978438795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 184109493316665450206694293 8630132499218692978438795)
                ·
                  refine ⟨12945198748828039467658193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8630132499218692978438795 12945198748828039467658193)
                  ·
                    refine ⟨9708899061621029600743645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12945198748828039467658193 9708899061621029600743645)
                    ·
                      refine ⟨3640837148107886100278867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9708899061621029600743645 3640837148107886100278867)
                      ·
                        rfl

theorem cell23_7090505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 2, 3].length) (baseStart_7090505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090505 prefixEnd_7090505 := by exact prefixLift 7090505
  have htrace : WordTrace (prefixWord ++ tailWord_7090505) baseStart_7090505 baseEnd_7090505 := by
    simpa [prefixWord, tailWord_7090505, baseEnd_7090505] using wordTrace_append hprefix tailTrace_7090505
  have hstable : (prefixWord ++ tailWord_7090505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090505).length < 2 ^ (prefixWord ++ tailWord_7090505).sum := by decide
  have hdescent : baseEnd_7090505 < baseStart_7090505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090536 : List Nat := [2, 1, 4, 2, 2, 1, 2, 4, 1, 2, 2]
def baseStart_7090536 : Nat := 118140960795 + 7090536 * 2 ^ 59
def prefixEnd_7090536 : Nat := 4983230072969 + 3 ^ 40 * 7090536 * 2
def baseEnd_7090536 : Nat := 3640853066008175478991225

theorem tailTrace_7090536 : CollatzResearch.WordTrace tailWord_7090536 prefixEnd_7090536 3640853066008175478991225 := by
  unfold tailWord_7090536
  simp only [CollatzResearch.WordTrace]
  refine ⟨129306546920103256991945731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172408729226804342655927641 129306546920103256991945731)
  ·
    refine ⟨193959820380154885487918597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129306546920103256991945731 193959820380154885487918597)
    ·
      refine ⟨36367466321279041028984737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193959820380154885487918597 36367466321279041028984737)
      ·
        refine ⟨27275599740959280771738553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36367466321279041028984737 27275599740959280771738553)
        ·
          refine ⟨20456699805719460578803915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27275599740959280771738553 20456699805719460578803915)
          ·
            refine ⟨30685049708579190868205873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20456699805719460578803915 30685049708579190868205873)
            ·
              refine ⟨23013787281434393151154405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30685049708579190868205873 23013787281434393151154405)
              ·
                refine ⟨4315085115268948715841451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23013787281434393151154405 4315085115268948715841451)
                ·
                  refine ⟨6472627672903423073762177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4315085115268948715841451 6472627672903423073762177)
                  ·
                    refine ⟨4854470754677567305321633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6472627672903423073762177 4854470754677567305321633)
                    ·
                      refine ⟨3640853066008175478991225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4854470754677567305321633 3640853066008175478991225)
                      ·
                        rfl

theorem cell23_7090536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_7090536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090536 prefixEnd_7090536 := by exact prefixLift 7090536
  have htrace : WordTrace (prefixWord ++ tailWord_7090536) baseStart_7090536 baseEnd_7090536 := by
    simpa [prefixWord, tailWord_7090536, baseEnd_7090536] using wordTrace_append hprefix tailTrace_7090536
  have hstable : (prefixWord ++ tailWord_7090536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090536).length < 2 ^ (prefixWord ++ tailWord_7090536).sum := by decide
  have hdescent : baseEnd_7090536 < baseStart_7090536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090570 : List Nat := [3, 1, 2, 5, 1, 2, 1, 3, 1, 2, 2]
def baseStart_7090570 : Nat := 118140960795 + 7090570 * 2 ^ 59
def prefixEnd_7090570 : Nat := 4983230072969 + 3 ^ 40 * 7090570 * 2
def baseEnd_7090570 : Nat := 3640870524350428345966069

theorem tailTrace_7090570 : CollatzResearch.WordTrace tailWord_7090570 prefixEnd_7090570 3640870524350428345966069 := by
  unfold tailWord_7090570
  simp only [CollatzResearch.WordTrace]
  refine ⟨64653583480520834447657291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172409555948055558527086109 64653583480520834447657291)
  ·
    refine ⟨96980375220781251671485937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64653583480520834447657291 96980375220781251671485937)
    ·
      refine ⟨72735281415585938753614453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96980375220781251671485937 72735281415585938753614453)
      ·
        refine ⟨6818932632711181758151355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72735281415585938753614453 6818932632711181758151355)
        ·
          refine ⟨10228398949066772637227033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6818932632711181758151355 10228398949066772637227033)
          ·
            refine ⟨7671299211800079477920275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10228398949066772637227033 7671299211800079477920275)
            ·
              refine ⟨11506948817700119216880413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7671299211800079477920275 11506948817700119216880413)
              ·
                refine ⟨4315105806637544706330155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11506948817700119216880413 4315105806637544706330155)
                ·
                  refine ⟨6472658709956317059495233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4315105806637544706330155 6472658709956317059495233)
                  ·
                    refine ⟨4854494032467237794621425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6472658709956317059495233 4854494032467237794621425)
                    ·
                      refine ⟨3640870524350428345966069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4854494032467237794621425 3640870524350428345966069)
                      ·
                        rfl

theorem cell23_7090570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_7090570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090570 prefixEnd_7090570 := by exact prefixLift 7090570
  have htrace : WordTrace (prefixWord ++ tailWord_7090570) baseStart_7090570 baseEnd_7090570 := by
    simpa [prefixWord, tailWord_7090570, baseEnd_7090570] using wordTrace_append hprefix tailTrace_7090570
  have hstable : (prefixWord ++ tailWord_7090570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090570).length < 2 ^ (prefixWord ++ tailWord_7090570).sum := by decide
  have hdescent : baseEnd_7090570 < baseStart_7090570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090613 : List Nat := [1, 3, 3, 2, 4, 1, 1, 2, 1, 3, 2]
def baseStart_7090613 : Nat := 118140960795 + 7090613 * 2 ^ 59
def prefixEnd_7090613 : Nat := 4983230072969 + 3 ^ 40 * 7090613 * 2
def baseEnd_7090613 : Nat := 3640892604018571677728371

theorem tailTrace_7090613 : CollatzResearch.WordTrace tailWord_7090613 prefixEnd_7090613 3640892604018571677728371 := by
  unfold tailWord_7090613
  simp only [CollatzResearch.WordTrace]
  refine ⟨258615902260927556134444493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172410601507285037422962995 258615902260927556134444493)
  ·
    refine ⟨96980963347847833550416685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258615902260927556134444493 96980963347847833550416685)
    ·
      refine ⟨36367861255442937581406257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96980963347847833550416685 36367861255442937581406257)
      ·
        refine ⟨27275895941582203186054693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36367861255442937581406257 27275895941582203186054693)
        ·
          refine ⟨5114230489046663097385255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27275895941582203186054693 5114230489046663097385255)
          ·
            refine ⟨7671345733569994646077883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5114230489046663097385255 7671345733569994646077883)
            ·
              refine ⟨11507018600354991969116825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7671345733569994646077883 11507018600354991969116825)
              ·
                refine ⟨8630263950266243976837619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11507018600354991969116825 8630263950266243976837619)
                ·
                  refine ⟨12945395925399365965256429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8630263950266243976837619 12945395925399365965256429)
                  ·
                    refine ⟨4854523472024762236971161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12945395925399365965256429 4854523472024762236971161)
                    ·
                      refine ⟨3640892604018571677728371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4854523472024762236971161 3640892604018571677728371)
                      ·
                        rfl

theorem cell23_7090613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_7090613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090613 prefixEnd_7090613 := by exact prefixLift 7090613
  have htrace : WordTrace (prefixWord ++ tailWord_7090613) baseStart_7090613 baseEnd_7090613 := by
    simpa [prefixWord, tailWord_7090613, baseEnd_7090613] using wordTrace_append hprefix tailTrace_7090613
  have hstable : (prefixWord ++ tailWord_7090613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090613).length < 2 ^ (prefixWord ++ tailWord_7090613).sum := by decide
  have hdescent : baseEnd_7090613 < baseStart_7090613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090618 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8]
def baseStart_7090618 : Nat := 118140960795 + 7090618 * 2 ^ 59
def prefixEnd_7090618 : Nat := 4983230072969 + 3 ^ 40 * 7090618 * 2
def baseEnd_7090618 : Nat := 3640895171421844158165847

theorem tailTrace_7090618 : CollatzResearch.WordTrace tailWord_7090618 prefixEnd_7090618 3640895171421844158165847 := by
  unfold tailWord_7090618
  simp only [CollatzResearch.WordTrace]
  refine ⟨64654021156477360497094127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172410723083939627992251005 64654021156477360497094127)
  ·
    refine ⟨96981031734716040745641191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64654021156477360497094127 96981031734716040745641191)
    ·
      refine ⟨145471547602074061118461787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96981031734716040745641191 145471547602074061118461787)
      ·
        refine ⟨218207321403111091677692681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145471547602074061118461787 218207321403111091677692681)
        ·
          refine ⟨163655491052333318758269511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218207321403111091677692681 163655491052333318758269511)
          ·
            refine ⟨245483236578499978137404267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163655491052333318758269511 245483236578499978137404267)
            ·
              refine ⟨368224854867749967206106401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245483236578499978137404267 368224854867749967206106401)
              ·
                refine ⟨276168641150812475404579801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368224854867749967206106401 276168641150812475404579801)
                ·
                  refine ⟨207126480863109356553434851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276168641150812475404579801 207126480863109356553434851)
                  ·
                    refine ⟨310689721294664034830152277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 207126480863109356553434851 310689721294664034830152277)
                    ·
                      refine ⟨3640895171421844158165847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 310689721294664034830152277 3640895171421844158165847)
                      ·
                        rfl

theorem cell23_7090618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_7090618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090618 prefixEnd_7090618 := by exact prefixLift 7090618
  have htrace : WordTrace (prefixWord ++ tailWord_7090618) baseStart_7090618 baseEnd_7090618 := by
    simpa [prefixWord, tailWord_7090618, baseEnd_7090618] using wordTrace_append hprefix tailTrace_7090618
  have hstable : (prefixWord ++ tailWord_7090618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090618).length < 2 ^ (prefixWord ++ tailWord_7090618).sum := by decide
  have hdescent : baseEnd_7090618 < baseStart_7090618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090655 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 5]
def baseStart_7090655 : Nat := 118140960795 + 7090655 * 2 ^ 59
def prefixEnd_7090655 : Nat := 4983230072969 + 3 ^ 40 * 7090655 * 2
def baseEnd_7090655 : Nat := 3640914170206060513403177

theorem tailTrace_7090655 : CollatzResearch.WordTrace tailWord_7090655 prefixEnd_7090655 3640914170206060513403177 := by
  unfold tailWord_7090655
  simp only [CollatzResearch.WordTrace]
  refine ⟨258617434126775397307473419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172411622751183598204982279 258617434126775397307473419)
  ·
    refine ⟨387926151190163095961210129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258617434126775397307473419 387926151190163095961210129)
    ·
      refine ⟨290944613392622321970907597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387926151190163095961210129 290944613392622321970907597)
      ·
        refine ⟨109104230022233370739090349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290944613392622321970907597 109104230022233370739090349)
        ·
          refine ⟨40914086258337514027158881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109104230022233370739090349 40914086258337514027158881)
          ·
            refine ⟨30685564693753135520369161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40914086258337514027158881 30685564693753135520369161)
            ·
              refine ⟨23014173520314851640276871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30685564693753135520369161 23014173520314851640276871)
              ·
                refine ⟨34521260280472277460415307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23014173520314851640276871 34521260280472277460415307)
                ·
                  refine ⟨51781890420708416190622961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34521260280472277460415307 51781890420708416190622961)
                  ·
                    refine ⟨38836417815531312142967221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51781890420708416190622961 38836417815531312142967221)
                    ·
                      refine ⟨3640914170206060513403177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38836417815531312142967221 3640914170206060513403177)
                      ·
                        rfl

theorem cell23_7090655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_7090655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090655 prefixEnd_7090655 := by exact prefixLift 7090655
  have htrace : WordTrace (prefixWord ++ tailWord_7090655) baseStart_7090655 baseEnd_7090655 := by
    simpa [prefixWord, tailWord_7090655, baseEnd_7090655] using wordTrace_append hprefix tailTrace_7090655
  have hstable : (prefixWord ++ tailWord_7090655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090655).length < 2 ^ (prefixWord ++ tailWord_7090655).sum := by decide
  have hdescent : baseEnd_7090655 < baseStart_7090655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090705 : List Nat := [1, 2, 2, 1, 1, 2, 2, 6, 6]
def baseStart_7090705 : Nat := 118140960795 + 7090705 * 2 ^ 59
def prefixEnd_7090705 : Nat := 4983230072969 + 3 ^ 40 * 7090705 * 2
def baseEnd_7090705 : Nat := 404548871582087257530883

theorem tailTrace_7090705 : CollatzResearch.WordTrace tailWord_7090705 prefixEnd_7090705 404548871582087257530883 := by
  unfold tailWord_7090705
  simp only [CollatzResearch.WordTrace]
  refine ⟨258619257776594255846793569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172412838517729503897862379 258619257776594255846793569)
  ·
    refine ⟨193964443332445691885095177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258619257776594255846793569 193964443332445691885095177)
    ·
      refine ⟨145473332499334268913821383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193964443332445691885095177 145473332499334268913821383)
      ·
        refine ⟨218209998749001403370732075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145473332499334268913821383 218209998749001403370732075)
        ·
          refine ⟨327314998123502105056098113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218209998749001403370732075 327314998123502105056098113)
          ·
            refine ⟨245486248592626578792073585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327314998123502105056098113 245486248592626578792073585)
            ·
              refine ⟨184114686444469934094055189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245486248592626578792073585 184114686444469934094055189)
              ·
                refine ⟨8630375927084528160658837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 184114686444469934094055189 8630375927084528160658837)
                ·
                  refine ⟨404548871582087257530883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8630375927084528160658837 404548871582087257530883)
                  ·
                    rfl

theorem cell23_7090705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 6].length) (baseStart_7090705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090705 prefixEnd_7090705 := by exact prefixLift 7090705
  have htrace : WordTrace (prefixWord ++ tailWord_7090705) baseStart_7090705 baseEnd_7090705 := by
    simpa [prefixWord, tailWord_7090705, baseEnd_7090705] using wordTrace_append hprefix tailTrace_7090705
  have hstable : (prefixWord ++ tailWord_7090705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090705).length < 2 ^ (prefixWord ++ tailWord_7090705).sum := by decide
  have hdescent : baseEnd_7090705 < baseStart_7090705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090709 : List Nat := [1, 3, 2, 1, 3, 1, 1, 6, 1, 4]
def baseStart_7090709 : Nat := 118140960795 + 7090709 * 2 ^ 59
def prefixEnd_7090709 : Nat := 4983230072969 + 3 ^ 40 * 7090709 * 2
def baseEnd_7090709 : Nat := 1213647299387134434042643

theorem tailTrace_7090709 : CollatzResearch.WordTrace tailWord_7090709 prefixEnd_7090709 1213647299387134434042643 := by
  unfold tailWord_7090709
  simp only [CollatzResearch.WordTrace]
  refine ⟨258619403668579764529939181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172412935779053176353292787 258619403668579764529939181)
  ·
    refine ⟨96982276375717411698727193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258619403668579764529939181 96982276375717411698727193)
    ·
      refine ⟨72736707281788058774045395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96982276375717411698727193 72736707281788058774045395)
      ·
        refine ⟨109105060922682088161068093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72736707281788058774045395 109105060922682088161068093)
        ·
          refine ⟨40914397846005783060400535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109105060922682088161068093 40914397846005783060400535)
          ·
            refine ⟨61371596769008674590600803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40914397846005783060400535 61371596769008674590600803)
            ·
              refine ⟨92057395153513011885901205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61371596769008674590600803 92057395153513011885901205)
              ·
                refine ⟨4315190397820922432151619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92057395153513011885901205 4315190397820922432151619)
                ·
                  refine ⟨6472785596731383648227429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4315190397820922432151619 6472785596731383648227429)
                  ·
                    refine ⟨1213647299387134434042643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6472785596731383648227429 1213647299387134434042643)
                    ·
                      rfl

theorem cell23_7090709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_7090709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090709 prefixEnd_7090709 := by exact prefixLift 7090709
  have htrace : WordTrace (prefixWord ++ tailWord_7090709) baseStart_7090709 baseEnd_7090709 := by
    simpa [prefixWord, tailWord_7090709, baseEnd_7090709] using wordTrace_append hprefix tailTrace_7090709
  have hstable : (prefixWord ++ tailWord_7090709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090709).length < 2 ^ (prefixWord ++ tailWord_7090709).sum := by decide
  have hdescent : baseEnd_7090709 < baseStart_7090709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090752 : List Nat := [2, 1, 1, 2, 2, 2, 4, 3, 1, 5]
def baseStart_7090752 : Nat := 118140960795 + 7090752 * 2 ^ 59
def prefixEnd_7090752 : Nat := 4983230072969 + 3 ^ 40 * 7090752 * 2
def baseEnd_7090752 : Nat := 1213654659276515544630077

theorem tailTrace_7090752 : CollatzResearch.WordTrace tailWord_7090752 prefixEnd_7090752 1213654659276515544630077 := by
  unfold tailWord_7090752
  simp only [CollatzResearch.WordTrace]
  refine ⟨129310486003711991436877255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172413981338282655249169673 129310486003711991436877255)
  ·
    refine ⟨193965729005567987155315883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129310486003711991436877255 193965729005567987155315883)
    ·
      refine ⟨290948593508351980732973825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193965729005567987155315883 290948593508351980732973825)
      ·
        refine ⟨218211445131263985549730369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290948593508351980732973825 218211445131263985549730369)
        ·
          refine ⟨163658583848447989162297777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218211445131263985549730369 163658583848447989162297777)
          ·
            refine ⟨122743937886335991871723333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163658583848447989162297777 122743937886335991871723333)
            ·
              refine ⟨23014488353687998475948125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122743937886335991871723333 23014488353687998475948125)
              ·
                refine ⟨8630433132632999428480547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23014488353687998475948125 8630433132632999428480547)
                ·
                  refine ⟨12945649698949499142720821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8630433132632999428480547 12945649698949499142720821)
                  ·
                    refine ⟨1213654659276515544630077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12945649698949499142720821 1213654659276515544630077)
                    ·
                      rfl

theorem cell23_7090752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 1, 5].length) (baseStart_7090752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090752 prefixEnd_7090752 := by exact prefixLift 7090752
  have htrace : WordTrace (prefixWord ++ tailWord_7090752) baseStart_7090752 baseEnd_7090752 := by
    simpa [prefixWord, tailWord_7090752, baseEnd_7090752] using wordTrace_append hprefix tailTrace_7090752
  have hstable : (prefixWord ++ tailWord_7090752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090752).length < 2 ^ (prefixWord ++ tailWord_7090752).sum := by decide
  have hdescent : baseEnd_7090752 < baseStart_7090752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090759 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 4, 3, 2]
def baseStart_7090759 : Nat := 118140960795 + 7090759 * 2 ^ 59
def prefixEnd_7090759 : Nat := 4983230072969 + 3 ^ 40 * 7090759 * 2
def baseEnd_7090759 : Nat := 3640967572194128106502699

theorem tailTrace_7090759 : CollatzResearch.WordTrace tailWord_7090759 prefixEnd_7090759 3640967572194128106502699 := by
  unfold tailWord_7090759
  simp only [CollatzResearch.WordTrace]
  refine ⟨258621227318398623069259331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172414151545599082046172887 258621227318398623069259331)
  ·
    refine ⟨387931840977597934603888997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258621227318398623069259331 387931840977597934603888997)
    ·
      refine ⟨72737220183299612738229187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 387931840977597934603888997 72737220183299612738229187)
      ·
        refine ⟨109105830274949419107343781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72737220183299612738229187 109105830274949419107343781)
        ·
          refine ⟨20457343176553016082626959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109105830274949419107343781 20457343176553016082626959)
          ·
            refine ⟨30686014764829524123940439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20457343176553016082626959 30686014764829524123940439)
            ·
              refine ⟨46029022147244286185910659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30686014764829524123940439 46029022147244286185910659)
              ·
                refine ⟨69043533220866429278865989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46029022147244286185910659 69043533220866429278865989)
                ·
                  refine ⟨12945662478912455489787373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69043533220866429278865989 12945662478912455489787373)
                  ·
                    refine ⟨4854623429592170808670265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12945662478912455489787373 4854623429592170808670265)
                    ·
                      refine ⟨3640967572194128106502699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4854623429592170808670265 3640967572194128106502699)
                      ·
                        rfl

theorem cell23_7090759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_7090759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090759 prefixEnd_7090759 := by exact prefixLift 7090759
  have htrace : WordTrace (prefixWord ++ tailWord_7090759) baseStart_7090759 baseEnd_7090759 := by
    simpa [prefixWord, tailWord_7090759, baseEnd_7090759] using wordTrace_append hprefix tailTrace_7090759
  have hstable : (prefixWord ++ tailWord_7090759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090759).length < 2 ^ (prefixWord ++ tailWord_7090759).sum := by decide
  have hdescent : baseEnd_7090759 < baseStart_7090759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090766 : List Nat := [4, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3]
def baseStart_7090766 : Nat := 118140960795 + 7090766 * 2 ^ 59
def prefixEnd_7090766 : Nat := 4983230072969 + 3 ^ 40 * 7090766 * 2
def baseEnd_7090766 : Nat := 3640971166558709579115167

theorem tailTrace_7090766 : CollatzResearch.WordTrace tailWord_7090766 prefixEnd_7090766 3640971166558709579115167 := by
  unfold tailWord_7090766
  simp only [CollatzResearch.WordTrace]
  refine ⟨32327685328671657908095519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172414321752915508843176101 32327685328671657908095519)
  ·
    refine ⟨48491527993007486862143279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32327685328671657908095519 48491527993007486862143279)
    ·
      refine ⟨72737291989511230293214919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48491527993007486862143279 72737291989511230293214919)
      ·
        refine ⟨109105937984266845439822379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72737291989511230293214919 109105937984266845439822379)
        ·
          refine ⟨163658906976400268159733569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109105937984266845439822379 163658906976400268159733569)
          ·
            refine ⟨122744180232300201119800177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163658906976400268159733569 122744180232300201119800177)
            ·
              refine ⟨92058135174225150839850133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122744180232300201119800177 92058135174225150839850133)
              ·
                refine ⟨4315225086291803945617975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92058135174225150839850133 4315225086291803945617975)
                ·
                  refine ⟨6472837629437705918426963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4315225086291803945617975 6472837629437705918426963)
                  ·
                    refine ⟨9709256444156558877640445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6472837629437705918426963 9709256444156558877640445)
                    ·
                      refine ⟨3640971166558709579115167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9709256444156558877640445 3640971166558709579115167)
                      ·
                        rfl

theorem cell23_7090766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_7090766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090766 prefixEnd_7090766 := by exact prefixLift 7090766
  have htrace : WordTrace (prefixWord ++ tailWord_7090766) baseStart_7090766 baseEnd_7090766 := by
    simpa [prefixWord, tailWord_7090766, baseEnd_7090766] using wordTrace_append hprefix tailTrace_7090766
  have hstable : (prefixWord ++ tailWord_7090766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090766).length < 2 ^ (prefixWord ++ tailWord_7090766).sum := by decide
  have hdescent : baseEnd_7090766 < baseStart_7090766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090786 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_7090786 : Nat := 118140960795 + 7090786 * 2 ^ 59
def prefixEnd_7090786 : Nat := 4983230072969 + 3 ^ 40 * 7090786 * 2
def baseEnd_7090786 : Nat := 1213660478723933166955025

theorem tailTrace_7090786 : CollatzResearch.WordTrace tailWord_7090786 prefixEnd_7090786 1213660478723933166955025 := by
  unfold tailWord_7090786
  simp only [CollatzResearch.WordTrace]
  refine ⟨64655553022325201670123053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172414808059533871120328141 64655553022325201670123053)
  ·
    refine ⟨24245832383371950626296145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64655553022325201670123053 24245832383371950626296145)
    ·
      refine ⟨18184374287528962969722109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24245832383371950626296145 18184374287528962969722109)
      ·
        refine ⟨6819140357823361113645791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18184374287528962969722109 6819140357823361113645791)
        ·
          refine ⟨10228710536735041670468687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6819140357823361113645791 10228710536735041670468687)
          ·
            refine ⟨15343065805102562505703031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10228710536735041670468687 15343065805102562505703031)
            ·
              refine ⟨23014598707653843758554547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15343065805102562505703031 23014598707653843758554547)
              ·
                refine ⟨34521898061480765637831821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23014598707653843758554547 34521898061480765637831821)
                ·
                  refine ⟨12945711773055287114186933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34521898061480765637831821 12945711773055287114186933)
                  ·
                    refine ⟨1213660478723933166955025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12945711773055287114186933 1213660478723933166955025)
                    ·
                      rfl

theorem cell23_7090786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_7090786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090786 prefixEnd_7090786 := by exact prefixLift 7090786
  have htrace : WordTrace (prefixWord ++ tailWord_7090786) baseStart_7090786 baseEnd_7090786 := by
    simpa [prefixWord, tailWord_7090786, baseEnd_7090786] using wordTrace_append hprefix tailTrace_7090786
  have hstable : (prefixWord ++ tailWord_7090786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090786).length < 2 ^ (prefixWord ++ tailWord_7090786).sum := by decide
  have hdescent : baseEnd_7090786 < baseStart_7090786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090789 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 3, 1, 4]
def baseStart_7090789 : Nat := 118140960795 + 7090789 * 2 ^ 59
def prefixEnd_7090789 : Nat := 4983230072969 + 3 ^ 40 * 7090789 * 2
def baseEnd_7090789 : Nat := 3640982976613762989127561

theorem tailTrace_7090789 : CollatzResearch.WordTrace tailWord_7090789 prefixEnd_7090789 3640982976613762989127561 := by
  unfold tailWord_7090789
  simp only [CollatzResearch.WordTrace]
  refine ⟨258622321508289938192851421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172414881005526625461900947 258622321508289938192851421)
  ·
    refine ⟨96983370565608726822319283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258622321508289938192851421 96983370565608726822319283)
    ·
      refine ⟨145475055848413090233478925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96983370565608726822319283 145475055848413090233478925)
      ·
        refine ⟨54553145943154908837554597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145475055848413090233478925 54553145943154908837554597)
        ·
          refine ⟨10228714864341545407041487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54553145943154908837554597 10228714864341545407041487)
          ·
            refine ⟨15343072296512318110562231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10228714864341545407041487 15343072296512318110562231)
            ·
              refine ⟨23014608444768477165843347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15343072296512318110562231 23014608444768477165843347)
              ·
                refine ⟨34521912667152715748765021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23014608444768477165843347 34521912667152715748765021)
                ·
                  refine ⟨12945717250182268405786883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34521912667152715748765021 12945717250182268405786883)
                  ·
                    refine ⟨19418575875273402608680325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12945717250182268405786883 19418575875273402608680325)
                    ·
                      refine ⟨3640982976613762989127561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19418575875273402608680325 3640982976613762989127561)
                      ·
                        rfl

theorem cell23_7090789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_7090789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090789 prefixEnd_7090789 := by exact prefixLift 7090789
  have htrace : WordTrace (prefixWord ++ tailWord_7090789) baseStart_7090789 baseEnd_7090789 := by
    simpa [prefixWord, tailWord_7090789, baseEnd_7090789] using wordTrace_append hprefix tailTrace_7090789
  have hstable : (prefixWord ++ tailWord_7090789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090789).length < 2 ^ (prefixWord ++ tailWord_7090789).sum := by decide
  have hdescent : baseEnd_7090789 < baseStart_7090789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090809 : List Nat := [1, 2, 1, 3, 3, 4, 1, 1, 1, 1, 5]
def baseStart_7090809 : Nat := 118140960795 + 7090809 * 2 ^ 59
def prefixEnd_7090809 : Nat := 4983230072969 + 3 ^ 40 * 7090809 * 2
def baseEnd_7090809 : Nat := 3640993246226852910877469

theorem tailTrace_7090809 : CollatzResearch.WordTrace tailWord_7090809 prefixEnd_7090809 3640993246226852910877469 := by
  unfold tailWord_7090809
  simp only [CollatzResearch.WordTrace]
  refine ⟨258623050968217481608579481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172415367312144987739052987 258623050968217481608579481)
  ·
    refine ⟨193967288226163111206434611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258623050968217481608579481 193967288226163111206434611)
    ·
      refine ⟨290950932339244666809651917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193967288226163111206434611 290950932339244666809651917)
      ·
        refine ⟨109106599627216750053619469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290950932339244666809651917 109106599627216750053619469)
        ·
          refine ⟨40914974860206281270107301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109106599627216750053619469 40914974860206281270107301)
          ·
            refine ⟨7671557786288677738145119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40914974860206281270107301 7671557786288677738145119)
            ·
              refine ⟨11507336679433016607217679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7671557786288677738145119 11507336679433016607217679)
              ·
                refine ⟨17261005019149524910826519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11507336679433016607217679 17261005019149524910826519)
                ·
                  refine ⟨25891507528724287366239779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17261005019149524910826519 25891507528724287366239779)
                  ·
                    refine ⟨38837261293086431049359669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25891507528724287366239779 38837261293086431049359669)
                    ·
                      refine ⟨3640993246226852910877469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38837261293086431049359669 3640993246226852910877469)
                      ·
                        rfl

theorem cell23_7090809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_7090809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090809 prefixEnd_7090809 := by exact prefixLift 7090809
  have htrace : WordTrace (prefixWord ++ tailWord_7090809) baseStart_7090809 baseEnd_7090809 := by
    simpa [prefixWord, tailWord_7090809, baseEnd_7090809] using wordTrace_append hprefix tailTrace_7090809
  have hstable : (prefixWord ++ tailWord_7090809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090809).length < 2 ^ (prefixWord ++ tailWord_7090809).sum := by decide
  have hdescent : baseEnd_7090809 < baseStart_7090809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090815 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 6]
def baseStart_7090815 : Nat := 118140960795 + 7090815 * 2 ^ 59
def prefixEnd_7090815 : Nat := 4983230072969 + 3 ^ 40 * 7090815 * 2
def baseEnd_7090815 : Nat := 3640996327110779887402441

theorem tailTrace_7090815 : CollatzResearch.WordTrace tailWord_7090815 prefixEnd_7090815 3640996327110779887402441 := by
  unfold tailWord_7090815
  simp only [CollatzResearch.WordTrace]
  refine ⟨258623269806195744633297899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172415513204130496422198599 258623269806195744633297899)
  ·
    refine ⟨387934904709293616949946849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258623269806195744633297899 387934904709293616949946849)
    ·
      refine ⟨290951178531970212712460137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387934904709293616949946849 290951178531970212712460137)
      ·
        refine ⟨218213383898977659534345103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290951178531970212712460137 218213383898977659534345103)
        ·
          refine ⟨327320075848466489301517655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218213383898977659534345103 327320075848466489301517655)
          ·
            refine ⟨490980113772699733952276483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327320075848466489301517655 490980113772699733952276483)
            ·
              refine ⟨736470170659049600928414725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490980113772699733952276483 736470170659049600928414725)
              ·
                refine ⟨138088156998571800174077761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 736470170659049600928414725 138088156998571800174077761)
                ·
                  refine ⟨103566117748928850130558321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138088156998571800174077761 103566117748928850130558321)
                  ·
                    refine ⟨77674588311696637597918741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103566117748928850130558321 77674588311696637597918741)
                    ·
                      refine ⟨3640996327110779887402441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77674588311696637597918741 3640996327110779887402441)
                      ·
                        rfl

theorem cell23_7090815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_7090815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090815 prefixEnd_7090815 := by exact prefixLift 7090815
  have htrace : WordTrace (prefixWord ++ tailWord_7090815) baseStart_7090815 baseEnd_7090815 := by
    simpa [prefixWord, tailWord_7090815, baseEnd_7090815] using wordTrace_append hprefix tailTrace_7090815
  have hstable : (prefixWord ++ tailWord_7090815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090815).length < 2 ^ (prefixWord ++ tailWord_7090815).sum := by decide
  have hdescent : baseEnd_7090815 < baseStart_7090815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090823 : List Nat := [1, 1, 4, 2, 1, 2, 3, 4, 1, 2, 2]
def baseStart_7090823 : Nat := 118140960795 + 7090823 * 2 ^ 59
def prefixEnd_7090823 : Nat := 4983230072969 + 3 ^ 40 * 7090823 * 2
def baseEnd_7090823 : Nat := 3641000434956015856102405

theorem tailTrace_7090823 : CollatzResearch.WordTrace tailWord_7090823 prefixEnd_7090823 3641000434956015856102405 := by
  unfold tailWord_7090823
  simp only [CollatzResearch.WordTrace]
  refine ⟨258623561590166761999589123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172415707726777841333059415 258623561590166761999589123)
  ·
    refine ⟨387935342385250142999383685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258623561590166761999589123 387935342385250142999383685)
    ·
      refine ⟨72737876697234401812384441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 387935342385250142999383685 72737876697234401812384441)
      ·
        refine ⟨54553407522925801359288331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72737876697234401812384441 54553407522925801359288331)
        ·
          refine ⟨81830111284388702038932497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54553407522925801359288331 81830111284388702038932497)
          ·
            refine ⟨61372583463291526529199373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81830111284388702038932497 61372583463291526529199373)
            ·
              refine ⟨23014718798734322448449765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61372583463291526529199373 23014718798734322448449765)
              ·
                refine ⟨4315259774762685459084331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23014718798734322448449765 4315259774762685459084331)
                ·
                  refine ⟨6472889662144028188626497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4315259774762685459084331 6472889662144028188626497)
                  ·
                    refine ⟨4854667246608021141469873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6472889662144028188626497 4854667246608021141469873)
                    ·
                      refine ⟨3641000434956015856102405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4854667246608021141469873 3641000434956015856102405)
                      ·
                        rfl

theorem cell23_7090823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_7090823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090823 prefixEnd_7090823 := by exact prefixLift 7090823
  have htrace : WordTrace (prefixWord ++ tailWord_7090823) baseStart_7090823 baseEnd_7090823 := by
    simpa [prefixWord, tailWord_7090823, baseEnd_7090823] using wordTrace_append hprefix tailTrace_7090823
  have hstable : (prefixWord ++ tailWord_7090823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090823).length < 2 ^ (prefixWord ++ tailWord_7090823).sum := by decide
  have hdescent : baseEnd_7090823 < baseStart_7090823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090836 : List Nat := [2, 4, 2, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_7090836 : Nat := 118140960795 + 7090836 * 2 ^ 59
def prefixEnd_7090836 : Nat := 4983230072969 + 3 ^ 40 * 7090836 * 2
def baseEnd_7090836 : Nat := 3641007110204524305239845

theorem tailTrace_7090836 : CollatzResearch.WordTrace tailWord_7090836 prefixEnd_7090836 3641007110204524305239845 := by
  unfold tailWord_7090836
  simp only [CollatzResearch.WordTrace]
  refine ⟨129312017869559832609906181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172416023826079776813208241 129312017869559832609906181)
  ·
    refine ⟨24246003350542468614357409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129312017869559832609906181 24246003350542468614357409)
    ·
      refine ⟨18184502512906851460768057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24246003350542468614357409 18184502512906851460768057)
      ·
        refine ⟨13638376884680138595576043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18184502512906851460768057 13638376884680138595576043)
        ·
          refine ⟨20457565327020207893364065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13638376884680138595576043 20457565327020207893364065)
          ·
            refine ⟨15343173995265155920023049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20457565327020207893364065 15343173995265155920023049)
            ·
              refine ⟨11507380496448866940017287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15343173995265155920023049 11507380496448866940017287)
              ·
                refine ⟨17261070744673300410025931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11507380496448866940017287 17261070744673300410025931)
                ·
                  refine ⟨25891606117009950615038897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17261070744673300410025931 25891606117009950615038897)
                  ·
                    refine ⟨19418704587757462961279173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25891606117009950615038897 19418704587757462961279173)
                    ·
                      refine ⟨3641007110204524305239845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19418704587757462961279173 3641007110204524305239845)
                      ·
                        rfl

theorem cell23_7090836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_7090836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090836 prefixEnd_7090836 := by exact prefixLift 7090836
  have htrace : WordTrace (prefixWord ++ tailWord_7090836) baseStart_7090836 baseEnd_7090836 := by
    simpa [prefixWord, tailWord_7090836, baseEnd_7090836] using wordTrace_append hprefix tailTrace_7090836
  have hstable : (prefixWord ++ tailWord_7090836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090836).length < 2 ^ (prefixWord ++ tailWord_7090836).sum := by decide
  have hdescent : baseEnd_7090836 < baseStart_7090836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090839 : List Nat := [1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 3]
def baseStart_7090839 : Nat := 118140960795 + 7090839 * 2 ^ 59
def prefixEnd_7090839 : Nat := 4983230072969 + 3 ^ 40 * 7090839 * 2
def baseEnd_7090839 : Nat := 3641008650646487793502331

theorem tailTrace_7090839 : CollatzResearch.WordTrace tailWord_7090839 prefixEnd_7090839 3641008650646487793502331 := by
  unfold tailWord_7090839
  simp only [CollatzResearch.WordTrace]
  refine ⟨258624145158108796732171571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172416096772072531154781047 258624145158108796732171571)
  ·
    refine ⟨387936217737163195098257357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258624145158108796732171571 387936217737163195098257357)
    ·
      refine ⟨145476081651436198161846509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387936217737163195098257357 145476081651436198161846509)
      ·
        refine ⟨54553530619288574310692441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145476081651436198161846509 54553530619288574310692441)
        ·
          refine ⟨40915147964466430733019331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54553530619288574310692441 40915147964466430733019331)
          ·
            refine ⟨61372721946699646099528997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40915147964466430733019331 61372721946699646099528997)
            ·
              refine ⟨11507385365006183643661687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61372721946699646099528997 11507385365006183643661687)
              ·
                refine ⟨17261078047509275465492531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11507385365006183643661687 17261078047509275465492531)
                ·
                  refine ⟨25891617071263913198238797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17261078047509275465492531 25891617071263913198238797)
                  ·
                    refine ⟨9709356401723967449339549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25891617071263913198238797 9709356401723967449339549)
                    ·
                      refine ⟨3641008650646487793502331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9709356401723967449339549 3641008650646487793502331)
                      ·
                        rfl

theorem cell23_7090839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_7090839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090839 prefixEnd_7090839 := by exact prefixLift 7090839
  have htrace : WordTrace (prefixWord ++ tailWord_7090839) baseStart_7090839 baseEnd_7090839 := by
    simpa [prefixWord, tailWord_7090839, baseEnd_7090839] using wordTrace_append hprefix tailTrace_7090839
  have hstable : (prefixWord ++ tailWord_7090839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090839).length < 2 ^ (prefixWord ++ tailWord_7090839).sum := by decide
  have hdescent : baseEnd_7090839 < baseStart_7090839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090852 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_7090852 : Nat := 118140960795 + 7090852 * 2 ^ 59
def prefixEnd_7090852 : Nat := 4983230072969 + 3 ^ 40 * 7090852 * 2
def baseEnd_7090852 : Nat := 3641015325894996242639771

theorem tailTrace_7090852 : CollatzResearch.WordTrace tailWord_7090852 prefixEnd_7090852 3641015325894996242639771 := by
  unfold tailWord_7090852
  simp only [CollatzResearch.WordTrace]
  refine ⟨129312309653530849976197405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172416412871374466634929873 129312309653530849976197405)
  ·
    refine ⟨48492116120074068741074027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129312309653530849976197405 48492116120074068741074027)
    ·
      refine ⟨72738174180111103111611041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48492116120074068741074027 72738174180111103111611041)
      ·
        refine ⟨54553630635083327333708281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72738174180111103111611041 54553630635083327333708281)
        ·
          refine ⟨40915222976312495500281211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54553630635083327333708281 40915222976312495500281211)
          ·
            refine ⟨61372834464468743250421817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40915222976312495500281211 61372834464468743250421817)
            ·
              refine ⟨46029625848351557437816363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61372834464468743250421817 46029625848351557437816363)
              ·
                refine ⟨69044438772527336156724545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46029625848351557437816363 69044438772527336156724545)
                ·
                  refine ⟨51783329079395502117543409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69044438772527336156724545 51783329079395502117543409)
                  ·
                    refine ⟨38837496809546626588157557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51783329079395502117543409 38837496809546626588157557)
                    ·
                      refine ⟨3641015325894996242639771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38837496809546626588157557 3641015325894996242639771)
                      ·
                        rfl

theorem cell23_7090852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_7090852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090852 prefixEnd_7090852 := by exact prefixLift 7090852
  have htrace : WordTrace (prefixWord ++ tailWord_7090852) baseStart_7090852 baseEnd_7090852 := by
    simpa [prefixWord, tailWord_7090852, baseEnd_7090852] using wordTrace_append hprefix tailTrace_7090852
  have hstable : (prefixWord ++ tailWord_7090852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090852).length < 2 ^ (prefixWord ++ tailWord_7090852).sum := by decide
  have hdescent : baseEnd_7090852 < baseStart_7090852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090900 : List Nat := [2, 4, 1, 3, 2, 1, 2, 2, 1, 3, 2]
def baseStart_7090900 : Nat := 118140960795 + 7090900 * 2 ^ 59
def prefixEnd_7090900 : Nat := 4983230072969 + 3 ^ 40 * 7090900 * 2
def baseEnd_7090900 : Nat := 3641039972966412054839551

theorem tailTrace_7090900 : CollatzResearch.WordTrace tailWord_7090900 prefixEnd_7090900 3641039972966412054839551 := by
  unfold tailWord_7090900
  simp only [CollatzResearch.WordTrace]
  refine ⟨129313185005443902075071077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172417580007258536100094769 129313185005443902075071077)
  ·
    refine ⟨24246222188520731639075827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129313185005443902075071077 24246222188520731639075827)
    ·
      refine ⟨36369333282781097458613741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24246222188520731639075827 36369333282781097458613741)
      ·
        refine ⟨13638499981042911546980153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36369333282781097458613741 13638499981042911546980153)
        ·
          refine ⟨10228874985782183660235115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13638499981042911546980153 10228874985782183660235115)
          ·
            refine ⟨15343312478673275490352673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10228874985782183660235115 15343312478673275490352673)
            ·
              refine ⟨11507484359004956617764505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15343312478673275490352673 11507484359004956617764505)
              ·
                refine ⟨8630613269253717463323379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11507484359004956617764505 8630613269253717463323379)
                ·
                  refine ⟨12945919903880576194985069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8630613269253717463323379 12945919903880576194985069)
                  ·
                    refine ⟨4854719963955216073119401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12945919903880576194985069 4854719963955216073119401)
                    ·
                      refine ⟨3641039972966412054839551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4854719963955216073119401 3641039972966412054839551)
                      ·
                        rfl

theorem cell23_7090900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_7090900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090900 prefixEnd_7090900 := by exact prefixLift 7090900
  have htrace : WordTrace (prefixWord ++ tailWord_7090900) baseStart_7090900 baseEnd_7090900 := by
    simpa [prefixWord, tailWord_7090900, baseEnd_7090900] using wordTrace_append hprefix tailTrace_7090900
  have hstable : (prefixWord ++ tailWord_7090900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090900).length < 2 ^ (prefixWord ++ tailWord_7090900).sum := by decide
  have hdescent : baseEnd_7090900 < baseStart_7090900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090936 : List Nat := [2, 1, 2, 1, 1, 2, 7, 2, 5]
def baseStart_7090936 : Nat := 118140960795 + 7090936 * 2 ^ 59
def prefixEnd_7090936 : Nat := 4983230072969 + 3 ^ 40 * 7090936 * 2
def baseEnd_7090936 : Nat := 404562050918885990443265

theorem tailTrace_7090936 : CollatzResearch.WordTrace tailWord_7090936 prefixEnd_7090936 404562050918885990443265 := by
  unfold tailWord_7090936
  simp only [CollatzResearch.WordTrace]
  refine ⟨129313841519378691149226331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172418455359171588198968441 129313841519378691149226331)
  ·
    refine ⟨193970762279068036723839497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129313841519378691149226331 193970762279068036723839497)
    ·
      refine ⟨145478071709301027542879623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193970762279068036723839497 145478071709301027542879623)
      ·
        refine ⟨218217107563951541314319435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145478071709301027542879623 218217107563951541314319435)
        ·
          refine ⟨327325661345927311971479153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218217107563951541314319435 327325661345927311971479153)
          ·
            refine ⟨245494246009445483978609365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327325661345927311971479153 245494246009445483978609365)
            ·
              refine ⟨5753771390846378530748657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 245494246009445483978609365 5753771390846378530748657)
              ·
                refine ⟨4315328543134783898061493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5753771390846378530748657 4315328543134783898061493)
                ·
                  refine ⟨404562050918885990443265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4315328543134783898061493 404562050918885990443265)
                  ·
                    rfl

theorem cell23_7090936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 5].length) (baseStart_7090936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090936 prefixEnd_7090936 := by exact prefixLift 7090936
  have htrace : WordTrace (prefixWord ++ tailWord_7090936) baseStart_7090936 baseEnd_7090936 := by
    simpa [prefixWord, tailWord_7090936, baseEnd_7090936] using wordTrace_append hprefix tailTrace_7090936
  have hstable : (prefixWord ++ tailWord_7090936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090936).length < 2 ^ (prefixWord ++ tailWord_7090936).sum := by decide
  have hdescent : baseEnd_7090936 < baseStart_7090936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090969 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 3, 6, 2]
def baseStart_7090969 : Nat := 118140960795 + 7090969 * 2 ^ 59
def prefixEnd_7090969 : Nat := 4983230072969 + 3 ^ 40 * 7090969 * 2
def baseEnd_7090969 : Nat := 3641075403131572284876733

theorem tailTrace_7090969 : CollatzResearch.WordTrace tailWord_7090969 prefixEnd_7090969 3641075403131572284876733 := by
  unfold tailWord_7090969
  simp only [CollatzResearch.WordTrace]
  refine ⟨258628886647637828934403961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172419257765091885956269307 258628886647637828934403961)
  ·
    refine ⟨193971664985728371700802971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258628886647637828934403961 193971664985728371700802971)
    ·
      refine ⟨290957497478592557551204457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193971664985728371700802971 290957497478592557551204457)
      ·
        refine ⟨218218123108944418163403343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290957497478592557551204457 218218123108944418163403343)
        ·
          refine ⟨327327184663416627245105015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218218123108944418163403343 327327184663416627245105015)
          ·
            refine ⟨490990776995124940867657523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327327184663416627245105015 490990776995124940867657523)
            ·
              refine ⟨736486165492687411301486285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490990776995124940867657523 736486165492687411301486285)
              ·
                refine ⟨276182312059757779238057357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 736486165492687411301486285 276182312059757779238057357)
                ·
                  refine ⟨103568367022409167214271509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276182312059757779238057357 103568367022409167214271509)
                  ·
                    refine ⟨4854767204175429713168977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103568367022409167214271509 4854767204175429713168977)
                    ·
                      refine ⟨3641075403131572284876733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4854767204175429713168977 3641075403131572284876733)
                      ·
                        rfl

theorem cell23_7090969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 6, 2].length) (baseStart_7090969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090969 prefixEnd_7090969 := by exact prefixLift 7090969
  have htrace : WordTrace (prefixWord ++ tailWord_7090969) baseStart_7090969 baseEnd_7090969 := by
    simpa [prefixWord, tailWord_7090969, baseEnd_7090969] using wordTrace_append hprefix tailTrace_7090969
  have hstable : (prefixWord ++ tailWord_7090969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090969).length < 2 ^ (prefixWord ++ tailWord_7090969).sum := by decide
  have hdescent : baseEnd_7090969 < baseStart_7090969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7090992 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 8]
def baseStart_7090992 : Nat := 118140960795 + 7090992 * 2 ^ 59
def prefixEnd_7090992 : Nat := 4983230072969 + 3 ^ 40 * 7090992 * 2
def baseEnd_7090992 : Nat := 404565245909625077209903

theorem tailTrace_7090992 : CollatzResearch.WordTrace tailWord_7090992 prefixEnd_7090992 404565245909625077209903 := by
  unfold tailWord_7090992
  simp only [CollatzResearch.WordTrace]
  refine ⟨129314862763277251931245615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172419817017703002574994153 129314862763277251931245615)
  ·
    refine ⟨193972294144915877896868423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129314862763277251931245615 193972294144915877896868423)
    ·
      refine ⟨290958441217373816845302635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193972294144915877896868423 290958441217373816845302635)
      ·
        refine ⟨436437661826060725267953953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290958441217373816845302635 436437661826060725267953953)
        ·
          refine ⟨327328246369545543950965465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436437661826060725267953953 327328246369545543950965465)
          ·
            refine ⟨245496184777159157963224099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327328246369545543950965465 245496184777159157963224099)
            ·
              refine ⟨368244277165738736944836149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245496184777159157963224099 368244277165738736944836149)
              ·
                refine ⟨34522900984288006588578389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 368244277165738736944836149 34522900984288006588578389)
                ·
                  refine ⟨404565245909625077209903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34522900984288006588578389 404565245909625077209903)
                  ·
                    rfl

theorem cell23_7090992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 8].length) (baseStart_7090992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7090992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7090992 prefixEnd_7090992 := by exact prefixLift 7090992
  have htrace : WordTrace (prefixWord ++ tailWord_7090992) baseStart_7090992 baseEnd_7090992 := by
    simpa [prefixWord, tailWord_7090992, baseEnd_7090992] using wordTrace_append hprefix tailTrace_7090992
  have hstable : (prefixWord ++ tailWord_7090992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7090992).length < 2 ^ (prefixWord ++ tailWord_7090992).sum := by decide
  have hdescent : baseEnd_7090992 < baseStart_7090992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7090992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091059 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 4]
def baseStart_7091059 : Nat := 118140960795 + 7091059 * 2 ^ 59
def prefixEnd_7091059 : Nat := 4983230072969 + 3 ^ 40 * 7091059 * 2
def baseEnd_7091059 : Nat := 3641121616390476932751319

theorem tailTrace_7091059 : CollatzResearch.WordTrace tailWord_7091059 prefixEnd_7091059 3641121616390476932751319 := by
  unfold tailWord_7091059
  simp only [CollatzResearch.WordTrace]
  refine ⟨258632169217311774305180231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172421446144874516203453487 258632169217311774305180231)
  ·
    refine ⟨387948253825967661457770347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258632169217311774305180231 387948253825967661457770347)
    ·
      refine ⟨581922380738951492186655521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387948253825967661457770347 581922380738951492186655521)
      ·
        refine ⟨436441785554213619139991641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581922380738951492186655521 436441785554213619139991641)
        ·
          refine ⟨327331339165660214354993731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436441785554213619139991641 327331339165660214354993731)
          ·
            refine ⟨490997008748490321532490597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327331339165660214354993731 490997008748490321532490597)
            ·
              refine ⟨92061939140341935287341987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 490997008748490321532490597 92061939140341935287341987)
              ·
                refine ⟨138092908710512902931012981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92061939140341935287341987 138092908710512902931012981)
                ·
                  refine ⟨12946210191610584649782467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138092908710512902931012981 12946210191610584649782467)
                  ·
                    refine ⟨19419315287415876974673701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12946210191610584649782467 19419315287415876974673701)
                    ·
                      refine ⟨3641121616390476932751319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19419315287415876974673701 3641121616390476932751319)
                      ·
                        rfl

theorem cell23_7091059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 4].length) (baseStart_7091059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091059 prefixEnd_7091059 := by exact prefixLift 7091059
  have htrace : WordTrace (prefixWord ++ tailWord_7091059) baseStart_7091059 baseEnd_7091059 := by
    simpa [prefixWord, tailWord_7091059, baseEnd_7091059] using wordTrace_append hprefix tailTrace_7091059
  have hstable : (prefixWord ++ tailWord_7091059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091059).length < 2 ^ (prefixWord ++ tailWord_7091059).sum := by decide
  have hdescent : baseEnd_7091059 < baseStart_7091059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091076 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 1, 8, 2]
def baseStart_7091076 : Nat := 118140960795 + 7091076 * 2 ^ 59
def prefixEnd_7091076 : Nat := 4983230072969 + 3 ^ 40 * 7091076 * 2
def baseEnd_7091076 : Nat := 3641130345561603366238741

theorem tailTrace_7091076 : CollatzResearch.WordTrace tailWord_7091076 prefixEnd_7091076 3641130345561603366238741 := by
  unfold tailWord_7091076
  simp only [CollatzResearch.WordTrace]
  refine ⟨129316394629125093104274541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172421859505500124139032721 129316394629125093104274541)
  ·
    refine ⟨48493647985921909914102953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129316394629125093104274541 48493647985921909914102953)
    ·
      refine ⟨36370235989441432435577215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48493647985921909914102953 36370235989441432435577215)
      ·
        refine ⟨54555353984162148653365823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36370235989441432435577215 54555353984162148653365823)
        ·
          refine ⟨81833030976243222980048735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54555353984162148653365823 81833030976243222980048735)
          ·
            refine ⟨122749546464364834470073103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81833030976243222980048735 122749546464364834470073103)
            ·
              refine ⟨184124319696547251705109655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122749546464364834470073103 184124319696547251705109655)
              ·
                refine ⟨276186479544820877557664483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184124319696547251705109655 276186479544820877557664483)
                ·
                  refine ⟨414279719317231316336496725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276186479544820877557664483 414279719317231316336496725)
                  ·
                    refine ⟨4854840460748804488318321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 414279719317231316336496725 4854840460748804488318321)
                    ·
                      refine ⟨3641130345561603366238741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4854840460748804488318321 3641130345561603366238741)
                      ·
                        rfl

theorem cell23_7091076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_7091076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091076 prefixEnd_7091076 := by exact prefixLift 7091076
  have htrace : WordTrace (prefixWord ++ tailWord_7091076) baseStart_7091076 baseEnd_7091076 := by
    simpa [prefixWord, tailWord_7091076, baseEnd_7091076] using wordTrace_append hprefix tailTrace_7091076
  have hstable : (prefixWord ++ tailWord_7091076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091076).length < 2 ^ (prefixWord ++ tailWord_7091076).sum := by decide
  have hdescent : baseEnd_7091076 < baseStart_7091076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091089 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 4]
def baseStart_7091089 : Nat := 118140960795 + 7091089 * 2 ^ 59
def prefixEnd_7091089 : Nat := 4983230072969 + 3 ^ 40 * 7091089 * 2
def baseEnd_7091089 : Nat := 3641137020810111815376181

theorem tailTrace_7091089 : CollatzResearch.WordTrace tailWord_7091089 prefixEnd_7091089 3641137020810111815376181 := by
  unfold tailWord_7091089
  simp only [CollatzResearch.WordTrace]
  refine ⟨258633263407203089428772321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172422175604802059619181547 258633263407203089428772321)
  ·
    refine ⟨193974947555402317071579241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258633263407203089428772321 193974947555402317071579241)
    ·
      refine ⟨145481210666551737803684431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193974947555402317071579241 145481210666551737803684431)
      ·
        refine ⟨218221815999827606705526647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145481210666551737803684431 218221815999827606705526647)
        ·
          refine ⟨327332723999741410058289971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218221815999827606705526647 327332723999741410058289971)
          ·
            refine ⟨490999085999612115087434957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327332723999741410058289971 490999085999612115087434957)
            ·
              refine ⟨184124657249854543157788109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 490999085999612115087434957 184124657249854543157788109)
              ·
                refine ⟨69046746468695453684170541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184124657249854543157788109 69046746468695453684170541)
                ·
                  refine ⟨25892529925760795131563953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69046746468695453684170541 25892529925760795131563953)
                  ·
                    refine ⟨19419397444320596348672965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25892529925760795131563953 19419397444320596348672965)
                    ·
                      refine ⟨3641137020810111815376181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19419397444320596348672965 3641137020810111815376181)
                      ·
                        rfl

theorem cell23_7091089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_7091089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091089 prefixEnd_7091089 := by exact prefixLift 7091089
  have htrace : WordTrace (prefixWord ++ tailWord_7091089) baseStart_7091089 baseEnd_7091089 := by
    simpa [prefixWord, tailWord_7091089, baseEnd_7091089] using wordTrace_append hprefix tailTrace_7091089
  have hstable : (prefixWord ++ tailWord_7091089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091089).length < 2 ^ (prefixWord ++ tailWord_7091089).sum := by decide
  have hdescent : baseEnd_7091089 < baseStart_7091089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091106 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_7091106 : Nat := 118140960795 + 7091106 * 2 ^ 59
def prefixEnd_7091106 : Nat := 4983230072969 + 3 ^ 40 * 7091106 * 2
def baseEnd_7091106 : Nat := 3641145749981238248863603

theorem tailTrace_7091106 : CollatzResearch.WordTrace tailWord_7091106 prefixEnd_7091106 3641145749981238248863603 := by
  unfold tailWord_7091106
  simp only [CollatzResearch.WordTrace]
  refine ⟨64658470862035375333035293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172422588965427667554760781 64658470862035375333035293)
  ·
    refine ⟨24246926573263265749888235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64658470862035375333035293 24246926573263265749888235)
    ·
      refine ⟨36370389859894898624832353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24246926573263265749888235 36370389859894898624832353)
      ·
        refine ⟨27277792394921173968624265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36370389859894898624832353 27277792394921173968624265)
        ·
          refine ⟨20458344296190880476468199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27277792394921173968624265 20458344296190880476468199)
          ·
            refine ⟨30687516444286320714702299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20458344296190880476468199 30687516444286320714702299)
            ·
              refine ⟨46031274666429481072053449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30687516444286320714702299 46031274666429481072053449)
              ·
                refine ⟨34523455999822110804040087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46031274666429481072053449 34523455999822110804040087)
                ·
                  refine ⟨51785183999733166206060131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34523455999822110804040087 51785183999733166206060131)
                  ·
                    refine ⟨77677775999599749309090197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51785183999733166206060131 77677775999599749309090197)
                    ·
                      refine ⟨3641145749981238248863603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77677775999599749309090197 3641145749981238248863603)
                      ·
                        rfl

theorem cell23_7091106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_7091106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091106 prefixEnd_7091106 := by exact prefixLift 7091106
  have htrace : WordTrace (prefixWord ++ tailWord_7091106) baseStart_7091106 baseEnd_7091106 := by
    simpa [prefixWord, tailWord_7091106, baseEnd_7091106] using wordTrace_append hprefix tailTrace_7091106
  have hstable : (prefixWord ++ tailWord_7091106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091106).length < 2 ^ (prefixWord ++ tailWord_7091106).sum := by decide
  have hdescent : baseEnd_7091106 < baseStart_7091106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091140 : List Nat := [2, 3, 3, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_7091140 : Nat := 118140960795 + 7091140 * 2 ^ 59
def prefixEnd_7091140 : Nat := 4983230072969 + 3 ^ 40 * 7091140 * 2
def baseEnd_7091140 : Nat := 3641163208323491115838447

theorem tailTrace_7091140 : CollatzResearch.WordTrace tailWord_7091140 prefixEnd_7091140 3641163208323491115838447 := by
  unfold tailWord_7091140
  simp only [CollatzResearch.WordTrace]
  refine ⟨129317561765009162569439437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172423415686678883425919249 129317561765009162569439437)
  ·
    refine ⟨48494085661878435963539789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129317561765009162569439437 48494085661878435963539789)
    ·
      refine ⟨18185282123204413486327421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48494085661878435963539789 18185282123204413486327421)
      ·
        refine ⟨6819480796201655057372783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18185282123204413486327421 6819480796201655057372783)
        ·
          refine ⟨10229221194302482586059175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6819480796201655057372783 10229221194302482586059175)
          ·
            refine ⟨15343831791453723879088763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10229221194302482586059175 15343831791453723879088763)
            ·
              refine ⟨23015747687180585818633145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15343831791453723879088763 23015747687180585818633145)
              ·
                refine ⟨17261810765385439363974859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23015747687180585818633145 17261810765385439363974859)
                ·
                  refine ⟨25892716148078159045962289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17261810765385439363974859 25892716148078159045962289)
                  ·
                    refine ⟨19419537111058619284471717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25892716148078159045962289 19419537111058619284471717)
                    ·
                      refine ⟨3641163208323491115838447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19419537111058619284471717 3641163208323491115838447)
                      ·
                        rfl

theorem cell23_7091140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_7091140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091140 prefixEnd_7091140 := by exact prefixLift 7091140
  have htrace : WordTrace (prefixWord ++ tailWord_7091140) baseStart_7091140 baseEnd_7091140 := by
    simpa [prefixWord, tailWord_7091140, baseEnd_7091140] using wordTrace_append hprefix tailTrace_7091140
  have hstable : (prefixWord ++ tailWord_7091140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091140).length < 2 ^ (prefixWord ++ tailWord_7091140).sum := by decide
  have hdescent : baseEnd_7091140 < baseStart_7091140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091160 : List Nat := [2, 1, 2, 2, 2, 4, 2, 2, 2, 1, 3]
def baseStart_7091160 : Nat := 118140960795 + 7091160 * 2 ^ 59
def prefixEnd_7091160 : Nat := 4983230072969 + 3 ^ 40 * 7091160 * 2
def baseEnd_7091160 : Nat := 3641173477936581037588355

theorem tailTrace_7091160 : CollatzResearch.WordTrace tailWord_7091160 prefixEnd_7091160 3641173477936581037588355 := by
  unfold tailWord_7091160
  simp only [CollatzResearch.WordTrace]
  refine ⟨129317926494972934277303467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172423901993297245703071289 129317926494972934277303467)
  ·
    refine ⟨193976889742459401415955201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129317926494972934277303467 193976889742459401415955201)
    ·
      refine ⟨145482667306844551061966401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193976889742459401415955201 145482667306844551061966401)
      ·
        refine ⟨109112000480133413296474801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145482667306844551061966401 109112000480133413296474801)
        ·
          refine ⟨81834000360100059972356101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109112000480133413296474801 81834000360100059972356101)
          ·
            refine ⟨15343875067518761244816769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81834000360100059972356101 15343875067518761244816769)
            ·
              refine ⟨11507906300639070933612577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15343875067518761244816769 11507906300639070933612577)
              ·
                refine ⟨8630929725479303200209433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11507906300639070933612577 8630929725479303200209433)
                ·
                  refine ⟨6473197294109477400157075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8630929725479303200209433 6473197294109477400157075)
                  ·
                    refine ⟨9709795941164216100235613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6473197294109477400157075 9709795941164216100235613)
                    ·
                      refine ⟨3641173477936581037588355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9709795941164216100235613 3641173477936581037588355)
                      ·
                        rfl

theorem cell23_7091160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_7091160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091160 prefixEnd_7091160 := by exact prefixLift 7091160
  have htrace : WordTrace (prefixWord ++ tailWord_7091160) baseStart_7091160 baseEnd_7091160 := by
    simpa [prefixWord, tailWord_7091160, baseEnd_7091160] using wordTrace_append hprefix tailTrace_7091160
  have hstable : (prefixWord ++ tailWord_7091160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091160).length < 2 ^ (prefixWord ++ tailWord_7091160).sum := by decide
  have hdescent : baseEnd_7091160 < baseStart_7091160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091183 : List Nat := [1, 1, 2, 1, 4, 3, 1, 3, 1, 4, 2]
def baseStart_7091183 : Nat := 118140960795 + 7091183 * 2 ^ 59
def prefixEnd_7091183 : Nat := 4983230072969 + 3 ^ 40 * 7091183 * 2
def baseEnd_7091183 : Nat := 3641185287991634447600749

theorem tailTrace_7091183 : CollatzResearch.WordTrace tailWord_7091183 prefixEnd_7091183 3641185287991634447600749 := by
  unfold tailWord_7091183
  simp only [CollatzResearch.WordTrace]
  refine ⟨258636691868862543482694203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172424461245908362321796135 258636691868862543482694203)
  ·
    refine ⟨387955037803293815224041305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258636691868862543482694203 387955037803293815224041305)
    ·
      refine ⟨290966278352470361418030979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387955037803293815224041305 290966278352470361418030979)
      ·
        refine ⟨436449417528705542127046469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290966278352470361418030979 436449417528705542127046469)
        ·
          refine ⟨81834265786632289148821213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 436449417528705542127046469 81834265786632289148821213)
          ·
            refine ⟨30687849669987108430807955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81834265786632289148821213 30687849669987108430807955)
            ·
              refine ⟨46031774504980662646211933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30687849669987108430807955 46031774504980662646211933)
              ·
                refine ⟨17261915439367748492329475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46031774504980662646211933 17261915439367748492329475)
                ·
                  refine ⟨25892873159051622738494213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17261915439367748492329475 25892873159051622738494213)
                  ·
                    refine ⟨4854913717322179263467665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25892873159051622738494213 4854913717322179263467665)
                    ·
                      refine ⟨3641185287991634447600749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4854913717322179263467665 3641185287991634447600749)
                      ·
                        rfl

theorem cell23_7091183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 4, 2].length) (baseStart_7091183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091183 prefixEnd_7091183 := by exact prefixLift 7091183
  have htrace : WordTrace (prefixWord ++ tailWord_7091183) baseStart_7091183 baseEnd_7091183 := by
    simpa [prefixWord, tailWord_7091183, baseEnd_7091183] using wordTrace_append hprefix tailTrace_7091183
  have hstable : (prefixWord ++ tailWord_7091183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091183).length < 2 ^ (prefixWord ++ tailWord_7091183).sum := by decide
  have hdescent : baseEnd_7091183 < baseStart_7091183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091199 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 7]
def baseStart_7091199 : Nat := 118140960795 + 7091199 * 2 ^ 59
def prefixEnd_7091199 : Nat := 4983230072969 + 3 ^ 40 * 7091199 * 2
def baseEnd_7091199 : Nat := 3641193503682106385000675

theorem tailTrace_7091199 : CollatzResearch.WordTrace tailWord_7091199 prefixEnd_7091199 3641193503682106385000675 := by
  unfold tailWord_7091199
  simp only [CollatzResearch.WordTrace]
  refine ⟨258637275436804578215276651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172424850291203052143517767 258637275436804578215276651)
  ·
    refine ⟨387955913155206867322914977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258637275436804578215276651 387955913155206867322914977)
    ·
      refine ⟨290966934866405150492186233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387955913155206867322914977 290966934866405150492186233)
      ·
        refine ⟨218225201149803862869139675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290966934866405150492186233 218225201149803862869139675)
        ·
          refine ⟨327337801724705794303709513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218225201149803862869139675 327337801724705794303709513)
          ·
            refine ⟨245503351293529345727782135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327337801724705794303709513 245503351293529345727782135)
            ·
              refine ⟨368255026940294018591673203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245503351293529345727782135 368255026940294018591673203)
              ·
                refine ⟨552382540410441027887509805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368255026940294018591673203 552382540410441027887509805)
                ·
                  refine ⟨207143452653915385457816177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552382540410441027887509805 207143452653915385457816177)
                  ·
                    refine ⟨155357589490436539093362133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 207143452653915385457816177 155357589490436539093362133)
                    ·
                      refine ⟨3641193503682106385000675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155357589490436539093362133 3641193503682106385000675)
                      ·
                        rfl

theorem cell23_7091199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_7091199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091199 prefixEnd_7091199 := by exact prefixLift 7091199
  have htrace : WordTrace (prefixWord ++ tailWord_7091199) baseStart_7091199 baseEnd_7091199 := by
    simpa [prefixWord, tailWord_7091199, baseEnd_7091199] using wordTrace_append hprefix tailTrace_7091199
  have hstable : (prefixWord ++ tailWord_7091199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091199).length < 2 ^ (prefixWord ++ tailWord_7091199).sum := by decide
  have hdescent : baseEnd_7091199 < baseStart_7091199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091223 : List Nat := [1, 1, 3, 5, 1, 2, 2, 1, 7]
def baseStart_7091223 : Nat := 118140960795 + 7091223 * 2 ^ 59
def prefixEnd_7091223 : Nat := 4983230072969 + 3 ^ 40 * 7091223 * 2
def baseEnd_7091223 : Nat := 404578425246423810122285

theorem tailTrace_7091223 : CollatzResearch.WordTrace tailWord_7091223 prefixEnd_7091223 404578425246423810122285 := by
  unfold tailWord_7091223
  simp only [CollatzResearch.WordTrace]
  refine ⟨258638150788717630314150323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172425433859145086876100215 258638150788717630314150323)
  ·
    refine ⟨387957226183076445471225485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258638150788717630314150323 387957226183076445471225485)
    ·
      refine ⟨145483959818653667051709557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387957226183076445471225485 145483959818653667051709557)
      ·
        refine ⟨13639121232998781286097771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145483959818653667051709557 13639121232998781286097771)
        ·
          refine ⟨20458681849498171929146657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13639121232998781286097771 20458681849498171929146657)
          ·
            refine ⟨15344011387123628946859993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20458681849498171929146657 15344011387123628946859993)
            ·
              refine ⟨11508008540342721710144995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15344011387123628946859993 11508008540342721710144995)
              ·
                refine ⟨17262012810514082565217493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11508008540342721710144995 17262012810514082565217493)
                ·
                  refine ⟨404578425246423810122285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17262012810514082565217493 404578425246423810122285)
                  ·
                    rfl

theorem cell23_7091223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 7].length) (baseStart_7091223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091223 prefixEnd_7091223 := by exact prefixLift 7091223
  have htrace : WordTrace (prefixWord ++ tailWord_7091223) baseStart_7091223 baseEnd_7091223 := by
    simpa [prefixWord, tailWord_7091223, baseEnd_7091223] using wordTrace_append hprefix tailTrace_7091223
  have hstable : (prefixWord ++ tailWord_7091223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091223).length < 2 ^ (prefixWord ++ tailWord_7091223).sum := by decide
  have hdescent : baseEnd_7091223 < baseStart_7091223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091233 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 2, 3, 3]
def baseStart_7091233 : Nat := 118140960795 + 7091233 * 2 ^ 59
def prefixEnd_7091233 : Nat := 4983230072969 + 3 ^ 40 * 7091233 * 2
def baseEnd_7091233 : Nat := 3641210962024359251975519

theorem tailTrace_7091233 : CollatzResearch.WordTrace tailWord_7091233 prefixEnd_7091233 3641210962024359251975519 := by
  unfold tailWord_7091233
  simp only [CollatzResearch.WordTrace]
  refine ⟨258638515518681402022014353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172425677012454268014676235 258638515518681402022014353)
  ·
    refine ⟨193978886639011051516510765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258638515518681402022014353 193978886639011051516510765)
    ·
      refine ⟨72742082489629144318691537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193978886639011051516510765 72742082489629144318691537)
      ·
        refine ⟨54556561867221858239018653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72742082489629144318691537 54556561867221858239018653)
        ·
          refine ⟨20458710700208196839631995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54556561867221858239018653 20458710700208196839631995)
          ·
            refine ⟨30688066050312295259447993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20458710700208196839631995 30688066050312295259447993)
            ·
              refine ⟨23016049537734221444585995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30688066050312295259447993 23016049537734221444585995)
              ·
                refine ⟨34524074306601332166878993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23016049537734221444585995 34524074306601332166878993)
                ·
                  refine ⟨25893055729950999125159245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34524074306601332166878993 25893055729950999125159245)
                  ·
                    refine ⟨9709895898731624671934717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25893055729950999125159245 9709895898731624671934717)
                    ·
                      refine ⟨3641210962024359251975519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9709895898731624671934717 3641210962024359251975519)
                      ·
                        rfl

theorem cell23_7091233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_7091233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091233 prefixEnd_7091233 := by exact prefixLift 7091233
  have htrace : WordTrace (prefixWord ++ tailWord_7091233) baseStart_7091233 baseEnd_7091233 := by
    simpa [prefixWord, tailWord_7091233, baseEnd_7091233] using wordTrace_append hprefix tailTrace_7091233
  have hstable : (prefixWord ++ tailWord_7091233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091233).length < 2 ^ (prefixWord ++ tailWord_7091233).sum := by decide
  have hdescent : baseEnd_7091233 < baseStart_7091233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091234 : List Nat := [3, 3, 1, 1, 1, 4, 3, 1, 2, 2, 2]
def baseStart_7091234 : Nat := 118140960795 + 7091234 * 2 ^ 59
def prefixEnd_7091234 : Nat := 4983230072969 + 3 ^ 40 * 7091234 * 2
def baseEnd_7091234 : Nat := 3641211475505013748063015

theorem tailTrace_7091234 : CollatzResearch.WordTrace tailWord_7091234 prefixEnd_7091234 3641211475505013748063015 := by
  unfold tailWord_7091234
  simp only [CollatzResearch.WordTrace]
  refine ⟨64659637997919444798200189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172425701327785186128533837 64659637997919444798200189)
  ·
    refine ⟨24247364249219791799325071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64659637997919444798200189 24247364249219791799325071)
    ·
      refine ⟨36371046373829687698987607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24247364249219791799325071 36371046373829687698987607)
      ·
        refine ⟨54556569560744531548481411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36371046373829687698987607 54556569560744531548481411)
        ·
          refine ⟨81834854341116797322722117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54556569560744531548481411 81834854341116797322722117)
          ·
            refine ⟨15344035188959399498010397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81834854341116797322722117 15344035188959399498010397)
            ·
              refine ⟨5754013195859774811753899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15344035188959399498010397 5754013195859774811753899)
              ·
                refine ⟨8631019793789662217630849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5754013195859774811753899 8631019793789662217630849)
                ·
                  refine ⟨6473264845342246663223137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8631019793789662217630849 6473264845342246663223137)
                  ·
                    refine ⟨4854948634006684997417353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6473264845342246663223137 4854948634006684997417353)
                    ·
                      refine ⟨3641211475505013748063015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4854948634006684997417353 3641211475505013748063015)
                      ·
                        rfl

theorem cell23_7091234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_7091234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091234 prefixEnd_7091234 := by exact prefixLift 7091234
  have htrace : WordTrace (prefixWord ++ tailWord_7091234) baseStart_7091234 baseEnd_7091234 := by
    simpa [prefixWord, tailWord_7091234, baseEnd_7091234] using wordTrace_append hprefix tailTrace_7091234
  have hstable : (prefixWord ++ tailWord_7091234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091234).length < 2 ^ (prefixWord ++ tailWord_7091234).sum := by decide
  have hdescent : baseEnd_7091234 < baseStart_7091234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091270 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_7091270 : Nat := 118140960795 + 7091270 * 2 ^ 59
def prefixEnd_7091270 : Nat := 4983230072969 + 3 ^ 40 * 7091270 * 2
def baseEnd_7091270 : Nat := 1213743320269525202404283

theorem tailTrace_7091270 : CollatzResearch.WordTrace tailWord_7091270 prefixEnd_7091270 1213743320269525202404283 := by
  unfold tailWord_7091270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8082495781860854916909727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 172426576679698238227407509 8082495781860854916909727)
  ·
    refine ⟨12123743672791282375364591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8082495781860854916909727 12123743672791282375364591)
    ·
      refine ⟨18185615509186923563046887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12123743672791282375364591 18185615509186923563046887)
      ·
        refine ⟨27278423263780385344570331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18185615509186923563046887 27278423263780385344570331)
        ·
          refine ⟨40917634895670578016855497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27278423263780385344570331 40917634895670578016855497)
          ·
            refine ⟨30688226171752933512641623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40917634895670578016855497 30688226171752933512641623)
            ·
              refine ⟨46032339257629400268962435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30688226171752933512641623 46032339257629400268962435)
              ·
                refine ⟨69048508886444100403443653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46032339257629400268962435 69048508886444100403443653)
                ·
                  refine ⟨12946595416208268825645685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69048508886444100403443653 12946595416208268825645685)
                  ·
                    refine ⟨1213743320269525202404283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12946595416208268825645685 1213743320269525202404283)
                    ·
                      rfl

theorem cell23_7091270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_7091270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091270 prefixEnd_7091270 := by exact prefixLift 7091270
  have htrace : WordTrace (prefixWord ++ tailWord_7091270) baseStart_7091270 baseEnd_7091270 := by
    simpa [prefixWord, tailWord_7091270, baseEnd_7091270] using wordTrace_append hprefix tailTrace_7091270
  have hstable : (prefixWord ++ tailWord_7091270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091270).length < 2 ^ (prefixWord ++ tailWord_7091270).sum := by decide
  have hdescent : baseEnd_7091270 < baseStart_7091270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091273 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 2, 4, 2]
def baseStart_7091273 : Nat := 118140960795 + 7091273 * 2 ^ 59
def prefixEnd_7091273 : Nat := 4983230072969 + 3 ^ 40 * 7091273 * 2
def baseEnd_7091273 : Nat := 3641231501250539095475335

theorem tailTrace_7091273 : CollatzResearch.WordTrace tailWord_7091273 prefixEnd_7091273 3641231501250539095475335 := by
  unfold tailWord_7091273
  simp only [CollatzResearch.WordTrace]
  refine ⟨258639974438536488853470473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172426649625690992568980315 258639974438536488853470473)
  ·
    refine ⟨193979980828902366640102855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258639974438536488853470473 193979980828902366640102855)
    ·
      refine ⟨290969971243353549960154283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193979980828902366640102855 290969971243353549960154283)
      ·
        refine ⟨436454956865030324940231425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290969971243353549960154283 436454956865030324940231425)
        ·
          refine ⟨327341217648772743705173569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436454956865030324940231425 327341217648772743705173569)
          ·
            refine ⟨245505913236579557778880177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327341217648772743705173569 245505913236579557778880177)
            ·
              refine ⟨184129434927434668334160133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245505913236579557778880177 184129434927434668334160133)
              ·
                refine ⟨34524269048894000312655025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184129434927434668334160133 34524269048894000312655025)
                ·
                  refine ⟨25893201786670500234491269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34524269048894000312655025 25893201786670500234491269)
                  ·
                    refine ⟨4854975335000718793967113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25893201786670500234491269 4854975335000718793967113)
                    ·
                      refine ⟨3641231501250539095475335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4854975335000718793967113 3641231501250539095475335)
                      ·
                        rfl

theorem cell23_7091273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 4, 2].length) (baseStart_7091273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091273 prefixEnd_7091273 := by exact prefixLift 7091273
  have htrace : WordTrace (prefixWord ++ tailWord_7091273) baseStart_7091273 baseEnd_7091273 := by
    simpa [prefixWord, tailWord_7091273, baseEnd_7091273] using wordTrace_append hprefix tailTrace_7091273
  have hstable : (prefixWord ++ tailWord_7091273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091273).length < 2 ^ (prefixWord ++ tailWord_7091273).sum := by decide
  have hdescent : baseEnd_7091273 < baseStart_7091273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091310 : List Nat := [4, 1, 2, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_7091310 : Nat := 118140960795 + 7091310 * 2 ^ 59
def prefixEnd_7091310 : Nat := 4983230072969 + 3 ^ 40 * 7091310 * 2
def baseEnd_7091310 : Nat := 3641250500034755450712665

theorem tailTrace_7091310 : CollatzResearch.WordTrace tailWord_7091310 prefixEnd_7091310 3641250500034755450712665 := by
  unfold tailWord_7091310
  simp only [CollatzResearch.WordTrace]
  refine ⟨32330165492425305521570923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172427549292934962781711589 32330165492425305521570923)
  ·
    refine ⟨48495248238637958282356385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32330165492425305521570923 48495248238637958282356385)
    ·
      refine ⟨36371436178978468711767289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48495248238637958282356385 36371436178978468711767289)
      ·
        refine ⟨27278577134233851533825467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36371436178978468711767289 27278577134233851533825467)
        ·
          refine ⟨40917865701350777300738201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27278577134233851533825467 40917865701350777300738201)
          ·
            refine ⟨30688399276013082975553651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40917865701350777300738201 30688399276013082975553651)
            ·
              refine ⟨46032598914019624463330477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30688399276013082975553651 46032598914019624463330477)
              ·
                refine ⟨17262224592757359173748929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46032598914019624463330477 17262224592757359173748929)
                ·
                  refine ⟨12946668444568019380311697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17262224592757359173748929 12946668444568019380311697)
                  ·
                    refine ⟨9710001333426014535233773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12946668444568019380311697 9710001333426014535233773)
                    ·
                      refine ⟨3641250500034755450712665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9710001333426014535233773 3641250500034755450712665)
                      ·
                        rfl

theorem cell23_7091310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_7091310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091310 prefixEnd_7091310 := by exact prefixLift 7091310
  have htrace : WordTrace (prefixWord ++ tailWord_7091310) baseStart_7091310 baseEnd_7091310 := by
    simpa [prefixWord, tailWord_7091310, baseEnd_7091310] using wordTrace_append hprefix tailTrace_7091310
  have hstable : (prefixWord ++ tailWord_7091310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091310).length < 2 ^ (prefixWord ++ tailWord_7091310).sum := by decide
  have hdescent : baseEnd_7091310 < baseStart_7091310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091367 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_7091367 : Nat := 118140960795 + 7091367 * 2 ^ 59
def prefixEnd_7091367 : Nat := 4983230072969 + 3 ^ 40 * 7091367 * 2
def baseEnd_7091367 : Nat := 3641279768432061727699903

theorem tailTrace_7091367 : CollatzResearch.WordTrace tailWord_7091367 prefixEnd_7091367 3641279768432061727699903 := by
  unfold tailWord_7091367
  simp only [CollatzResearch.WordTrace]
  refine ⟨258643402900195942907392355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172428935266797295271594903 258643402900195942907392355)
  ·
    refine ⟨387965104350293914361088533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258643402900195942907392355 387965104350293914361088533)
    ·
      refine ⟨18185864266420027235676025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 387965104350293914361088533 18185864266420027235676025)
      ·
        refine ⟨13639398199815020426757019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18185864266420027235676025 13639398199815020426757019)
        ·
          refine ⟨20459097299722530640135529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13639398199815020426757019 20459097299722530640135529)
          ·
            refine ⟨15344322974791897980101647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20459097299722530640135529 15344322974791897980101647)
            ·
              refine ⟨23016484462187846970152471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15344322974791897980101647 23016484462187846970152471)
              ·
                refine ⟨34524726693281770455228707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23016484462187846970152471 34524726693281770455228707)
                ·
                  refine ⟨51787090039922655682843061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34524726693281770455228707 51787090039922655682843061)
                  ·
                    refine ⟨4855039691242748970266537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51787090039922655682843061 4855039691242748970266537)
                    ·
                      refine ⟨3641279768432061727699903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4855039691242748970266537 3641279768432061727699903)
                      ·
                        rfl

theorem cell23_7091367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_7091367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091367 prefixEnd_7091367 := by exact prefixLift 7091367
  have htrace : WordTrace (prefixWord ++ tailWord_7091367) baseStart_7091367 baseEnd_7091367 := by
    simpa [prefixWord, tailWord_7091367, baseEnd_7091367] using wordTrace_append hprefix tailTrace_7091367
  have hstable : (prefixWord ++ tailWord_7091367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091367).length < 2 ^ (prefixWord ++ tailWord_7091367).sum := by decide
  have hdescent : baseEnd_7091367 < baseStart_7091367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091377 : List Nat := [1, 2, 2, 5, 1, 1, 4, 1, 1, 5]
def baseStart_7091377 : Nat := 118140960795 + 7091377 * 2 ^ 59
def prefixEnd_7091377 : Nat := 4983230072969 + 3 ^ 40 * 7091377 * 2
def baseEnd_7091377 : Nat := 1213761634412868896191619

theorem tailTrace_7091377 : CollatzResearch.WordTrace tailWord_7091377 prefixEnd_7091377 1213761634412868896191619 := by
  unfold tailWord_7091377
  simp only [CollatzResearch.WordTrace]
  refine ⟨258643767630159714615256385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172429178420106476410170923 258643767630159714615256385)
  ·
    refine ⟨193982825722619785961442289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258643767630159714615256385 193982825722619785961442289)
    ·
      refine ⟨145487119291964839471081717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193982825722619785961442289 145487119291964839471081717)
      ·
        refine ⟨13639417433621703700413911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145487119291964839471081717 13639417433621703700413911)
        ·
          refine ⟨20459126150432555550620867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13639417433621703700413911 20459126150432555550620867)
          ·
            refine ⟨30688689225648833325931301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20459126150432555550620867 30688689225648833325931301)
            ·
              refine ⟨5754129229809156248612119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30688689225648833325931301 5754129229809156248612119)
              ·
                refine ⟨8631193844713734372918179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5754129229809156248612119 8631193844713734372918179)
                ·
                  refine ⟨12946790767070601559377269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8631193844713734372918179 12946790767070601559377269)
                  ·
                    refine ⟨1213761634412868896191619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12946790767070601559377269 1213761634412868896191619)
                    ·
                      rfl

theorem cell23_7091377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 1, 5].length) (baseStart_7091377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091377 prefixEnd_7091377 := by exact prefixLift 7091377
  have htrace : WordTrace (prefixWord ++ tailWord_7091377) baseStart_7091377 baseEnd_7091377 := by
    simpa [prefixWord, tailWord_7091377, baseEnd_7091377] using wordTrace_append hprefix tailTrace_7091377
  have hstable : (prefixWord ++ tailWord_7091377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091377).length < 2 ^ (prefixWord ++ tailWord_7091377).sum := by decide
  have hdescent : baseEnd_7091377 < baseStart_7091377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091383 : List Nat := [1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 5]
def baseStart_7091383 : Nat := 118140960795 + 7091383 * 2 ^ 59
def prefixEnd_7091383 : Nat := 4983230072969 + 3 ^ 40 * 7091383 * 2
def baseEnd_7091383 : Nat := 3641287984122533665099829

theorem tailTrace_7091383 : CollatzResearch.WordTrace tailWord_7091383 prefixEnd_7091383 3641287984122533665099829 := by
  unfold tailWord_7091383
  simp only [CollatzResearch.WordTrace]
  refine ⟨258643986468137977639974803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172429324312091985093316535 258643986468137977639974803)
  ·
    refine ⟨387965979702206966459962205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258643986468137977639974803 387965979702206966459962205)
    ·
      refine ⟨145487242388327612422485827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387965979702206966459962205 145487242388327612422485827)
      ·
        refine ⟨218230863582491418633728741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145487242388327612422485827 218230863582491418633728741)
        ·
          refine ⟨40918286921717140993824139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218230863582491418633728741 40918286921717140993824139)
          ·
            refine ⟨61377430382575711490736209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40918286921717140993824139 61377430382575711490736209)
            ·
              refine ⟨46033072786931783618052157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61377430382575711490736209 46033072786931783618052157)
              ·
                refine ⟨17262402295099418856769559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46033072786931783618052157 17262402295099418856769559)
                ·
                  refine ⟨25893603442649128285154339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17262402295099418856769559 25893603442649128285154339)
                  ·
                    refine ⟨38840405163973692427731509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25893603442649128285154339 38840405163973692427731509)
                    ·
                      refine ⟨3641287984122533665099829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38840405163973692427731509 3641287984122533665099829)
                      ·
                        rfl

theorem cell23_7091383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_7091383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091383 prefixEnd_7091383 := by exact prefixLift 7091383
  have htrace : WordTrace (prefixWord ++ tailWord_7091383) baseStart_7091383 baseEnd_7091383 := by
    simpa [prefixWord, tailWord_7091383, baseEnd_7091383] using wordTrace_append hprefix tailTrace_7091383
  have hstable : (prefixWord ++ tailWord_7091383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091383).length < 2 ^ (prefixWord ++ tailWord_7091383).sum := by decide
  have hdescent : baseEnd_7091383 < baseStart_7091383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091440 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 7, 3, 2]
def baseStart_7091440 : Nat := 118140960795 + 7091440 * 2 ^ 59
def prefixEnd_7091440 : Nat := 4983230072969 + 3 ^ 40 * 7091440 * 2
def baseEnd_7091440 : Nat := 3641317252519839942087067

theorem tailTrace_7091440 : CollatzResearch.WordTrace tailWord_7091440 prefixEnd_7091440 3641317252519839942087067 := by
  unfold tailWord_7091440
  simp only [CollatzResearch.WordTrace]
  refine ⟨129323032714465738187399887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172430710285954317583199849 129323032714465738187399887)
  ·
    refine ⟨193984549071698607281099831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129323032714465738187399887 193984549071698607281099831)
    ·
      refine ⟨290976823607547910921649747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193984549071698607281099831 290976823607547910921649747)
      ·
        refine ⟨436465235411321866382474621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290976823607547910921649747 436465235411321866382474621)
        ·
          refine ⟨163674463279245699893427983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436465235411321866382474621 163674463279245699893427983)
          ·
            refine ⟨245511694918868549840141975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163674463279245699893427983 245511694918868549840141975)
            ·
              refine ⟨368267542378302824760212963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245511694918868549840141975 368267542378302824760212963)
              ·
                refine ⟨552401313567454237140319445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368267542378302824760212963 552401313567454237140319445)
                ·
                  refine ⟨12946905786737208682976237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 552401313567454237140319445 12946905786737208682976237)
                  ·
                    refine ⟨4855089670026453256116089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12946905786737208682976237 4855089670026453256116089)
                    ·
                      refine ⟨3641317252519839942087067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4855089670026453256116089 3641317252519839942087067)
                      ·
                        rfl

theorem cell23_7091440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 7, 3, 2].length) (baseStart_7091440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091440 prefixEnd_7091440 := by exact prefixLift 7091440
  have htrace : WordTrace (prefixWord ++ tailWord_7091440) baseStart_7091440 baseEnd_7091440 := by
    simpa [prefixWord, tailWord_7091440, baseEnd_7091440] using wordTrace_append hprefix tailTrace_7091440
  have hstable : (prefixWord ++ tailWord_7091440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091440).length < 2 ^ (prefixWord ++ tailWord_7091440).sum := by decide
  have hdescent : baseEnd_7091440 < baseStart_7091440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091458 : List Nat := [3, 4, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_7091458 : Nat := 118140960795 + 7091458 * 2 ^ 59
def prefixEnd_7091458 : Nat := 4983230072969 + 3 ^ 40 * 7091458 * 2
def baseEnd_7091458 : Nat := 1213775498390540290553995

theorem tailTrace_7091458 : CollatzResearch.WordTrace tailWord_7091458 prefixEnd_7091458 1213775498390540290553995 := by
  unfold tailWord_7091458
  simp only [CollatzResearch.WordTrace]
  refine ⟨64661680485716566362238757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172431147961910843632636685 64661680485716566362238757)
  ·
    refine ⟨12124065091071856192919767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64661680485716566362238757 12124065091071856192919767)
    ·
      refine ⟨18186097636607784289379651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12124065091071856192919767 18186097636607784289379651)
      ·
        refine ⟨27279146454911676434069477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18186097636607784289379651 27279146454911676434069477)
        ·
          refine ⟨5114839960295939331388027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27279146454911676434069477 5114839960295939331388027)
          ·
            refine ⟨7672259940443908997082041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5114839960295939331388027 7672259940443908997082041)
            ·
              refine ⟨5754194955332931747811531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7672259940443908997082041 5754194955332931747811531)
              ·
                refine ⟨8631292432999397621717297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5754194955332931747811531 8631292432999397621717297)
                ·
                  refine ⟨6473469324749548216287973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8631292432999397621717297 6473469324749548216287973)
                  ·
                    refine ⟨1213775498390540290553995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6473469324749548216287973 1213775498390540290553995)
                    ·
                      rfl

theorem cell23_7091458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_7091458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091458 prefixEnd_7091458 := by exact prefixLift 7091458
  have htrace : WordTrace (prefixWord ++ tailWord_7091458) baseStart_7091458 baseEnd_7091458 := by
    simpa [prefixWord, tailWord_7091458, baseEnd_7091458] using wordTrace_append hprefix tailTrace_7091458
  have hstable : (prefixWord ++ tailWord_7091458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091458).length < 2 ^ (prefixWord ++ tailWord_7091458).sum := by decide
  have hdescent : baseEnd_7091458 < baseStart_7091458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091464 : List Nat := [2, 1, 3, 2, 4, 1, 1, 3, 2, 1, 3]
def baseStart_7091464 : Nat := 118140960795 + 7091464 * 2 ^ 59
def prefixEnd_7091464 : Nat := 4983230072969 + 3 ^ 40 * 7091464 * 2
def baseEnd_7091464 : Nat := 3641329576055547848186957

theorem tailTrace_7091464 : CollatzResearch.WordTrace tailWord_7091464 prefixEnd_7091464 3641329576055547848186957 := by
  unfold tailWord_7091464
  simp only [CollatzResearch.WordTrace]
  refine ⟨129323470390422264236836723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172431293853896352315782297 129323470390422264236836723)
  ·
    refine ⟨193985205585633396355255085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129323470390422264236836723 193985205585633396355255085)
    ·
      refine ⟨72744452094612523633220657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193985205585633396355255085 72744452094612523633220657)
      ·
        refine ⟨54558339070959392724915493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72744452094612523633220657 54558339070959392724915493)
        ·
          refine ⟨10229688575804886135921655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54558339070959392724915493 10229688575804886135921655)
          ·
            refine ⟨15344532863707329203882483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10229688575804886135921655 15344532863707329203882483)
            ·
              refine ⟨23016799295560993805823725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15344532863707329203882483 23016799295560993805823725)
              ·
                refine ⟨8631299735835372677183897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23016799295560993805823725 8631299735835372677183897)
                ·
                  refine ⟨6473474801876529507887923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8631299735835372677183897 6473474801876529507887923)
                  ·
                    refine ⟨9710212202814794261831885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6473474801876529507887923 9710212202814794261831885)
                    ·
                      refine ⟨3641329576055547848186957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9710212202814794261831885 3641329576055547848186957)
                      ·
                        rfl

theorem cell23_7091464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_7091464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091464 prefixEnd_7091464 := by exact prefixLift 7091464
  have htrace : WordTrace (prefixWord ++ tailWord_7091464) baseStart_7091464 baseEnd_7091464 := by
    simpa [prefixWord, tailWord_7091464, baseEnd_7091464] using wordTrace_append hprefix tailTrace_7091464
  have hstable : (prefixWord ++ tailWord_7091464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091464).length < 2 ^ (prefixWord ++ tailWord_7091464).sum := by decide
  have hdescent : baseEnd_7091464 < baseStart_7091464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091473 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 5]
def baseStart_7091473 : Nat := 118140960795 + 7091473 * 2 ^ 59
def prefixEnd_7091473 : Nat := 4983230072969 + 3 ^ 40 * 7091473 * 2
def baseEnd_7091473 : Nat := 3641334197381438312974415

theorem tailTrace_7091473 : CollatzResearch.WordTrace tailWord_7091473 prefixEnd_7091473 3641334197381438312974415 := by
  unfold tailWord_7091473
  simp only [CollatzResearch.WordTrace]
  refine ⟨258647269037811923010751073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172431512691874615340500715 258647269037811923010751073)
  ·
    refine ⟨193985451778358942258063305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258647269037811923010751073 193985451778358942258063305)
    ·
      refine ⟨145489088833769206693547479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193985451778358942258063305 145489088833769206693547479)
      ·
        refine ⟨218233633250653810040321219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145489088833769206693547479 218233633250653810040321219)
        ·
          refine ⟨327350449875980715060481829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218233633250653810040321219 327350449875980715060481829)
          ·
            refine ⟨61378209351746384073840343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 327350449875980715060481829 61378209351746384073840343)
            ·
              refine ⟨92067314027619576110760515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61378209351746384073840343 92067314027619576110760515)
              ·
                refine ⟨138100971041429364166140773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92067314027619576110760515 138100971041429364166140773)
                ·
                  refine ⟨25893932070268005781151395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138100971041429364166140773 25893932070268005781151395)
                  ·
                    refine ⟨38840898105402008671727093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25893932070268005781151395 38840898105402008671727093)
                    ·
                      refine ⟨3641334197381438312974415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38840898105402008671727093 3641334197381438312974415)
                      ·
                        rfl

theorem cell23_7091473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_7091473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091473 prefixEnd_7091473 := by exact prefixLift 7091473
  have htrace : WordTrace (prefixWord ++ tailWord_7091473) baseStart_7091473 baseEnd_7091473 := by
    simpa [prefixWord, tailWord_7091473, baseEnd_7091473] using wordTrace_append hprefix tailTrace_7091473
  have hstable : (prefixWord ++ tailWord_7091473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091473).length < 2 ^ (prefixWord ++ tailWord_7091473).sum := by decide
  have hdescent : baseEnd_7091473 < baseStart_7091473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091483 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 4]
def baseStart_7091483 : Nat := 118140960795 + 7091483 * 2 ^ 59
def prefixEnd_7091483 : Nat := 4983230072969 + 3 ^ 40 * 7091483 * 2
def baseEnd_7091483 : Nat := 3641339332187983273849369

theorem tailTrace_7091483 : CollatzResearch.WordTrace tailWord_7091483 prefixEnd_7091483 3641339332187983273849369 := by
  unfold tailWord_7091483
  simp only [CollatzResearch.WordTrace]
  refine ⟨258647633767775694718615103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172431755845183796479076735 258647633767775694718615103)
  ·
    refine ⟨387971450651663542077922655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258647633767775694718615103 387971450651663542077922655)
    ·
      refine ⟨581957175977495313116883983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387971450651663542077922655 581957175977495313116883983)
      ·
        refine ⟨872935763966242969675325975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581957175977495313116883983 872935763966242969675325975)
        ·
          refine ⟨1309403645949364454512988963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872935763966242969675325975 1309403645949364454512988963)
          ·
            refine ⟨1964105468924046681769483445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309403645949364454512988963 1964105468924046681769483445)
            ·
              refine ⟨184134887711629376415889073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1964105468924046681769483445 184134887711629376415889073)
              ·
                refine ⟨138101165783722032311916805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184134887711629376415889073 138101165783722032311916805)
                ·
                  refine ⟨25893968584447881058484401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138101165783722032311916805 25893968584447881058484401)
                  ·
                    refine ⟨19420476438335910793863301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25893968584447881058484401 19420476438335910793863301)
                    ·
                      refine ⟨3641339332187983273849369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19420476438335910793863301 3641339332187983273849369)
                      ·
                        rfl

theorem cell23_7091483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 4].length) (baseStart_7091483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091483 prefixEnd_7091483 := by exact prefixLift 7091483
  have htrace : WordTrace (prefixWord ++ tailWord_7091483) baseStart_7091483 baseEnd_7091483 := by
    simpa [prefixWord, tailWord_7091483, baseEnd_7091483] using wordTrace_append hprefix tailTrace_7091483
  have hstable : (prefixWord ++ tailWord_7091483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091483).length < 2 ^ (prefixWord ++ tailWord_7091483).sum := by decide
  have hdescent : baseEnd_7091483 < baseStart_7091483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091504 : List Nat := [2, 1, 1, 1, 2, 2, 6, 2, 2, 2, 2]
def baseStart_7091504 : Nat := 118140960795 + 7091504 * 2 ^ 59
def prefixEnd_7091504 : Nat := 4983230072969 + 3 ^ 40 * 7091504 * 2
def baseEnd_7091504 : Nat := 3641350115281727691686773

theorem tailTrace_7091504 : CollatzResearch.WordTrace tailWord_7091504 prefixEnd_7091504 3641350115281727691686773 := by
  unfold tailWord_7091504
  simp only [CollatzResearch.WordTrace]
  refine ⟨129324199850349807652564783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172432266467133076870086377 129324199850349807652564783)
  ·
    refine ⟨193986299775524711478847175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129324199850349807652564783 193986299775524711478847175)
    ·
      refine ⟨290979449663287067218270763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193986299775524711478847175 290979449663287067218270763)
      ·
        refine ⟨436469174494930600827406145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290979449663287067218270763 436469174494930600827406145)
        ·
          refine ⟨327351880871197950620554609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436469174494930600827406145 327351880871197950620554609)
          ·
            refine ⟨245513910653398462965415957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327351880871197950620554609 245513910653398462965415957)
            ·
              refine ⟨11508464561878052951503873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 245513910653398462965415957 11508464561878052951503873)
              ·
                refine ⟨8631348421408539713627905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11508464561878052951503873 8631348421408539713627905)
                ·
                  refine ⟨6473511316056404785220929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8631348421408539713627905 6473511316056404785220929)
                  ·
                    refine ⟨4855133487042303588915697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6473511316056404785220929 4855133487042303588915697)
                    ·
                      refine ⟨3641350115281727691686773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4855133487042303588915697 3641350115281727691686773)
                      ·
                        rfl

theorem cell23_7091504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 2, 2, 2].length) (baseStart_7091504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091504 prefixEnd_7091504 := by exact prefixLift 7091504
  have htrace : WordTrace (prefixWord ++ tailWord_7091504) baseStart_7091504 baseEnd_7091504 := by
    simpa [prefixWord, tailWord_7091504, baseEnd_7091504] using wordTrace_append hprefix tailTrace_7091504
  have hstable : (prefixWord ++ tailWord_7091504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091504).length < 2 ^ (prefixWord ++ tailWord_7091504).sum := by decide
  have hdescent : baseEnd_7091504 < baseStart_7091504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091520 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 3]
def baseStart_7091520 : Nat := 118140960795 + 7091520 * 2 ^ 59
def prefixEnd_7091520 : Nat := 4983230072969 + 3 ^ 40 * 7091520 * 2
def baseEnd_7091520 : Nat := 3641358330972199629086699

theorem tailTrace_7091520 : CollatzResearch.WordTrace tailWord_7091520 prefixEnd_7091520 3641358330972199629086699 := by
  unfold tailWord_7091520
  simp only [CollatzResearch.WordTrace]
  refine ⟨129324491634320825018856007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172432655512427766691808009 129324491634320825018856007)
  ·
    refine ⟨193986737451481237528284011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129324491634320825018856007 193986737451481237528284011)
    ·
      refine ⟨290980106177221856292426017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193986737451481237528284011 290980106177221856292426017)
      ·
        refine ⟨218235079632916392219319513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290980106177221856292426017 218235079632916392219319513)
        ·
          refine ⟨163676309724687294164489635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218235079632916392219319513 163676309724687294164489635)
          ·
            refine ⟨245514464587030941246734453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163676309724687294164489635 245514464587030941246734453)
            ·
              refine ⟨23016981055034150741881355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 245514464587030941246734453 23016981055034150741881355)
              ·
                refine ⟨34525471582551226112822033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23016981055034150741881355 34525471582551226112822033)
                ·
                  refine ⟨25894103686913419584616525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34525471582551226112822033 25894103686913419584616525)
                  ·
                    refine ⟨9710288882592532344231197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25894103686913419584616525 9710288882592532344231197)
                    ·
                      refine ⟨3641358330972199629086699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9710288882592532344231197 3641358330972199629086699)
                      ·
                        rfl

theorem cell23_7091520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_7091520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091520 prefixEnd_7091520 := by exact prefixLift 7091520
  have htrace : WordTrace (prefixWord ++ tailWord_7091520) baseStart_7091520 baseEnd_7091520 := by
    simpa [prefixWord, tailWord_7091520, baseEnd_7091520] using wordTrace_append hprefix tailTrace_7091520
  have hstable : (prefixWord ++ tailWord_7091520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091520).length < 2 ^ (prefixWord ++ tailWord_7091520).sum := by decide
  have hdescent : baseEnd_7091520 < baseStart_7091520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091521 : List Nat := [1, 2, 5, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_7091521 : Nat := 118140960795 + 7091521 * 2 ^ 59
def prefixEnd_7091521 : Nat := 4983230072969 + 3 ^ 40 * 7091521 * 2
def baseEnd_7091521 : Nat := 3641358844452854125174195

theorem tailTrace_7091521 : CollatzResearch.WordTrace tailWord_7091521 prefixEnd_7091521 3641358844452854125174195 := by
  unfold tailWord_7091521
  simp only [CollatzResearch.WordTrace]
  refine ⟨258649019741638027208498417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172432679827758684805665611 258649019741638027208498417)
  ·
    refine ⟨193986764806228520406373813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258649019741638027208498417 193986764806228520406373813)
    ·
      refine ⟨18186259200583923788097545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193986764806228520406373813 18186259200583923788097545)
      ·
        refine ⟨13639694400437942841073159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18186259200583923788097545 13639694400437942841073159)
        ·
          refine ⟨20459541600656914261609739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13639694400437942841073159 20459541600656914261609739)
          ·
            refine ⟨30689312400985371392414609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20459541600656914261609739 30689312400985371392414609)
            ·
              refine ⟨23016984300739028544310957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30689312400985371392414609 23016984300739028544310957)
              ·
                refine ⟨8631369112777135704116609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23016984300739028544310957 8631369112777135704116609)
                ·
                  refine ⟨6473526834582851778087457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8631369112777135704116609 6473526834582851778087457)
                  ·
                    refine ⟨4855145125937138833565593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6473526834582851778087457 4855145125937138833565593)
                    ·
                      refine ⟨3641358844452854125174195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4855145125937138833565593 3641358844452854125174195)
                      ·
                        rfl

theorem cell23_7091521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_7091521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091521 prefixEnd_7091521 := by exact prefixLift 7091521
  have htrace : WordTrace (prefixWord ++ tailWord_7091521) baseStart_7091521 baseEnd_7091521 := by
    simpa [prefixWord, tailWord_7091521, baseEnd_7091521] using wordTrace_append hprefix tailTrace_7091521
  have hstable : (prefixWord ++ tailWord_7091521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091521).length < 2 ^ (prefixWord ++ tailWord_7091521).sum := by decide
  have hdescent : baseEnd_7091521 < baseStart_7091521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091523 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 1, 7]
def baseStart_7091523 : Nat := 118140960795 + 7091523 * 2 ^ 59
def prefixEnd_7091523 : Nat := 4983230072969 + 3 ^ 40 * 7091523 * 2
def baseEnd_7091523 : Nat := 1213786623804721039116395

theorem tailTrace_7091523 : CollatzResearch.WordTrace tailWord_7091523 prefixEnd_7091523 1213786623804721039116395 := by
  unfold tailWord_7091523
  simp only [CollatzResearch.WordTrace]
  refine ⟨258649092687630781550071223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172432728458420521033380815 258649092687630781550071223)
  ·
    refine ⟨387973639031446172325106835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258649092687630781550071223 387973639031446172325106835)
    ·
      refine ⟨581960458547169258487660253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387973639031446172325106835 581960458547169258487660253)
      ·
        refine ⟨218235171955188471932872595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 581960458547169258487660253 218235171955188471932872595)
        ·
          refine ⟨327352757932782707899308893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218235171955188471932872595 327352757932782707899308893)
          ·
            refine ⟨122757284224793515462240835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327352757932782707899308893 122757284224793515462240835)
            ·
              refine ⟨184135926337190273193361253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122757284224793515462240835 184135926337190273193361253)
              ·
                refine ⟨34525486188223176223755235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184135926337190273193361253 34525486188223176223755235)
                ·
                  refine ⟨51788229282334764335632853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34525486188223176223755235 51788229282334764335632853)
                  ·
                    refine ⟨1213786623804721039116395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51788229282334764335632853 1213786623804721039116395)
                    ·
                      rfl

theorem cell23_7091523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 7].length) (baseStart_7091523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091523 prefixEnd_7091523 := by exact prefixLift 7091523
  have htrace : WordTrace (prefixWord ++ tailWord_7091523) baseStart_7091523 baseEnd_7091523 := by
    simpa [prefixWord, tailWord_7091523, baseEnd_7091523] using wordTrace_append hprefix tailTrace_7091523
  have hstable : (prefixWord ++ tailWord_7091523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091523).length < 2 ^ (prefixWord ++ tailWord_7091523).sum := by decide
  have hdescent : baseEnd_7091523 < baseStart_7091523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091540 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_7091540 : Nat := 118140960795 + 7091540 * 2 ^ 59
def prefixEnd_7091540 : Nat := 4983230072969 + 3 ^ 40 * 7091540 * 2
def baseEnd_7091540 : Nat := 1213789533528429850278869

theorem tailTrace_7091540 : CollatzResearch.WordTrace tailWord_7091540 prefixEnd_7091540 1213789533528429850278869 := by
  unfold tailWord_7091540
  simp only [CollatzResearch.WordTrace]
  refine ⟨129324856364284596726720037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172433141819046128968960049 129324856364284596726720037)
  ·
    refine ⟨24248410568303361886260007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129324856364284596726720037 24248410568303361886260007)
    ·
      refine ⟨36372615852455042829390011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24248410568303361886260007 36372615852455042829390011)
      ·
        refine ⟨54558923778682564244085017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36372615852455042829390011 54558923778682564244085017)
        ·
          refine ⟨40919192834011923183063763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54558923778682564244085017 40919192834011923183063763)
          ·
            refine ⟨61378789251017884774595645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40919192834011923183063763 61378789251017884774595645)
            ·
              refine ⟨23017045969131706790473367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61378789251017884774595645 23017045969131706790473367)
              ·
                refine ⟨34525568953697560185710051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23017045969131706790473367 34525568953697560185710051)
                ·
                  refine ⟨51788353430546340278565077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34525568953697560185710051 51788353430546340278565077)
                  ·
                    refine ⟨1213789533528429850278869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51788353430546340278565077 1213789533528429850278869)
                    ·
                      rfl

theorem cell23_7091540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_7091540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091540 prefixEnd_7091540 := by exact prefixLift 7091540
  have htrace : WordTrace (prefixWord ++ tailWord_7091540) baseStart_7091540 baseEnd_7091540 := by
    simpa [prefixWord, tailWord_7091540, baseEnd_7091540] using wordTrace_append hprefix tailTrace_7091540
  have hstable : (prefixWord ++ tailWord_7091540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091540).length < 2 ^ (prefixWord ++ tailWord_7091540).sum := by decide
  have hdescent : baseEnd_7091540 < baseStart_7091540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091553 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 1, 10]
def baseStart_7091553 : Nat := 118140960795 + 7091553 * 2 ^ 59
def prefixEnd_7091553 : Nat := 4983230072969 + 3 ^ 40 * 7091553 * 2
def baseEnd_7091553 : Nat := 1213791758611265999991349

theorem tailTrace_7091553 : CollatzResearch.WordTrace tailWord_7091553 prefixEnd_7091553 1213791758611265999991349 := by
  unfold tailWord_7091553
  simp only [CollatzResearch.WordTrace]
  refine ⟨258650186877522096673663313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172433457918348064449108875 258650186877522096673663313)
  ·
    refine ⟨193987640158141572505247485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258650186877522096673663313 193987640158141572505247485)
    ·
      refine ⟨72745365059303089689467807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193987640158141572505247485 72745365059303089689467807)
      ·
        refine ⟨109118047588954634534201711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72745365059303089689467807 109118047588954634534201711)
        ·
          refine ⟨163677071383431951801302567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109118047588954634534201711 163677071383431951801302567)
          ·
            refine ⟨245515607075147927701953851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163677071383431951801302567 245515607075147927701953851)
            ·
              refine ⟨368273410612721891552930777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245515607075147927701953851 368273410612721891552930777)
              ·
                refine ⟨276205057959541418664698083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368273410612721891552930777 276205057959541418664698083)
                ·
                  refine ⟨414307586939312127997047125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276205057959541418664698083 414307586939312127997047125)
                  ·
                    refine ⟨1213791758611265999991349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 414307586939312127997047125 1213791758611265999991349)
                    ·
                      rfl

theorem cell23_7091553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_7091553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091553 prefixEnd_7091553 := by exact prefixLift 7091553
  have htrace : WordTrace (prefixWord ++ tailWord_7091553) baseStart_7091553 baseEnd_7091553 := by
    simpa [prefixWord, tailWord_7091553, baseEnd_7091553] using wordTrace_append hprefix tailTrace_7091553
  have hstable : (prefixWord ++ tailWord_7091553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091553).length < 2 ^ (prefixWord ++ tailWord_7091553).sum := by decide
  have hdescent : baseEnd_7091553 < baseStart_7091553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091577 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 2, 4, 2]
def baseStart_7091577 : Nat := 118140960795 + 7091577 * 2 ^ 59
def prefixEnd_7091577 : Nat := 4983230072969 + 3 ^ 40 * 7091577 * 2
def baseEnd_7091577 : Nat := 3641387599369505906073937

theorem tailTrace_7091577 : CollatzResearch.WordTrace tailWord_7091577 prefixEnd_7091577 3641387599369505906073937 := by
  unfold tailWord_7091577
  simp only [CollatzResearch.WordTrace]
  refine ⟨258651062229435148772536985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172434041486290099181691323 258651062229435148772536985)
  ·
    refine ⟨193988296672076361579402739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258651062229435148772536985 193988296672076361579402739)
    ·
      refine ⟨290982445008114542369104109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193988296672076361579402739 290982445008114542369104109)
      ·
        refine ⟨109118416878042953388414041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290982445008114542369104109 109118416878042953388414041)
        ·
          refine ⟨81838812658532215041310531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109118416878042953388414041 81838812658532215041310531)
          ·
            refine ⟨122758218987798322561965797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81838812658532215041310531 122758218987798322561965797)
            ·
              refine ⟨23017166060212185480368587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122758218987798322561965797 23017166060212185480368587)
              ·
                refine ⟨34525749090318278220552881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23017166060212185480368587 34525749090318278220552881)
                ·
                  refine ⟨25894311817738708665414661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34525749090318278220552881 25894311817738708665414661)
                  ·
                    refine ⟨4855183465826007874765249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25894311817738708665414661 4855183465826007874765249)
                    ·
                      refine ⟨3641387599369505906073937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4855183465826007874765249 3641387599369505906073937)
                      ·
                        rfl

theorem cell23_7091577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_7091577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091577 prefixEnd_7091577 := by exact prefixLift 7091577
  have htrace : WordTrace (prefixWord ++ tailWord_7091577) baseStart_7091577 baseEnd_7091577 := by
    simpa [prefixWord, tailWord_7091577, baseEnd_7091577] using wordTrace_append hprefix tailTrace_7091577
  have hstable : (prefixWord ++ tailWord_7091577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091577).length < 2 ^ (prefixWord ++ tailWord_7091577).sum := by decide
  have hdescent : baseEnd_7091577 < baseStart_7091577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091580 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 3, 4, 3]
def baseStart_7091580 : Nat := 118140960795 + 7091580 * 2 ^ 59
def prefixEnd_7091580 : Nat := 4983230072969 + 3 ^ 40 * 7091580 * 2
def baseEnd_7091580 : Nat := 3641389139811469394336423

theorem tailTrace_7091580 : CollatzResearch.WordTrace tailWord_7091580 prefixEnd_7091580 3641389139811469394336423 := by
  unfold tailWord_7091580
  simp only [CollatzResearch.WordTrace]
  refine ⟨129325585824212140142448097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172434114432282853523264129 129325585824212140142448097)
  ·
    refine ⟨96994189368159105106836073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129325585824212140142448097 96994189368159105106836073)
    ·
      refine ⟨72745642026119328830127055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96994189368159105106836073 72745642026119328830127055)
      ·
        refine ⟨109118463039178993245190583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72745642026119328830127055 109118463039178993245190583)
        ·
          refine ⟨163677694558768489867785875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109118463039178993245190583 163677694558768489867785875)
          ·
            refine ⟨245516541838152734801678813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163677694558768489867785875 245516541838152734801678813)
            ·
              refine ⟨92068703189307275550629555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245516541838152734801678813 92068703189307275550629555)
              ·
                refine ⟨138103054783960913325944333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92068703189307275550629555 138103054783960913325944333)
                ·
                  refine ⟨51788645543985342497229125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138103054783960913325944333 51788645543985342497229125)
                  ·
                    refine ⟨9710371039497251718230461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51788645543985342497229125 9710371039497251718230461)
                    ·
                      refine ⟨3641389139811469394336423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9710371039497251718230461 3641389139811469394336423)
                      ·
                        rfl

theorem cell23_7091580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_7091580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091580 prefixEnd_7091580 := by exact prefixLift 7091580
  have htrace : WordTrace (prefixWord ++ tailWord_7091580) baseStart_7091580 baseEnd_7091580 := by
    simpa [prefixWord, tailWord_7091580, baseEnd_7091580] using wordTrace_append hprefix tailTrace_7091580
  have hstable : (prefixWord ++ tailWord_7091580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091580).length < 2 ^ (prefixWord ++ tailWord_7091580).sum := by decide
  have hdescent : baseEnd_7091580 < baseStart_7091580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091583 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 12]
def baseStart_7091583 : Nat := 118140960795 + 7091583 * 2 ^ 59
def prefixEnd_7091583 : Nat := 4983230072969 + 3 ^ 40 * 7091583 * 2
def baseEnd_7091583 : Nat := 404598964472603653622101

theorem tailTrace_7091583 : CollatzResearch.WordTrace tailWord_7091583 prefixEnd_7091583 404598964472603653622101 := by
  unfold tailWord_7091583
  simp only [CollatzResearch.WordTrace]
  refine ⟨258651281067413411797255403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172434187378275607864836935 258651281067413411797255403)
  ·
    refine ⟨387976921601120117695883105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258651281067413411797255403 387976921601120117695883105)
    ·
      refine ⟨290982691200840088271912329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387976921601120117695883105 290982691200840088271912329)
      ·
        refine ⟨218237018400630066203934247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290982691200840088271912329 218237018400630066203934247)
        ·
          refine ⟨327355527600945099305901371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218237018400630066203934247 327355527600945099305901371)
          ·
            refine ⟨491033291401417648958852057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327355527600945099305901371 491033291401417648958852057)
            ·
              refine ⟨368274968551063236719139043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491033291401417648958852057 368274968551063236719139043)
              ·
                refine ⟨552412452826594855078708565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368274968551063236719139043 552412452826594855078708565)
                ·
                  refine ⟨404598964472603653622101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 552412452826594855078708565 404598964472603653622101)
                  ·
                    rfl

theorem cell23_7091583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 12].length) (baseStart_7091583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091583 prefixEnd_7091583 := by exact prefixLift 7091583
  have htrace : WordTrace (prefixWord ++ tailWord_7091583) baseStart_7091583 baseEnd_7091583 := by
    simpa [prefixWord, tailWord_7091583, baseEnd_7091583] using wordTrace_append hprefix tailTrace_7091583
  have hstable : (prefixWord ++ tailWord_7091583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091583).length < 2 ^ (prefixWord ++ tailWord_7091583).sum := by decide
  have hdescent : baseEnd_7091583 < baseStart_7091583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091587 : List Nat := [1, 1, 1, 3, 5, 1, 2, 2, 3, 4]
def baseStart_7091587 : Nat := 118140960795 + 7091587 * 2 ^ 59
def prefixEnd_7091587 : Nat := 4983230072969 + 3 ^ 40 * 7091587 * 2
def baseEnd_7091587 : Nat := 1213797578058683622316297

theorem tailTrace_7091587 : CollatzResearch.WordTrace tailWord_7091587 prefixEnd_7091587 1213797578058683622316297 := by
  unfold tailWord_7091587
  simp only [CollatzResearch.WordTrace]
  refine ⟨258651426959398920480401015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172434284639599280320267343 258651426959398920480401015)
  ·
    refine ⟨387977140439098380720601523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258651426959398920480401015 387977140439098380720601523)
    ·
      refine ⟨581965710658647571080902285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387977140439098380720601523 581965710658647571080902285)
      ·
        refine ⟨218237141496992839155338357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 581965710658647571080902285 218237141496992839155338357)
        ·
          refine ⟨20459732015343078670812971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 218237141496992839155338357 20459732015343078670812971)
          ·
            refine ⟨30689598023014618006219457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20459732015343078670812971 30689598023014618006219457)
            ·
              refine ⟨23017198517260963504664593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30689598023014618006219457 23017198517260963504664593)
              ·
                refine ⟨17262898887945722628498445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23017198517260963504664593 17262898887945722628498445)
                ·
                  refine ⟨6473587082979645985686917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17262898887945722628498445 6473587082979645985686917)
                  ·
                    refine ⟨1213797578058683622316297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6473587082979645985686917 1213797578058683622316297)
                    ·
                      rfl

theorem cell23_7091587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 4].length) (baseStart_7091587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091587 prefixEnd_7091587 := by exact prefixLift 7091587
  have htrace : WordTrace (prefixWord ++ tailWord_7091587) baseStart_7091587 baseEnd_7091587 := by
    simpa [prefixWord, tailWord_7091587, baseEnd_7091587] using wordTrace_append hprefix tailTrace_7091587
  have hstable : (prefixWord ++ tailWord_7091587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091587).length < 2 ^ (prefixWord ++ tailWord_7091587).sum := by decide
  have hdescent : baseEnd_7091587 < baseStart_7091587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091680 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 6]
def baseStart_7091680 : Nat := 118140960795 + 7091680 * 2 ^ 59
def prefixEnd_7091680 : Nat := 4983230072969 + 3 ^ 40 * 7091680 * 2
def baseEnd_7091680 : Nat := 3641440487876919003085963

theorem tailTrace_7091680 : CollatzResearch.WordTrace tailWord_7091680 prefixEnd_7091680 3641440487876919003085963 := by
  unfold tailWord_7091680
  simp only [CollatzResearch.WordTrace]
  refine ⟨129327409474030998681768247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172436545965374664909024329 129327409474030998681768247)
  ·
    refine ⟨193991114211046498022652371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129327409474030998681768247 193991114211046498022652371)
    ·
      refine ⟨290986671316569747033978557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193991114211046498022652371 290986671316569747033978557)
      ·
        refine ⟨109120001743713655137741959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290986671316569747033978557 109120001743713655137741959)
        ·
          refine ⟨163680002615570482706612939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109120001743713655137741959 163680002615570482706612939)
          ·
            refine ⟨245520003923355724059919409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163680002615570482706612939 245520003923355724059919409)
            ·
              refine ⟨184140002942516793044939557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245520003923355724059919409 184140002942516793044939557)
              ·
                refine ⟨34526250551721898695926167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184140002942516793044939557 34526250551721898695926167)
                ·
                  refine ⟨51789375827582848043889251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34526250551721898695926167 51789375827582848043889251)
                  ·
                    refine ⟨77684063741374272065833877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51789375827582848043889251 77684063741374272065833877)
                    ·
                      refine ⟨3641440487876919003085963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77684063741374272065833877 3641440487876919003085963)
                      ·
                        rfl

theorem cell23_7091680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_7091680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091680 prefixEnd_7091680 := by exact prefixLift 7091680
  have htrace : WordTrace (prefixWord ++ tailWord_7091680) baseStart_7091680 baseEnd_7091680 := by
    simpa [prefixWord, tailWord_7091680, baseEnd_7091680] using wordTrace_append hprefix tailTrace_7091680
  have hstable : (prefixWord ++ tailWord_7091680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091680).length < 2 ^ (prefixWord ++ tailWord_7091680).sum := by decide
  have hdescent : baseEnd_7091680 < baseStart_7091680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
