import V185TrunkScan23Chunk0682

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4038509 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_4038509 : Nat := 118140960795 + 4038509 * 2 ^ 59
def prefixEnd_4038509 : Nat := 4983230072969 + 3 ^ 40 * 4038509 * 2
def baseEnd_4038509 : Nat := 2073696244508445048664741

theorem tailTrace_4038509 : CollatzResearch.WordTrace tailWord_4038509 prefixEnd_4038509 2073696244508445048664741 := by
  unfold tailWord_4038509
  simp only [CollatzResearch.WordTrace]
  refine ⟨147296524126179090270702581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98197682750786060180468387 147296524126179090270702581)
  ·
    refine ⟨13809049136829289712878367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147296524126179090270702581 13809049136829289712878367)
    ·
      refine ⟨20713573705243934569317551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13809049136829289712878367 20713573705243934569317551)
      ·
        refine ⟨31070360557865901853976327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20713573705243934569317551 31070360557865901853976327)
        ·
          refine ⟨46605540836798852780964491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31070360557865901853976327 46605540836798852780964491)
          ·
            refine ⟨69908311255198279171446737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46605540836798852780964491 69908311255198279171446737)
            ·
              refine ⟨52431233441398709378585053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69908311255198279171446737 52431233441398709378585053)
              ·
                refine ⟨19661712540524516016969395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52431233441398709378585053 19661712540524516016969395)
                ·
                  refine ⟨29492568810786774025454093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19661712540524516016969395 29492568810786774025454093)
                  ·
                    refine ⟨11059713304045040259545285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29492568810786774025454093 11059713304045040259545285)
                    ·
                      refine ⟨2073696244508445048664741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11059713304045040259545285 2073696244508445048664741)
                      ·
                        rfl

theorem cell23_4038509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_4038509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038509 prefixEnd_4038509 := by exact prefixLift 4038509
  have htrace : WordTrace (prefixWord ++ tailWord_4038509) baseStart_4038509 baseEnd_4038509 := by
    simpa [prefixWord, tailWord_4038509, baseEnd_4038509] using wordTrace_append hprefix tailTrace_4038509
  have hstable : (prefixWord ++ tailWord_4038509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038509).length < 2 ^ (prefixWord ++ tailWord_4038509).sum := by decide
  have hdescent : baseEnd_4038509 < baseStart_4038509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038549 : List Nat := [1, 3, 2, 1, 1, 3, 1, 5, 6]
def baseStart_4038549 : Nat := 118140960795 + 4038549 * 2 ^ 59
def prefixEnd_4038549 : Nat := 4983230072969 + 3 ^ 40 * 4038549 * 2
def baseEnd_4038549 : Nat := 230412975970513876907173

theorem tailTrace_4038549 : CollatzResearch.WordTrace tailWord_4038549 prefixEnd_4038549 230412975970513876907173 := by
  unfold tailWord_4038549
  simp only [CollatzResearch.WordTrace]
  refine ⟨147297983046034177102158701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98198655364022784734772467 147297983046034177102158701)
  ·
    refine ⟨55236743642262816413309513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147297983046034177102158701 55236743642262816413309513)
    ·
      refine ⟨41427557731697112309982135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55236743642262816413309513 41427557731697112309982135)
      ·
        refine ⟨62141336597545668464973203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41427557731697112309982135 62141336597545668464973203)
        ·
          refine ⟨93212004896318502697459805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62141336597545668464973203 93212004896318502697459805)
          ·
            refine ⟨34954501836119438511547427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93212004896318502697459805 34954501836119438511547427)
            ·
              refine ⟨52431752754179157767321141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34954501836119438511547427 52431752754179157767321141)
              ·
                refine ⟨4915476820704296040686357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52431752754179157767321141 4915476820704296040686357)
                ·
                  refine ⟨230412975970513876907173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4915476820704296040686357 230412975970513876907173)
                  ·
                    rfl

theorem cell23_4038549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 6].length) (baseStart_4038549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038549 prefixEnd_4038549 := by exact prefixLift 4038549
  have htrace : WordTrace (prefixWord ++ tailWord_4038549) baseStart_4038549 baseEnd_4038549 := by
    simpa [prefixWord, tailWord_4038549, baseEnd_4038549] using wordTrace_append hprefix tailTrace_4038549
  have hstable : (prefixWord ++ tailWord_4038549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038549).length < 2 ^ (prefixWord ++ tailWord_4038549).sum := by decide
  have hdescent : baseEnd_4038549 < baseStart_4038549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038609 : List Nat := [1, 2, 2, 1, 2, 1, 2, 5, 1, 6]
def baseStart_4038609 : Nat := 118140960795 + 4038609 * 2 ^ 59
def prefixEnd_4038609 : Nat := 4983230072969 + 3 ^ 40 * 4038609 * 2
def baseEnd_4038609 : Nat := 691249197524631552471427

theorem tailTrace_4038609 : CollatzResearch.WordTrace tailWord_4038609 prefixEnd_4038609 691249197524631552471427 := by
  unfold tailWord_4038609
  simp only [CollatzResearch.WordTrace]
  refine ⟨147300171425816807349342881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98200114283877871566228587 147300171425816807349342881)
  ·
    refine ⟨110475128569362605512007161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147300171425816807349342881 110475128569362605512007161)
    ·
      refine ⟨82856346427021954134005371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110475128569362605512007161 82856346427021954134005371)
      ·
        refine ⟨124284519640532931201008057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82856346427021954134005371 124284519640532931201008057)
        ·
          refine ⟨93213389730399698400756043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124284519640532931201008057 93213389730399698400756043)
          ·
            refine ⟨139820084595599547601134065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93213389730399698400756043 139820084595599547601134065)
            ·
              refine ⟨104865063446699660700850549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139820084595599547601134065 104865063446699660700850549)
              ·
                refine ⟨9831099698128093190704739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104865063446699660700850549 9831099698128093190704739)
                ·
                  refine ⟨14746649547192139786057109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9831099698128093190704739 14746649547192139786057109)
                  ·
                    refine ⟨691249197524631552471427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14746649547192139786057109 691249197524631552471427)
                    ·
                      rfl

theorem cell23_4038609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_4038609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038609 prefixEnd_4038609 := by exact prefixLift 4038609
  have htrace : WordTrace (prefixWord ++ tailWord_4038609) baseStart_4038609 baseEnd_4038609 := by
    simpa [prefixWord, tailWord_4038609, baseEnd_4038609] using wordTrace_append hprefix tailTrace_4038609
  have hstable : (prefixWord ++ tailWord_4038609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038609).length < 2 ^ (prefixWord ++ tailWord_4038609).sum := by decide
  have hdescent : baseEnd_4038609 < baseStart_4038609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038613 : List Nat := [1, 3, 2, 3, 2, 2, 2, 2, 1, 5]
def baseStart_4038613 : Nat := 118140960795 + 4038613 * 2 ^ 59
def prefixEnd_4038613 : Nat := 4983230072969 + 3 ^ 40 * 4038613 * 2
def baseEnd_4038613 : Nat := 691249882165504213921421

theorem tailTrace_4038613 : CollatzResearch.WordTrace tailWord_4038613 prefixEnd_4038613 691249882165504213921421 := by
  unfold tailWord_4038613
  simp only [CollatzResearch.WordTrace]
  refine ⟨147300317317802316032488493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98200211545201544021658995 147300317317802316032488493)
  ·
    refine ⟨55237618994175868512183185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147300317317802316032488493 55237618994175868512183185)
    ·
      refine ⟨41428214245631901384137389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55237618994175868512183185 41428214245631901384137389)
      ·
        refine ⟨15535580342111963019051521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41428214245631901384137389 15535580342111963019051521)
        ·
          refine ⟨11651685256583972264288641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15535580342111963019051521 11651685256583972264288641)
          ·
            refine ⟨8738763942437979198216481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11651685256583972264288641 8738763942437979198216481)
            ·
              refine ⟨6554072956828484398662361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8738763942437979198216481 6554072956828484398662361)
              ·
                refine ⟨4915554717621363298996771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6554072956828484398662361 4915554717621363298996771)
                ·
                  refine ⟨7373332076432044948495157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4915554717621363298996771 7373332076432044948495157)
                  ·
                    refine ⟨691249882165504213921421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7373332076432044948495157 691249882165504213921421)
                    ·
                      rfl

theorem cell23_4038613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_4038613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038613 prefixEnd_4038613 := by exact prefixLift 4038613
  have htrace : WordTrace (prefixWord ++ tailWord_4038613) baseStart_4038613 baseEnd_4038613 := by
    simpa [prefixWord, tailWord_4038613, baseEnd_4038613] using wordTrace_append hprefix tailTrace_4038613
  have hstable : (prefixWord ++ tailWord_4038613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038613).length < 2 ^ (prefixWord ++ tailWord_4038613).sum := by decide
  have hdescent : baseEnd_4038613 < baseStart_4038613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038616 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 2, 6, 2]
def baseStart_4038616 : Nat := 118140960795 + 4038616 * 2 ^ 59
def prefixEnd_4038616 : Nat := 4983230072969 + 3 ^ 40 * 4038616 * 2
def baseEnd_4038616 : Nat := 2073751186938476130026749

theorem tailTrace_4038616 : CollatzResearch.WordTrace tailWord_4038616 prefixEnd_4038616 2073751186938476130026749 := by
  unfold tailWord_4038616
  simp only [CollatzResearch.WordTrace]
  refine ⟨73650213368395723772423851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98200284491194298363231801 73650213368395723772423851)
  ·
    refine ⟨110475320052593585658635777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73650213368395723772423851 110475320052593585658635777)
    ·
      refine ⟨82856490039445189243976833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110475320052593585658635777 82856490039445189243976833)
      ·
        refine ⟨62142367529583891932982625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82856490039445189243976833 62142367529583891932982625)
        ·
          refine ⟨46606775647187918949736969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62142367529583891932982625 46606775647187918949736969)
          ·
            refine ⟨34955081735390939212302727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46606775647187918949736969 34955081735390939212302727)
            ·
              refine ⟨52432622603086408818454091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34955081735390939212302727 52432622603086408818454091)
              ·
                refine ⟨78648933904629613227681137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52432622603086408818454091 78648933904629613227681137)
                ·
                  refine ⟨58986700428472209920760853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78648933904629613227681137 58986700428472209920760853)
                  ·
                    refine ⟨2765001582584634840035665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58986700428472209920760853 2765001582584634840035665)
                    ·
                      refine ⟨2073751186938476130026749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2765001582584634840035665 2073751186938476130026749)
                      ·
                        rfl

theorem cell23_4038616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_4038616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038616 prefixEnd_4038616 := by exact prefixLift 4038616
  have htrace : WordTrace (prefixWord ++ tailWord_4038616) baseStart_4038616 baseEnd_4038616 := by
    simpa [prefixWord, tailWord_4038616, baseEnd_4038616] using wordTrace_append hprefix tailTrace_4038616
  have hstable : (prefixWord ++ tailWord_4038616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038616).length < 2 ^ (prefixWord ++ tailWord_4038616).sum := by decide
  have hdescent : baseEnd_4038616 < baseStart_4038616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038627 : List Nat := [1, 1, 1, 6, 1, 4, 1, 3, 1, 1, 3]
def baseStart_4038627 : Nat := 118140960795 + 4038627 * 2 ^ 59
def prefixEnd_4038627 : Nat := 4983230072969 + 3 ^ 40 * 4038627 * 2
def baseEnd_4038627 : Nat := 2073756835225675586989199

theorem tailTrace_4038627 : CollatzResearch.WordTrace tailWord_4038627 prefixEnd_4038627 2073756835225675586989199 := by
  unfold tailWord_4038627
  simp only [CollatzResearch.WordTrace]
  refine ⟨147300827939751596423498135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98200551959834397615665423 147300827939751596423498135)
  ·
    refine ⟨220951241909627394635247203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147300827939751596423498135 220951241909627394635247203)
    ·
      refine ⟨331426862864441091952870805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220951241909627394635247203 331426862864441091952870805)
      ·
        refine ⟨15535634196770676185290819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 331426862864441091952870805 15535634196770676185290819)
        ·
          refine ⟨23303451295156014277936229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15535634196770676185290819 23303451295156014277936229)
          ·
            refine ⟨4369397117841752677113043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23303451295156014277936229 4369397117841752677113043)
            ·
              refine ⟨6554095676762629015669565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4369397117841752677113043 6554095676762629015669565)
              ·
                refine ⟨2457785878785985880876087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6554095676762629015669565 2457785878785985880876087)
                ·
                  refine ⟨3686678818178978821314131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2457785878785985880876087 3686678818178978821314131)
                  ·
                    refine ⟨5530018227268468231971197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3686678818178978821314131 5530018227268468231971197)
                    ·
                      refine ⟨2073756835225675586989199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5530018227268468231971197 2073756835225675586989199)
                      ·
                        rfl

theorem cell23_4038627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_4038627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038627 prefixEnd_4038627 := by exact prefixLift 4038627
  have htrace : WordTrace (prefixWord ++ tailWord_4038627) baseStart_4038627 baseEnd_4038627 := by
    simpa [prefixWord, tailWord_4038627, baseEnd_4038627] using wordTrace_append hprefix tailTrace_4038627
  have hstable : (prefixWord ++ tailWord_4038627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038627).length < 2 ^ (prefixWord ++ tailWord_4038627).sum := by decide
  have hdescent : baseEnd_4038627 < baseStart_4038627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038637 : List Nat := [1, 5, 1, 4, 1, 1, 1, 2, 2, 3, 2]
def baseStart_4038637 : Nat := 118140960795 + 4038637 * 2 ^ 59
def prefixEnd_4038637 : Nat := 4983230072969 + 3 ^ 40 * 4038637 * 2
def baseEnd_4038637 : Nat := 2073761970032220547864153

theorem tailTrace_4038637 : CollatzResearch.WordTrace tailWord_4038637 prefixEnd_4038637 2073761970032220547864153 := by
  unfold tailWord_4038637
  simp only [CollatzResearch.WordTrace]
  refine ⟨147301192669715368131362165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98200795113143578754241443 147301192669715368131362165)
  ·
    refine ⟨13809486812785815762315203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147301192669715368131362165 13809486812785815762315203)
    ·
      refine ⟨20714230219178723643472805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13809486812785815762315203 20714230219178723643472805)
      ·
        refine ⟨3883918166096010683151151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20714230219178723643472805 3883918166096010683151151)
        ·
          refine ⟨5825877249144016024726727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3883918166096010683151151 5825877249144016024726727)
          ·
            refine ⟨8738815873716024037090091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5825877249144016024726727 8738815873716024037090091)
            ·
              refine ⟨13108223810574036055635137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8738815873716024037090091 13108223810574036055635137)
              ·
                refine ⟨9831167857930527041726353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13108223810574036055635137 9831167857930527041726353)
                ·
                  refine ⟨7373375893447895281294765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9831167857930527041726353 7373375893447895281294765)
                  ·
                    refine ⟨2765015960042960730485537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7373375893447895281294765 2765015960042960730485537)
                    ·
                      refine ⟨2073761970032220547864153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2765015960042960730485537 2073761970032220547864153)
                      ·
                        rfl

theorem cell23_4038637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_4038637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038637 prefixEnd_4038637 := by exact prefixLift 4038637
  have htrace : WordTrace (prefixWord ++ tailWord_4038637) baseStart_4038637 baseEnd_4038637 := by
    simpa [prefixWord, tailWord_4038637, baseEnd_4038637] using wordTrace_append hprefix tailTrace_4038637
  have hstable : (prefixWord ++ tailWord_4038637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038637).length < 2 ^ (prefixWord ++ tailWord_4038637).sum := by decide
  have hdescent : baseEnd_4038637 < baseStart_4038637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038706 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_4038706 : Nat := 118140960795 + 4038706 * 2 ^ 59
def prefixEnd_4038706 : Nat := 4983230072969 + 3 ^ 40 * 4038706 * 2
def baseEnd_4038706 : Nat := 2073797400197380777901335

theorem tailTrace_4038706 : CollatzResearch.WordTrace tailWord_4038706 prefixEnd_4038706 2073797400197380777901335 := by
  unfold tailWord_4038706
  simp only [CollatzResearch.WordTrace]
  refine ⟨36825927326616348228905993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98202472870976928610415981 36825927326616348228905993)
  ·
    refine ⟨27619445494962261171679495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36825927326616348228905993 27619445494962261171679495)
    ·
      refine ⟨41429168242443391757519243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27619445494962261171679495 41429168242443391757519243)
      ·
        refine ⟨62143752363665087636278865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41429168242443391757519243 62143752363665087636278865)
        ·
          refine ⟨46607814272748815727209149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62143752363665087636278865 46607814272748815727209149)
          ·
            refine ⟨17477930352280805897703431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46607814272748815727209149 17477930352280805897703431)
            ·
              refine ⟨26216895528421208846555147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17477930352280805897703431 26216895528421208846555147)
              ·
                refine ⟨39325343292631813269832721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26216895528421208846555147 39325343292631813269832721)
                ·
                  refine ⟨29494007469473859952374541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39325343292631813269832721 29494007469473859952374541)
                  ·
                    refine ⟨11060252801052697482140453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29494007469473859952374541 11060252801052697482140453)
                    ·
                      refine ⟨2073797400197380777901335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11060252801052697482140453 2073797400197380777901335)
                      ·
                        rfl

theorem cell23_4038706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_4038706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038706 prefixEnd_4038706 := by exact prefixLift 4038706
  have htrace : WordTrace (prefixWord ++ tailWord_4038706) baseStart_4038706 baseEnd_4038706 := by
    simpa [prefixWord, tailWord_4038706, baseEnd_4038706] using wordTrace_append hprefix tailTrace_4038706
  have hstable : (prefixWord ++ tailWord_4038706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038706).length < 2 ^ (prefixWord ++ tailWord_4038706).sum := by decide
  have hdescent : baseEnd_4038706 < baseStart_4038706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038710 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_4038710 : Nat := 118140960795 + 4038710 * 2 ^ 59
def prefixEnd_4038710 : Nat := 4983230072969 + 3 ^ 40 * 4038710 * 2
def baseEnd_4038710 : Nat := 2073799454119998762251317

theorem tailTrace_4038710 : CollatzResearch.WordTrace tailWord_4038710 prefixEnd_4038710 2073799454119998762251317 := by
  unfold tailWord_4038710
  simp only [CollatzResearch.WordTrace]
  refine ⟨9206490949903181349923099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98202570132300601065846389 9206490949903181349923099)
  ·
    refine ⟨13809736424854772024884649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9206490949903181349923099 13809736424854772024884649)
    ·
      refine ⟨10357302318641079018663487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13809736424854772024884649 10357302318641079018663487)
      ·
        refine ⟨15535953477961618527995231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10357302318641079018663487 15535953477961618527995231)
        ·
          refine ⟨23303930216942427791992847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15535953477961618527995231 23303930216942427791992847)
          ·
            refine ⟨34955895325413641687989271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23303930216942427791992847 34955895325413641687989271)
            ·
              refine ⟨52433842988120462531983907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34955895325413641687989271 52433842988120462531983907)
              ·
                refine ⟨78650764482180693797975861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52433842988120462531983907 78650764482180693797975861)
                ·
                  refine ⟨7373509170204440043560237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78650764482180693797975861 7373509170204440043560237)
                  ·
                    refine ⟨2765065938826665016335089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7373509170204440043560237 2765065938826665016335089)
                    ·
                      refine ⟨2073799454119998762251317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2765065938826665016335089 2073799454119998762251317)
                      ·
                        rfl

theorem cell23_4038710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_4038710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038710 prefixEnd_4038710 := by exact prefixLift 4038710
  have htrace : WordTrace (prefixWord ++ tailWord_4038710) baseStart_4038710 baseEnd_4038710 := by
    simpa [prefixWord, tailWord_4038710, baseEnd_4038710] using wordTrace_append hprefix tailTrace_4038710
  have hstable : (prefixWord ++ tailWord_4038710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038710).length < 2 ^ (prefixWord ++ tailWord_4038710).sum := by decide
  have hdescent : baseEnd_4038710 < baseStart_4038710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038716 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 2, 6]
def baseStart_4038716 : Nat := 118140960795 + 4038716 * 2 ^ 59
def prefixEnd_4038716 : Nat := 4983230072969 + 3 ^ 40 * 4038716 * 2
def baseEnd_4038716 : Nat := 691267511667975246258763

theorem tailTrace_4038716 : CollatzResearch.WordTrace tailWord_4038716 prefixEnd_4038716 691267511667975246258763 := by
  unfold tailWord_4038716
  simp only [CollatzResearch.WordTrace]
  refine ⟨73652037018214582311744001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98202716024286109748992001 73652037018214582311744001)
  ·
    refine ⟨55239027763660936733808001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73652037018214582311744001 55239027763660936733808001)
    ·
      refine ⟨41429270822745702550356001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55239027763660936733808001 41429270822745702550356001)
      ·
        refine ⟨31071953117059276912767001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41429270822745702550356001 31071953117059276912767001)
        ·
          refine ⟨23303964837794457684575251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31071953117059276912767001 23303964837794457684575251)
          ·
            refine ⟨34955947256691686526862877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23303964837794457684575251 34955947256691686526862877)
            ·
              refine ⟨13108480221259382447573579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34955947256691686526862877 13108480221259382447573579)
              ·
                refine ⟨19662720331889073671360369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13108480221259382447573579 19662720331889073671360369)
                ·
                  refine ⟨14747040248916805253520277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19662720331889073671360369 14747040248916805253520277)
                  ·
                    refine ⟨691267511667975246258763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14747040248916805253520277 691267511667975246258763)
                    ·
                      rfl

theorem cell23_4038716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_4038716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038716 prefixEnd_4038716 := by exact prefixLift 4038716
  have htrace : WordTrace (prefixWord ++ tailWord_4038716) baseStart_4038716 baseEnd_4038716 := by
    simpa [prefixWord, tailWord_4038716, baseEnd_4038716] using wordTrace_append hprefix tailTrace_4038716
  have hstable : (prefixWord ++ tailWord_4038716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038716).length < 2 ^ (prefixWord ++ tailWord_4038716).sum := by decide
  have hdescent : baseEnd_4038716 < baseStart_4038716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038740 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 4, 2, 2]
def baseStart_4038740 : Nat := 118140960795 + 4038740 * 2 ^ 59
def prefixEnd_4038740 : Nat := 4983230072969 + 3 ^ 40 * 4038740 * 2
def baseEnd_4038740 : Nat := 2073814858539633644876179

theorem tailTrace_4038740 : CollatzResearch.WordTrace tailWord_4038740 prefixEnd_4038740 2073814858539633644876179 := by
  unfold tailWord_4038740
  simp only [CollatzResearch.WordTrace]
  refine ⟨73652474694171108361180837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98203299592228144481574449 73652474694171108361180837)
  ·
    refine ⟨13809839005157082817721407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73652474694171108361180837 13809839005157082817721407)
    ·
      refine ⟨20714758507735624226582111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13809839005157082817721407 20714758507735624226582111)
      ·
        refine ⟨31072137761603436339873167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20714758507735624226582111 31072137761603436339873167)
        ·
          refine ⟨46608206642405154509809751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31072137761603436339873167 46608206642405154509809751)
          ·
            refine ⟨69912309963607731764714627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46608206642405154509809751 69912309963607731764714627)
            ·
              refine ⟨104868464945411597647071941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69912309963607731764714627 104868464945411597647071941)
              ·
                refine ⟨19662837177264674558825989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104868464945411597647071941 19662837177264674558825989)
                ·
                  refine ⟨3686781970737126479779873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19662837177264674558825989 3686781970737126479779873)
                  ·
                    refine ⟨2765086478052844859834905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3686781970737126479779873 2765086478052844859834905)
                    ·
                      refine ⟨2073814858539633644876179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2765086478052844859834905 2073814858539633644876179)
                      ·
                        rfl

theorem cell23_4038740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_4038740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038740 prefixEnd_4038740 := by exact prefixLift 4038740
  have htrace : WordTrace (prefixWord ++ tailWord_4038740) baseStart_4038740 baseEnd_4038740 := by
    simpa [prefixWord, tailWord_4038740, baseEnd_4038740] using wordTrace_append hprefix tailTrace_4038740
  have hstable : (prefixWord ++ tailWord_4038740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038740).length < 2 ^ (prefixWord ++ tailWord_4038740).sum := by decide
  have hdescent : baseEnd_4038740 < baseStart_4038740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038757 : List Nat := [1, 3, 1, 3, 2, 2, 3, 2, 2, 2, 2]
def baseStart_4038757 : Nat := 118140960795 + 4038757 * 2 ^ 59
def prefixEnd_4038757 : Nat := 4983230072969 + 3 ^ 40 * 4038757 * 2
def baseEnd_4038757 : Nat := 2073823587710760078363601

theorem tailTrace_4038757 : CollatzResearch.WordTrace tailWord_4038757 prefixEnd_4038757 2073823587710760078363601 := by
  unfold tailWord_4038757
  simp only [CollatzResearch.WordTrace]
  refine ⟨147305569429280628625730525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98203712952853752417153683 147305569429280628625730525)
  ·
    refine ⟨55239588535980235734648947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147305569429280628625730525 55239588535980235734648947)
    ·
      refine ⟨82859382803970353601973421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55239588535980235734648947 82859382803970353601973421)
      ·
        refine ⟨31072268551488882600740033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82859382803970353601973421 31072268551488882600740033)
        ·
          refine ⟨23304201413616661950555025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31072268551488882600740033 23304201413616661950555025)
          ·
            refine ⟨17478151060212496462916269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23304201413616661950555025 17478151060212496462916269)
            ·
              refine ⟨6554306647579686173593601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17478151060212496462916269 6554306647579686173593601)
              ·
                refine ⟨4915729985684764630195201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6554306647579686173593601 4915729985684764630195201)
                ·
                  refine ⟨3686797489263573472646401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4915729985684764630195201 3686797489263573472646401)
                  ·
                    refine ⟨2765098116947680104484801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3686797489263573472646401 2765098116947680104484801)
                    ·
                      refine ⟨2073823587710760078363601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2765098116947680104484801 2073823587710760078363601)
                      ·
                        rfl

theorem cell23_4038757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_4038757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038757 prefixEnd_4038757 := by exact prefixLift 4038757
  have htrace : WordTrace (prefixWord ++ tailWord_4038757) baseStart_4038757 baseEnd_4038757 := by
    simpa [prefixWord, tailWord_4038757, baseEnd_4038757] using wordTrace_append hprefix tailTrace_4038757
  have hstable : (prefixWord ++ tailWord_4038757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038757).length < 2 ^ (prefixWord ++ tailWord_4038757).sum := by decide
  have hdescent : baseEnd_4038757 < baseStart_4038757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038810 : List Nat := [3, 1, 1, 5, 2, 1, 1, 2, 2, 5]
def baseStart_4038810 : Nat := 118140960795 + 4038810 * 2 ^ 59
def prefixEnd_4038810 : Nat := 4983230072969 + 3 ^ 40 * 4038810 * 2
def baseEnd_4038810 : Nat := 691283600728482790333619

theorem tailTrace_4038810 : CollatzResearch.WordTrace tailWord_4038810 prefixEnd_4038810 691283600728482790333619 := by
  unfold tailWord_4038810
  simp only [CollatzResearch.WordTrace]
  refine ⟨36826875624522154669352471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98205001665392412451606589 36826875624522154669352471)
  ·
    refine ⟨55240313436783232004028707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36826875624522154669352471 55240313436783232004028707)
    ·
      refine ⟨82860470155174848006043061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55240313436783232004028707 82860470155174848006043061)
      ·
        refine ⟨7768169077047642000566537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82860470155174848006043061 7768169077047642000566537)
        ·
          refine ⟨5826126807785731500424903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7768169077047642000566537 5826126807785731500424903)
          ·
            refine ⟨8739190211678597250637355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5826126807785731500424903 8739190211678597250637355)
            ·
              refine ⟨13108785317517895875956033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8739190211678597250637355 13108785317517895875956033)
              ·
                refine ⟨9831588988138421906967025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13108785317517895875956033 9831588988138421906967025)
                ·
                  refine ⟨7373691741103816430225269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9831588988138421906967025 7373691741103816430225269)
                  ·
                    refine ⟨691283600728482790333619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7373691741103816430225269 691283600728482790333619)
                    ·
                      rfl

theorem cell23_4038810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_4038810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038810 prefixEnd_4038810 := by exact prefixLift 4038810
  have htrace : WordTrace (prefixWord ++ tailWord_4038810) baseStart_4038810 baseEnd_4038810 := by
    simpa [prefixWord, tailWord_4038810, baseEnd_4038810] using wordTrace_append hprefix tailTrace_4038810
  have hstable : (prefixWord ++ tailWord_4038810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038810).length < 2 ^ (prefixWord ++ tailWord_4038810).sum := by decide
  have hdescent : baseEnd_4038810 < baseStart_4038810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038813 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_4038813 : Nat := 118140960795 + 4038813 * 2 ^ 59
def prefixEnd_4038813 : Nat := 4983230072969 + 3 ^ 40 * 4038813 * 2
def baseEnd_4038813 : Nat := 2073852342627411859263343

theorem tailTrace_4038813 : CollatzResearch.WordTrace tailWord_4038813 prefixEnd_4038813 2073852342627411859263343 := by
  unfold tailWord_4038813
  simp only [CollatzResearch.WordTrace]
  refine ⟨147307611917077750189769093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98205074611385166793179395 147307611917077750189769093)
  ·
    refine ⟨27620177234452078160581705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147307611917077750189769093 27620177234452078160581705)
    ·
      refine ⟨20715132925839058620436279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27620177234452078160581705 20715132925839058620436279)
      ·
        refine ⟨31072699388758587930654419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20715132925839058620436279 31072699388758587930654419)
        ·
          refine ⟨46609049083137881895981629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31072699388758587930654419 46609049083137881895981629)
          ·
            refine ⟨17478393406176705710993111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46609049083137881895981629 17478393406176705710993111)
            ·
              refine ⟨26217590109265058566489667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17478393406176705710993111 26217590109265058566489667)
              ·
                refine ⟨39326385163897587849734501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26217590109265058566489667 39326385163897587849734501)
                ·
                  refine ⟨7373697218230797721825219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39326385163897587849734501 7373697218230797721825219)
                  ·
                    refine ⟨11060545827346196582737829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7373697218230797721825219 11060545827346196582737829)
                    ·
                      refine ⟨2073852342627411859263343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11060545827346196582737829 2073852342627411859263343)
                      ·
                        rfl

theorem cell23_4038813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_4038813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038813 prefixEnd_4038813 := by exact prefixLift 4038813
  have htrace : WordTrace (prefixWord ++ tailWord_4038813) baseStart_4038813 baseEnd_4038813 := by
    simpa [prefixWord, tailWord_4038813, baseEnd_4038813] using wordTrace_append hprefix tailTrace_4038813
  have hstable : (prefixWord ++ tailWord_4038813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038813).length < 2 ^ (prefixWord ++ tailWord_4038813).sum := by decide
  have hdescent : baseEnd_4038813 < baseStart_4038813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038814 : List Nat := [4, 3, 1, 1, 3, 1, 3, 2, 5]
def baseStart_4038814 : Nat := 118140960795 + 4038814 * 2 ^ 59
def prefixEnd_4038814 : Nat := 4983230072969 + 3 ^ 40 * 4038814 * 2
def baseEnd_4038814 : Nat := 230428095123118483927871

theorem tailTrace_4038814 : CollatzResearch.WordTrace tailWord_4038814 prefixEnd_4038814 230428095123118483927871 := by
  unfold tailWord_4038814
  simp only [CollatzResearch.WordTrace]
  refine ⟨18413456048759265920069437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98205098926716084907036997 18413456048759265920069437)
  ·
    refine ⟨6905046018284724720026039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18413456048759265920069437 6905046018284724720026039)
    ·
      refine ⟨10357569027427087080039059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6905046018284724720026039 10357569027427087080039059)
      ·
        refine ⟨15536353541140630620058589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10357569027427087080039059 15536353541140630620058589)
        ·
          refine ⟨5826132577927736482521971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15536353541140630620058589 5826132577927736482521971)
          ·
            refine ⟨8739198866891604723782957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5826132577927736482521971 8739198866891604723782957)
            ·
              refine ⟨3277199575084351771418609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8739198866891604723782957 3277199575084351771418609)
              ·
                refine ⟨2457899681313263828563957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3277199575084351771418609 2457899681313263828563957)
                ·
                  refine ⟨230428095123118483927871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2457899681313263828563957 230428095123118483927871)
                  ·
                    rfl

theorem cell23_4038814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_4038814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038814 prefixEnd_4038814 := by exact prefixLift 4038814
  have htrace : WordTrace (prefixWord ++ tailWord_4038814) baseStart_4038814 baseEnd_4038814 := by
    simpa [prefixWord, tailWord_4038814, baseEnd_4038814] using wordTrace_append hprefix tailTrace_4038814
  have hstable : (prefixWord ++ tailWord_4038814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038814).length < 2 ^ (prefixWord ++ tailWord_4038814).sum := by decide
  have hdescent : baseEnd_4038814 < baseStart_4038814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038856 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_4038856 : Nat := 118140960795 + 4038856 * 2 ^ 59
def prefixEnd_4038856 : Nat := 4983230072969 + 3 ^ 40 * 4038856 * 2
def baseEnd_4038856 : Nat := 2073874422295555191025645

theorem tailTrace_4038856 : CollatzResearch.WordTrace tailWord_4038856 prefixEnd_4038856 2073874422295555191025645 := by
  unfold tailWord_4038856
  simp only [CollatzResearch.WordTrace]
  refine ⟨73654590127960984266792211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98206120170614645689056281 73654590127960984266792211)
  ·
    refine ⟨110481885191941476400188317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73654590127960984266792211 110481885191941476400188317)
    ·
      refine ⟨41430706946978053650070619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110481885191941476400188317 41430706946978053650070619)
      ·
        refine ⟨62146060420467080475105929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41430706946978053650070619 62146060420467080475105929)
        ·
          refine ⟨46609545315350310356329447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62146060420467080475105929 46609545315350310356329447)
          ·
            refine ⟨69914317973025465534494171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46609545315350310356329447 69914317973025465534494171)
            ·
              refine ⟨104871476959538198301741257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69914317973025465534494171 104871476959538198301741257)
              ·
                refine ⟨78653607719653648726305943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104871476959538198301741257 78653607719653648726305943)
                ·
                  refine ⟨117980411579480473089458915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78653607719653648726305943 117980411579480473089458915)
                  ·
                    refine ⟨176970617369220709634188373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117980411579480473089458915 176970617369220709634188373)
                    ·
                      refine ⟨2073874422295555191025645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 176970617369220709634188373 2073874422295555191025645)
                      ·
                        rfl

theorem cell23_4038856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_4038856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038856 prefixEnd_4038856 := by exact prefixLift 4038856
  have htrace : WordTrace (prefixWord ++ tailWord_4038856) baseStart_4038856 baseEnd_4038856 := by
    simpa [prefixWord, tailWord_4038856, baseEnd_4038856] using wordTrace_append hprefix tailTrace_4038856
  have hstable : (prefixWord ++ tailWord_4038856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038856).length < 2 ^ (prefixWord ++ tailWord_4038856).sum := by decide
  have hdescent : baseEnd_4038856 < baseStart_4038856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038880 : List Nat := [2, 1, 1, 3, 1, 3, 2, 3, 3, 1, 3]
def baseStart_4038880 : Nat := 118140960795 + 4038880 * 2 ^ 59
def prefixEnd_4038880 : Nat := 4983230072969 + 3 ^ 40 * 4038880 * 2
def baseEnd_4038880 : Nat := 2073886745831263097125535

theorem tailTrace_4038880 : CollatzResearch.WordTrace tailWord_4038880 prefixEnd_4038880 2073886745831263097125535 := by
  unfold tailWord_4038880
  simp only [CollatzResearch.WordTrace]
  refine ⟨73655027803917510316229047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98206703738556680421638729 73655027803917510316229047)
  ·
    refine ⟨110482541705876265474343571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73655027803917510316229047 110482541705876265474343571)
    ·
      refine ⟨165723812558814398211515357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110482541705876265474343571 165723812558814398211515357)
      ·
        refine ⟨62146429709555399329318259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165723812558814398211515357 62146429709555399329318259)
        ·
          refine ⟨93219644564333098993977389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62146429709555399329318259 93219644564333098993977389)
          ·
            refine ⟨34957366711624912122741521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93219644564333098993977389 34957366711624912122741521)
            ·
              refine ⟨26218025033718684092056141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34957366711624912122741521 26218025033718684092056141)
              ·
                refine ⟨9831759387644506534521053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26218025033718684092056141 9831759387644506534521053)
                ·
                  refine ⟨3686909770366689950445395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9831759387644506534521053 3686909770366689950445395)
                  ·
                    refine ⟨5530364655550034925668093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3686909770366689950445395 5530364655550034925668093)
                    ·
                      refine ⟨2073886745831263097125535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5530364655550034925668093 2073886745831263097125535)
                      ·
                        rfl

theorem cell23_4038880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_4038880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038880 prefixEnd_4038880 := by exact prefixLift 4038880
  have htrace : WordTrace (prefixWord ++ tailWord_4038880) baseStart_4038880 baseEnd_4038880 := by
    simpa [prefixWord, tailWord_4038880, baseEnd_4038880] using wordTrace_append hprefix tailTrace_4038880
  have hstable : (prefixWord ++ tailWord_4038880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038880).length < 2 ^ (prefixWord ++ tailWord_4038880).sum := by decide
  have hdescent : baseEnd_4038880 < baseStart_4038880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038890 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 1, 5, 2]
def baseStart_4038890 : Nat := 118140960795 + 4038890 * 2 ^ 59
def prefixEnd_4038890 : Nat := 4983230072969 + 3 ^ 40 * 4038890 * 2
def baseEnd_4038890 : Nat := 2073891880637808058000489

theorem tailTrace_4038890 : CollatzResearch.WordTrace tailWord_4038890 prefixEnd_4038890 2073891880637808058000489 := by
  unfold tailWord_4038890
  simp only [CollatzResearch.WordTrace]
  refine ⟨36827605084449698085080531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98206946891865861560214749 36827605084449698085080531)
  ·
    refine ⟨55241407626674547127620797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36827605084449698085080531 55241407626674547127620797)
    ·
      refine ⟨20715527860002955172857799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55241407626674547127620797 20715527860002955172857799)
      ·
        refine ⟨31073291790004432759286699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20715527860002955172857799 31073291790004432759286699)
        ·
          refine ⟨46609937685006649138930049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31073291790004432759286699 46609937685006649138930049)
          ·
            refine ⟨34957453263754986854197537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46609937685006649138930049 34957453263754986854197537)
            ·
              refine ⟨26218089947816240140648153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34957453263754986854197537 26218089947816240140648153)
              ·
                refine ⟨19663567460862180105486115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26218089947816240140648153 19663567460862180105486115)
                ·
                  refine ⟨29495351191293270158229173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19663567460862180105486115 29495351191293270158229173)
                  ·
                    refine ⟨2765189174183744077333985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29495351191293270158229173 2765189174183744077333985)
                    ·
                      refine ⟨2073891880637808058000489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2765189174183744077333985 2073891880637808058000489)
                      ·
                        rfl

theorem cell23_4038890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_4038890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038890 prefixEnd_4038890 := by exact prefixLift 4038890
  have htrace : WordTrace (prefixWord ++ tailWord_4038890) baseStart_4038890 baseEnd_4038890 := by
    simpa [prefixWord, tailWord_4038890, baseEnd_4038890] using wordTrace_append hprefix tailTrace_4038890
  have hstable : (prefixWord ++ tailWord_4038890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038890).length < 2 ^ (prefixWord ++ tailWord_4038890).sum := by decide
  have hdescent : baseEnd_4038890 < baseStart_4038890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038913 : List Nat := [1, 2, 4, 1, 1, 2, 1, 4, 1, 6]
def baseStart_4038913 : Nat := 118140960795 + 4038913 * 2 ^ 59
def prefixEnd_4038913 : Nat := 4983230072969 + 3 ^ 40 * 4038913 * 2
def baseEnd_4038913 : Nat := 691301230230953822670961

theorem tailTrace_4038913 : CollatzResearch.WordTrace tailWord_4038913 prefixEnd_4038913 691301230230953822670961 := by
  unfold tailWord_4038913
  simp only [CollatzResearch.WordTrace]
  refine ⟨147311259216715467268409393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98207506144476978178939595 147311259216715467268409393)
  ·
    refine ⟨110483444412536600451307045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147311259216715467268409393 110483444412536600451307045)
    ·
      refine ⟨20715645827350612584620071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110483444412536600451307045 20715645827350612584620071)
      ·
        refine ⟨31073468741025918876930107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20715645827350612584620071 31073468741025918876930107)
        ·
          refine ⟨46610203111538878315395161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31073468741025918876930107 46610203111538878315395161)
          ·
            refine ⟨34957652333654158736546371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46610203111538878315395161 34957652333654158736546371)
            ·
              refine ⟨52436478500481238104819557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34957652333654158736546371 52436478500481238104819557)
              ·
                refine ⟨9831839718840232144653667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52436478500481238104819557 9831839718840232144653667)
                ·
                  refine ⟨14747759578260348216980501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9831839718840232144653667 14747759578260348216980501)
                  ·
                    refine ⟨691301230230953822670961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14747759578260348216980501 691301230230953822670961)
                    ·
                      rfl

theorem cell23_4038913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_4038913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038913 prefixEnd_4038913 := by exact prefixLift 4038913
  have htrace : WordTrace (prefixWord ++ tailWord_4038913) baseStart_4038913 baseEnd_4038913 := by
    simpa [prefixWord, tailWord_4038913, baseEnd_4038913] using wordTrace_append hprefix tailTrace_4038913
  have hstable : (prefixWord ++ tailWord_4038913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038913).length < 2 ^ (prefixWord ++ tailWord_4038913).sum := by decide
  have hdescent : baseEnd_4038913 < baseStart_4038913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038923 : List Nat := [1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 5]
def baseStart_4038923 : Nat := 118140960795 + 4038923 * 2 ^ 59
def prefixEnd_4038923 : Nat := 4983230072969 + 3 ^ 40 * 4038923 * 2
def baseEnd_4038923 : Nat := 2073908825499406428887837

theorem tailTrace_4038923 : CollatzResearch.WordTrace tailWord_4038923 prefixEnd_4038923 2073908825499406428887837 := by
  unfold tailWord_4038923
  simp only [CollatzResearch.WordTrace]
  refine ⟨147311623946679238976273423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98207749297786159317515615 147311623946679238976273423)
  ·
    refine ⟨220967435920018858464410135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147311623946679238976273423 220967435920018858464410135)
    ·
      refine ⟨331451153880028287696615203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220967435920018858464410135 331451153880028287696615203)
      ·
        refine ⟨497176730820042431544922805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331451153880028287696615203 497176730820042431544922805)
        ·
          refine ⟨46610318514378977957336513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 497176730820042431544922805 46610318514378977957336513)
          ·
            refine ⟨34957738885784233468002385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46610318514378977957336513 34957738885784233468002385)
            ·
              refine ⟨26218304164338175101001789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34957738885784233468002385 26218304164338175101001789)
              ·
                refine ⟨9831864061626815662875671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26218304164338175101001789 9831864061626815662875671)
                ·
                  refine ⟨14747796092440223494313507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9831864061626815662875671 14747796092440223494313507)
                  ·
                    refine ⟨22121694138660335241470261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14747796092440223494313507 22121694138660335241470261)
                    ·
                      refine ⟨2073908825499406428887837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22121694138660335241470261 2073908825499406428887837)
                      ·
                        rfl

theorem cell23_4038923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 5].length) (baseStart_4038923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038923 prefixEnd_4038923 := by exact prefixLift 4038923
  have htrace : WordTrace (prefixWord ++ tailWord_4038923) baseStart_4038923 baseEnd_4038923 := by
    simpa [prefixWord, tailWord_4038923, baseEnd_4038923] using wordTrace_append hprefix tailTrace_4038923
  have hstable : (prefixWord ++ tailWord_4038923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038923).length < 2 ^ (prefixWord ++ tailWord_4038923).sum := by decide
  have hdescent : baseEnd_4038923 < baseStart_4038923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038933 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_4038933 : Nat := 118140960795 + 4038933 * 2 ^ 59
def prefixEnd_4038933 : Nat := 4983230072969 + 3 ^ 40 * 4038933 * 2
def baseEnd_4038933 : Nat := 2073913960305951389762791

theorem tailTrace_4038933 : CollatzResearch.WordTrace tailWord_4038933 prefixEnd_4038933 2073913960305951389762791 := by
  unfold tailWord_4038933
  simp only [CollatzResearch.WordTrace]
  refine ⟨147311988676643010684137453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98207992451095340456091635 147311988676643010684137453)
  ·
    refine ⟨55241995753741129006551545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147311988676643010684137453 55241995753741129006551545)
    ·
      refine ⟨41431496815305846754913659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55241995753741129006551545 41431496815305846754913659)
      ·
        refine ⟨62147245222958770132370489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41431496815305846754913659 62147245222958770132370489)
        ·
          refine ⟨46610433917219077599277867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62147245222958770132370489 46610433917219077599277867)
          ·
            refine ⟨69915650875828616398916801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46610433917219077599277867 69915650875828616398916801)
            ·
              refine ⟨52436738156871462299187601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69915650875828616398916801 52436738156871462299187601)
              ·
                refine ⟨39327553617653596724390701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52436738156871462299187601 39327553617653596724390701)
                ·
                  refine ⟨14747832606620098771646513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39327553617653596724390701 14747832606620098771646513)
                  ·
                    refine ⟨11060874454965074078734885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14747832606620098771646513 11060874454965074078734885)
                    ·
                      refine ⟨2073913960305951389762791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11060874454965074078734885 2073913960305951389762791)
                      ·
                        rfl

theorem cell23_4038933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_4038933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038933 prefixEnd_4038933 := by exact prefixLift 4038933
  have htrace : WordTrace (prefixWord ++ tailWord_4038933) baseStart_4038933 baseEnd_4038933 := by
    simpa [prefixWord, tailWord_4038933, baseEnd_4038933] using wordTrace_append hprefix tailTrace_4038933
  have hstable : (prefixWord ++ tailWord_4038933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038933).length < 2 ^ (prefixWord ++ tailWord_4038933).sum := by decide
  have hdescent : baseEnd_4038933 < baseStart_4038933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038947 : List Nat := [1, 1, 1, 4, 2, 2, 5, 1, 2, 4]
def baseStart_4038947 : Nat := 118140960795 + 4038947 * 2 ^ 59
def prefixEnd_4038947 : Nat := 4983230072969 + 3 ^ 40 * 4038947 * 2
def baseEnd_4038947 : Nat := 691307049678371444995909

theorem tailTrace_4038947 : CollatzResearch.WordTrace tailWord_4038947 prefixEnd_4038947 691307049678371444995909 := by
  unfold tailWord_4038947
  simp only [CollatzResearch.WordTrace]
  refine ⟨147312499298592291075147095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98208332865728194050098063 147312499298592291075147095)
  ·
    refine ⟨220968748947888436612720643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147312499298592291075147095 220968748947888436612720643)
    ·
      refine ⟨331453123421832654919080965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220968748947888436612720643 331453123421832654919080965)
      ·
        refine ⟨62147460641593622797327681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331453123421832654919080965 62147460641593622797327681)
        ·
          refine ⟨46610595481195217097995761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62147460641593622797327681 46610595481195217097995761)
          ·
            refine ⟨34957946610896412823496821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46610595481195217097995761 34957946610896412823496821)
            ·
              refine ⟨3277307494771538702202827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34957946610896412823496821 3277307494771538702202827)
              ·
                refine ⟨4915961242157308053304241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3277307494771538702202827 4915961242157308053304241)
                ·
                  refine ⟨3686970931617981039978181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4915961242157308053304241 3686970931617981039978181)
                  ·
                    refine ⟨691307049678371444995909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3686970931617981039978181 691307049678371444995909)
                    ·
                      rfl

theorem cell23_4038947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 2, 4].length) (baseStart_4038947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038947 prefixEnd_4038947 := by exact prefixLift 4038947
  have htrace : WordTrace (prefixWord ++ tailWord_4038947) baseStart_4038947 baseEnd_4038947 := by
    simpa [prefixWord, tailWord_4038947, baseEnd_4038947] using wordTrace_append hprefix tailTrace_4038947
  have hstable : (prefixWord ++ tailWord_4038947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038947).length < 2 ^ (prefixWord ++ tailWord_4038947).sum := by decide
  have hdescent : baseEnd_4038947 < baseStart_4038947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038951 : List Nat := [1, 1, 8, 1, 1, 1, 2, 2, 1, 5]
def baseStart_4038951 : Nat := 118140960795 + 4038951 * 2 ^ 59
def prefixEnd_4038951 : Nat := 4983230072969 + 3 ^ 40 * 4038951 * 2
def baseEnd_4038951 : Nat := 691307734319244106445903

theorem tailTrace_4038951 : CollatzResearch.WordTrace tailWord_4038951 prefixEnd_4038951 691307734319244106445903 := by
  unfold tailWord_4038951
  simp only [CollatzResearch.WordTrace]
  refine ⟨147312645190577799758292707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98208430127051866505528471 147312645190577799758292707)
  ·
    refine ⟨220968967785866699637439061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147312645190577799758292707 220968967785866699637439061)
    ·
      refine ⟨2589480091240625386376239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 220968967785866699637439061 2589480091240625386376239)
      ·
        refine ⟨3884220136860938079564359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2589480091240625386376239 3884220136860938079564359)
        ·
          refine ⟨5826330205291407119346539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3884220136860938079564359 5826330205291407119346539)
          ·
            refine ⟨8739495307937110679019809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5826330205291407119346539 8739495307937110679019809)
            ·
              refine ⟨6554621480952833009264857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8739495307937110679019809 6554621480952833009264857)
              ·
                refine ⟨4915966110714624756948643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6554621480952833009264857 4915966110714624756948643)
                ·
                  refine ⟨7373949166071937135422965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4915966110714624756948643 7373949166071937135422965)
                  ·
                    refine ⟨691307734319244106445903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7373949166071937135422965 691307734319244106445903)
                    ·
                      rfl

theorem cell23_4038951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_4038951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038951 prefixEnd_4038951 := by exact prefixLift 4038951
  have htrace : WordTrace (prefixWord ++ tailWord_4038951) baseStart_4038951 baseEnd_4038951 := by
    simpa [prefixWord, tailWord_4038951, baseEnd_4038951] using wordTrace_append hprefix tailTrace_4038951
  have hstable : (prefixWord ++ tailWord_4038951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038951).length < 2 ^ (prefixWord ++ tailWord_4038951).sum := by decide
  have hdescent : baseEnd_4038951 < baseStart_4038951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038954 : List Nat := [3, 1, 4, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_4038954 : Nat := 118140960795 + 4038954 * 2 ^ 59
def prefixEnd_4038954 : Nat := 4983230072969 + 3 ^ 40 * 4038954 * 2
def baseEnd_4038954 : Nat := 2073924743399695807600195

theorem tailTrace_4038954 : CollatzResearch.WordTrace tailWord_4038954 prefixEnd_4038954 2073924743399695807600195 := by
  unfold tailWord_4038954
  simp only [CollatzResearch.WordTrace]
  refine ⟨36828188652391732817662979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98208503073044620847101277 36828188652391732817662979)
  ·
    refine ⟨55242282978587599226494469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36828188652391732817662979 55242282978587599226494469)
    ·
      refine ⟨10357928058485174854967713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55242282978587599226494469 10357928058485174854967713)
      ·
        refine ⟨7768446043863881141225785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10357928058485174854967713 7768446043863881141225785)
        ·
          refine ⟨5826334532897910855919339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7768446043863881141225785 5826334532897910855919339)
          ·
            refine ⟨8739501799346866283879009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5826334532897910855919339 8739501799346866283879009)
            ·
              refine ⟨6554626349510149712909257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8739501799346866283879009 6554626349510149712909257)
              ·
                refine ⟨4915969762132612284681943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6554626349510149712909257 4915969762132612284681943)
                ·
                  refine ⟨7373954643198918427022915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4915969762132612284681943 7373954643198918427022915)
                  ·
                    refine ⟨11060931964798377640534373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7373954643198918427022915 11060931964798377640534373)
                    ·
                      refine ⟨2073924743399695807600195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11060931964798377640534373 2073924743399695807600195)
                      ·
                        rfl

theorem cell23_4038954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_4038954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038954 prefixEnd_4038954 := by exact prefixLift 4038954
  have htrace : WordTrace (prefixWord ++ tailWord_4038954) baseStart_4038954 baseEnd_4038954 := by
    simpa [prefixWord, tailWord_4038954, baseEnd_4038954] using wordTrace_append hprefix tailTrace_4038954
  have hstable : (prefixWord ++ tailWord_4038954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038954).length < 2 ^ (prefixWord ++ tailWord_4038954).sum := by decide
  have hdescent : baseEnd_4038954 < baseStart_4038954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038977 : List Nat := [1, 2, 5, 2, 3, 1, 9]
def baseStart_4038977 : Nat := 118140960795 + 4038977 * 2 ^ 59
def prefixEnd_4038977 : Nat := 4983230072969 + 3 ^ 40 * 4038977 * 2
def baseEnd_4038977 : Nat := 25604154980922829847069

theorem tailTrace_4038977 : CollatzResearch.WordTrace tailWord_4038977 prefixEnd_4038977 25604154980922829847069 := by
  unfold tailWord_4038977
  simp only [CollatzResearch.WordTrace]
  refine ⟨147313593488483606198739185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98209062325655737465826123 147313593488483606198739185)
  ·
    refine ⟨110485195116362704649054389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147313593488483606198739185 110485195116362704649054389)
    ·
      refine ⟨10357987042159003560848849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110485195116362704649054389 10357987042159003560848849)
      ·
        refine ⟨7768490281619252670636637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10357987042159003560848849 7768490281619252670636637)
        ·
          refine ⟨2913183855607219751488739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7768490281619252670636637 2913183855607219751488739)
          ·
            refine ⟨4369775783410829627233109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2913183855607219751488739 4369775783410829627233109)
            ·
              refine ⟨25604154980922829847069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4369775783410829627233109 25604154980922829847069)
              ·
                rfl

theorem cell23_4038977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 9].length) (baseStart_4038977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038977 prefixEnd_4038977 := by exact prefixLift 4038977
  have htrace : WordTrace (prefixWord ++ tailWord_4038977) baseStart_4038977 baseEnd_4038977 := by
    simpa [prefixWord, tailWord_4038977, baseEnd_4038977] using wordTrace_append hprefix tailTrace_4038977
  have hstable : (prefixWord ++ tailWord_4038977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038977).length < 2 ^ (prefixWord ++ tailWord_4038977).sum := by decide
  have hdescent : baseEnd_4038977 < baseStart_4038977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038983 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_4038983 : Nat := 118140960795 + 4038983 * 2 ^ 59
def prefixEnd_4038983 : Nat := 4983230072969 + 3 ^ 40 * 4038983 * 2
def baseEnd_4038983 : Nat := 2073939634338676194137561

theorem tailTrace_4038983 : CollatzResearch.WordTrace tailWord_4038983 prefixEnd_4038983 2073939634338676194137561 := by
  unfold tailWord_4038983
  simp only [CollatzResearch.WordTrace]
  refine ⟨147313812326461869223457603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98209208217641246148971735 147313812326461869223457603)
  ·
    refine ⟨220970718489692803835186405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147313812326461869223457603 220970718489692803835186405)
    ·
      refine ⟨41432009716817400719097451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220970718489692803835186405 41432009716817400719097451)
      ·
        refine ⟨62148014575226101078646177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41432009716817400719097451 62148014575226101078646177)
        ·
          refine ⟨46611010931419575808984633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62148014575226101078646177 46611010931419575808984633)
          ·
            refine ⟨34958258198564681856738475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46611010931419575808984633 34958258198564681856738475)
            ·
              refine ⟨52437387297847022785107713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34958258198564681856738475 52437387297847022785107713)
              ·
                refine ⟨39328040473385267088830785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52437387297847022785107713 39328040473385267088830785)
                ·
                  refine ⟨29496030355038950316623089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39328040473385267088830785 29496030355038950316623089)
                  ·
                    refine ⟨22122022766279212737467317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29496030355038950316623089 22122022766279212737467317)
                    ·
                      refine ⟨2073939634338676194137561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22122022766279212737467317 2073939634338676194137561)
                      ·
                        rfl

theorem cell23_4038983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_4038983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038983 prefixEnd_4038983 := by exact prefixLift 4038983
  have htrace : WordTrace (prefixWord ++ tailWord_4038983) baseStart_4038983 baseEnd_4038983 := by
    simpa [prefixWord, tailWord_4038983, baseEnd_4038983] using wordTrace_append hprefix tailTrace_4038983
  have hstable : (prefixWord ++ tailWord_4038983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038983).length < 2 ^ (prefixWord ++ tailWord_4038983).sum := by decide
  have hdescent : baseEnd_4038983 < baseStart_4038983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039023 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 4]
def baseStart_4039023 : Nat := 118140960795 + 4039023 * 2 ^ 59
def prefixEnd_4039023 : Nat := 4983230072969 + 3 ^ 40 * 4039023 * 2
def baseEnd_4039023 : Nat := 2073960173564856037637377

theorem tailTrace_4039023 : CollatzResearch.WordTrace tailWord_4039023 prefixEnd_4039023 2073960173564856037637377 := by
  unfold tailWord_4039023
  simp only [CollatzResearch.WordTrace]
  refine ⟨147315271246316956054913723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98210180830877970703275815 147315271246316956054913723)
  ·
    refine ⟨220972906869475434082370585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147315271246316956054913723 220972906869475434082370585)
    ·
      refine ⟨165729680152106575561777939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220972906869475434082370585 165729680152106575561777939)
      ·
        refine ⟨248594520228159863342666909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165729680152106575561777939 248594520228159863342666909)
        ·
          refine ⟨93222945085559948753500091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248594520228159863342666909 93222945085559948753500091)
          ·
            refine ⟨139834417628339923130250137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93222945085559948753500091 139834417628339923130250137)
            ·
              refine ⟨104875813221254942347687603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139834417628339923130250137 104875813221254942347687603)
              ·
                refine ⟨157313719831882413521531405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104875813221254942347687603 157313719831882413521531405)
                ·
                  refine ⟨58992644936955905070574277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157313719831882413521531405 58992644936955905070574277)
                  ·
                    refine ⟨11061120925679232200732677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58992644936955905070574277 11061120925679232200732677)
                    ·
                      refine ⟨2073960173564856037637377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11061120925679232200732677 2073960173564856037637377)
                      ·
                        rfl

theorem cell23_4039023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_4039023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039023 prefixEnd_4039023 := by exact prefixLift 4039023
  have htrace : WordTrace (prefixWord ++ tailWord_4039023) baseStart_4039023 baseEnd_4039023 := by
    simpa [prefixWord, tailWord_4039023, baseEnd_4039023] using wordTrace_append hprefix tailTrace_4039023
  have hstable : (prefixWord ++ tailWord_4039023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039023).length < 2 ^ (prefixWord ++ tailWord_4039023).sum := by decide
  have hdescent : baseEnd_4039023 < baseStart_4039023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039082 : List Nat := [3, 1, 6, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_4039082 : Nat := 118140960795 + 4039082 * 2 ^ 59
def prefixEnd_4039082 : Nat := 4983230072969 + 3 ^ 40 * 4039082 * 2
def baseEnd_4039082 : Nat := 2073990468923471306799607

theorem tailTrace_4039082 : CollatzResearch.WordTrace tailWord_4039082 prefixEnd_4039082 2073990468923471306799607 := by
  unfold tailWord_4039082
  simp only [CollatzResearch.WordTrace]
  refine ⟨36829355788275802282827875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98211615435402139420874333 36829355788275802282827875)
  ·
    refine ⟨55244033682413703424241813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36829355788275802282827875 55244033682413703424241813)
    ·
      refine ⟨2589564078863142348011335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55244033682413703424241813 2589564078863142348011335)
      ·
        refine ⟨3884346118294713522017003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2589564078863142348011335 3884346118294713522017003)
        ·
          refine ⟨5826519177442070283025505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3884346118294713522017003 5826519177442070283025505)
          ·
            refine ⟨4369889383081552712269129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5826519177442070283025505 4369889383081552712269129)
            ·
              refine ⟨3277417037311164534201847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4369889383081552712269129 3277417037311164534201847)
              ·
                refine ⟨4916125555966746801302771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3277417037311164534201847 4916125555966746801302771)
                ·
                  refine ⟨7374188333950120201954157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4916125555966746801302771 7374188333950120201954157)
                  ·
                    refine ⟨2765320625231295075732809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7374188333950120201954157 2765320625231295075732809)
                    ·
                      refine ⟨2073990468923471306799607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2765320625231295075732809 2073990468923471306799607)
                      ·
                        rfl

theorem cell23_4039082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_4039082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039082 prefixEnd_4039082 := by exact prefixLift 4039082
  have htrace : WordTrace (prefixWord ++ tailWord_4039082) baseStart_4039082 baseEnd_4039082 := by
    simpa [prefixWord, tailWord_4039082, baseEnd_4039082] using wordTrace_append hprefix tailTrace_4039082
  have hstable : (prefixWord ++ tailWord_4039082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039082).length < 2 ^ (prefixWord ++ tailWord_4039082).sum := by decide
  have hdescent : baseEnd_4039082 < baseStart_4039082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039130 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4]
def baseStart_4039130 : Nat := 118140960795 + 4039130 * 2 ^ 59
def prefixEnd_4039130 : Nat := 4983230072969 + 3 ^ 40 * 4039130 * 2
def baseEnd_4039130 : Nat := 2074015115994887118999385

theorem tailTrace_4039130 : CollatzResearch.WordTrace tailWord_4039130 prefixEnd_4039130 2074015115994887118999385 := by
  unfold tailWord_4039130
  simp only [CollatzResearch.WordTrace]
  refine ⟨36829793464232328332264711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98212782571286208886039229 36829793464232328332264711)
  ·
    refine ⟨55244690196348492498397067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36829793464232328332264711 55244690196348492498397067)
    ·
      refine ⟨82867035294522738747595601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55244690196348492498397067 82867035294522738747595601)
      ·
        refine ⟨62150276470892054060696701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82867035294522738747595601 62150276470892054060696701)
        ·
          refine ⟨23306353676584520272761263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62150276470892054060696701 23306353676584520272761263)
          ·
            refine ⟨34959530514876780409141895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23306353676584520272761263 34959530514876780409141895)
            ·
              refine ⟨52439295772315170613712843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34959530514876780409141895 52439295772315170613712843)
              ·
                refine ⟨78658943658472755920569265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52439295772315170613712843 78658943658472755920569265)
                ·
                  refine ⟨58994207743854566940426949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78658943658472755920569265 58994207743854566940426949)
                  ·
                    refine ⟨11061413951972731301330053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58994207743854566940426949 11061413951972731301330053)
                    ·
                      refine ⟨2074015115994887118999385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11061413951972731301330053 2074015115994887118999385)
                      ·
                        rfl

theorem cell23_4039130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_4039130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039130 prefixEnd_4039130 := by exact prefixLift 4039130
  have htrace : WordTrace (prefixWord ++ tailWord_4039130) baseStart_4039130 baseEnd_4039130 := by
    simpa [prefixWord, tailWord_4039130, baseEnd_4039130] using wordTrace_append hprefix tailTrace_4039130
  have hstable : (prefixWord ++ tailWord_4039130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039130).length < 2 ^ (prefixWord ++ tailWord_4039130).sum := by decide
  have hdescent : baseEnd_4039130 < baseStart_4039130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039137 : List Nat := [1, 2, 3, 1, 2, 2, 2, 3, 2, 2, 3]
def baseStart_4039137 : Nat := 118140960795 + 4039137 * 2 ^ 59
def prefixEnd_4039137 : Nat := 4983230072969 + 3 ^ 40 * 4039137 * 2
def baseEnd_4039137 : Nat := 2074018710359468591611853

theorem tailTrace_4039137 : CollatzResearch.WordTrace tailWord_4039137 prefixEnd_4039137 2074018710359468591611853 := by
  unfold tailWord_4039137
  simp only [CollatzResearch.WordTrace]
  refine ⟨147319429167903953524563665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98212952778602635683042443 147319429167903953524563665)
  ·
    refine ⟨110489571875927965143422749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147319429167903953524563665 110489571875927965143422749)
    ·
      refine ⟨41433589453472986928783531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110489571875927965143422749 41433589453472986928783531)
      ·
        refine ⟨62150384180209480393175297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41433589453472986928783531 62150384180209480393175297)
        ·
          refine ⟨46612788135157110294881473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62150384180209480393175297 46612788135157110294881473)
          ·
            refine ⟨34959591101367832721161105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46612788135157110294881473 34959591101367832721161105)
            ·
              refine ⟨26219693326025874540870829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34959591101367832721161105 26219693326025874540870829)
              ·
                refine ⟨9832384997259702952826561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26219693326025874540870829 9832384997259702952826561)
                ·
                  refine ⟨7374288747944777214619921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9832384997259702952826561 7374288747944777214619921)
                  ·
                    refine ⟨5530716560958582910964941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7374288747944777214619921 5530716560958582910964941)
                    ·
                      refine ⟨2074018710359468591611853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5530716560958582910964941 2074018710359468591611853)
                      ·
                        rfl

theorem cell23_4039137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_4039137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039137 prefixEnd_4039137 := by exact prefixLift 4039137
  have htrace : WordTrace (prefixWord ++ tailWord_4039137) baseStart_4039137 baseEnd_4039137 := by
    simpa [prefixWord, tailWord_4039137, baseEnd_4039137] using wordTrace_append hprefix tailTrace_4039137
  have hstable : (prefixWord ++ tailWord_4039137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039137).length < 2 ^ (prefixWord ++ tailWord_4039137).sum := by decide
  have hdescent : baseEnd_4039137 < baseStart_4039137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039177 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 1, 5, 2]
def baseStart_4039177 : Nat := 118140960795 + 4039177 * 2 ^ 59
def prefixEnd_4039177 : Nat := 4983230072969 + 3 ^ 40 * 4039177 * 2
def baseEnd_4039177 : Nat := 2074039249585648435111669

theorem tailTrace_4039177 : CollatzResearch.WordTrace tailWord_4039177 prefixEnd_4039177 2074039249585648435111669 := by
  unfold tailWord_4039177
  simp only [CollatzResearch.WordTrace]
  refine ⟨147320888087759040356019785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98213925391839360237346523 147320888087759040356019785)
  ·
    refine ⟨110490666065819280267014839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147320888087759040356019785 110490666065819280267014839)
    ·
      refine ⟨165735999098728920400522259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110490666065819280267014839 165735999098728920400522259)
      ·
        refine ⟨248603998648093380600783389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165735999098728920400522259 248603998648093380600783389)
        ·
          refine ⟨93226499493035017725293771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248603998648093380600783389 93226499493035017725293771)
          ·
            refine ⟨139839749239552526587940657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93226499493035017725293771 139839749239552526587940657)
            ·
              refine ⟨104879811929664394940955493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139839749239552526587940657 104879811929664394940955493)
              ·
                refine ⟨19664964736812074051429155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104879811929664394940955493 19664964736812074051429155)
                ·
                  refine ⟨29497447105218111077143733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19664964736812074051429155 29497447105218111077143733)
                  ·
                    refine ⟨2765385666114197913482225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29497447105218111077143733 2765385666114197913482225)
                    ·
                      refine ⟨2074039249585648435111669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2765385666114197913482225 2074039249585648435111669)
                      ·
                        rfl

theorem cell23_4039177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 5, 2].length) (baseStart_4039177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039177 prefixEnd_4039177 := by exact prefixLift 4039177
  have htrace : WordTrace (prefixWord ++ tailWord_4039177) baseStart_4039177 baseEnd_4039177 := by
    simpa [prefixWord, tailWord_4039177, baseEnd_4039177] using wordTrace_append hprefix tailTrace_4039177
  have hstable : (prefixWord ++ tailWord_4039177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039177).length < 2 ^ (prefixWord ++ tailWord_4039177).sum := by decide
  have hdescent : baseEnd_4039177 < baseStart_4039177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039194 : List Nat := [3, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2]
def baseStart_4039194 : Nat := 118140960795 + 4039194 * 2 ^ 59
def prefixEnd_4039194 : Nat := 4983230072969 + 3 ^ 40 * 4039194 * 2
def baseEnd_4039194 : Nat := 2074047978756774868599091

theorem tailTrace_4039194 : CollatzResearch.WordTrace tailWord_4039194 prefixEnd_4039194 2074047978756774868599091 := by
  unfold tailWord_4039194
  simp only [CollatzResearch.WordTrace]
  refine ⟨36830377032174363064847159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98214338752464968172925757 36830377032174363064847159)
  ·
    refine ⟨55245565548261544597270739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36830377032174363064847159 55245565548261544597270739)
    ·
      refine ⟨82868348322392316895906109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55245565548261544597270739 82868348322392316895906109)
      ·
        refine ⟨31075630620897118835964791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82868348322392316895906109 31075630620897118835964791)
        ·
          refine ⟨46613445931345678253947187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31075630620897118835964791 46613445931345678253947187)
          ·
            refine ⟨69920168897018517380920781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46613445931345678253947187 69920168897018517380920781)
            ·
              refine ⟨26220063336381944017845293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69920168897018517380920781 26220063336381944017845293)
              ·
                refine ⟨9832523751143229006691985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26220063336381944017845293 9832523751143229006691985)
                ·
                  refine ⟨7374392813357421755018989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9832523751143229006691985 7374392813357421755018989)
                  ·
                    refine ⟨2765397305009033158132121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7374392813357421755018989 2765397305009033158132121)
                    ·
                      refine ⟨2074047978756774868599091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2765397305009033158132121 2074047978756774868599091)
                      ·
                        rfl

theorem cell23_4039194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_4039194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039194 prefixEnd_4039194 := by exact prefixLift 4039194
  have htrace : WordTrace (prefixWord ++ tailWord_4039194) baseStart_4039194 baseEnd_4039194 := by
    simpa [prefixWord, tailWord_4039194, baseEnd_4039194] using wordTrace_append hprefix tailTrace_4039194
  have hstable : (prefixWord ++ tailWord_4039194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039194).length < 2 ^ (prefixWord ++ tailWord_4039194).sum := by decide
  have hdescent : baseEnd_4039194 < baseStart_4039194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039201 : List Nat := [1, 2, 3, 2, 2, 1, 2, 5, 1, 1, 3]
def baseStart_4039201 : Nat := 118140960795 + 4039201 * 2 ^ 59
def prefixEnd_4039201 : Nat := 4983230072969 + 3 ^ 40 * 4039201 * 2
def baseEnd_4039201 : Nat := 2074051573121356341211559

theorem tailTrace_4039201 : CollatzResearch.WordTrace tailWord_4039201 prefixEnd_4039201 2074051573121356341211559 := by
  unfold tailWord_4039201
  simp only [CollatzResearch.WordTrace]
  refine ⟨147321763439672092454893457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98214508959781394969928971 147321763439672092454893457)
  ·
    refine ⟨110491322579754069341170093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147321763439672092454893457 110491322579754069341170093)
    ·
      refine ⟨41434245967407776002938785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110491322579754069341170093 41434245967407776002938785)
      ·
        refine ⟨31075684475555832002204089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41434245967407776002938785 31075684475555832002204089)
        ·
          refine ⟨23306763356666874001653067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31075684475555832002204089 23306763356666874001653067)
          ·
            refine ⟨34960145035000311002479601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23306763356666874001653067 34960145035000311002479601)
            ·
              refine ⟨26220108776250233251859701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34960145035000311002479601 26220108776250233251859701)
              ·
                refine ⟨2458135197773459367361847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26220108776250233251859701 2458135197773459367361847)
                ·
                  refine ⟨3687202796660189051042771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2458135197773459367361847 3687202796660189051042771)
                  ·
                    refine ⟨5530804194990283576564157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3687202796660189051042771 5530804194990283576564157)
                    ·
                      refine ⟨2074051573121356341211559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5530804194990283576564157 2074051573121356341211559)
                      ·
                        rfl

theorem cell23_4039201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_4039201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039201 prefixEnd_4039201 := by exact prefixLift 4039201
  have htrace : WordTrace (prefixWord ++ tailWord_4039201) baseStart_4039201 baseEnd_4039201 := by
    simpa [prefixWord, tailWord_4039201, baseEnd_4039201] using wordTrace_append hprefix tailTrace_4039201
  have hstable : (prefixWord ++ tailWord_4039201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039201).length < 2 ^ (prefixWord ++ tailWord_4039201).sum := by decide
  have hdescent : baseEnd_4039201 < baseStart_4039201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039217 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 4, 4]
def baseStart_4039217 : Nat := 118140960795 + 4039217 * 2 ^ 59
def prefixEnd_4039217 : Nat := 4983230072969 + 3 ^ 40 * 4039217 * 2
def baseEnd_4039217 : Nat := 691353262937276092870495

theorem tailTrace_4039217 : CollatzResearch.WordTrace tailWord_4039217 prefixEnd_4039217 691353262937276092870495 := by
  unfold tailWord_4039217
  simp only [CollatzResearch.WordTrace]
  refine ⟨147322347007614127187475905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98214898005076084791650603 147322347007614127187475905)
  ·
    refine ⟨110491760255710595390606929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147322347007614127187475905 110491760255710595390606929)
    ·
      refine ⟨82868820191782946542955197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110491760255710595390606929 82868820191782946542955197)
      ·
        refine ⟨31075807571918604953608199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82868820191782946542955197 31075807571918604953608199)
        ·
          refine ⟨46613711357877907430412299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31075807571918604953608199 46613711357877907430412299)
          ·
            refine ⟨69920567036816861145618449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46613711357877907430412299 69920567036816861145618449)
            ·
              refine ⟨52440425277612645859213837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69920567036816861145618449 52440425277612645859213837)
              ·
                refine ⟨19665159479104742197205189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52440425277612645859213837 19665159479104742197205189)
                ·
                  refine ⟨3687217402332139161975973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19665159479104742197205189 3687217402332139161975973)
                  ·
                    refine ⟨691353262937276092870495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3687217402332139161975973 691353262937276092870495)
                    ·
                      rfl

theorem cell23_4039217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_4039217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039217 prefixEnd_4039217 := by exact prefixLift 4039217
  have htrace : WordTrace (prefixWord ++ tailWord_4039217) baseStart_4039217 baseEnd_4039217 := by
    simpa [prefixWord, tailWord_4039217, baseEnd_4039217] using wordTrace_append hprefix tailTrace_4039217
  have hstable : (prefixWord ++ tailWord_4039217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039217).length < 2 ^ (prefixWord ++ tailWord_4039217).sum := by decide
  have hdescent : baseEnd_4039217 < baseStart_4039217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039218 : List Nat := [3, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3]
def baseStart_4039218 : Nat := 118140960795 + 4039218 * 2 ^ 59
def prefixEnd_4039218 : Nat := 4983230072969 + 3 ^ 40 * 4039218 * 2
def baseEnd_4039218 : Nat := 2074060302292482774698981

theorem tailTrace_4039218 : CollatzResearch.WordTrace tailWord_4039218 prefixEnd_4039218 2074060302292482774698981 := by
  unfold tailWord_4039218
  simp only [CollatzResearch.WordTrace]
  refine ⟨36830595870152626089565577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98214922320407002905508205 36830595870152626089565577)
  ·
    refine ⟨27622946902614469567174183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36830595870152626089565577 27622946902614469567174183)
    ·
      refine ⟨41434420353921704350761275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27622946902614469567174183 41434420353921704350761275)
      ·
        refine ⟨62151630530882556526141913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41434420353921704350761275 62151630530882556526141913)
        ·
          refine ⟨46613722898161917394606435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62151630530882556526141913 46613722898161917394606435)
          ·
            refine ⟨69920584347242876091909653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46613722898161917394606435 69920584347242876091909653)
            ·
              refine ⟨3277527391277009816808265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69920584347242876091909653 3277527391277009816808265)
              ·
                refine ⟨2458145543457757362606199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3277527391277009816808265 2458145543457757362606199)
                ·
                  refine ⟨3687218315186636043909299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2458145543457757362606199 3687218315186636043909299)
                  ·
                    refine ⟨5530827472779954065863949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3687218315186636043909299 5530827472779954065863949)
                    ·
                      refine ⟨2074060302292482774698981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5530827472779954065863949 2074060302292482774698981)
                      ·
                        rfl

theorem cell23_4039218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_4039218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039218 prefixEnd_4039218 := by exact prefixLift 4039218
  have htrace : WordTrace (prefixWord ++ tailWord_4039218) baseStart_4039218 baseEnd_4039218 := by
    simpa [prefixWord, tailWord_4039218, baseEnd_4039218] using wordTrace_append hprefix tailTrace_4039218
  have hstable : (prefixWord ++ tailWord_4039218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039218).length < 2 ^ (prefixWord ++ tailWord_4039218).sum := by decide
  have hdescent : baseEnd_4039218 < baseStart_4039218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039237 : List Nat := [1, 3, 1, 1, 1, 5, 1, 3, 1, 2, 4]
def baseStart_4039237 : Nat := 118140960795 + 4039237 * 2 ^ 59
def prefixEnd_4039237 : Nat := 4983230072969 + 3 ^ 40 * 4039237 * 2
def baseEnd_4039237 : Nat := 2074070058424918200361393

theorem tailTrace_4039237 : CollatzResearch.WordTrace tailWord_4039237 prefixEnd_4039237 2074070058424918200361393 := by
  unfold tailWord_4039237
  simp only [CollatzResearch.WordTrace]
  refine ⟨147323076467541670603203965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98215384311694447068802643 147323076467541670603203965)
  ·
    refine ⟨55246153675328126476201487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147323076467541670603203965 55246153675328126476201487)
    ·
      refine ⟨82869230512992189714302231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55246153675328126476201487 82869230512992189714302231)
      ·
        refine ⟨124303845769488284571453347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82869230512992189714302231 124303845769488284571453347)
        ·
          refine ⟨186455768654232426857180021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124303845769488284571453347 186455768654232426857180021)
          ·
            refine ⟨17480228311334290017860627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186455768654232426857180021 17480228311334290017860627)
            ·
              refine ⟨26220342467001435026790941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17480228311334290017860627 26220342467001435026790941)
              ·
                refine ⟨9832628425125538135046603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26220342467001435026790941 9832628425125538135046603)
                ·
                  refine ⟨14748942637688307202569905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9832628425125538135046603 14748942637688307202569905)
                  ·
                    refine ⟨11061706978266230401927429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14748942637688307202569905 11061706978266230401927429)
                    ·
                      refine ⟨2074070058424918200361393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11061706978266230401927429 2074070058424918200361393)
                      ·
                        rfl

theorem cell23_4039237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_4039237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039237 prefixEnd_4039237 := by exact prefixLift 4039237
  have htrace : WordTrace (prefixWord ++ tailWord_4039237) baseStart_4039237 baseEnd_4039237 := by
    simpa [prefixWord, tailWord_4039237, baseEnd_4039237] using wordTrace_append hprefix tailTrace_4039237
  have hstable : (prefixWord ++ tailWord_4039237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039237).length < 2 ^ (prefixWord ++ tailWord_4039237).sum := by decide
  have hdescent : baseEnd_4039237 < baseStart_4039237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039240 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_4039240 : Nat := 118140960795 + 4039240 * 2 ^ 59
def prefixEnd_4039240 : Nat := 4983230072969 + 3 ^ 40 * 4039240 * 2
def baseEnd_4039240 : Nat := 2074071598866881688623879

theorem tailTrace_4039240 : CollatzResearch.WordTrace tailWord_4039240 prefixEnd_4039240 2074071598866881688623879 := by
  unfold tailWord_4039240
  simp only [CollatzResearch.WordTrace]
  refine ⟨73661592943265401057781587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98215457257687201410375449 73661592943265401057781587)
  ·
    refine ⟨110492389414898101586672381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73661592943265401057781587 110492389414898101586672381)
    ·
      refine ⟨41434646030586788095002143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110492389414898101586672381 41434646030586788095002143)
      ·
        refine ⟨62151969045880182142503215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41434646030586788095002143 62151969045880182142503215)
        ·
          refine ⟨93227953568820273213754823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62151969045880182142503215 93227953568820273213754823)
          ·
            refine ⟨139841930353230409820632235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93227953568820273213754823 139841930353230409820632235)
            ·
              refine ⟨209762895529845614730948353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139841930353230409820632235 209762895529845614730948353)
              ·
                refine ⟨157322171647384211048211265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209762895529845614730948353 157322171647384211048211265)
                ·
                  refine ⟨117991628735538158286158449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157322171647384211048211265 117991628735538158286158449)
                  ·
                    refine ⟨88493721551653618714618837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117991628735538158286158449 88493721551653618714618837)
                    ·
                      refine ⟨2074071598866881688623879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88493721551653618714618837 2074071598866881688623879)
                      ·
                        rfl

theorem cell23_4039240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_4039240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039240 prefixEnd_4039240 := by exact prefixLift 4039240
  have htrace : WordTrace (prefixWord ++ tailWord_4039240) baseStart_4039240 baseEnd_4039240 := by
    simpa [prefixWord, tailWord_4039240, baseEnd_4039240] using wordTrace_append hprefix tailTrace_4039240
  have hstable : (prefixWord ++ tailWord_4039240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039240).length < 2 ^ (prefixWord ++ tailWord_4039240).sum := by decide
  have hdescent : baseEnd_4039240 < baseStart_4039240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039244 : List Nat := [2, 2, 1, 3, 1, 2, 2, 4, 1, 2, 3]
def baseStart_4039244 : Nat := 118140960795 + 4039244 * 2 ^ 59
def prefixEnd_4039244 : Nat := 4983230072969 + 3 ^ 40 * 4039244 * 2
def baseEnd_4039244 : Nat := 2074073652789499672973861

theorem tailTrace_4039244 : CollatzResearch.WordTrace tailWord_4039244 prefixEnd_4039244 2074073652789499672973861 := by
  unfold tailWord_4039244
  simp only [CollatzResearch.WordTrace]
  refine ⟨73661665889258155399354393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98215554519010873865805857 73661665889258155399354393)
  ·
    refine ⟨55246249416943616549515795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73661665889258155399354393 55246249416943616549515795)
    ·
      refine ⟨82869374125415424824273693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55246249416943616549515795 82869374125415424824273693)
      ·
        refine ⟨31076015297030784309102635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82869374125415424824273693 31076015297030784309102635)
        ·
          refine ⟨46614022945546176463653953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31076015297030784309102635 46614022945546176463653953)
          ·
            refine ⟨34960517209159632347740465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46614022945546176463653953 34960517209159632347740465)
            ·
              refine ⟨26220387906869724260805349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34960517209159632347740465 26220387906869724260805349)
              ·
                refine ⟨4916322732538073298901003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26220387906869724260805349 4916322732538073298901003)
                ·
                  refine ⟨7374484098807109948351505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4916322732538073298901003 7374484098807109948351505)
                  ·
                    refine ⟨5530863074105332461263629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7374484098807109948351505 5530863074105332461263629)
                    ·
                      refine ⟨2074073652789499672973861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5530863074105332461263629 2074073652789499672973861)
                      ·
                        rfl

theorem cell23_4039244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_4039244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039244 prefixEnd_4039244 := by exact prefixLift 4039244
  have htrace : WordTrace (prefixWord ++ tailWord_4039244) baseStart_4039244 baseEnd_4039244 := by
    simpa [prefixWord, tailWord_4039244, baseEnd_4039244] using wordTrace_append hprefix tailTrace_4039244
  have hstable : (prefixWord ++ tailWord_4039244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039244).length < 2 ^ (prefixWord ++ tailWord_4039244).sum := by decide
  have hdescent : baseEnd_4039244 < baseStart_4039244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039298 : List Nat := [3, 4, 3, 1, 1, 1, 1, 9]
def baseStart_4039298 : Nat := 118140960795 + 4039298 * 2 ^ 59
def prefixEnd_4039298 : Nat := 4983230072969 + 3 ^ 40 * 4039298 * 2
def baseEnd_4039298 : Nat := 76818569657216387470319

theorem tailTrace_4039298 : CollatzResearch.WordTrace tailWord_4039298 prefixEnd_4039298 76818569657216387470319 := by
  unfold tailWord_4039298
  simp only [CollatzResearch.WordTrace]
  refine ⟨36831325330080169505293637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98216867546880452014116365 36831325330080169505293637)
  ·
    refine ⟨6905873499390031782242557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36831325330080169505293637 6905873499390031782242557)
    ·
      refine ⟨2589702562271261918340959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6905873499390031782242557 2589702562271261918340959)
      ·
        refine ⟨3884553843406892877511439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2589702562271261918340959 3884553843406892877511439)
        ·
          refine ⟨5826830765110339316267159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3884553843406892877511439 5826830765110339316267159)
          ·
            refine ⟨8740246147665508974400739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5826830765110339316267159 8740246147665508974400739)
            ·
              refine ⟨13110369221498263461601109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8740246147665508974400739 13110369221498263461601109)
              ·
                refine ⟨76818569657216387470319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13110369221498263461601109 76818569657216387470319)
                ·
                  rfl

theorem cell23_4039298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 9].length) (baseStart_4039298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039298 prefixEnd_4039298 := by exact prefixLift 4039298
  have htrace : WordTrace (prefixWord ++ tailWord_4039298) baseStart_4039298 baseEnd_4039298 := by
    simpa [prefixWord, tailWord_4039298, baseEnd_4039298] using wordTrace_append hprefix tailTrace_4039298
  have hstable : (prefixWord ++ tailWord_4039298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039298).length < 2 ^ (prefixWord ++ tailWord_4039298).sum := by decide
  have hdescent : baseEnd_4039298 < baseStart_4039298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039301 : List Nat := [1, 3, 1, 1, 4, 2, 1, 4, 1, 3, 2]
def baseStart_4039301 : Nat := 118140960795 + 4039301 * 2 ^ 59
def prefixEnd_4039301 : Nat := 4983230072969 + 3 ^ 40 * 4039301 * 2
def baseEnd_4039301 : Nat := 2074102921186805949961099

theorem tailTrace_4039301 : CollatzResearch.WordTrace tailWord_4039301 prefixEnd_4039301 2074102921186805949961099 := by
  unfold tailWord_4039301
  simp only [CollatzResearch.WordTrace]
  refine ⟨147325410739309809533533757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98216940492873206355689171 147325410739309809533533757)
  ·
    refine ⟨55247029027241178575075159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147325410739309809533533757 55247029027241178575075159)
    ·
      refine ⟨82870543540861767862612739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55247029027241178575075159 82870543540861767862612739)
      ·
        refine ⟨124305815311292651793919109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82870543540861767862612739 124305815311292651793919109)
        ·
          refine ⟨23307340370867372211359833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124305815311292651793919109 23307340370867372211359833)
          ·
            refine ⟨17480505278150529158519875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23307340370867372211359833 17480505278150529158519875)
            ·
              refine ⟨26220757917225793737779813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17480505278150529158519875 26220757917225793737779813)
              ·
                refine ⟨4916392109479836325833715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26220757917225793737779813 4916392109479836325833715)
                ·
                  refine ⟨7374588164219754488750573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4916392109479836325833715 7374588164219754488750573)
                  ·
                    refine ⟨2765470561582407933281465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7374588164219754488750573 2765470561582407933281465)
                    ·
                      refine ⟨2074102921186805949961099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2765470561582407933281465 2074102921186805949961099)
                      ·
                        rfl

theorem cell23_4039301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 3, 2].length) (baseStart_4039301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039301 prefixEnd_4039301 := by exact prefixLift 4039301
  have htrace : WordTrace (prefixWord ++ tailWord_4039301) baseStart_4039301 baseEnd_4039301 := by
    simpa [prefixWord, tailWord_4039301, baseEnd_4039301] using wordTrace_append hprefix tailTrace_4039301
  have hstable : (prefixWord ++ tailWord_4039301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039301).length < 2 ^ (prefixWord ++ tailWord_4039301).sum := by decide
  have hdescent : baseEnd_4039301 < baseStart_4039301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039317 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 3, 6, 3]
def baseStart_4039317 : Nat := 118140960795 + 4039317 * 2 ^ 59
def prefixEnd_4039317 : Nat := 4983230072969 + 3 ^ 40 * 4039317 * 2
def baseEnd_4039317 : Nat := 2074111136877277887361025

theorem tailTrace_4039317 : CollatzResearch.WordTrace tailWord_4039317 prefixEnd_4039317 2074111136877277887361025 := by
  unfold tailWord_4039317
  simp only [CollatzResearch.WordTrace]
  refine ⟨147325994307251844266116205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98217329538167896177410803 147325994307251844266116205)
  ·
    refine ⟨55247247865219441599793577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147325994307251844266116205 55247247865219441599793577)
    ·
      refine ⟨41435435898914581199845183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55247247865219441599793577 41435435898914581199845183)
      ·
        refine ⟨62153153848371871799767775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41435435898914581199845183 62153153848371871799767775)
        ·
          refine ⟨93229730772557807699651663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62153153848371871799767775 93229730772557807699651663)
          ·
            refine ⟨139844596158836711549477495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93229730772557807699651663 139844596158836711549477495)
            ·
              refine ⟨209766894238255067324216243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139844596158836711549477495 209766894238255067324216243)
              ·
                refine ⟨314650341357382600986324365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209766894238255067324216243 314650341357382600986324365)
                ·
                  refine ⟨117993878009018475369871637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314650341357382600986324365 117993878009018475369871637)
                  ·
                    refine ⟨5530963031672741032962733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117993878009018475369871637 5530963031672741032962733)
                    ·
                      refine ⟨2074111136877277887361025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5530963031672741032962733 2074111136877277887361025)
                      ·
                        rfl

theorem cell23_4039317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_4039317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039317 prefixEnd_4039317 := by exact prefixLift 4039317
  have htrace : WordTrace (prefixWord ++ tailWord_4039317) baseStart_4039317 baseEnd_4039317 := by
    simpa [prefixWord, tailWord_4039317, baseEnd_4039317] using wordTrace_append hprefix tailTrace_4039317
  have hstable : (prefixWord ++ tailWord_4039317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039317).length < 2 ^ (prefixWord ++ tailWord_4039317).sum := by decide
  have hdescent : baseEnd_4039317 < baseStart_4039317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039342 : List Nat := [4, 1, 4, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_4039342 : Nat := 118140960795 + 4039342 * 2 ^ 59
def prefixEnd_4039342 : Nat := 4983230072969 + 3 ^ 40 * 4039342 * 2
def baseEnd_4039342 : Nat := 2074123973893640289548411

theorem tailTrace_4039342 : CollatzResearch.WordTrace tailWord_4039342 prefixEnd_4039342 2074123973893640289548411 := by
  unfold tailWord_4039342
  simp only [CollatzResearch.WordTrace]
  refine ⟨18415863266520159191972035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98217937421440849023850853 18415863266520159191972035)
  ·
    refine ⟨27623794899780238787958053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18415863266520159191972035 27623794899780238787958053)
    ·
      refine ⟨5179461543708794772742135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27623794899780238787958053 5179461543708794772742135)
      ·
        refine ⟨7769192315563192159113203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5179461543708794772742135 7769192315563192159113203)
        ·
          refine ⟨11653788473344788238669805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7769192315563192159113203 11653788473344788238669805)
          ·
            refine ⟨4370170677504295589501177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11653788473344788238669805 4370170677504295589501177)
            ·
              refine ⟨3277628008128221692125883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4370170677504295589501177 3277628008128221692125883)
              ·
                refine ⟨4916442012192332538188825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3277628008128221692125883 4916442012192332538188825)
                ·
                  refine ⟨3687331509144249403641619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4916442012192332538188825 3687331509144249403641619)
                  ·
                    refine ⟨5530997263716374105462429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3687331509144249403641619 5530997263716374105462429)
                    ·
                      refine ⟨2074123973893640289548411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5530997263716374105462429 2074123973893640289548411)
                      ·
                        rfl

theorem cell23_4039342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_4039342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039342 prefixEnd_4039342 := by exact prefixLift 4039342
  have htrace : WordTrace (prefixWord ++ tailWord_4039342) baseStart_4039342 baseEnd_4039342 := by
    simpa [prefixWord, tailWord_4039342, baseEnd_4039342] using wordTrace_append hprefix tailTrace_4039342
  have hstable : (prefixWord ++ tailWord_4039342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039342).length < 2 ^ (prefixWord ++ tailWord_4039342).sum := by decide
  have hdescent : baseEnd_4039342 < baseStart_4039342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039377 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 3, 2, 5]
def baseStart_4039377 : Nat := 118140960795 + 4039377 * 2 ^ 59
def prefixEnd_4039377 : Nat := 4983230072969 + 3 ^ 40 * 4039377 * 2
def baseEnd_4039377 : Nat := 2074141945716547652610749

theorem tailTrace_4039377 : CollatzResearch.WordTrace tailWord_4039377 prefixEnd_4039377 2074141945716547652610749 := by
  unfold tailWord_4039377
  simp only [CollatzResearch.WordTrace]
  refine ⟨147328182687034474513300385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98218788458022983008866923 147328182687034474513300385)
  ·
    refine ⟨110496137015275855884975289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147328182687034474513300385 110496137015275855884975289)
    ·
      refine ⟨82872102761456891913731467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110496137015275855884975289 82872102761456891913731467)
      ·
        refine ⟨124308154142185337870597201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82872102761456891913731467 124308154142185337870597201)
        ·
          refine ⟨93231115606639003402947901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124308154142185337870597201 93231115606639003402947901)
          ·
            refine ⟨34961668352489626276105463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93231115606639003402947901 34961668352489626276105463)
            ·
              refine ⟨52442502528734439414158195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34961668352489626276105463 52442502528734439414158195)
              ·
                refine ⟨78663753793101659121237293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52442502528734439414158195 78663753793101659121237293)
                ·
                  refine ⟨29498907672413122170463985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78663753793101659121237293 29498907672413122170463985)
                  ·
                    refine ⟨22124180754309841627847989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29498907672413122170463985 22124180754309841627847989)
                    ·
                      refine ⟨2074141945716547652610749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22124180754309841627847989 2074141945716547652610749)
                      ·
                        rfl

theorem cell23_4039377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_4039377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039377 prefixEnd_4039377 := by exact prefixLift 4039377
  have htrace : WordTrace (prefixWord ++ tailWord_4039377) baseStart_4039377 baseEnd_4039377 := by
    simpa [prefixWord, tailWord_4039377, baseEnd_4039377] using wordTrace_append hprefix tailTrace_4039377
  have hstable : (prefixWord ++ tailWord_4039377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039377).length < 2 ^ (prefixWord ++ tailWord_4039377).sum := by decide
  have hdescent : baseEnd_4039377 < baseStart_4039377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039384 : List Nat := [2, 1, 2, 2, 3, 2, 2, 2, 2, 5]
def baseStart_4039384 : Nat := 118140960795 + 4039384 * 2 ^ 59
def prefixEnd_4039384 : Nat := 4983230072969 + 3 ^ 40 * 4039384 * 2
def baseEnd_4039384 : Nat := 691381846693709708407739

theorem tailTrace_4039384 : CollatzResearch.WordTrace tailWord_4039384 prefixEnd_4039384 691381846693709708407739 := by
  unfold tailWord_4039384
  simp only [CollatzResearch.WordTrace]
  refine ⟨73664218999004557354402603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98218958665339409805870137 73664218999004557354402603)
  ·
    refine ⟨110496328498506836031603905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73664218999004557354402603 110496328498506836031603905)
    ·
      refine ⟨82872246373880127023702929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110496328498506836031603905 82872246373880127023702929)
      ·
        refine ⟨62154184780410095267777197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82872246373880127023702929 62154184780410095267777197)
        ·
          refine ⟨23307819292653785725416449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62154184780410095267777197 23307819292653785725416449)
          ·
            refine ⟨17480864469490339294062337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23307819292653785725416449 17480864469490339294062337)
            ·
              refine ⟨13110648352117754470546753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17480864469490339294062337 13110648352117754470546753)
              ·
                refine ⟨9832986264088315852910065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13110648352117754470546753 9832986264088315852910065)
                ·
                  refine ⟨7374739698066236889682549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9832986264088315852910065 7374739698066236889682549)
                  ·
                    refine ⟨691381846693709708407739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7374739698066236889682549 691381846693709708407739)
                    ·
                      rfl

theorem cell23_4039384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_4039384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039384 prefixEnd_4039384 := by exact prefixLift 4039384
  have htrace : WordTrace (prefixWord ++ tailWord_4039384) baseStart_4039384 baseEnd_4039384 := by
    simpa [prefixWord, tailWord_4039384, baseEnd_4039384] using wordTrace_append hprefix tailTrace_4039384
  have hstable : (prefixWord ++ tailWord_4039384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039384).length < 2 ^ (prefixWord ++ tailWord_4039384).sum := by decide
  have hdescent : baseEnd_4039384 < baseStart_4039384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039388 : List Nat := [2, 2, 5, 1, 1, 2, 1, 4, 5]
def baseStart_4039388 : Nat := 118140960795 + 4039388 * 2 ^ 59
def prefixEnd_4039388 : Nat := 4983230072969 + 3 ^ 40 * 4039388 * 2
def baseEnd_4039388 : Nat := 230460843778194123285911

theorem tailTrace_4039388 : CollatzResearch.WordTrace tailWord_4039388 prefixEnd_4039388 230460843778194123285911 := by
  unfold tailWord_4039388
  simp only [CollatzResearch.WordTrace]
  refine ⟨73664291944997311695975409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98219055926663082261300545 73664291944997311695975409)
  ·
    refine ⟨55248218958747983771981557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73664291944997311695975409 55248218958747983771981557)
    ·
      refine ⟨5179520527382623478623271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55248218958747983771981557 5179520527382623478623271)
      ·
        refine ⟨7769280791073935217934907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5179520527382623478623271 7769280791073935217934907)
        ·
          refine ⟨11653921186610902826902361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7769280791073935217934907 11653921186610902826902361)
          ·
            refine ⟨8740440889958177120176771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11653921186610902826902361 8740440889958177120176771)
            ·
              refine ⟨13110661334937265680265157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8740440889958177120176771 13110661334937265680265157)
              ·
                refine ⟨2458249000300737315049717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13110661334937265680265157 2458249000300737315049717)
                ·
                  refine ⟨230460843778194123285911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2458249000300737315049717 230460843778194123285911)
                  ·
                    rfl

theorem cell23_4039388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 5].length) (baseStart_4039388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039388 prefixEnd_4039388 := by exact prefixLift 4039388
  have htrace : WordTrace (prefixWord ++ tailWord_4039388) baseStart_4039388 baseEnd_4039388 := by
    simpa [prefixWord, tailWord_4039388, baseEnd_4039388] using wordTrace_append hprefix tailTrace_4039388
  have hstable : (prefixWord ++ tailWord_4039388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039388).length < 2 ^ (prefixWord ++ tailWord_4039388).sum := by decide
  have hdescent : baseEnd_4039388 < baseStart_4039388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039417 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 4, 1, 6]
def baseStart_4039417 : Nat := 118140960795 + 4039417 * 2 ^ 59
def prefixEnd_4039417 : Nat := 4983230072969 + 3 ^ 40 * 4039417 * 2
def baseEnd_4039417 : Nat := 2074162484942727496110565

theorem tailTrace_4039417 : CollatzResearch.WordTrace tailWord_4039417 prefixEnd_4039417 2074162484942727496110565 := by
  unfold tailWord_4039417
  simp only [CollatzResearch.WordTrace]
  refine ⟨147329641606889561344756505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98219761071259707563171003 147329641606889561344756505)
  ·
    refine ⟨110497231205167171008567379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147329641606889561344756505 110497231205167171008567379)
    ·
      refine ⟨165745846807750756512851069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110497231205167171008567379 165745846807750756512851069)
      ·
        refine ⟨62154692552906533692319151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165745846807750756512851069 62154692552906533692319151)
        ·
          refine ⟨93232038829359800538478727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62154692552906533692319151 93232038829359800538478727)
          ·
            refine ⟨139848058244039700807718091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93232038829359800538478727 139848058244039700807718091)
            ·
              refine ⟨209772087366059551211577137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139848058244039700807718091 209772087366059551211577137)
              ·
                refine ⟨157329065524544663408682853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209772087366059551211577137 157329065524544663408682853)
                ·
                  refine ⟨29499199785852124389128035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157329065524544663408682853 29499199785852124389128035)
                  ·
                    refine ⟨44248799678778186583692053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29499199785852124389128035 44248799678778186583692053)
                    ·
                      refine ⟨2074162484942727496110565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44248799678778186583692053 2074162484942727496110565)
                      ·
                        rfl

theorem cell23_4039417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_4039417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039417 prefixEnd_4039417 := by exact prefixLift 4039417
  have htrace : WordTrace (prefixWord ++ tailWord_4039417) baseStart_4039417 baseEnd_4039417 := by
    simpa [prefixWord, tailWord_4039417, baseEnd_4039417] using wordTrace_append hprefix tailTrace_4039417
  have hstable : (prefixWord ++ tailWord_4039417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039417).length < 2 ^ (prefixWord ++ tailWord_4039417).sum := by decide
  have hdescent : baseEnd_4039417 < baseStart_4039417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039427 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 8]
def baseStart_4039427 : Nat := 118140960795 + 4039427 * 2 ^ 59
def prefixEnd_4039427 : Nat := 4983230072969 + 3 ^ 40 * 4039427 * 2
def baseEnd_4039427 : Nat := 230463068861030272998391

theorem tailTrace_4039427 : CollatzResearch.WordTrace tailWord_4039427 prefixEnd_4039427 230463068861030272998391 := by
  unfold tailWord_4039427
  simp only [CollatzResearch.WordTrace]
  refine ⟨147330006336853333052620535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98220004224568888701747023 147330006336853333052620535)
  ·
    refine ⟨220995009505279999578930803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147330006336853333052620535 220995009505279999578930803)
    ·
      refine ⟨331492514257919999368396205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220995009505279999578930803 331492514257919999368396205)
      ·
        refine ⟨124309692846719999763148577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331492514257919999368396205 124309692846719999763148577)
        ·
          refine ⟨93232269635039999822361433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124309692846719999763148577 93232269635039999822361433)
          ·
            refine ⟨69924202226279999866771075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93232269635039999822361433 69924202226279999866771075)
            ·
              refine ⟨104886303339419999800156613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69924202226279999866771075 104886303339419999800156613)
              ·
                refine ⟨19666181876141249962529365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104886303339419999800156613 19666181876141249962529365)
                ·
                  refine ⟨230463068861030272998391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19666181876141249962529365 230463068861030272998391)
                  ·
                    rfl

theorem cell23_4039427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 8].length) (baseStart_4039427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039427 prefixEnd_4039427 := by exact prefixLift 4039427
  have htrace : WordTrace (prefixWord ++ tailWord_4039427) baseStart_4039427 baseEnd_4039427 := by
    simpa [prefixWord, tailWord_4039427, baseEnd_4039427] using wordTrace_append hprefix tailTrace_4039427
  have hstable : (prefixWord ++ tailWord_4039427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039427).length < 2 ^ (prefixWord ++ tailWord_4039427).sum := by decide
  have hdescent : baseEnd_4039427 < baseStart_4039427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039461 : List Nat := [1, 3, 1, 2, 3, 1, 5, 1, 6]
def baseStart_4039461 : Nat := 118140960795 + 4039461 * 2 ^ 59
def prefixEnd_4039461 : Nat := 4983230072969 + 3 ^ 40 * 4039461 * 2
def baseEnd_4039461 : Nat := 230465008676836147106707

theorem tailTrace_4039461 : CollatzResearch.WordTrace tailWord_4039461 prefixEnd_4039461 230465008676836147106707 := by
  unfold tailWord_4039461
  simp only [CollatzResearch.WordTrace]
  refine ⟨147331246418730156859358237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98220830945820104572905491 147331246418730156859358237)
  ·
    refine ⟨55249217407023808822259339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147331246418730156859358237 55249217407023808822259339)
    ·
      refine ⟨82873826110535713233389009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55249217407023808822259339 82873826110535713233389009)
      ·
        refine ⟨62155369582901784925041757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82873826110535713233389009 62155369582901784925041757)
        ·
          refine ⟨23308263593588169346890659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62155369582901784925041757 23308263593588169346890659)
          ·
            refine ⟨34962395390382254020335989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23308263593588169346890659 34962395390382254020335989)
            ·
              refine ⟨3277724567848336314406499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34962395390382254020335989 3277724567848336314406499)
              ·
                refine ⟨4916586851772504471609749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3277724567848336314406499 4916586851772504471609749)
                ·
                  refine ⟨230465008676836147106707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4916586851772504471609749 230465008676836147106707)
                  ·
                    rfl

theorem cell23_4039461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 6].length) (baseStart_4039461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039461 prefixEnd_4039461 := by exact prefixLift 4039461
  have htrace : WordTrace (prefixWord ++ tailWord_4039461) baseStart_4039461 baseEnd_4039461 := by
    simpa [prefixWord, tailWord_4039461, baseEnd_4039461] using wordTrace_append hprefix tailTrace_4039461
  have hstable : (prefixWord ++ tailWord_4039461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039461).length < 2 ^ (prefixWord ++ tailWord_4039461).sum := by decide
  have hdescent : baseEnd_4039461 < baseStart_4039461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039464 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_4039464 : Nat := 118140960795 + 4039464 * 2 ^ 59
def prefixEnd_4039464 : Nat := 4983230072969 + 3 ^ 40 * 4039464 * 2
def baseEnd_4039464 : Nat := 2074186618533488812222849

theorem tailTrace_4039464 : CollatzResearch.WordTrace tailWord_4039464 prefixEnd_4039464 2074186618533488812222849 := by
  unfold tailWord_4039464
  simp only [CollatzResearch.WordTrace]
  refine ⟨73665677918859644185858723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98220903891812858914478297 73665677918859644185858723)
  ·
    refine ⟨110498516878289466278788085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73665677918859644185858723 110498516878289466278788085)
    ·
      refine ⟨10359235957339637463636383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110498516878289466278788085 10359235957339637463636383)
      ·
        refine ⟨15538853936009456195454575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10359235957339637463636383 15538853936009456195454575)
        ·
          refine ⟨23308280904014184293181863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15538853936009456195454575 23308280904014184293181863)
          ·
            refine ⟨34962421356021276439772795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23308280904014184293181863 34962421356021276439772795)
            ·
              refine ⟨52443632034031914659659193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34962421356021276439772795 52443632034031914659659193)
              ·
                refine ⟨39332724025523935994744395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52443632034031914659659193 39332724025523935994744395)
                ·
                  refine ⟨58999086038285903992116593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39332724025523935994744395 58999086038285903992116593)
                  ·
                    refine ⟨44249314528714427994087445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58999086038285903992116593 44249314528714427994087445)
                    ·
                      refine ⟨2074186618533488812222849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44249314528714427994087445 2074186618533488812222849)
                      ·
                        rfl

theorem cell23_4039464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_4039464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039464 prefixEnd_4039464 := by exact prefixLift 4039464
  have htrace : WordTrace (prefixWord ++ tailWord_4039464) baseStart_4039464 baseEnd_4039464 := by
    simpa [prefixWord, tailWord_4039464, baseEnd_4039464] using wordTrace_append hprefix tailTrace_4039464
  have hstable : (prefixWord ++ tailWord_4039464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039464).length < 2 ^ (prefixWord ++ tailWord_4039464).sum := by decide
  have hdescent : baseEnd_4039464 < baseStart_4039464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039467 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 7]
def baseStart_4039467 : Nat := 118140960795 + 4039467 * 2 ^ 59
def prefixEnd_4039467 : Nat := 4983230072969 + 3 ^ 40 * 4039467 * 2
def baseEnd_4039467 : Nat := 2074188158975452300485335

theorem tailTrace_4039467 : CollatzResearch.WordTrace tailWord_4039467 prefixEnd_4039467 2074188158975452300485335 := by
  unfold tailWord_4039467
  simp only [CollatzResearch.WordTrace]
  refine ⟨147331465256708419884076655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98220976837805613256051103 147331465256708419884076655)
  ·
    refine ⟨220997197885062629826114983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147331465256708419884076655 220997197885062629826114983)
    ·
      refine ⟨331495796827593944739172475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220997197885062629826114983 331495796827593944739172475)
      ·
        refine ⟨497243695241390917108758713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331495796827593944739172475 497243695241390917108758713)
        ·
          refine ⟨372932771431043187831569035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497243695241390917108758713 372932771431043187831569035)
          ·
            refine ⟨559399157146564781747353553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372932771431043187831569035 559399157146564781747353553)
            ·
              refine ⟨419549367859923586310515165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 559399157146564781747353553 419549367859923586310515165)
              ·
                refine ⟨157331012947471344866443187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 419549367859923586310515165 157331012947471344866443187)
                ·
                  refine ⟨235996519421207017299664781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157331012947471344866443187 235996519421207017299664781)
                  ·
                    refine ⟨88498694782952631487374293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 235996519421207017299664781 88498694782952631487374293)
                    ·
                      refine ⟨2074188158975452300485335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88498694782952631487374293 2074188158975452300485335)
                      ·
                        rfl

theorem cell23_4039467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 7].length) (baseStart_4039467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039467 prefixEnd_4039467 := by exact prefixLift 4039467
  have htrace : WordTrace (prefixWord ++ tailWord_4039467) baseStart_4039467 baseEnd_4039467 := by
    simpa [prefixWord, tailWord_4039467, baseEnd_4039467] using wordTrace_append hprefix tailTrace_4039467
  have hstable : (prefixWord ++ tailWord_4039467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039467).length < 2 ^ (prefixWord ++ tailWord_4039467).sum := by decide
  have hdescent : baseEnd_4039467 < baseStart_4039467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039482 : List Nat := [3, 1, 1, 1, 7, 1, 1, 3, 1, 4]
def baseStart_4039482 : Nat := 118140960795 + 4039482 * 2 ^ 59
def prefixEnd_4039482 : Nat := 4983230072969 + 3 ^ 40 * 4039482 * 2
def baseEnd_4039482 : Nat := 691398620395089913932589

theorem tailTrace_4039482 : CollatzResearch.WordTrace tailWord_4039482 prefixEnd_4039482 691398620395089913932589 := by
  unfold tailWord_4039482
  simp only [CollatzResearch.WordTrace]
  refine ⟨36833003087913519361468175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98221341567769384963915133 36833003087913519361468175)
  ·
    refine ⟨55249504631870279042202263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36833003087913519361468175 55249504631870279042202263)
    ·
      refine ⟨82874256947805418563303395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55249504631870279042202263 82874256947805418563303395)
      ·
        refine ⟨124311385421708127844955093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82874256947805418563303395 124311385421708127844955093)
        ·
          refine ⟨2913548095821284246366135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 124311385421708127844955093 2913548095821284246366135)
          ·
            refine ⟨4370322143731926369549203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2913548095821284246366135 4370322143731926369549203)
            ·
              refine ⟨6555483215597889554323805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4370322143731926369549203 6555483215597889554323805)
              ·
                refine ⟨2458306205849208582871427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6555483215597889554323805 2458306205849208582871427)
                ·
                  refine ⟨3687459308773812874307141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2458306205849208582871427 3687459308773812874307141)
                  ·
                    refine ⟨691398620395089913932589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3687459308773812874307141 691398620395089913932589)
                    ·
                      rfl

theorem cell23_4039482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 1, 4].length) (baseStart_4039482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039482 prefixEnd_4039482 := by exact prefixLift 4039482
  have htrace : WordTrace (prefixWord ++ tailWord_4039482) baseStart_4039482 baseEnd_4039482 := by
    simpa [prefixWord, tailWord_4039482, baseEnd_4039482] using wordTrace_append hprefix tailTrace_4039482
  have hstable : (prefixWord ++ tailWord_4039482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039482).length < 2 ^ (prefixWord ++ tailWord_4039482).sum := by decide
  have hdescent : baseEnd_4039482 < baseStart_4039482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039505 : List Nat := [1, 2, 2, 1, 6, 2, 1, 1, 3, 1, 3]
def baseStart_4039505 : Nat := 118140960795 + 4039505 * 2 ^ 59
def prefixEnd_4039505 : Nat := 4983230072969 + 3 ^ 40 * 4039505 * 2
def baseEnd_4039505 : Nat := 2074207671240323151810161

theorem tailTrace_4039505 : CollatzResearch.WordTrace tailWord_4039505 prefixEnd_4039505 2074207671240323151810161 := by
  unfold tailWord_4039505
  simp only [CollatzResearch.WordTrace]
  refine ⟨147332851230570752373959969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98221900820380501582639979 147332851230570752373959969)
  ·
    refine ⟨110499638422928064280469977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147332851230570752373959969 110499638422928064280469977)
    ·
      refine ⟨82874728817196048210352483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110499638422928064280469977 82874728817196048210352483)
      ·
        refine ⟨124312093225794072315528725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82874728817196048210352483 124312093225794072315528725)
        ·
          refine ⟨5827129369959097139790409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 124312093225794072315528725 5827129369959097139790409)
          ·
            refine ⟨4370347027469322854842807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5827129369959097139790409 4370347027469322854842807)
            ·
              refine ⟨6555520541203984282264211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4370347027469322854842807 6555520541203984282264211)
              ·
                refine ⟨9833280811805976423396317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6555520541203984282264211 9833280811805976423396317)
                ·
                  refine ⟨3687480304427241158773619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9833280811805976423396317 3687480304427241158773619)
                  ·
                    refine ⟨5531220456640861738160429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3687480304427241158773619 5531220456640861738160429)
                    ·
                      refine ⟨2074207671240323151810161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5531220456640861738160429 2074207671240323151810161)
                      ·
                        rfl

theorem cell23_4039505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 1, 3].length) (baseStart_4039505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039505 prefixEnd_4039505 := by exact prefixLift 4039505
  have htrace : WordTrace (prefixWord ++ tailWord_4039505) baseStart_4039505 baseEnd_4039505 := by
    simpa [prefixWord, tailWord_4039505, baseEnd_4039505] using wordTrace_append hprefix tailTrace_4039505
  have hstable : (prefixWord ++ tailWord_4039505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039505).length < 2 ^ (prefixWord ++ tailWord_4039505).sum := by decide
  have hdescent : baseEnd_4039505 < baseStart_4039505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039528 : List Nat := [2, 1, 4, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_4039528 : Nat := 118140960795 + 4039528 * 2 ^ 59
def prefixEnd_4039528 : Nat := 4983230072969 + 3 ^ 40 * 4039528 * 2
def baseEnd_4039528 : Nat := 2074219481295376561822555

theorem tailTrace_4039528 : CollatzResearch.WordTrace tailWord_4039528 prefixEnd_4039528 2074219481295376561822555 := by
  unfold tailWord_4039528
  simp only [CollatzResearch.WordTrace]
  refine ⟨73666845054743713651023619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98222460072991618201364825 73666845054743713651023619)
  ·
    refine ⟨110500267582115570476535429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73666845054743713651023619 110500267582115570476535429)
    ·
      refine ⟨20718800171646669464350393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110500267582115570476535429 20718800171646669464350393)
      ·
        refine ⟨15539100128735002098262795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20718800171646669464350393 15539100128735002098262795)
        ·
          refine ⟨23308650193102503147394193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15539100128735002098262795 23308650193102503147394193)
          ·
            refine ⟨17481487644826877360545645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23308650193102503147394193 17481487644826877360545645)
            ·
              refine ⟨6555557866810079010204617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17481487644826877360545645 6555557866810079010204617)
              ·
                refine ⟨4916668400107559257653463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6555557866810079010204617 4916668400107559257653463)
                ·
                  refine ⟨7375002600161338886480195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4916668400107559257653463 7375002600161338886480195)
                  ·
                    refine ⟨11062503900242008329720293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7375002600161338886480195 11062503900242008329720293)
                    ·
                      refine ⟨2074219481295376561822555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11062503900242008329720293 2074219481295376561822555)
                      ·
                        rfl

theorem cell23_4039528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_4039528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039528 prefixEnd_4039528 := by exact prefixLift 4039528
  have htrace : WordTrace (prefixWord ++ tailWord_4039528) baseStart_4039528 baseEnd_4039528 := by
    simpa [prefixWord, tailWord_4039528, baseEnd_4039528] using wordTrace_append hprefix tailTrace_4039528
  have hstable : (prefixWord ++ tailWord_4039528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039528).length < 2 ^ (prefixWord ++ tailWord_4039528).sum := by decide
  have hdescent : baseEnd_4039528 < baseStart_4039528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039541 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_4039541 : Nat := 118140960795 + 4039541 * 2 ^ 59
def prefixEnd_4039541 : Nat := 4983230072969 + 3 ^ 40 * 4039541 * 2
def baseEnd_4039541 : Nat := 2074226156543885010959995

theorem tailTrace_4039541 : CollatzResearch.WordTrace tailWord_4039541 prefixEnd_4039541 2074226156543885010959995 := by
  unfold tailWord_4039541
  simp only [CollatzResearch.WordTrace]
  refine ⟨147334164258440330522270477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98222776172293553681513651 147334164258440330522270477)
  ·
    refine ⟨55250311596915123945851429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147334164258440330522270477 55250311596915123945851429)
    ·
      refine ⟨10359433424421585739847143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55250311596915123945851429 10359433424421585739847143)
      ·
        refine ⟨15539150136632378609770715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10359433424421585739847143 15539150136632378609770715)
        ·
          refine ⟨23308725204948567914656073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15539150136632378609770715 23308725204948567914656073)
          ·
            refine ⟨17481543903711425935992055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23308725204948567914656073 17481543903711425935992055)
            ·
              refine ⟨26222315855567138903988083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17481543903711425935992055 26222315855567138903988083)
              ·
                refine ⟨39333473783350708355982125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26222315855567138903988083 39333473783350708355982125)
                ·
                  refine ⟨14750052668756515633493297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39333473783350708355982125 14750052668756515633493297)
                  ·
                    refine ⟨11062539501567386725119973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14750052668756515633493297 11062539501567386725119973)
                    ·
                      refine ⟨2074226156543885010959995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11062539501567386725119973 2074226156543885010959995)
                      ·
                        rfl

theorem cell23_4039541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_4039541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039541 prefixEnd_4039541 := by exact prefixLift 4039541
  have htrace : WordTrace (prefixWord ++ tailWord_4039541) baseStart_4039541 baseEnd_4039541 := by
    simpa [prefixWord, tailWord_4039541, baseEnd_4039541] using wordTrace_append hprefix tailTrace_4039541
  have hstable : (prefixWord ++ tailWord_4039541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039541).length < 2 ^ (prefixWord ++ tailWord_4039541).sum := by decide
  have hdescent : baseEnd_4039541 < baseStart_4039541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039564 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 2, 7]
def baseStart_4039564 : Nat := 118140960795 + 4039564 * 2 ^ 59
def prefixEnd_4039564 : Nat := 4983230072969 + 3 ^ 40 * 4039564 * 2
def baseEnd_4039564 : Nat := 691412655532979473657463

theorem tailTrace_4039564 : CollatzResearch.WordTrace tailWord_4039564 prefixEnd_4039564 691412655532979473657463 := by
  unfold tailWord_4039564
  simp only [CollatzResearch.WordTrace]
  refine ⟨73667501568678502725178873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98223335424904670300238497 73667501568678502725178873)
  ·
    refine ⟨55250626176508877043884155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73667501568678502725178873 55250626176508877043884155)
    ·
      refine ⟨82875939264763315565826233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55250626176508877043884155 82875939264763315565826233)
      ·
        refine ⟨62156954448572486674369675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82875939264763315565826233 62156954448572486674369675)
        ·
          refine ⟨93235431672858730011554513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62156954448572486674369675 93235431672858730011554513)
          ·
            refine ⟨69926573754644047508665885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93235431672858730011554513 69926573754644047508665885)
            ·
              refine ⟨26222465157991517815749707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69926573754644047508665885 26222465157991517815749707)
              ·
                refine ⟨39333697736987276723624561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26222465157991517815749707 39333697736987276723624561)
                ·
                  refine ⟨29500273302740457542718421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39333697736987276723624561 29500273302740457542718421)
                  ·
                    refine ⟨691412655532979473657463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29500273302740457542718421 691412655532979473657463)
                    ·
                      rfl

theorem cell23_4039564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_4039564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039564 prefixEnd_4039564 := by exact prefixLift 4039564
  have htrace : WordTrace (prefixWord ++ tailWord_4039564) baseStart_4039564 baseEnd_4039564 := by
    simpa [prefixWord, tailWord_4039564, baseEnd_4039564] using wordTrace_append hprefix tailTrace_4039564
  have hstable : (prefixWord ++ tailWord_4039564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039564).length < 2 ^ (prefixWord ++ tailWord_4039564).sum := by decide
  have hdescent : baseEnd_4039564 < baseStart_4039564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039588 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 3, 3, 2]
def baseStart_4039588 : Nat := 118140960795 + 4039588 * 2 ^ 59
def prefixEnd_4039588 : Nat := 4983230072969 + 3 ^ 40 * 4039588 * 2
def baseEnd_4039588 : Nat := 2074250290134646327072279

theorem tailTrace_4039588 : CollatzResearch.WordTrace tailWord_4039588 prefixEnd_4039588 2074250290134646327072279 := by
  unfold tailWord_4039588
  simp only [CollatzResearch.WordTrace]
  refine ⟨73667939244635028774615709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98223918992846705032820945 73667939244635028774615709)
  ·
    refine ⟨27625477216738135790480891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73667939244635028774615709 27625477216738135790480891)
    ·
      refine ⟨41438215825107203685721337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27625477216738135790480891 41438215825107203685721337)
      ·
        refine ⟨31078661868830402764291003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41438215825107203685721337 31078661868830402764291003)
        ·
          refine ⟨46617992803245604146436505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31078661868830402764291003 46617992803245604146436505)
          ·
            refine ⟨34963494602434203109827379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46617992803245604146436505 34963494602434203109827379)
            ·
              refine ⟨52445241903651304664741069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34963494602434203109827379 52445241903651304664741069)
              ·
                refine ⟨19666965713869239249277901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52445241903651304664741069 19666965713869239249277901)
                ·
                  refine ⟨7375112142700964718479213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19666965713869239249277901 7375112142700964718479213)
                  ·
                    refine ⟨2765667053512861769429705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7375112142700964718479213 2765667053512861769429705)
                    ·
                      refine ⟨2074250290134646327072279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2765667053512861769429705 2074250290134646327072279)
                      ·
                        rfl

theorem cell23_4039588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_4039588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039588 prefixEnd_4039588 := by exact prefixLift 4039588
  have htrace : WordTrace (prefixWord ++ tailWord_4039588) baseStart_4039588 baseEnd_4039588 := by
    simpa [prefixWord, tailWord_4039588, baseEnd_4039588] using wordTrace_append hprefix tailTrace_4039588
  have hstable : (prefixWord ++ tailWord_4039588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039588).length < 2 ^ (prefixWord ++ tailWord_4039588).sum := by decide
  have hdescent : baseEnd_4039588 < baseStart_4039588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039605 : List Nat := [1, 3, 3, 2, 1, 1, 3, 3, 1, 3, 2]
def baseStart_4039605 : Nat := 118140960795 + 4039605 * 2 ^ 59
def prefixEnd_4039605 : Nat := 4983230072969 + 3 ^ 40 * 4039605 * 2
def baseEnd_4039605 : Nat := 2074259019305772760559701

theorem tailTrace_4039605 : CollatzResearch.WordTrace tailWord_4039605 prefixEnd_4039605 2074259019305772760559701 := by
  unfold tailWord_4039605
  simp only [CollatzResearch.WordTrace]
  refine ⟨147336498530208469452600269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98224332353472312968400179 147336498530208469452600269)
  ·
    refine ⟨55251186948828176044725101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147336498530208469452600269 55251186948828176044725101)
    ·
      refine ⟨20719195105810566016771913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55251186948828176044725101 20719195105810566016771913)
      ·
        refine ⟨15539396329357924512578935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20719195105810566016771913 15539396329357924512578935)
        ·
          refine ⟨23309094494036886768868403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15539396329357924512578935 23309094494036886768868403)
          ·
            refine ⟨34963641741055330153302605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23309094494036886768868403 34963641741055330153302605)
            ·
              refine ⟨13111365652895748807488477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34963641741055330153302605 13111365652895748807488477)
              ·
                refine ⟨4916762119835905802808179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13111365652895748807488477 4916762119835905802808179)
                ·
                  refine ⟨7375143179753858704212269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4916762119835905802808179 7375143179753858704212269)
                  ·
                    refine ⟨2765678692407697014079601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7375143179753858704212269 2765678692407697014079601)
                    ·
                      refine ⟨2074259019305772760559701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2765678692407697014079601 2074259019305772760559701)
                      ·
                        rfl

theorem cell23_4039605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_4039605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039605 prefixEnd_4039605 := by exact prefixLift 4039605
  have htrace : WordTrace (prefixWord ++ tailWord_4039605) baseStart_4039605 baseEnd_4039605 := by
    simpa [prefixWord, tailWord_4039605, baseEnd_4039605] using wordTrace_append hprefix tailTrace_4039605
  have hstable : (prefixWord ++ tailWord_4039605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039605).length < 2 ^ (prefixWord ++ tailWord_4039605).sum := by decide
  have hdescent : baseEnd_4039605 < baseStart_4039605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039606 : List Nat := [5, 1, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_4039606 : Nat := 118140960795 + 4039606 * 2 ^ 59
def prefixEnd_4039606 : Nat := 4983230072969 + 3 ^ 40 * 4039606 * 2
def baseEnd_4039606 : Nat := 691419844262142418882399

theorem tailTrace_4039606 : CollatzResearch.WordTrace tailWord_4039606 prefixEnd_4039606 691419844262142418882399 := by
  unfold tailWord_4039606
  simp only [CollatzResearch.WordTrace]
  refine ⟨9208533437700302913961667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98224356668803231082257781 9208533437700302913961667)
  ·
    refine ⟨13812800156550454370942501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9208533437700302913961667 13812800156550454370942501)
    ·
      refine ⟨2589900029353210194551719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13812800156550454370942501 2589900029353210194551719)
      ·
        refine ⟨3884850044029815291827579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2589900029353210194551719 3884850044029815291827579)
        ·
          refine ⟨5827275066044722937741369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3884850044029815291827579 5827275066044722937741369)
          ·
            refine ⟨4370456299533542203306027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5827275066044722937741369 4370456299533542203306027)
            ·
              refine ⟨6555684449300313304959041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4370456299533542203306027 6555684449300313304959041)
              ·
                refine ⟨4916763336975234978719281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6555684449300313304959041 4916763336975234978719281)
                ·
                  refine ⟨3687572502731426234039461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4916763336975234978719281 3687572502731426234039461)
                  ·
                    refine ⟨691419844262142418882399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3687572502731426234039461 691419844262142418882399)
                    ·
                      rfl

theorem cell23_4039606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_4039606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039606 prefixEnd_4039606 := by exact prefixLift 4039606
  have htrace : WordTrace (prefixWord ++ tailWord_4039606) baseStart_4039606 baseEnd_4039606 := by
    simpa [prefixWord, tailWord_4039606, baseEnd_4039606] using wordTrace_append hprefix tailTrace_4039606
  have hstable : (prefixWord ++ tailWord_4039606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039606).length < 2 ^ (prefixWord ++ tailWord_4039606).sum := by decide
  have hdescent : baseEnd_4039606 < baseStart_4039606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039631 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 4]
def baseStart_4039631 : Nat := 118140960795 + 4039631 * 2 ^ 59
def prefixEnd_4039631 : Nat := 4983230072969 + 3 ^ 40 * 4039631 * 2
def baseEnd_4039631 : Nat := 2074272369802789658834581

theorem tailTrace_4039631 : CollatzResearch.WordTrace tailWord_4039631 prefixEnd_4039631 2074272369802789658834581 := by
  unfold tailWord_4039631
  simp only [CollatzResearch.WordTrace]
  refine ⟨147337446828114275893046747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98224964552076183928697831 147337446828114275893046747)
  ·
    refine ⟨221006170242171413839570121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147337446828114275893046747 221006170242171413839570121)
    ·
      refine ⟨165754627681628560379677591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221006170242171413839570121 165754627681628560379677591)
      ·
        refine ⟨248631941522442840569516387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165754627681628560379677591 248631941522442840569516387)
        ·
          refine ⟨372947912283664260854274581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248631941522442840569516387 372947912283664260854274581)
          ·
            refine ⟨17481933388296762227544121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 372947912283664260854274581 17481933388296762227544121)
            ·
              refine ⟨13111450041222571670658091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17481933388296762227544121 13111450041222571670658091)
              ·
                refine ⟨19667175061833857505987137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13111450041222571670658091 19667175061833857505987137)
                ·
                  refine ⟨14750381296375393129490353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19667175061833857505987137 14750381296375393129490353)
                  ·
                    refine ⟨11062785972281544847117765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14750381296375393129490353 11062785972281544847117765)
                    ·
                      refine ⟨2074272369802789658834581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11062785972281544847117765 2074272369802789658834581)
                      ·
                        rfl

theorem cell23_4039631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_4039631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039631 prefixEnd_4039631 := by exact prefixLift 4039631
  have htrace : WordTrace (prefixWord ++ tailWord_4039631) baseStart_4039631 baseEnd_4039631 := by
    simpa [prefixWord, tailWord_4039631, baseEnd_4039631] using wordTrace_append hprefix tailTrace_4039631
  have hstable : (prefixWord ++ tailWord_4039631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039631).length < 2 ^ (prefixWord ++ tailWord_4039631).sum := by decide
  have hdescent : baseEnd_4039631 < baseStart_4039631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039641 : List Nat := [1, 2, 1, 2, 5, 1, 2, 2, 7]
def baseStart_4039641 : Nat := 118140960795 + 4039641 * 2 ^ 59
def prefixEnd_4039641 : Nat := 4983230072969 + 3 ^ 40 * 4039641 * 2
def baseEnd_4039641 : Nat := 230475278289926068856615

theorem tailTrace_4039641 : CollatzResearch.WordTrace tailWord_4039641 prefixEnd_4039641 230475278289926068856615 := by
  unfold tailWord_4039641
  simp only [CollatzResearch.WordTrace]
  refine ⟨147337811558078047600910777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98225207705385365067273851 147337811558078047600910777)
  ·
    refine ⟨110503358668558535700683083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147337811558078047600910777 110503358668558535700683083)
    ·
      refine ⟨165755038002837803551024625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110503358668558535700683083 165755038002837803551024625)
      ·
        refine ⟨124316278502128352663268469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165755038002837803551024625 124316278502128352663268469)
        ·
          refine ⟨11654651109574533062181419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124316278502128352663268469 11654651109574533062181419)
          ·
            refine ⟨17481976664361799593272129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11654651109574533062181419 17481976664361799593272129)
            ·
              refine ⟨13111482498271349694954097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17481976664361799593272129 13111482498271349694954097)
              ·
                refine ⟨9833611873703512271215573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13111482498271349694954097 9833611873703512271215573)
                ·
                  refine ⟨230475278289926068856615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9833611873703512271215573 230475278289926068856615)
                  ·
                    rfl

theorem cell23_4039641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 7].length) (baseStart_4039641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039641 prefixEnd_4039641 := by exact prefixLift 4039641
  have htrace : WordTrace (prefixWord ++ tailWord_4039641) baseStart_4039641 baseEnd_4039641 := by
    simpa [prefixWord, tailWord_4039641, baseEnd_4039641] using wordTrace_append hprefix tailTrace_4039641
  have hstable : (prefixWord ++ tailWord_4039641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039641).length < 2 ^ (prefixWord ++ tailWord_4039641).sum := by decide
  have hdescent : baseEnd_4039641 < baseStart_4039641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039681 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_4039681 : Nat := 118140960795 + 4039681 * 2 ^ 59
def prefixEnd_4039681 : Nat := 4983230072969 + 3 ^ 40 * 4039681 * 2
def baseEnd_4039681 : Nat := 2074298043835514463209351

theorem tailTrace_4039681 : CollatzResearch.WordTrace tailWord_4039681 prefixEnd_4039681 2074298043835514463209351 := by
  unfold tailWord_4039681
  simp only [CollatzResearch.WordTrace]
  refine ⟨147339270477933134432366897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98226180318622089621577931 147339270477933134432366897)
  ·
    refine ⟨110504452858449850824275173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147339270477933134432366897 110504452858449850824275173)
    ·
      refine ⟨20719584910959347029551595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110504452858449850824275173 20719584910959347029551595)
      ·
        refine ⟨31079377366439020544327393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20719584910959347029551595 31079377366439020544327393)
        ·
          refine ⟨23309533024829265408245545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31079377366439020544327393 23309533024829265408245545)
          ·
            refine ⟨17482149768621949056184159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23309533024829265408245545 17482149768621949056184159)
            ·
              refine ⟨26223224652932923584276239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17482149768621949056184159 26223224652932923584276239)
              ·
                refine ⟨39334836979399385376414359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26223224652932923584276239 39334836979399385376414359)
                ·
                  refine ⟨59002255469099078064621539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39334836979399385376414359 59002255469099078064621539)
                  ·
                    refine ⟨88503383203648617096932309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59002255469099078064621539 88503383203648617096932309)
                    ·
                      refine ⟨2074298043835514463209351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88503383203648617096932309 2074298043835514463209351)
                      ·
                        rfl

theorem cell23_4039681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_4039681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039681 prefixEnd_4039681 := by exact prefixLift 4039681
  have htrace : WordTrace (prefixWord ++ tailWord_4039681) baseStart_4039681 baseEnd_4039681 := by
    simpa [prefixWord, tailWord_4039681, baseEnd_4039681] using wordTrace_append hprefix tailTrace_4039681
  have hstable : (prefixWord ++ tailWord_4039681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039681).length < 2 ^ (prefixWord ++ tailWord_4039681).sum := by decide
  have hdescent : baseEnd_4039681 < baseStart_4039681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039728 : List Nat := [2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 3]
def baseStart_4039728 : Nat := 118140960795 + 4039728 * 2 ^ 59
def prefixEnd_4039728 : Nat := 4983230072969 + 3 ^ 40 * 4039728 * 2
def baseEnd_4039728 : Nat := 2074322177426275779321635

theorem tailTrace_4039728 : CollatzResearch.WordTrace tailWord_4039728 prefixEnd_4039728 2074322177426275779321635 := by
  unfold tailWord_4039728
  simp only [CollatzResearch.WordTrace]
  refine ⟨73670492354381430729663919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98227323139175240972885225 73670492354381430729663919)
  ·
    refine ⟨110505738531572146094495879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73670492354381430729663919 110505738531572146094495879)
    ·
      refine ⟨165758607797358219141743819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110505738531572146094495879 165758607797358219141743819)
      ·
        refine ⟨248637911696037328712615729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165758607797358219141743819 248637911696037328712615729)
        ·
          refine ⟨186478433772027996534461797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248637911696037328712615729 186478433772027996534461797)
          ·
            refine ⟨34964706332255249350211587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186478433772027996534461797 34964706332255249350211587)
            ·
              refine ⟨52447059498382874025317381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34964706332255249350211587 52447059498382874025317381)
              ·
                refine ⟨9833823655946788879747009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52447059498382874025317381 9833823655946788879747009)
                ·
                  refine ⟨7375367741960091659810257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9833823655946788879747009 7375367741960091659810257)
                  ·
                    refine ⟨5531525806470068744857693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7375367741960091659810257 5531525806470068744857693)
                    ·
                      refine ⟨2074322177426275779321635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5531525806470068744857693 2074322177426275779321635)
                      ·
                        rfl

theorem cell23_4039728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 3].length) (baseStart_4039728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039728 prefixEnd_4039728 := by exact prefixLift 4039728
  have htrace : WordTrace (prefixWord ++ tailWord_4039728) baseStart_4039728 baseEnd_4039728 := by
    simpa [prefixWord, tailWord_4039728, baseEnd_4039728] using wordTrace_append hprefix tailTrace_4039728
  have hstable : (prefixWord ++ tailWord_4039728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039728).length < 2 ^ (prefixWord ++ tailWord_4039728).sum := by decide
  have hdescent : baseEnd_4039728 < baseStart_4039728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039742 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 2, 4, 2]
def baseStart_4039742 : Nat := 118140960795 + 4039742 * 2 ^ 59
def prefixEnd_4039742 : Nat := 4983230072969 + 3 ^ 40 * 4039742 * 2
def baseEnd_4039742 : Nat := 2074329366155438724546571

theorem tailTrace_4039742 : CollatzResearch.WordTrace tailWord_4039742 prefixEnd_4039742 2074329366155438724546571 := by
  unfold tailWord_4039742
  simp only [CollatzResearch.WordTrace]
  refine ⟨18417686916339017731292185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98227663553808094566891653 18417686916339017731292185)
  ·
    refine ⟨13813265187254263298469139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18417686916339017731292185 13813265187254263298469139)
    ·
      refine ⟨20719897780881394947703709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13813265187254263298469139 20719897780881394947703709)
      ·
        refine ⟨7769961667830523105388891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20719897780881394947703709 7769961667830523105388891)
        ·
          refine ⟨11654942501745784658083337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7769961667830523105388891 11654942501745784658083337)
          ·
            refine ⟨8741206876309338493562503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11654942501745784658083337 8741206876309338493562503)
            ·
              refine ⟨13111810314464007740343755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8741206876309338493562503 13111810314464007740343755)
              ·
                refine ⟨19667715471696011610515633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13111810314464007740343755 19667715471696011610515633)
                ·
                  refine ⟨14750786603772008707886725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19667715471696011610515633 14750786603772008707886725)
                  ·
                    refine ⟨2765772488207251632728761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14750786603772008707886725 2765772488207251632728761)
                    ·
                      refine ⟨2074329366155438724546571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2765772488207251632728761 2074329366155438724546571)
                      ·
                        rfl

theorem cell23_4039742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_4039742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039742 prefixEnd_4039742 := by exact prefixLift 4039742
  have htrace : WordTrace (prefixWord ++ tailWord_4039742) baseStart_4039742 baseEnd_4039742 := by
    simpa [prefixWord, tailWord_4039742, baseEnd_4039742] using wordTrace_append hprefix tailTrace_4039742
  have hstable : (prefixWord ++ tailWord_4039742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039742).length < 2 ^ (prefixWord ++ tailWord_4039742).sum := by decide
  have hdescent : baseEnd_4039742 < baseStart_4039742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039762 : List Nat := [3, 2, 2, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_4039762 : Nat := 118140960795 + 4039762 * 2 ^ 59
def prefixEnd_4039762 : Nat := 4983230072969 + 3 ^ 40 * 4039762 * 2
def baseEnd_4039762 : Nat := 2074339635768528646296479

theorem tailTrace_4039762 : CollatzResearch.WordTrace tailWord_4039762 prefixEnd_4039762 2074339635768528646296479 := by
  unfold tailWord_4039762
  simp only [CollatzResearch.WordTrace]
  refine ⟨36835556197659921316516385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98228149860426456844043693 36835556197659921316516385)
  ·
    refine ⟨27626667148244940987387289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36835556197659921316516385 27626667148244940987387289)
    ·
      refine ⟨20720000361183705740540467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27626667148244940987387289 20720000361183705740540467)
      ·
        refine ⟨31080000541775558610810701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20720000361183705740540467 31080000541775558610810701)
        ·
          refine ⟨11655000203165834479054013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31080000541775558610810701 11655000203165834479054013)
          ·
            refine ⟨4370625076187187929645255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11655000203165834479054013 4370625076187187929645255)
            ·
              refine ⟨6555937614280781894467883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4370625076187187929645255 6555937614280781894467883)
              ·
                refine ⟨9833906421421172841701825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6555937614280781894467883 9833906421421172841701825)
                ·
                  refine ⟨7375429816065879631276369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9833906421421172841701825 7375429816065879631276369)
                  ·
                    refine ⟨5531572362049409723457277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7375429816065879631276369 5531572362049409723457277)
                    ·
                      refine ⟨2074339635768528646296479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5531572362049409723457277 2074339635768528646296479)
                      ·
                        rfl

theorem cell23_4039762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_4039762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039762 prefixEnd_4039762 := by exact prefixLift 4039762
  have htrace : WordTrace (prefixWord ++ tailWord_4039762) baseStart_4039762 baseEnd_4039762 := by
    simpa [prefixWord, tailWord_4039762, baseEnd_4039762] using wordTrace_append hprefix tailTrace_4039762
  have hstable : (prefixWord ++ tailWord_4039762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039762).length < 2 ^ (prefixWord ++ tailWord_4039762).sum := by decide
  have hdescent : baseEnd_4039762 < baseStart_4039762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039792 : List Nat := [2, 1, 1, 1, 5, 1, 1, 6, 1, 1, 3]
def baseStart_4039792 : Nat := 118140960795 + 4039792 * 2 ^ 59
def prefixEnd_4039792 : Nat := 4983230072969 + 3 ^ 40 * 4039792 * 2
def baseEnd_4039792 : Nat := 2074355040188163528921341

theorem tailTrace_4039792 : CollatzResearch.WordTrace tailWord_4039792 prefixEnd_4039792 2074355040188163528921341 := by
  unfold tailWord_4039792
  simp only [CollatzResearch.WordTrace]
  refine ⟨73671659490265500194828815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98228879320354000259771753 73671659490265500194828815)
  ·
    refine ⟨110507489235398250292243223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73671659490265500194828815 110507489235398250292243223)
    ·
      refine ⟨165761233853097375438364835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110507489235398250292243223 165761233853097375438364835)
      ·
        refine ⟨248641850779646063157547253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165761233853097375438364835 248641850779646063157547253)
        ·
          refine ⟨23310173510591818421020055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 248641850779646063157547253 23310173510591818421020055)
          ·
            refine ⟨34965260265887727631530083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23310173510591818421020055 34965260265887727631530083)
            ·
              refine ⟨52447890398831591447295125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34965260265887727631530083 52447890398831591447295125)
              ·
                refine ⟨2458494862445230849091959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52447890398831591447295125 2458494862445230849091959)
                ·
                  refine ⟨3687742293667846273637939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2458494862445230849091959 3687742293667846273637939)
                  ·
                    refine ⟨5531613440501769410456909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3687742293667846273637939 5531613440501769410456909)
                    ·
                      refine ⟨2074355040188163528921341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5531613440501769410456909 2074355040188163528921341)
                      ·
                        rfl

theorem cell23_4039792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 1, 1, 3].length) (baseStart_4039792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039792 prefixEnd_4039792 := by exact prefixLift 4039792
  have htrace : WordTrace (prefixWord ++ tailWord_4039792) baseStart_4039792 baseEnd_4039792 := by
    simpa [prefixWord, tailWord_4039792, baseEnd_4039792] using wordTrace_append hprefix tailTrace_4039792
  have hstable : (prefixWord ++ tailWord_4039792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039792).length < 2 ^ (prefixWord ++ tailWord_4039792).sum := by decide
  have hdescent : baseEnd_4039792 < baseStart_4039792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039808 : List Nat := [2, 1, 1, 2, 1, 3, 5, 1, 1, 6]
def baseStart_4039808 : Nat := 118140960795 + 4039808 * 2 ^ 59
def prefixEnd_4039808 : Nat := 4983230072969 + 3 ^ 40 * 4039808 * 2
def baseEnd_4039808 : Nat := 691454418626211822107089

theorem tailTrace_4039808 : CollatzResearch.WordTrace tailWord_4039808 prefixEnd_4039808 691454418626211822107089 := by
  unfold tailWord_4039808
  simp only [CollatzResearch.WordTrace]
  refine ⟨73671951274236517561120039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98229268365648690081493385 73671951274236517561120039)
  ·
    refine ⟨110507926911354776341680059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73671951274236517561120039 110507926911354776341680059)
    ·
      refine ⟨165761890367032164512520089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110507926911354776341680059 165761890367032164512520089)
      ·
        refine ⟨124321417775274123384390067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165761890367032164512520089 124321417775274123384390067)
        ·
          refine ⟨186482126662911185076585101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124321417775274123384390067 186482126662911185076585101)
          ·
            refine ⟨69930797498591694403719413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186482126662911185076585101 69930797498591694403719413)
            ·
              refine ⟨6556012265492971350348695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69930797498591694403719413 6556012265492971350348695)
              ·
                refine ⟨9834018398239457025523043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6556012265492971350348695 9834018398239457025523043)
                ·
                  refine ⟨14751027597359185538284565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9834018398239457025523043 14751027597359185538284565)
                  ·
                    refine ⟨691454418626211822107089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14751027597359185538284565 691454418626211822107089)
                    ·
                      rfl

theorem cell23_4039808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 1, 6].length) (baseStart_4039808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039808 prefixEnd_4039808 := by exact prefixLift 4039808
  have htrace : WordTrace (prefixWord ++ tailWord_4039808) baseStart_4039808 baseEnd_4039808 := by
    simpa [prefixWord, tailWord_4039808, baseEnd_4039808] using wordTrace_append hprefix tailTrace_4039808
  have hstable : (prefixWord ++ tailWord_4039808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039808).length < 2 ^ (prefixWord ++ tailWord_4039808).sum := by decide
  have hdescent : baseEnd_4039808 < baseStart_4039808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039818 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_4039818 : Nat := 118140960795 + 4039818 * 2 ^ 59
def prefixEnd_4039818 : Nat := 4983230072969 + 3 ^ 40 * 4039818 * 2
def baseEnd_4039818 : Nat := 2074368390685180427196221

theorem tailTrace_4039818 : CollatzResearch.WordTrace tailWord_4039818 prefixEnd_4039818 2074368390685180427196221 := by
  unfold tailWord_4039818
  simp only [CollatzResearch.WordTrace]
  refine ⟨36836066819609201707526027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98229511518957871220069405 36836066819609201707526027)
  ·
    refine ⟨55254100229413802561289041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36836066819609201707526027 55254100229413802561289041)
    ·
      refine ⟨41440575172060351920966781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55254100229413802561289041 41440575172060351920966781)
      ·
        refine ⟨15540215689522631970362543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41440575172060351920966781 15540215689522631970362543)
        ·
          refine ⟨23310323534283947955543815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15540215689522631970362543 23310323534283947955543815)
          ·
            refine ⟨34965485301425921933315723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23310323534283947955543815 34965485301425921933315723)
            ·
              refine ⟨52448227952138882899973585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34965485301425921933315723 52448227952138882899973585)
              ·
                refine ⟨39336170964104162174980189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52448227952138882899973585 39336170964104162174980189)
                ·
                  refine ⟨14751064111539060815617571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39336170964104162174980189 14751064111539060815617571)
                  ·
                    refine ⟨22126596167308591223426357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14751064111539060815617571 22126596167308591223426357)
                    ·
                      refine ⟨2074368390685180427196221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22126596167308591223426357 2074368390685180427196221)
                      ·
                        rfl

theorem cell23_4039818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_4039818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039818 prefixEnd_4039818 := by exact prefixLift 4039818
  have htrace : WordTrace (prefixWord ++ tailWord_4039818) baseStart_4039818 baseEnd_4039818 := by
    simpa [prefixWord, tailWord_4039818, baseEnd_4039818] using wordTrace_append hprefix tailTrace_4039818
  have hstable : (prefixWord ++ tailWord_4039818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039818).length < 2 ^ (prefixWord ++ tailWord_4039818).sum := by decide
  have hdescent : baseEnd_4039818 < baseStart_4039818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039826 : List Nat := [3, 2, 3, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_4039826 : Nat := 118140960795 + 4039826 * 2 ^ 59
def prefixEnd_4039826 : Nat := 4983230072969 + 3 ^ 40 * 4039826 * 2
def baseEnd_4039826 : Nat := 2074372498530416395896185

theorem tailTrace_4039826 : CollatzResearch.WordTrace tailWord_4039826 prefixEnd_4039826 2074372498530416395896185 := by
  unfold tailWord_4039826
  simp only [CollatzResearch.WordTrace]
  refine ⟨36836139765601956049098833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98229706041605216130930221 36836139765601956049098833)
  ·
    refine ⟨27627104824201467036824125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36836139765601956049098833 27627104824201467036824125)
    ·
      refine ⟨10360164309075550138809047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27627104824201467036824125 10360164309075550138809047)
      ·
        refine ⟨15540246463613325208213571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10360164309075550138809047 15540246463613325208213571)
        ·
          refine ⟨23310369695419987812320357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15540246463613325208213571 23310369695419987812320357)
          ·
            refine ⟨4370694317891247714810067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23310369695419987812320357 4370694317891247714810067)
            ·
              refine ⟨6556041476836871572215101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4370694317891247714810067 6556041476836871572215101)
              ·
                refine ⟨2458515553813826839580663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6556041476836871572215101 2458515553813826839580663)
                ·
                  refine ⟨3687773330720740259370995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2458515553813826839580663 3687773330720740259370995)
                  ·
                    refine ⟨5531659996081110389056493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3687773330720740259370995 5531659996081110389056493)
                    ·
                      refine ⟨2074372498530416395896185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5531659996081110389056493 2074372498530416395896185)
                      ·
                        rfl

theorem cell23_4039826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_4039826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039826 prefixEnd_4039826 := by exact prefixLift 4039826
  have htrace : WordTrace (prefixWord ++ tailWord_4039826) baseStart_4039826 baseEnd_4039826 := by
    simpa [prefixWord, tailWord_4039826, baseEnd_4039826] using wordTrace_append hprefix tailTrace_4039826
  have hstable : (prefixWord ++ tailWord_4039826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039826).length < 2 ^ (prefixWord ++ tailWord_4039826).sum := by decide
  have hdescent : baseEnd_4039826 < baseStart_4039826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039898 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 2, 6]
def baseStart_4039898 : Nat := 118140960795 + 4039898 * 2 ^ 59
def prefixEnd_4039898 : Nat := 4983230072969 + 3 ^ 40 * 4039898 * 2
def baseEnd_4039898 : Nat := 691469823045846704731951

theorem tailTrace_4039898 : CollatzResearch.WordTrace tailWord_4039898 prefixEnd_4039898 691469823045846704731951 := by
  unfold tailWord_4039898
  simp only [CollatzResearch.WordTrace]
  refine ⟨36836796279536745123254087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98231456745431320328677565 36836796279536745123254087)
  ·
    refine ⟨55255194419305117684881131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36836796279536745123254087 55255194419305117684881131)
    ·
      refine ⟨82882791628957676527321697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55255194419305117684881131 82882791628957676527321697)
      ·
        refine ⟨62162093721718257395491273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82882791628957676527321697 62162093721718257395491273)
        ·
          refine ⟨46621570291288693046618455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62162093721718257395491273 46621570291288693046618455)
          ·
            refine ⟨69932355436933039569927683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46621570291288693046618455 69932355436933039569927683)
            ·
              refine ⟨104898533155399559354891525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69932355436933039569927683 104898533155399559354891525)
              ·
                refine ⟨19668474966637417379042161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104898533155399559354891525 19668474966637417379042161)
                ·
                  refine ⟨14751356224978063034281621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19668474966637417379042161 14751356224978063034281621)
                  ·
                    refine ⟨691469823045846704731951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14751356224978063034281621 691469823045846704731951)
                    ·
                      rfl

theorem cell23_4039898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_4039898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039898 prefixEnd_4039898 := by exact prefixLift 4039898
  have htrace : WordTrace (prefixWord ++ tailWord_4039898) baseStart_4039898 baseEnd_4039898 := by
    simpa [prefixWord, tailWord_4039898, baseEnd_4039898] using wordTrace_append hprefix tailTrace_4039898
  have hstable : (prefixWord ++ tailWord_4039898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039898).length < 2 ^ (prefixWord ++ tailWord_4039898).sum := by decide
  have hdescent : baseEnd_4039898 < baseStart_4039898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039908 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_4039908 : Nat := 118140960795 + 4039908 * 2 ^ 59
def prefixEnd_4039908 : Nat := 4983230072969 + 3 ^ 40 * 4039908 * 2
def baseEnd_4039908 : Nat := 2074414603944085075070807

theorem tailTrace_4039908 : CollatzResearch.WordTrace tailWord_4039908 prefixEnd_4039908 2074414603944085075070807 := by
  unfold tailWord_4039908
  simp only [CollatzResearch.WordTrace]
  refine ⟨73673774924055376100440189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98231699898740501467253585 73673774924055376100440189)
  ·
    refine ⟨27627665596520766037665071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73673774924055376100440189 27627665596520766037665071)
    ·
      refine ⟨41441498394781149056497607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27627665596520766037665071 41441498394781149056497607)
      ·
        refine ⟨62162247592171723584746411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41441498394781149056497607 62162247592171723584746411)
        ·
          refine ⟨93243371388257585377119617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62162247592171723584746411 93243371388257585377119617)
          ·
            refine ⟨69932528541193189032839713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93243371388257585377119617 69932528541193189032839713)
            ·
              refine ⟨52449396405894891774629785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69932528541193189032839713 52449396405894891774629785)
              ·
                refine ⟨39337047304421168830972339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52449396405894891774629785 39337047304421168830972339)
                ·
                  refine ⟨59005570956631753246458509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39337047304421168830972339 59005570956631753246458509)
                  ·
                    refine ⟨22127089108736907467421941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59005570956631753246458509 22127089108736907467421941)
                    ·
                      refine ⟨2074414603944085075070807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22127089108736907467421941 2074414603944085075070807)
                      ·
                        rfl

theorem cell23_4039908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_4039908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039908 prefixEnd_4039908 := by exact prefixLift 4039908
  have htrace : WordTrace (prefixWord ++ tailWord_4039908) baseStart_4039908 baseEnd_4039908 := by
    simpa [prefixWord, tailWord_4039908, baseEnd_4039908] using wordTrace_append hprefix tailTrace_4039908
  have hstable : (prefixWord ++ tailWord_4039908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039908).length < 2 ^ (prefixWord ++ tailWord_4039908).sum := by decide
  have hdescent : baseEnd_4039908 < baseStart_4039908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4039962 : List Nat := [3, 1, 1, 3, 3, 1, 2, 4, 5]
def baseStart_4039962 : Nat := 118140960795 + 4039962 * 2 ^ 59
def prefixEnd_4039962 : Nat := 4983230072969 + 3 ^ 40 * 4039962 * 2
def baseEnd_4039962 : Nat := 230493592433269762643951

theorem tailTrace_4039962 : CollatzResearch.WordTrace tailWord_4039962 prefixEnd_4039962 230493592433269762643951 := by
  unfold tailWord_4039962
  simp only [CollatzResearch.WordTrace]
  refine ⟨36837379847478779855836535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98233012926610079615564093 36837379847478779855836535)
  ·
    refine ⟨55256069771218169783754803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36837379847478779855836535 55256069771218169783754803)
    ·
      refine ⟨82884104656827254675632205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55256069771218169783754803 82884104656827254675632205)
      ·
        refine ⟨31081539246310220503362077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82884104656827254675632205 31081539246310220503362077)
        ·
          refine ⟨11655577217366332688760779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31081539246310220503362077 11655577217366332688760779)
          ·
            refine ⟨17483365826049499033141169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11655577217366332688760779 17483365826049499033141169)
            ·
              refine ⟨13112524369537124274855877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17483365826049499033141169 13112524369537124274855877)
              ·
                refine ⟨2458598319288210801535477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13112524369537124274855877 2458598319288210801535477)
                ·
                  refine ⟨230493592433269762643951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2458598319288210801535477 230493592433269762643951)
                  ·
                    rfl

theorem cell23_4039962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 5].length) (baseStart_4039962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4039962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4039962 prefixEnd_4039962 := by exact prefixLift 4039962
  have htrace : WordTrace (prefixWord ++ tailWord_4039962) baseStart_4039962 baseEnd_4039962 := by
    simpa [prefixWord, tailWord_4039962, baseEnd_4039962] using wordTrace_append hprefix tailTrace_4039962
  have hstable : (prefixWord ++ tailWord_4039962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4039962).length < 2 ^ (prefixWord ++ tailWord_4039962).sum := by decide
  have hdescent : baseEnd_4039962 < baseStart_4039962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4039962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040005 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 5, 4]
def baseStart_4040005 : Nat := 118140960795 + 4040005 * 2 ^ 59
def prefixEnd_4040005 : Nat := 4983230072969 + 3 ^ 40 * 4040005 * 2
def baseEnd_4040005 : Nat := 691488137189190398519287

theorem tailTrace_4040005 : CollatzResearch.WordTrace tailWord_4040005 prefixEnd_4040005 691488137189190398519287 := by
  unfold tailWord_4040005
  simp only [CollatzResearch.WordTrace]
  refine ⟨147351087728759337767161469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98234058485839558511440979 147351087728759337767161469)
  ·
    refine ⟨55256657898284751662685551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147351087728759337767161469 55256657898284751662685551)
    ·
      refine ⟨82884986847427127494028327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55256657898284751662685551 82884986847427127494028327)
      ·
        refine ⟨124327480271140691241042491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82884986847427127494028327 124327480271140691241042491)
        ·
          refine ⟨186491220406711036861563737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124327480271140691241042491 186491220406711036861563737)
          ·
            refine ⟨139868415305033277646172803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186491220406711036861563737 139868415305033277646172803)
            ·
              refine ⟨209802622957549916469259205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139868415305033277646172803 209802622957549916469259205)
              ·
                refine ⟨39337991804540609337986101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209802622957549916469259205 39337991804540609337986101)
                ·
                  refine ⟨3687936731675682125436197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39337991804540609337986101 3687936731675682125436197)
                  ·
                    refine ⟨691488137189190398519287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3687936731675682125436197 691488137189190398519287)
                    ·
                      rfl

theorem cell23_4040005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_4040005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040005 prefixEnd_4040005 := by exact prefixLift 4040005
  have htrace : WordTrace (prefixWord ++ tailWord_4040005) baseStart_4040005 baseEnd_4040005 := by
    simpa [prefixWord, tailWord_4040005, baseEnd_4040005] using wordTrace_append hprefix tailTrace_4040005
  have hstable : (prefixWord ++ tailWord_4040005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040005).length < 2 ^ (prefixWord ++ tailWord_4040005).sum := by decide
  have hdescent : baseEnd_4040005 < baseStart_4040005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040012 : List Nat := [2, 2, 1, 3, 2, 3, 1, 2, 2, 1, 4]
def baseStart_4040012 : Nat := 118140960795 + 4040012 * 2 ^ 59
def prefixEnd_4040012 : Nat := 4983230072969 + 3 ^ 40 * 4040012 * 2
def baseEnd_4040012 : Nat := 2074468005932152668170329

theorem tailTrace_4040012 : CollatzResearch.WordTrace tailWord_4040012 prefixEnd_4040012 2074468005932152668170329 := by
  unfold tailWord_4040012
  simp only [CollatzResearch.WordTrace]
  refine ⟨73675671519866988981333145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98234228693155985308444193 73675671519866988981333145)
  ·
    refine ⟨55256753639900241735999859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73675671519866988981333145 55256753639900241735999859)
    ·
      refine ⟨82885130459850362603999789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55256753639900241735999859 82885130459850362603999789)
      ·
        refine ⟨31081923922443885976499921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82885130459850362603999789 31081923922443885976499921)
        ·
          refine ⟨23311442941832914482374941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31081923922443885976499921 23311442941832914482374941)
          ·
            refine ⟨8741791103187342930890603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23311442941832914482374941 8741791103187342930890603)
            ·
              refine ⟨13112686654781014396335905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8741791103187342930890603 13112686654781014396335905)
              ·
                refine ⟨9834514991085760797251929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13112686654781014396335905 9834514991085760797251929)
                ·
                  refine ⟨7375886243314320597938947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9834514991085760797251929 7375886243314320597938947)
                  ·
                    refine ⟨11063829364971480896908421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7375886243314320597938947 11063829364971480896908421)
                    ·
                      refine ⟨2074468005932152668170329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11063829364971480896908421 2074468005932152668170329)
                      ·
                        rfl

theorem cell23_4040012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_4040012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040012 prefixEnd_4040012 := by exact prefixLift 4040012
  have htrace : WordTrace (prefixWord ++ tailWord_4040012) baseStart_4040012 baseEnd_4040012 := by
    simpa [prefixWord, tailWord_4040012, baseEnd_4040012] using wordTrace_append hprefix tailTrace_4040012
  have hstable : (prefixWord ++ tailWord_4040012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040012).length < 2 ^ (prefixWord ++ tailWord_4040012).sum := by decide
  have hdescent : baseEnd_4040012 < baseStart_4040012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040013 : List Nat := [1, 6, 1, 3, 1, 1, 3, 2, 5]
def baseStart_4040013 : Nat := 118140960795 + 4040013 * 2 ^ 59
def prefixEnd_4040013 : Nat := 4983230072969 + 3 ^ 40 * 4040013 * 2
def baseEnd_4040013 : Nat := 230496502156978573806425

theorem tailTrace_4040013 : CollatzResearch.WordTrace tailWord_4040013 prefixEnd_4040013 230496502156978573806425 := by
  unfold tailWord_4040013
  simp only [CollatzResearch.WordTrace]
  refine ⟨147351379512730355133452693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98234253008486903422301795 147351379512730355133452693)
  ·
    refine ⟨6907095914659235396880595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 147351379512730355133452693 6907095914659235396880595)
    ·
      refine ⟨10360643871988853095320893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6907095914659235396880595 10360643871988853095320893)
      ·
        refine ⟨3885241451995819910745335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10360643871988853095320893 3885241451995819910745335)
        ·
          refine ⟨5827862177993729866118003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3885241451995819910745335 5827862177993729866118003)
          ·
            refine ⟨8741793266990594799177005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5827862177993729866118003 8741793266990594799177005)
            ·
              refine ⟨3278172475121473049691377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8741793266990594799177005 3278172475121473049691377)
              ·
                refine ⟨2458629356341104787268533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3278172475121473049691377 2458629356341104787268533)
                ·
                  refine ⟨230496502156978573806425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2458629356341104787268533 230496502156978573806425)
                  ·
                    rfl

theorem cell23_4040013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_4040013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040013 prefixEnd_4040013 := by exact prefixLift 4040013
  have htrace : WordTrace (prefixWord ++ tailWord_4040013) baseStart_4040013 baseEnd_4040013 := by
    simpa [prefixWord, tailWord_4040013, baseEnd_4040013] using wordTrace_append hprefix tailTrace_4040013
  have hstable : (prefixWord ++ tailWord_4040013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040013).length < 2 ^ (prefixWord ++ tailWord_4040013).sum := by decide
  have hdescent : baseEnd_4040013 < baseStart_4040013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040046 : List Nat := [4, 1, 2, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_4040046 : Nat := 118140960795 + 4040046 * 2 ^ 59
def prefixEnd_4040046 : Nat := 4983230072969 + 3 ^ 40 * 4040046 * 2
def baseEnd_4040046 : Nat := 2074485464274405535145173

theorem tailTrace_4040046 : CollatzResearch.WordTrace tailWord_4040046 prefixEnd_4040046 2074485464274405535145173 := by
  unfold tailWord_4040046
  simp only [CollatzResearch.WordTrace]
  refine ⟨18419072890201350221175499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98235055414407201179602661 18419072890201350221175499)
  ·
    refine ⟨27628609335302025331763249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18419072890201350221175499 27628609335302025331763249)
    ·
      refine ⟨20721457001476518998822437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27628609335302025331763249 20721457001476518998822437)
      ·
        refine ⟨3885273187776847312279207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20721457001476518998822437 3885273187776847312279207)
        ·
          refine ⟨5827909781665270968418811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3885273187776847312279207 5827909781665270968418811)
          ·
            refine ⟨8741864672497906452628217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5827909781665270968418811 8741864672497906452628217)
            ·
              refine ⟨6556398504373429839471163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8741864672497906452628217 6556398504373429839471163)
              ·
                refine ⟨9834597756560144759206745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6556398504373429839471163 9834597756560144759206745)
                ·
                  refine ⟨7375948317420108569405059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9834597756560144759206745 7375948317420108569405059)
                  ·
                    refine ⟨11063922476130162854107589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7375948317420108569405059 11063922476130162854107589)
                    ·
                      refine ⟨2074485464274405535145173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11063922476130162854107589 2074485464274405535145173)
                      ·
                        rfl

theorem cell23_4040046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_4040046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040046 prefixEnd_4040046 := by exact prefixLift 4040046
  have htrace : WordTrace (prefixWord ++ tailWord_4040046) baseStart_4040046 baseEnd_4040046 := by
    simpa [prefixWord, tailWord_4040046, baseEnd_4040046] using wordTrace_append hprefix tailTrace_4040046
  have hstable : (prefixWord ++ tailWord_4040046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040046).length < 2 ^ (prefixWord ++ tailWord_4040046).sum := by decide
  have hdescent : baseEnd_4040046 < baseStart_4040046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040066 : List Nat := [3, 4, 2, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_4040066 : Nat := 118140960795 + 4040066 * 2 ^ 59
def prefixEnd_4040066 : Nat := 4983230072969 + 3 ^ 40 * 4040066 * 2
def baseEnd_4040066 : Nat := 2074495733887495456895081

theorem tailTrace_4040066 : CollatzResearch.WordTrace tailWord_4040066 prefixEnd_4040066 2074495733887495456895081 := by
  unfold tailWord_4040066
  simp only [CollatzResearch.WordTrace]
  refine ⟨36838328145384586296283013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98235541721025563456754701 36838328145384586296283013)
  ·
    refine ⟨6907186527259609930553065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36838328145384586296283013 6907186527259609930553065)
    ·
      refine ⟨5180389895444707447914799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6907186527259609930553065 5180389895444707447914799)
      ·
        refine ⟨7770584843167061171872199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5180389895444707447914799 7770584843167061171872199)
        ·
          refine ⟨11655877264750591757808299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7770584843167061171872199 11655877264750591757808299)
          ·
            refine ⟨17483815897125887636712449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11655877264750591757808299 17483815897125887636712449)
            ·
              refine ⟨13112861922844415727534337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17483815897125887636712449 13112861922844415727534337)
              ·
                refine ⟨9834646442133311795650753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13112861922844415727534337 9834646442133311795650753)
                ·
                  refine ⟨7375984831599983846738065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9834646442133311795650753 7375984831599983846738065)
                  ·
                    refine ⟨5531988623699987885053549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7375984831599983846738065 5531988623699987885053549)
                    ·
                      refine ⟨2074495733887495456895081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5531988623699987885053549 2074495733887495456895081)
                      ·
                        rfl

theorem cell23_4040066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_4040066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040066 prefixEnd_4040066 := by exact prefixLift 4040066
  have htrace : WordTrace (prefixWord ++ tailWord_4040066) baseStart_4040066 baseEnd_4040066 := by
    simpa [prefixWord, tailWord_4040066, baseEnd_4040066] using wordTrace_append hprefix tailTrace_4040066
  have hstable : (prefixWord ++ tailWord_4040066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040066).length < 2 ^ (prefixWord ++ tailWord_4040066).sum := by decide
  have hdescent : baseEnd_4040066 < baseStart_4040066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040073 : List Nat := [1, 2, 1, 1, 7, 2, 2, 2, 1, 4]
def baseStart_4040073 : Nat := 118140960795 + 4040073 * 2 ^ 59
def prefixEnd_4040073 : Nat := 4983230072969 + 3 ^ 40 * 4040073 * 2
def baseEnd_4040073 : Nat := 691499776084025643169183

theorem tailTrace_4040073 : CollatzResearch.WordTrace tailWord_4040073 prefixEnd_4040073 691499776084025643169183 := by
  unfold tailWord_4040073
  simp only [CollatzResearch.WordTrace]
  refine ⟨147353567892512985380636873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98235711928341990253757915 147353567892512985380636873)
  ·
    refine ⟨110515175919384739035477655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147353567892512985380636873 110515175919384739035477655)
    ·
      refine ⟨165772763879077108553216483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110515175919384739035477655 165772763879077108553216483)
      ·
        refine ⟨248659145818615662829824725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165772763879077108553216483 248659145818615662829824725)
        ·
          refine ⟨5827948730123804597574017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 248659145818615662829824725 5827948730123804597574017)
          ·
            refine ⟨4370961547592853448180513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5827948730123804597574017 4370961547592853448180513)
            ·
              refine ⟨3278221160694640086135385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4370961547592853448180513 3278221160694640086135385)
              ·
                refine ⟨2458665870520980064601539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3278221160694640086135385 2458665870520980064601539)
                ·
                  refine ⟨3687998805781470096902309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2458665870520980064601539 3687998805781470096902309)
                  ·
                    refine ⟨691499776084025643169183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3687998805781470096902309 691499776084025643169183)
                    ·
                      rfl

theorem cell23_4040073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 1, 4].length) (baseStart_4040073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040073 prefixEnd_4040073 := by exact prefixLift 4040073
  have htrace : WordTrace (prefixWord ++ tailWord_4040073) baseStart_4040073 baseEnd_4040073 := by
    simpa [prefixWord, tailWord_4040073, baseEnd_4040073] using wordTrace_append hprefix tailTrace_4040073
  have hstable : (prefixWord ++ tailWord_4040073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040073).length < 2 ^ (prefixWord ++ tailWord_4040073).sum := by decide
  have hdescent : baseEnd_4040073 < baseStart_4040073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040119 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 5, 2, 2]
def baseStart_4040119 : Nat := 118140960795 + 4040119 * 2 ^ 59
def prefixEnd_4040119 : Nat := 4983230072969 + 3 ^ 40 * 4040119 * 2
def baseEnd_4040119 : Nat := 2074522948362183749532337

theorem tailTrace_4040119 : CollatzResearch.WordTrace tailWord_4040119 prefixEnd_4040119 2074522948362183749532337 := by
  unfold tailWord_4040119
  simp only [CollatzResearch.WordTrace]
  refine ⟨147355245650346335236811411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98236830433564223491207607 147355245650346335236811411)
  ·
    refine ⟨221032868475519502855217117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147355245650346335236811411 221032868475519502855217117)
    ·
      refine ⟨82887325678319813570706419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221032868475519502855217117 82887325678319813570706419)
      ·
        refine ⟨124330988517479720356059629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82887325678319813570706419 124330988517479720356059629)
        ·
          refine ⟨46624120694054895133522361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124330988517479720356059629 46624120694054895133522361)
          ·
            refine ⟨34968090520541171350141771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46624120694054895133522361 34968090520541171350141771)
            ·
              refine ⟨52452135780811757025212657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34968090520541171350141771 52452135780811757025212657)
              ·
                refine ⟨39339101835608817768909493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52452135780811757025212657 39339101835608817768909493)
                ·
                  refine ⟨3688040797088326665835265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39339101835608817768909493 3688040797088326665835265)
                  ·
                    refine ⟨2766030597816244999376449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3688040797088326665835265 2766030597816244999376449)
                    ·
                      refine ⟨2074522948362183749532337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766030597816244999376449 2074522948362183749532337)
                      ·
                        rfl

theorem cell23_4040119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 2, 2].length) (baseStart_4040119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040119 prefixEnd_4040119 := by exact prefixLift 4040119
  have htrace : WordTrace (prefixWord ++ tailWord_4040119) baseStart_4040119 baseEnd_4040119 := by
    simpa [prefixWord, tailWord_4040119, baseEnd_4040119] using wordTrace_append hprefix tailTrace_4040119
  have hstable : (prefixWord ++ tailWord_4040119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040119).length < 2 ^ (prefixWord ++ tailWord_4040119).sum := by decide
  have hdescent : baseEnd_4040119 < baseStart_4040119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040125 : List Nat := [1, 4, 1, 2, 2, 1, 12]
def baseStart_4040125 : Nat := 118140960795 + 4040125 * 2 ^ 59
def prefixEnd_4040125 : Nat := 4983230072969 + 3 ^ 40 * 4040125 * 2
def baseEnd_4040125 : Nat := 25611432459828527482189

theorem tailTrace_4040125 : CollatzResearch.WordTrace tailWord_4040125 prefixEnd_4040125 25611432459828527482189 := by
  unfold tailWord_4040125
  simp only [CollatzResearch.WordTrace]
  refine ⟨147355464488324598261529829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98236976325549732174353219 147355464488324598261529829)
  ·
    refine ⟨27629149591560862174036843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147355464488324598261529829 27629149591560862174036843)
    ·
      refine ⟨41443724387341293261055265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27629149591560862174036843 41443724387341293261055265)
      ·
        refine ⟨31082793290505969945791449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41443724387341293261055265 31082793290505969945791449)
        ·
          refine ⟨23312094967879477459343587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31082793290505969945791449 23312094967879477459343587)
          ·
            refine ⟨34968142451819216189015381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23312094967879477459343587 34968142451819216189015381)
            ·
              refine ⟨25611432459828527482189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 34968142451819216189015381 25611432459828527482189)
              ·
                rfl

theorem cell23_4040125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 12].length) (baseStart_4040125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040125 prefixEnd_4040125 := by exact prefixLift 4040125
  have htrace : WordTrace (prefixWord ++ tailWord_4040125) baseStart_4040125 baseEnd_4040125 := by
    simpa [prefixWord, tailWord_4040125, baseEnd_4040125] using wordTrace_append hprefix tailTrace_4040125
  have hstable : (prefixWord ++ tailWord_4040125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040125).length < 2 ^ (prefixWord ++ tailWord_4040125).sum := by decide
  have hdescent : baseEnd_4040125 < baseStart_4040125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040136 : List Nat := [2, 1, 3, 1, 3, 1, 4, 1, 3, 2, 2]
def baseStart_4040136 : Nat := 118140960795 + 4040136 * 2 ^ 59
def prefixEnd_4040136 : Nat := 4983230072969 + 3 ^ 40 * 4040136 * 2
def baseEnd_4040136 : Nat := 2074531677533310183019759

theorem tailTrace_4040136 : CollatzResearch.WordTrace tailWord_4040136 prefixEnd_4040136 2074531677533310183019759 := by
  unfold tailWord_4040136
  simp only [CollatzResearch.WordTrace]
  refine ⟨73677932845642373570090131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98237243794189831426786841 73677932845642373570090131)
  ·
    refine ⟨110516899268463560355135197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73677932845642373570090131 110516899268463560355135197)
    ·
      refine ⟨41443837225673835133175699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110516899268463560355135197 41443837225673835133175699)
      ·
        refine ⟨62165755838510752699763549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41443837225673835133175699 62165755838510752699763549)
        ·
          refine ⟨23312158439441532262411331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62165755838510752699763549 23312158439441532262411331)
          ·
            refine ⟨34968237659162298393616997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23312158439441532262411331 34968237659162298393616997)
            ·
              refine ⟨6556544561092930948803187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34968237659162298393616997 6556544561092930948803187)
              ·
                refine ⟨9834816841639396423204781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6556544561092930948803187 9834816841639396423204781)
                ·
                  refine ⟨3688056315614773658701793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9834816841639396423204781 3688056315614773658701793)
                  ·
                    refine ⟨2766042236711080244026345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3688056315614773658701793 2766042236711080244026345)
                    ·
                      refine ⟨2074531677533310183019759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766042236711080244026345 2074531677533310183019759)
                      ·
                        rfl

theorem cell23_4040136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_4040136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040136 prefixEnd_4040136 := by exact prefixLift 4040136
  have htrace : WordTrace (prefixWord ++ tailWord_4040136) baseStart_4040136 baseEnd_4040136 := by
    simpa [prefixWord, tailWord_4040136, baseEnd_4040136] using wordTrace_append hprefix tailTrace_4040136
  have hstable : (prefixWord ++ tailWord_4040136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040136).length < 2 ^ (prefixWord ++ tailWord_4040136).sum := by decide
  have hdescent : baseEnd_4040136 < baseStart_4040136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040209 : List Nat := [1, 2, 2, 1, 1, 2, 4, 3, 1, 4, 2]
def baseStart_4040209 : Nat := 118140960795 + 4040209 * 2 ^ 59
def prefixEnd_4040209 : Nat := 4983230072969 + 3 ^ 40 * 4040209 * 2
def baseEnd_4040209 : Nat := 2074569161621088397406923

theorem tailTrace_4040209 : CollatzResearch.WordTrace tailWord_4040209 prefixEnd_4040209 2074569161621088397406923 := by
  unfold tailWord_4040209
  simp only [CollatzResearch.WordTrace]
  refine ⟨147358528220020280607587681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98239018813346853738391787 147358528220020280607587681)
  ·
    refine ⟨110518896165015210455690761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147358528220020280607587681 110518896165015210455690761)
    ·
      refine ⟨82889172123761407841768071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110518896165015210455690761 82889172123761407841768071)
      ·
        refine ⟨124333758185642111762652107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82889172123761407841768071 124333758185642111762652107)
        ·
          refine ⟨186500637278463167643978161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124333758185642111762652107 186500637278463167643978161)
          ·
            refine ⟨139875477958847375732983621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186500637278463167643978161 139875477958847375732983621)
            ·
              refine ⟨26226652117283882949934429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139875477958847375732983621 26226652117283882949934429)
              ·
                refine ⟨9834994543981456106225411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26226652117283882949934429 9834994543981456106225411)
                ·
                  refine ⟨14752491815972184159338117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9834994543981456106225411 14752491815972184159338117)
                  ·
                    refine ⟨2766092215494784529875897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14752491815972184159338117 2766092215494784529875897)
                    ·
                      refine ⟨2074569161621088397406923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766092215494784529875897 2074569161621088397406923)
                      ·
                        rfl

theorem cell23_4040209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 4, 2].length) (baseStart_4040209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040209 prefixEnd_4040209 := by exact prefixLift 4040209
  have htrace : WordTrace (prefixWord ++ tailWord_4040209) baseStart_4040209 baseEnd_4040209 := by
    simpa [prefixWord, tailWord_4040209, baseEnd_4040209] using wordTrace_append hprefix tailTrace_4040209
  have hstable : (prefixWord ++ tailWord_4040209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040209).length < 2 ^ (prefixWord ++ tailWord_4040209).sum := by decide
  have hdescent : baseEnd_4040209 < baseStart_4040209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040213 : List Nat := [1, 3, 2, 1, 3, 4, 1, 2, 1, 3, 2]
def baseStart_4040213 : Nat := 118140960795 + 4040213 * 2 ^ 59
def prefixEnd_4040213 : Nat := 4983230072969 + 3 ^ 40 * 4040213 * 2
def baseEnd_4040213 : Nat := 2074571215543706381756905

theorem tailTrace_4040213 : CollatzResearch.WordTrace tailWord_4040213 prefixEnd_4040213 2074571215543706381756905 := by
  unfold tailWord_4040213
  simp only [CollatzResearch.WordTrace]
  refine ⟨147358674112005789290733293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98239116074670526193822195 147358674112005789290733293)
  ·
    refine ⟨55259502792002170984024985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147358674112005789290733293 55259502792002170984024985)
    ·
      refine ⟨41444627094001628238018739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55259502792002170984024985 41444627094001628238018739)
      ·
        refine ⟨62166940641002442357028109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41444627094001628238018739 62166940641002442357028109)
        ·
          refine ⟨23312602740375915883885541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62166940641002442357028109 23312602740375915883885541)
          ·
            refine ⟨4371113013820484228228539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23312602740375915883885541 4371113013820484228228539)
            ·
              refine ⟨6556669520730726342342809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4371113013820484228228539 6556669520730726342342809)
              ·
                refine ⟨4917502140548044756757107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6556669520730726342342809 4917502140548044756757107)
                ·
                  refine ⟨7376253210822067135135661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4917502140548044756757107 7376253210822067135135661)
                  ·
                    refine ⟨2766094954058275175675873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7376253210822067135135661 2766094954058275175675873)
                    ·
                      refine ⟨2074571215543706381756905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766094954058275175675873 2074571215543706381756905)
                      ·
                        rfl

theorem cell23_4040213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_4040213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040213 prefixEnd_4040213 := by exact prefixLift 4040213
  have htrace : WordTrace (prefixWord ++ tailWord_4040213) baseStart_4040213 baseEnd_4040213 := by
    simpa [prefixWord, tailWord_4040213, baseEnd_4040213] using wordTrace_append hprefix tailTrace_4040213
  have hstable : (prefixWord ++ tailWord_4040213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040213).length < 2 ^ (prefixWord ++ tailWord_4040213).sum := by decide
  have hdescent : baseEnd_4040213 < baseStart_4040213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040226 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 6, 2, 2]
def baseStart_4040226 : Nat := 118140960795 + 4040226 * 2 ^ 59
def prefixEnd_4040226 : Nat := 4983230072969 + 3 ^ 40 * 4040226 * 2
def baseEnd_4040226 : Nat := 2074577890792214830894345

theorem tailTrace_4040226 : CollatzResearch.WordTrace tailWord_4040226 prefixEnd_4040226 2074577890792214830894345 := by
  unfold tailWord_4040226
  simp only [CollatzResearch.WordTrace]
  refine ⟨36839787065239673127739133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98239432173972461673971021 36839787065239673127739133)
  ·
    refine ⟨13814920149464877422902175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36839787065239673127739133 13814920149464877422902175)
    ·
      refine ⟨20722380224197316134353263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13814920149464877422902175 20722380224197316134353263)
      ·
        refine ⟨31083570336295974201529895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20722380224197316134353263 31083570336295974201529895)
        ·
          refine ⟨46625355504443961302294843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31083570336295974201529895 46625355504443961302294843)
          ·
            refine ⟨69938033256665941953442265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46625355504443961302294843 69938033256665941953442265)
            ·
              refine ⟨52453524942499456465081699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69938033256665941953442265 52453524942499456465081699)
              ·
                refine ⟨78680287413749184697622549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52453524942499456465081699 78680287413749184697622549)
                ·
                  refine ⟨3688138472519493032701057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78680287413749184697622549 3688138472519493032701057)
                  ·
                    refine ⟨2766103854389619774525793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3688138472519493032701057 2766103854389619774525793)
                    ·
                      refine ⟨2074577890792214830894345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766103854389619774525793 2074577890792214830894345)
                      ·
                        rfl

theorem cell23_4040226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_4040226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040226 prefixEnd_4040226 := by exact prefixLift 4040226
  have htrace : WordTrace (prefixWord ++ tailWord_4040226) baseStart_4040226 baseEnd_4040226 := by
    simpa [prefixWord, tailWord_4040226, baseEnd_4040226] using wordTrace_append hprefix tailTrace_4040226
  have hstable : (prefixWord ++ tailWord_4040226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040226).length < 2 ^ (prefixWord ++ tailWord_4040226).sum := by decide
  have hdescent : baseEnd_4040226 < baseStart_4040226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040243 : List Nat := [1, 1, 1, 2, 4, 4, 2, 2, 2, 2, 2]
def baseStart_4040243 : Nat := 118140960795 + 4040243 * 2 ^ 59
def prefixEnd_4040243 : Nat := 4983230072969 + 3 ^ 40 * 4040243 * 2
def baseEnd_4040243 : Nat := 2074586619963341264381767

theorem tailTrace_4040243 : CollatzResearch.WordTrace tailWord_4040243 prefixEnd_4040243 2074586619963341264381767 := by
  unfold tailWord_4040243
  simp only [CollatzResearch.WordTrace]
  refine ⟨147359768301897104414325383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98239845534598069609550255 147359768301897104414325383)
  ·
    refine ⟨221039652452845656621488075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147359768301897104414325383 221039652452845656621488075)
    ·
      refine ⟨331559478679268484932232113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221039652452845656621488075 331559478679268484932232113)
      ·
        refine ⟨248669609009451363699174085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331559478679268484932232113 248669609009451363699174085)
        ·
          refine ⟨46625551689272130693595141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248669609009451363699174085 46625551689272130693595141)
          ·
            refine ⟨8742290941738524505049089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46625551689272130693595141 8742290941738524505049089)
            ·
              refine ⟨6556718206303893378786817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8742290941738524505049089 6556718206303893378786817)
              ·
                refine ⟨4917538654727920034090113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6556718206303893378786817 4917538654727920034090113)
                ·
                  refine ⟨3688153991045940025567585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4917538654727920034090113 3688153991045940025567585)
                  ·
                    refine ⟨2766115493284455019175689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3688153991045940025567585 2766115493284455019175689)
                    ·
                      refine ⟨2074586619963341264381767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766115493284455019175689 2074586619963341264381767)
                      ·
                        rfl

theorem cell23_4040243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 2, 2].length) (baseStart_4040243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040243 prefixEnd_4040243 := by exact prefixLift 4040243
  have htrace : WordTrace (prefixWord ++ tailWord_4040243) baseStart_4040243 baseEnd_4040243 := by
    simpa [prefixWord, tailWord_4040243, baseEnd_4040243] using wordTrace_append hprefix tailTrace_4040243
  have hstable : (prefixWord ++ tailWord_4040243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040243).length < 2 ^ (prefixWord ++ tailWord_4040243).sum := by decide
  have hdescent : baseEnd_4040243 < baseStart_4040243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040279 : List Nat := [1, 1, 3, 2, 2, 3, 3, 1, 2, 5]
def baseStart_4040279 : Nat := 118140960795 + 4040279 * 2 ^ 59
def prefixEnd_4040279 : Nat := 4983230072969 + 3 ^ 40 * 4040279 * 2
def baseEnd_4040279 : Nat := 691535035088967707843867

theorem tailTrace_4040279 : CollatzResearch.WordTrace tailWord_4040279 prefixEnd_4040279 691535035088967707843867 := by
  unfold tailWord_4040279
  simp only [CollatzResearch.WordTrace]
  refine ⟨147361081329766682562635891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98240720886511121708423927 147361081329766682562635891)
  ·
    refine ⟨221041621994650023843953837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147361081329766682562635891 221041621994650023843953837)
    ·
      refine ⟨82890608247993758941482689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221041621994650023843953837 82890608247993758941482689)
      ·
        refine ⟨62167956185995319206112017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82890608247993758941482689 62167956185995319206112017)
        ·
          refine ⟨46625967139496489404584013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62167956185995319206112017 46625967139496489404584013)
          ·
            refine ⟨17484737677311183526719005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46625967139496489404584013 17484737677311183526719005)
            ·
              refine ⟨6556776628991693822519627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17484737677311183526719005 6556776628991693822519627)
              ·
                refine ⟨9835164943487540733779441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6556776628991693822519627 9835164943487540733779441)
                ·
                  refine ⟨7376373707615655550334581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9835164943487540733779441 7376373707615655550334581)
                  ·
                    refine ⟨691535035088967707843867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7376373707615655550334581 691535035088967707843867)
                    ·
                      rfl

theorem cell23_4040279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_4040279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040279 prefixEnd_4040279 := by exact prefixLift 4040279
  have htrace : WordTrace (prefixWord ++ tailWord_4040279) baseStart_4040279 baseEnd_4040279 := by
    simpa [prefixWord, tailWord_4040279, baseEnd_4040279] using wordTrace_append hprefix tailTrace_4040279
  have hstable : (prefixWord ++ tailWord_4040279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040279).length < 2 ^ (prefixWord ++ tailWord_4040279).sum := by decide
  have hdescent : baseEnd_4040279 < baseStart_4040279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040312 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 4, 4, 4]
def baseStart_4040312 : Nat := 118140960795 + 4040312 * 2 ^ 59
def prefixEnd_4040312 : Nat := 4983230072969 + 3 ^ 40 * 4040312 * 2
def baseEnd_4040312 : Nat := 2074622050128501494418949

theorem tailTrace_4040312 : CollatzResearch.WordTrace tailWord_4040312 prefixEnd_4040312 2074622050128501494418949 := by
  unfold tailWord_4040312
  simp only [CollatzResearch.WordTrace]
  refine ⟨73681142469323564599293595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98241523292431419465724793 73681142469323564599293595)
  ·
    refine ⟨110521713703985346898940393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73681142469323564599293595 110521713703985346898940393)
    ·
      refine ⟨82891285277989010174205295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110521713703985346898940393 82891285277989010174205295)
      ·
        refine ⟨124336927916983515261307943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82891285277989010174205295 124336927916983515261307943)
        ·
          refine ⟨186505391875475272891961915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124336927916983515261307943 186505391875475272891961915)
          ·
            refine ⟨279758087813212909337942873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186505391875475272891961915 279758087813212909337942873)
            ·
              refine ⟨209818565859909682003457155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279758087813212909337942873 209818565859909682003457155)
              ·
                refine ⟨314727848789864523005185733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209818565859909682003457155 314727848789864523005185733)
                ·
                  refine ⟨59011471648099598063472325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314727848789864523005185733 59011471648099598063472325)
                  ·
                    refine ⟨11064650934018674636901061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59011471648099598063472325 11064650934018674636901061)
                    ·
                      refine ⟨2074622050128501494418949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11064650934018674636901061 2074622050128501494418949)
                      ·
                        rfl

theorem cell23_4040312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_4040312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040312 prefixEnd_4040312 := by exact prefixLift 4040312
  have htrace : WordTrace (prefixWord ++ tailWord_4040312) baseStart_4040312 baseEnd_4040312 := by
    simpa [prefixWord, tailWord_4040312, baseEnd_4040312] using wordTrace_append hprefix tailTrace_4040312
  have hstable : (prefixWord ++ tailWord_4040312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040312).length < 2 ^ (prefixWord ++ tailWord_4040312).sum := by decide
  have hdescent : baseEnd_4040312 < baseStart_4040312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040343 : List Nat := [1, 1, 3, 3, 2, 2, 3, 3, 1, 4]
def baseStart_4040343 : Nat := 118140960795 + 4040343 * 2 ^ 59
def prefixEnd_4040343 : Nat := 4983230072969 + 3 ^ 40 * 4040343 * 2
def baseEnd_4040343 : Nat := 691545989342930291043769

theorem tailTrace_4040343 : CollatzResearch.WordTrace tailWord_4040343 prefixEnd_4040343 691545989342930291043769 := by
  unfold tailWord_4040343
  simp only [CollatzResearch.WordTrace]
  refine ⟨147363415601534821492965683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98242277067689880995310455 147363415601534821492965683)
  ·
    refine ⟨221045123402302232239448525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147363415601534821492965683 221045123402302232239448525)
    ·
      refine ⟨82891921275863337089793197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221045123402302232239448525 82891921275863337089793197)
      ·
        refine ⟨31084470478448751408672449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82891921275863337089793197 31084470478448751408672449)
        ·
          refine ⟨23313352858836563556504337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31084470478448751408672449 23313352858836563556504337)
          ·
            refine ⟨17485014644127422667378253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23313352858836563556504337 17485014644127422667378253)
            ·
              refine ⟨6556880491547783500266845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17485014644127422667378253 6556880491547783500266845)
              ·
                refine ⟨2458830184330418812600067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6556880491547783500266845 2458830184330418812600067)
                ·
                  refine ⟨3688245276495628218900101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2458830184330418812600067 3688245276495628218900101)
                  ·
                    refine ⟨691545989342930291043769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3688245276495628218900101 691545989342930291043769)
                    ·
                      rfl

theorem cell23_4040343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 1, 4].length) (baseStart_4040343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040343 prefixEnd_4040343 := by exact prefixLift 4040343
  have htrace : WordTrace (prefixWord ++ tailWord_4040343) baseStart_4040343 baseEnd_4040343 := by
    simpa [prefixWord, tailWord_4040343, baseEnd_4040343] using wordTrace_append hprefix tailTrace_4040343
  have hstable : (prefixWord ++ tailWord_4040343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040343).length < 2 ^ (prefixWord ++ tailWord_4040343).sum := by decide
  have hdescent : baseEnd_4040343 < baseStart_4040343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040389 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 3, 1, 4]
def baseStart_4040389 : Nat := 118140960795 + 4040389 * 2 ^ 59
def prefixEnd_4040389 : Nat := 4983230072969 + 3 ^ 40 * 4040389 * 2
def baseEnd_4040389 : Nat := 2074661588138897693156095

theorem tailTrace_4040389 : CollatzResearch.WordTrace tailWord_4040389 prefixEnd_4040389 2074661588138897693156095 := by
  unfold tailWord_4040389
  simp only [CollatzResearch.WordTrace]
  refine ⟨147365093359368171349140221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98243395572912114232760147 147365093359368171349140221)
  ·
    refine ⟨55261910009763064255927583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147365093359368171349140221 55261910009763064255927583)
    ·
      refine ⟨82892865014644596383891375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55261910009763064255927583 82892865014644596383891375)
      ·
        refine ⟨124339297521966894575837063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82892865014644596383891375 124339297521966894575837063)
        ·
          refine ⟨186508946282950341863755595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124339297521966894575837063 186508946282950341863755595)
          ·
            refine ⟨279763419424425512795633393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186508946282950341863755595 279763419424425512795633393)
            ·
              refine ⟨209822564568319134596725045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279763419424425512795633393 209822564568319134596725045)
              ·
                refine ⟨19670865428279918868442973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209822564568319134596725045 19670865428279918868442973)
                ·
                  refine ⟨7376574535604969575666115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19670865428279918868442973 7376574535604969575666115)
                  ·
                    refine ⟨11064861803407454363499173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7376574535604969575666115 11064861803407454363499173)
                    ·
                      refine ⟨2074661588138897693156095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11064861803407454363499173 2074661588138897693156095)
                      ·
                        rfl

theorem cell23_4040389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_4040389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040389 prefixEnd_4040389 := by exact prefixLift 4040389
  have htrace : WordTrace (prefixWord ++ tailWord_4040389) baseStart_4040389 baseEnd_4040389 := by
    simpa [prefixWord, tailWord_4040389, baseEnd_4040389] using wordTrace_append hprefix tailTrace_4040389
  have hstable : (prefixWord ++ tailWord_4040389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040389).length < 2 ^ (prefixWord ++ tailWord_4040389).sum := by decide
  have hdescent : baseEnd_4040389 < baseStart_4040389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040399 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 6, 4]
def baseStart_4040399 : Nat := 118140960795 + 4040399 * 2 ^ 59
def prefixEnd_4040399 : Nat := 4983230072969 + 3 ^ 40 * 4040399 * 2
def baseEnd_4040399 : Nat := 691555574315147551343683

theorem tailTrace_4040399 : CollatzResearch.WordTrace tailWord_4040399 prefixEnd_4040399 691555574315147551343683 := by
  unfold tailWord_4040399
  simp only [CollatzResearch.WordTrace]
  refine ⟨147365458089331943057004251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98243638726221295371336167 147365458089331943057004251)
  ·
    refine ⟨221048187133997914585506377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147365458089331943057004251 221048187133997914585506377)
    ·
      refine ⟨165786140350498435939129783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221048187133997914585506377 165786140350498435939129783)
      ·
        refine ⟨248679210525747653908694675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165786140350498435939129783 248679210525747653908694675)
        ·
          refine ⟨373018815788621480863042013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248679210525747653908694675 373018815788621480863042013)
          ·
            refine ⟨139882055920733055323640755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373018815788621480863042013 139882055920733055323640755)
            ·
              refine ⟨209823083881099582985461133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139882055920733055323640755 209823083881099582985461133)
              ·
                refine ⟨78683656455412343619547925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209823083881099582985461133 78683656455412343619547925)
                ·
                  refine ⟨3688296396347453607166309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78683656455412343619547925 3688296396347453607166309)
                  ·
                    refine ⟨691555574315147551343683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3688296396347453607166309 691555574315147551343683)
                    ·
                      rfl

theorem cell23_4040399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 4].length) (baseStart_4040399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040399 prefixEnd_4040399 := by exact prefixLift 4040399
  have htrace : WordTrace (prefixWord ++ tailWord_4040399) baseStart_4040399 baseEnd_4040399 := by
    simpa [prefixWord, tailWord_4040399, baseEnd_4040399] using wordTrace_append hprefix tailTrace_4040399
  have hstable : (prefixWord ++ tailWord_4040399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040399).length < 2 ^ (prefixWord ++ tailWord_4040399).sum := by decide
  have hdescent : baseEnd_4040399 < baseStart_4040399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040416 : List Nat := [2, 1, 1, 3, 1, 2, 3, 4, 2, 4]
def baseStart_4040416 : Nat := 118140960795 + 4040416 * 2 ^ 59
def prefixEnd_4040416 : Nat := 4983230072969 + 3 ^ 40 * 4040416 * 2
def baseEnd_4040416 : Nat := 691558484038856362506157

theorem tailTrace_4040416 : CollatzResearch.WordTrace tailWord_4040416 prefixEnd_4040416 691558484038856362506157 := by
  unfold tailWord_4040416
  simp only [CollatzResearch.WordTrace]
  refine ⟨73683039065135177480186551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98244052086846903306915401 73683039065135177480186551)
  ·
    refine ⟨110524558597702766220279827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73683039065135177480186551 110524558597702766220279827)
    ·
      refine ⟨165786837896554149330419741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110524558597702766220279827 165786837896554149330419741)
      ·
        refine ⟨62170064211207805998907403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165786837896554149330419741 62170064211207805998907403)
        ·
          refine ⟨93255096316811708998361105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62170064211207805998907403 93255096316811708998361105)
          ·
            refine ⟨69941322237608781748770829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93255096316811708998361105 69941322237608781748770829)
            ·
              refine ⟨26227995839103293155789061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69941322237608781748770829 26227995839103293155789061)
              ·
                refine ⟨4917749219831867466710449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26227995839103293155789061 4917749219831867466710449)
                ·
                  refine ⟨3688311914873900600032837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4917749219831867466710449 3688311914873900600032837)
                  ·
                    refine ⟨691558484038856362506157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3688311914873900600032837 691558484038856362506157)
                    ·
                      rfl

theorem cell23_4040416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 2, 4].length) (baseStart_4040416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040416 prefixEnd_4040416 := by exact prefixLift 4040416
  have htrace : WordTrace (prefixWord ++ tailWord_4040416) baseStart_4040416 baseEnd_4040416 := by
    simpa [prefixWord, tailWord_4040416, baseEnd_4040416] using wordTrace_append hprefix tailTrace_4040416
  have hstable : (prefixWord ++ tailWord_4040416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040416).length < 2 ^ (prefixWord ++ tailWord_4040416).sum := by decide
  have hdescent : baseEnd_4040416 < baseStart_4040416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040426 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_4040426 : Nat := 118140960795 + 4040426 * 2 ^ 59
def prefixEnd_4040426 : Nat := 4983230072969 + 3 ^ 40 * 4040426 * 2
def baseEnd_4040426 : Nat := 2074680586923114048393425

theorem tailTrace_4040426 : CollatzResearch.WordTrace tailWord_4040426 prefixEnd_4040426 2074680586923114048393425 := by
  unfold tailWord_4040426
  simp only [CollatzResearch.WordTrace]
  refine ⟨36841610715058531667059283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98244295240156084445491421 36841610715058531667059283)
  ·
    refine ⟨55262416072587797500588925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36841610715058531667059283 55262416072587797500588925)
    ·
      refine ⟨20723406027220424062720847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55262416072587797500588925 20723406027220424062720847)
      ·
        refine ⟨31085109040830636094081271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20723406027220424062720847 31085109040830636094081271)
        ·
          refine ⟨46627663561245954141121907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31085109040830636094081271 46627663561245954141121907)
          ·
            refine ⟨69941495341868931211682861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46627663561245954141121907 69941495341868931211682861)
            ·
              refine ⟨26228060753200849204381073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69941495341868931211682861 26228060753200849204381073)
              ·
                refine ⟨19671045564900636903285805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26228060753200849204381073 19671045564900636903285805)
                ·
                  refine ⟨7376642086837738838732177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19671045564900636903285805 7376642086837738838732177)
                  ·
                    refine ⟨5532481565128304129049133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7376642086837738838732177 5532481565128304129049133)
                    ·
                      refine ⟨2074680586923114048393425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5532481565128304129049133 2074680586923114048393425)
                      ·
                        rfl

theorem cell23_4040426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_4040426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040426 prefixEnd_4040426 := by exact prefixLift 4040426
  have htrace : WordTrace (prefixWord ++ tailWord_4040426) baseStart_4040426 baseEnd_4040426 := by
    simpa [prefixWord, tailWord_4040426, baseEnd_4040426] using wordTrace_append hprefix tailTrace_4040426
  have hstable : (prefixWord ++ tailWord_4040426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040426).length < 2 ^ (prefixWord ++ tailWord_4040426).sum := by decide
  have hdescent : baseEnd_4040426 < baseStart_4040426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040456 : List Nat := [2, 1, 3, 2, 2, 1, 1, 4, 1, 3, 3]
def baseStart_4040456 : Nat := 118140960795 + 4040456 * 2 ^ 59
def prefixEnd_4040456 : Nat := 4983230072969 + 3 ^ 40 * 4040456 * 2
def baseEnd_4040456 : Nat := 2074695991342748931018287

theorem tailTrace_4040456 : CollatzResearch.WordTrace tailWord_4040456 prefixEnd_4040456 2074695991342748931018287 := by
  unfold tailWord_4040456
  simp only [CollatzResearch.WordTrace]
  refine ⟨73683768525062720895914611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98245024700083627861219481 73683768525062720895914611)
  ·
    refine ⟨110525652787594081343871917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73683768525062720895914611 110525652787594081343871917)
    ·
      refine ⟨41447119795347780503951969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110525652787594081343871917 41447119795347780503951969)
      ·
        refine ⟨31085339846510835377963977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41447119795347780503951969 31085339846510835377963977)
        ·
          refine ⟨23314004884883126533472983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31085339846510835377963977 23314004884883126533472983)
          ·
            refine ⟨34971007327324689800209475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23314004884883126533472983 34971007327324689800209475)
            ·
              refine ⟨52456510990987034700314213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34971007327324689800209475 52456510990987034700314213)
              ·
                refine ⟨9835595810810069006308915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52456510990987034700314213 9835595810810069006308915)
                ·
                  refine ⟨14753393716215103509463373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9835595810810069006308915 14753393716215103509463373)
                  ·
                    refine ⟨5532522643580663816048765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14753393716215103509463373 5532522643580663816048765)
                    ·
                      refine ⟨2074695991342748931018287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5532522643580663816048765 2074695991342748931018287)
                      ·
                        rfl

theorem cell23_4040456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_4040456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040456 prefixEnd_4040456 := by exact prefixLift 4040456
  have htrace : WordTrace (prefixWord ++ tailWord_4040456) baseStart_4040456 baseEnd_4040456 := by
    simpa [prefixWord, tailWord_4040456, baseEnd_4040456] using wordTrace_append hprefix tailTrace_4040456
  have hstable : (prefixWord ++ tailWord_4040456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040456).length < 2 ^ (prefixWord ++ tailWord_4040456).sum := by decide
  have hdescent : baseEnd_4040456 < baseStart_4040456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040519 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 9]
def baseStart_4040519 : Nat := 118140960795 + 4040519 * 2 ^ 59
def prefixEnd_4040519 : Nat := 4983230072969 + 3 ^ 40 * 4040519 * 2
def baseEnd_4040519 : Nat := 230525371180442464947833

theorem tailTrace_4040519 : CollatzResearch.WordTrace tailWord_4040519 prefixEnd_4040519 230525371180442464947833 := by
  unfold tailWord_4040519
  simp only [CollatzResearch.WordTrace]
  refine ⟨147369834848897203551372611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98246556565931469034248407 147369834848897203551372611)
  ·
    refine ⟨221054752273345805327058917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147369834848897203551372611 221054752273345805327058917)
    ·
      refine ⟨41447766051252338498823547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221054752273345805327058917 41447766051252338498823547)
      ·
        refine ⟨62171649076878507748235321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41447766051252338498823547 62171649076878507748235321)
        ·
          refine ⟨46628736807658880811176491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62171649076878507748235321 46628736807658880811176491)
          ·
            refine ⟨69943105211488321216764737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46628736807658880811176491 69943105211488321216764737)
            ·
              refine ⟨52457328908616240912573553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69943105211488321216764737 52457328908616240912573553)
              ·
                refine ⟨39342996681462180684430165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52457328908616240912573553 39342996681462180684430165)
                ·
                  refine ⟨230525371180442464947833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39342996681462180684430165 230525371180442464947833)
                  ·
                    rfl

theorem cell23_4040519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 9].length) (baseStart_4040519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040519 prefixEnd_4040519 := by exact prefixLift 4040519
  have htrace : WordTrace (prefixWord ++ tailWord_4040519) baseStart_4040519 baseEnd_4040519 := by
    simpa [prefixWord, tailWord_4040519, baseEnd_4040519] using wordTrace_append hprefix tailTrace_4040519
  have hstable : (prefixWord ++ tailWord_4040519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040519).length < 2 ^ (prefixWord ++ tailWord_4040519).sum := by decide
  have hdescent : baseEnd_4040519 < baseStart_4040519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040530 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2]
def baseStart_4040530 : Nat := 118140960795 + 4040530 * 2 ^ 59
def prefixEnd_4040530 : Nat := 4983230072969 + 3 ^ 40 * 4040530 * 2
def baseEnd_4040530 : Nat := 2074733988911181641492947

theorem tailTrace_4040530 : CollatzResearch.WordTrace tailWord_4040530 prefixEnd_4040530 2074733988911181641492947 := by
  unfold tailWord_4040530
  simp only [CollatzResearch.WordTrace]
  refine ⟨36842559012964338107505761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98246824034571568286682029 36842559012964338107505761)
  ·
    refine ⟨27631919259723253580629321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36842559012964338107505761 27631919259723253580629321)
    ·
      refine ⟨20723939444792440185471991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27631919259723253580629321 20723939444792440185471991)
      ·
        refine ⟨31085909167188660278207987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20723939444792440185471991 31085909167188660278207987)
        ·
          refine ⟨46628863750782990417311981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31085909167188660278207987 46628863750782990417311981)
          ·
            refine ⟨17485823906543621406491993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46628863750782990417311981 17485823906543621406491993)
            ·
              refine ⟨13114367929907716054868995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17485823906543621406491993 13114367929907716054868995)
              ·
                refine ⟨19671551894861574082303493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13114367929907716054868995 19671551894861574082303493)
                ·
                  refine ⟨3688415980286545140431905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19671551894861574082303493 3688415980286545140431905)
                  ·
                    refine ⟨2766311985214908855323929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3688415980286545140431905 2766311985214908855323929)
                    ·
                      refine ⟨2074733988911181641492947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766311985214908855323929 2074733988911181641492947)
                      ·
                        rfl

theorem cell23_4040530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_4040530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040530 prefixEnd_4040530 := by exact prefixLift 4040530
  have htrace : WordTrace (prefixWord ++ tailWord_4040530) baseStart_4040530 baseEnd_4040530 := by
    simpa [prefixWord, tailWord_4040530, baseEnd_4040530] using wordTrace_append hprefix tailTrace_4040530
  have hstable : (prefixWord ++ tailWord_4040530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040530).length < 2 ^ (prefixWord ++ tailWord_4040530).sum := by decide
  have hdescent : baseEnd_4040530 < baseStart_4040530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040547 : List Nat := [1, 1, 1, 5, 4, 1, 1, 3, 2, 2, 2]
def baseStart_4040547 : Nat := 118140960795 + 4040547 * 2 ^ 59
def prefixEnd_4040547 : Nat := 4983230072969 + 3 ^ 40 * 4040547 * 2
def baseEnd_4040547 : Nat := 2074742718082308074980369

theorem tailTrace_4040547 : CollatzResearch.WordTrace tailWord_4040547 prefixEnd_4040547 2074742718082308074980369 := by
  unfold tailWord_4040547
  simp only [CollatzResearch.WordTrace]
  refine ⟨147370856092795764333391895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98247237395197176222261263 147370856092795764333391895)
  ·
    refine ⟨221056284139193646500087843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147370856092795764333391895 221056284139193646500087843)
    ·
      refine ⟨331584426208790469750131765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221056284139193646500087843 331584426208790469750131765)
      ·
        refine ⟨31086039957074106539074853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 331584426208790469750131765 31086039957074106539074853)
        ·
          refine ⟨5828632491951394976076535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31086039957074106539074853 5828632491951394976076535)
          ·
            refine ⟨8742948737927092464114803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5828632491951394976076535 8742948737927092464114803)
            ·
              refine ⟨13114423106890638696172205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8742948737927092464114803 13114423106890638696172205)
              ·
                refine ⟨4917908665083989511064577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13114423106890638696172205 4917908665083989511064577)
                ·
                  refine ⟨3688431498812992133298433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4917908665083989511064577 3688431498812992133298433)
                  ·
                    refine ⟨2766323624109744099973825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3688431498812992133298433 2766323624109744099973825)
                    ·
                      refine ⟨2074742718082308074980369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766323624109744099973825 2074742718082308074980369)
                      ·
                        rfl

theorem cell23_4040547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_4040547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040547 prefixEnd_4040547 := by exact prefixLift 4040547
  have htrace : WordTrace (prefixWord ++ tailWord_4040547) baseStart_4040547 baseEnd_4040547 := by
    simpa [prefixWord, tailWord_4040547, baseEnd_4040547] using wordTrace_append hprefix tailTrace_4040547
  have hstable : (prefixWord ++ tailWord_4040547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040547).length < 2 ^ (prefixWord ++ tailWord_4040547).sum := by decide
  have hdescent : baseEnd_4040547 < baseStart_4040547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040656 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 5, 5]
def baseStart_4040656 : Nat := 118140960795 + 4040656 * 2 ^ 59
def prefixEnd_4040656 : Nat := 4983230072969 + 3 ^ 40 * 4040656 * 2
def baseEnd_4040656 : Nat := 691599562491216049505789

theorem tailTrace_4040656 : CollatzResearch.WordTrace tailWord_4040656 prefixEnd_4040656 691599562491216049505789 := by
  unfold tailWord_4040656
  simp only [CollatzResearch.WordTrace]
  refine ⟨73687415824700437974554911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98249887766267250632739881 73687415824700437974554911)
  ·
    refine ⟨110531123737050656961832367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73687415824700437974554911 110531123737050656961832367)
    ·
      refine ⟨165796685605575985442748551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110531123737050656961832367 165796685605575985442748551)
      ·
        refine ⟨248695028408363978164122827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165796685605575985442748551 248695028408363978164122827)
        ·
          refine ⟨373042542612545967246184241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248695028408363978164122827 373042542612545967246184241)
          ·
            refine ⟨279781906959409475434638181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373042542612545967246184241 279781906959409475434638181)
            ·
              refine ⟨52459107554889276643994659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279781906959409475434638181 52459107554889276643994659)
              ·
                refine ⟨78688661332333914965991989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52459107554889276643994659 78688661332333914965991989)
                ·
                  refine ⟨7377061999906304528061749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78688661332333914965991989 7377061999906304528061749)
                  ·
                    refine ⟨691599562491216049505789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7377061999906304528061749 691599562491216049505789)
                    ·
                      rfl

theorem cell23_4040656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 5, 5].length) (baseStart_4040656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040656 prefixEnd_4040656 := by exact prefixLift 4040656
  have htrace : WordTrace (prefixWord ++ tailWord_4040656) baseStart_4040656 baseEnd_4040656 := by
    simpa [prefixWord, tailWord_4040656, baseEnd_4040656] using wordTrace_append hprefix tailTrace_4040656
  have hstable : (prefixWord ++ tailWord_4040656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040656).length < 2 ^ (prefixWord ++ tailWord_4040656).sum := by decide
  have hdescent : baseEnd_4040656 < baseStart_4040656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040660 : List Nat := [2, 4, 1, 2, 1, 1, 5, 1, 6]
def baseStart_4040660 : Nat := 118140960795 + 4040660 * 2 ^ 59
def prefixEnd_4040660 : Nat := 4983230072969 + 3 ^ 40 * 4040660 * 2
def baseEnd_4040660 : Nat := 230533415710696236985261

theorem tailTrace_4040660 : CollatzResearch.WordTrace tailWord_4040660 prefixEnd_4040660 230533415710696236985261 := by
  unfold tailWord_4040660
  simp only [CollatzResearch.WordTrace]
  refine ⟨73687488770693192316127717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98249985027590923088170289 73687488770693192316127717)
  ·
    refine ⟨13816404144504973559273947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73687488770693192316127717 13816404144504973559273947)
    ·
      refine ⟨20724606216757460338910921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13816404144504973559273947 20724606216757460338910921)
      ·
        refine ⟨15543454662568095254183191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20724606216757460338910921 15543454662568095254183191)
        ·
          refine ⟨23315181993852142881274787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15543454662568095254183191 23315181993852142881274787)
          ·
            refine ⟨34972772990778214321912181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23315181993852142881274787 34972772990778214321912181)
            ·
              refine ⟨3278697467885457592679267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34972772990778214321912181 3278697467885457592679267)
              ·
                refine ⟨4918046201828186389018901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3278697467885457592679267 4918046201828186389018901)
                ·
                  refine ⟨230533415710696236985261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4918046201828186389018901 230533415710696236985261)
                  ·
                    rfl

theorem cell23_4040660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_4040660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040660 prefixEnd_4040660 := by exact prefixLift 4040660
  have htrace : WordTrace (prefixWord ++ tailWord_4040660) baseStart_4040660 baseEnd_4040660 := by
    simpa [prefixWord, tailWord_4040660, baseEnd_4040660] using wordTrace_append hprefix tailTrace_4040660
  have hstable : (prefixWord ++ tailWord_4040660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040660).length < 2 ^ (prefixWord ++ tailWord_4040660).sum := by decide
  have hdescent : baseEnd_4040660 < baseStart_4040660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040663 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 3, 5, 2]
def baseStart_4040663 : Nat := 118140960795 + 4040663 * 2 ^ 59
def prefixEnd_4040663 : Nat := 4983230072969 + 3 ^ 40 * 4040663 * 2
def baseEnd_4040663 : Nat := 2074802281838229621129835

theorem tailTrace_4040663 : CollatzResearch.WordTrace tailWord_4040663 prefixEnd_4040663 2074802281838229621129835 := by
  unfold tailWord_4040663
  simp only [CollatzResearch.WordTrace]
  refine ⟨147375086960375516144614643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98250057973583677429743095 147375086960375516144614643)
  ·
    refine ⟨221062630440563274216921965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147375086960375516144614643 221062630440563274216921965)
    ·
      refine ⟨82898486415211227831345737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221062630440563274216921965 82898486415211227831345737)
      ·
        refine ⟨62173864811408420873509303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82898486415211227831345737 62173864811408420873509303)
        ·
          refine ⟨93260797217112631310263955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62173864811408420873509303 93260797217112631310263955)
          ·
            refine ⟨139891195825668946965395933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93260797217112631310263955 139891195825668946965395933)
            ·
              refine ⟨52459198434625855112023475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139891195825668946965395933 52459198434625855112023475)
              ·
                refine ⟨78688797651938782668035213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52459198434625855112023475 78688797651938782668035213)
                ·
                  refine ⟨29508299119477043500513205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78688797651938782668035213 29508299119477043500513205)
                  ·
                    refine ⟨2766403042450972828173113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29508299119477043500513205 2766403042450972828173113)
                    ·
                      refine ⟨2074802281838229621129835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766403042450972828173113 2074802281838229621129835)
                      ·
                        rfl

theorem cell23_4040663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_4040663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040663 prefixEnd_4040663 := by exact prefixLift 4040663
  have htrace : WordTrace (prefixWord ++ tailWord_4040663) baseStart_4040663 baseEnd_4040663 := by
    simpa [prefixWord, tailWord_4040663, baseEnd_4040663] using wordTrace_append hprefix tailTrace_4040663
  have hstable : (prefixWord ++ tailWord_4040663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040663).length < 2 ^ (prefixWord ++ tailWord_4040663).sum := by decide
  have hdescent : baseEnd_4040663 < baseStart_4040663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040673 : List Nat := [1, 2, 3, 1, 2, 1, 3, 4, 1, 5]
def baseStart_4040673 : Nat := 118140960795 + 4040673 * 2 ^ 59
def prefixEnd_4040673 : Nat := 4983230072969 + 3 ^ 40 * 4040673 * 2
def baseEnd_4040673 : Nat := 691602472214924860668263

theorem tailTrace_4040673 : CollatzResearch.WordTrace tailWord_4040673 prefixEnd_4040673 691602472214924860668263 := by
  unfold tailWord_4040673
  simp only [CollatzResearch.WordTrace]
  refine ⟨147375451690339287852478673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98250301126892858568319115 147375451690339287852478673)
  ·
    refine ⟨110531588767754465889359005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147375451690339287852478673 110531588767754465889359005)
    ·
      refine ⟨41449345787907924708509627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110531588767754465889359005 41449345787907924708509627)
      ·
        refine ⟨62174018681861887062764441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41449345787907924708509627 62174018681861887062764441)
        ·
          refine ⟨46630514011396415297073331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62174018681861887062764441 46630514011396415297073331)
          ·
            refine ⟨69945771017094622945609997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46630514011396415297073331 69945771017094622945609997)
            ·
              refine ⟨26229664131410483604603749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69945771017094622945609997 26229664131410483604603749)
              ·
                refine ⟨4918062024639465675863203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26229664131410483604603749 4918062024639465675863203)
                ·
                  refine ⟨7377093036959198513794805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4918062024639465675863203 7377093036959198513794805)
                  ·
                    refine ⟨691602472214924860668263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7377093036959198513794805 691602472214924860668263)
                    ·
                      rfl

theorem cell23_4040673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_4040673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040673 prefixEnd_4040673 := by exact prefixLift 4040673
  have htrace : WordTrace (prefixWord ++ tailWord_4040673) baseStart_4040673 baseEnd_4040673 := by
    simpa [prefixWord, tailWord_4040673, baseEnd_4040673] using wordTrace_append hprefix tailTrace_4040673
  have hstable : (prefixWord ++ tailWord_4040673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040673).length < 2 ^ (prefixWord ++ tailWord_4040673).sum := by decide
  have hdescent : baseEnd_4040673 < baseStart_4040673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040680 : List Nat := [2, 1, 4, 1, 1, 1, 1, 5, 2, 3, 2]
def baseStart_4040680 : Nat := 118140960795 + 4040680 * 2 ^ 59
def prefixEnd_4040680 : Nat := 4983230072969 + 3 ^ 40 * 4040680 * 2
def baseEnd_4040680 : Nat := 2074811011009356054617257

theorem tailTrace_4040680 : CollatzResearch.WordTrace tailWord_4040680 prefixEnd_4040680 2074811011009356054617257 := by
  unfold tailWord_4040680
  simp only [CollatzResearch.WordTrace]
  refine ⟨73687853500656964023991747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98250471334209285365322329 73687853500656964023991747)
  ·
    refine ⟨110531780250985446035987621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73687853500656964023991747 110531780250985446035987621)
    ·
      refine ⟨20724708797059771131747679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110531780250985446035987621 20724708797059771131747679)
      ·
        refine ⟨31087063195589656697621519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20724708797059771131747679 31087063195589656697621519)
        ·
          refine ⟨46630594793384485046432279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31087063195589656697621519 46630594793384485046432279)
          ·
            refine ⟨69945892190076727569648419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46630594793384485046432279 69945892190076727569648419)
            ·
              refine ⟨104918838285115091354472629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69945892190076727569648419 104918838285115091354472629)
              ·
                refine ⟨9836141089229539814481809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104918838285115091354472629 9836141089229539814481809)
                ·
                  refine ⟨7377105816922154860861357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9836141089229539814481809 7377105816922154860861357)
                  ·
                    refine ⟨2766414681345808072823009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7377105816922154860861357 2766414681345808072823009)
                    ·
                      refine ⟨2074811011009356054617257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766414681345808072823009 2074811011009356054617257)
                      ·
                        rfl

theorem cell23_4040680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_4040680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040680 prefixEnd_4040680 := by exact prefixLift 4040680
  have htrace : WordTrace (prefixWord ++ tailWord_4040680) baseStart_4040680 baseEnd_4040680 := by
    simpa [prefixWord, tailWord_4040680, baseEnd_4040680] using wordTrace_append hprefix tailTrace_4040680
  have hstable : (prefixWord ++ tailWord_4040680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040680).length < 2 ^ (prefixWord ++ tailWord_4040680).sum := by decide
  have hdescent : baseEnd_4040680 < baseStart_4040680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040730 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3]
def baseStart_4040730 : Nat := 118140960795 + 4040730 * 2 ^ 59
def prefixEnd_4040730 : Nat := 4983230072969 + 3 ^ 40 * 4040730 * 2
def baseEnd_4040730 : Nat := 2074836685042080858992027

theorem tailTrace_4040730 : CollatzResearch.WordTrace tailWord_4040730 prefixEnd_4040730 2074836685042080858992027 := by
  unfold tailWord_4040730
  simp only [CollatzResearch.WordTrace]
  refine ⟨36844382662783196646825911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98251687100755191058202429 36844382662783196646825911)
  ·
    refine ⟨55266573994174794970238867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36844382662783196646825911 55266573994174794970238867)
    ·
      refine ⟨82899860991262192455358301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55266573994174794970238867 82899860991262192455358301)
      ·
        refine ⟨31087447871723322170759363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82899860991262192455358301 31087447871723322170759363)
        ·
          refine ⟨46631171807584983256139045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31087447871723322170759363 46631171807584983256139045)
          ·
            refine ⟨8743344713922184360526071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46631171807584983256139045 8743344713922184360526071)
            ·
              refine ⟨13115017070883276540789107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8743344713922184360526071 13115017070883276540789107)
              ·
                refine ⟨19672525606324914811183661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13115017070883276540789107 19672525606324914811183661)
                ·
                  refine ⟨7377197102371843054193873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19672525606324914811183661 7377197102371843054193873)
                  ·
                    refine ⟨5532897826778882290645405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7377197102371843054193873 5532897826778882290645405)
                    ·
                      refine ⟨2074836685042080858992027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5532897826778882290645405 2074836685042080858992027)
                      ·
                        rfl

theorem cell23_4040730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_4040730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040730 prefixEnd_4040730 := by exact prefixLift 4040730
  have htrace : WordTrace (prefixWord ++ tailWord_4040730) baseStart_4040730 baseEnd_4040730 := by
    simpa [prefixWord, tailWord_4040730, baseEnd_4040730] using wordTrace_append hprefix tailTrace_4040730
  have hstable : (prefixWord ++ tailWord_4040730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040730).length < 2 ^ (prefixWord ++ tailWord_4040730).sum := by decide
  have hdescent : baseEnd_4040730 < baseStart_4040730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040733 : List Nat := [1, 4, 2, 2, 2, 1, 2, 9]
def baseStart_4040733 : Nat := 118140960795 + 4040733 * 2 ^ 59
def prefixEnd_4040733 : Nat := 4983230072969 + 3 ^ 40 * 4040733 * 2
def baseEnd_4040733 : Nat := 76845860203112753602019

theorem tailTrace_4040733 : CollatzResearch.WordTrace tailWord_4040733 prefixEnd_4040733 76845860203112753602019 := by
  unfold tailWord_4040733
  simp only [CollatzResearch.WordTrace]
  refine ⟨147377640070121918099662853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98251760046747945399775235 147377640070121918099662853)
  ·
    refine ⟨27633307513147859643686785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147377640070121918099662853 27633307513147859643686785)
    ·
      refine ⟨20724980634860894732765089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27633307513147859643686785 20724980634860894732765089)
      ·
        refine ⟨15543735476145671049573817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20724980634860894732765089 15543735476145671049573817)
        ·
          refine ⟨11657801607109253287180363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15543735476145671049573817 11657801607109253287180363)
          ·
            refine ⟨17486702410663879930770545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11657801607109253287180363 17486702410663879930770545)
            ·
              refine ⟨13115026807997909948077909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17486702410663879930770545 13115026807997909948077909)
              ·
                refine ⟨76845860203112753602019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13115026807997909948077909 76845860203112753602019)
                ·
                  rfl

theorem cell23_4040733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 9].length) (baseStart_4040733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040733 prefixEnd_4040733 := by exact prefixLift 4040733
  have htrace : WordTrace (prefixWord ++ tailWord_4040733) baseStart_4040733 baseEnd_4040733 := by
    simpa [prefixWord, tailWord_4040733, baseEnd_4040733] using wordTrace_append hprefix tailTrace_4040733
  have hstable : (prefixWord ++ tailWord_4040733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040733).length < 2 ^ (prefixWord ++ tailWord_4040733).sum := by decide
  have hdescent : baseEnd_4040733 < baseStart_4040733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040761 : List Nat := [1, 2, 1, 5, 3, 1, 1, 4, 1, 2, 2]
def baseStart_4040761 : Nat := 118140960795 + 4040761 * 2 ^ 59
def prefixEnd_4040761 : Nat := 4983230072969 + 3 ^ 40 * 4040761 * 2
def baseEnd_4040761 : Nat := 2074852602942370237704385

theorem tailTrace_4040761 : CollatzResearch.WordTrace tailWord_4040761 prefixEnd_4040761 2074852602942370237704385 := by
  unfold tailWord_4040761
  simp only [CollatzResearch.WordTrace]
  refine ⟨147378661314020478881682137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98252440876013652587788091 147378661314020478881682137)
  ·
    refine ⟨110533995985515359161261603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147378661314020478881682137 110533995985515359161261603)
    ·
      refine ⟨165800993978273038741892405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110533995985515359161261603 165800993978273038741892405)
      ·
        refine ⟨15543843185463097382052413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165800993978273038741892405 15543843185463097382052413)
        ·
          refine ⟨5828941194548661518269655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15543843185463097382052413 5828941194548661518269655)
          ·
            refine ⟨8743411791822992277404483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5828941194548661518269655 8743411791822992277404483)
            ·
              refine ⟨13115117687734488416106725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8743411791822992277404483 13115117687734488416106725)
              ·
                refine ⟨2459084566450216578020011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13115117687734488416106725 2459084566450216578020011)
                ·
                  refine ⟨3688626849675324867030017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2459084566450216578020011 3688626849675324867030017)
                  ·
                    refine ⟨2766470137256493650272513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3688626849675324867030017 2766470137256493650272513)
                    ·
                      refine ⟨2074852602942370237704385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766470137256493650272513 2074852602942370237704385)
                      ·
                        rfl

theorem cell23_4040761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_4040761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040761 prefixEnd_4040761 := by exact prefixLift 4040761
  have htrace : WordTrace (prefixWord ++ tailWord_4040761) baseStart_4040761 baseEnd_4040761 := by
    simpa [prefixWord, tailWord_4040761, baseEnd_4040761] using wordTrace_append hprefix tailTrace_4040761
  have hstable : (prefixWord ++ tailWord_4040761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040761).length < 2 ^ (prefixWord ++ tailWord_4040761).sum := by decide
  have hdescent : baseEnd_4040761 < baseStart_4040761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040803 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 5]
def baseStart_4040803 : Nat := 118140960795 + 4040803 * 2 ^ 59
def prefixEnd_4040803 : Nat := 4983230072969 + 3 ^ 40 * 4040803 * 2
def baseEnd_4040803 : Nat := 2074874169129859073379191

theorem tailTrace_4040803 : CollatzResearch.WordTrace tailWord_4040803 prefixEnd_4040803 2074874169129859073379191 := by
  unfold tailWord_4040803
  simp only [CollatzResearch.WordTrace]
  refine ⟨147380193179868320054711063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98253462119912213369807375 147380193179868320054711063)
  ·
    refine ⟨221070289769802480082066595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147380193179868320054711063 221070289769802480082066595)
    ·
      refine ⟨331605434654703720123099893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221070289769802480082066595 331605434654703720123099893)
      ·
        refine ⟨31088009498878473761540615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 331605434654703720123099893 31088009498878473761540615)
        ·
          refine ⟨46632014248317710642310923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31088009498878473761540615 46632014248317710642310923)
          ·
            refine ⟨69948021372476565963466385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46632014248317710642310923 69948021372476565963466385)
            ·
              refine ⟨52461016029357424472599789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69948021372476565963466385 52461016029357424472599789)
              ·
                refine ⟨19672881011009034177224921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52461016029357424472599789 19672881011009034177224921)
                ·
                  refine ⟨14754660758256775632918691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19672881011009034177224921 14754660758256775632918691)
                  ·
                    refine ⟨22131991137385163449378037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14754660758256775632918691 22131991137385163449378037)
                    ·
                      refine ⟨2074874169129859073379191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22131991137385163449378037 2074874169129859073379191)
                      ·
                        rfl

theorem cell23_4040803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_4040803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040803 prefixEnd_4040803 := by exact prefixLift 4040803
  have htrace : WordTrace (prefixWord ++ tailWord_4040803) baseStart_4040803 baseEnd_4040803 := by
    simpa [prefixWord, tailWord_4040803, baseEnd_4040803] using wordTrace_append hprefix tailTrace_4040803
  have hstable : (prefixWord ++ tailWord_4040803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040803).length < 2 ^ (prefixWord ++ tailWord_4040803).sum := by decide
  have hdescent : baseEnd_4040803 < baseStart_4040803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040804 : List Nat := [2, 3, 1, 1, 2, 1, 6, 1, 1, 3, 2]
def baseStart_4040804 : Nat := 118140960795 + 4040804 * 2 ^ 59
def prefixEnd_4040804 : Nat := 4983230072969 + 3 ^ 40 * 4040804 * 2
def baseEnd_4040804 : Nat := 2074874682610513569466687

theorem tailTrace_4040804 : CollatzResearch.WordTrace tailWord_4040804 prefixEnd_4040804 2074874682610513569466687 := by
  unfold tailWord_4040804
  simp only [CollatzResearch.WordTrace]
  refine ⟨73690114826432348612748733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98253486435243131483664977 73690114826432348612748733)
  ·
    refine ⟨27633793059912130729780775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73690114826432348612748733 27633793059912130729780775)
    ·
      refine ⟨41450689589868196094671163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27633793059912130729780775 41450689589868196094671163)
      ·
        refine ⟨62176034384802294142006745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41450689589868196094671163 62176034384802294142006745)
        ·
          refine ⟨46632025788601720606505059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62176034384802294142006745 46632025788601720606505059)
          ·
            refine ⟨69948038682902580909757589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46632025788601720606505059 69948038682902580909757589)
            ·
              refine ⟨3278814313261058480144887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69948038682902580909757589 3278814313261058480144887)
              ·
                refine ⟨4918221469891587720217331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3278814313261058480144887 4918221469891587720217331)
                ·
                  refine ⟨7377332204837381580325997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4918221469891587720217331 7377332204837381580325997)
                  ·
                    refine ⟨2766499576814018092622249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7377332204837381580325997 2766499576814018092622249)
                    ·
                      refine ⟨2074874682610513569466687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766499576814018092622249 2074874682610513569466687)
                      ·
                        rfl

theorem cell23_4040804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_4040804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040804 prefixEnd_4040804 := by exact prefixLift 4040804
  have htrace : WordTrace (prefixWord ++ tailWord_4040804) baseStart_4040804 baseEnd_4040804 := by
    simpa [prefixWord, tailWord_4040804, baseEnd_4040804] using wordTrace_append hprefix tailTrace_4040804
  have hstable : (prefixWord ++ tailWord_4040804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040804).length < 2 ^ (prefixWord ++ tailWord_4040804).sum := by decide
  have hdescent : baseEnd_4040804 < baseStart_4040804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040817 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 4, 2, 2]
def baseStart_4040817 : Nat := 118140960795 + 4040817 * 2 ^ 59
def prefixEnd_4040817 : Nat := 4983230072969 + 3 ^ 40 * 4040817 * 2
def baseEnd_4040817 : Nat := 2074881357859022018604127

theorem tailTrace_4040817 : CollatzResearch.WordTrace tailWord_4040817 prefixEnd_4040817 2074881357859022018604127 := by
  unfold tailWord_4040817
  simp only [CollatzResearch.WordTrace]
  refine ⟨147380703801817600445720705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98253802534545066963813803 147380703801817600445720705)
  ·
    refine ⟨110535527851363200334290529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147380703801817600445720705 110535527851363200334290529)
    ·
      refine ⟨82901645888522400250717897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110535527851363200334290529 82901645888522400250717897)
      ·
        refine ⟨62176234416391800188038423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82901645888522400250717897 62176234416391800188038423)
        ·
          refine ⟨93264351624587700282057635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62176234416391800188038423 93264351624587700282057635)
          ·
            refine ⟨139896527436881550423086453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93264351624587700282057635 139896527436881550423086453)
            ·
              refine ⟨13115299447207645352164355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139896527436881550423086453 13115299447207645352164355)
              ·
                refine ⟨19672949170811468028246533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13115299447207645352164355 19672949170811468028246533)
                ·
                  refine ⟨3688677969527150255296225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19672949170811468028246533 3688677969527150255296225)
                  ·
                    refine ⟨2766508477145362691472169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3688677969527150255296225 2766508477145362691472169)
                    ·
                      refine ⟨2074881357859022018604127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766508477145362691472169 2074881357859022018604127)
                      ·
                        rfl

theorem cell23_4040817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_4040817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040817 prefixEnd_4040817 := by exact prefixLift 4040817
  have htrace : WordTrace (prefixWord ++ tailWord_4040817) baseStart_4040817 baseEnd_4040817 := by
    simpa [prefixWord, tailWord_4040817, baseEnd_4040817] using wordTrace_append hprefix tailTrace_4040817
  have hstable : (prefixWord ++ tailWord_4040817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040817).length < 2 ^ (prefixWord ++ tailWord_4040817).sum := by decide
  have hdescent : baseEnd_4040817 < baseStart_4040817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040823 : List Nat := [1, 1, 3, 1, 1, 5, 1, 3, 7]
def baseStart_4040823 : Nat := 118140960795 + 4040823 * 2 ^ 59
def prefixEnd_4040823 : Nat := 4983230072969 + 3 ^ 40 * 4040823 * 2
def baseEnd_4040823 : Nat := 230542715415883221681011

theorem tailTrace_4040823 : CollatzResearch.WordTrace tailWord_4040823 prefixEnd_4040823 230542715415883221681011 := by
  unfold tailWord_4040823
  simp only [CollatzResearch.WordTrace]
  refine ⟨147380922639795863470439123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98253948426530575646959415 147380922639795863470439123)
  ·
    refine ⟨221071383959693795205658685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147380922639795863470439123 221071383959693795205658685)
    ·
      refine ⟨82901768984885173202122007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221071383959693795205658685 82901768984885173202122007)
      ·
        refine ⟨124352653477327759803183011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82901768984885173202122007 124352653477327759803183011)
        ·
          refine ⟨186528980215991639704774517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124352653477327759803183011 186528980215991639704774517)
          ·
            refine ⟨17487091895249216222322611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186528980215991639704774517 17487091895249216222322611)
            ·
              refine ⟨26230637842873824333483917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17487091895249216222322611 26230637842873824333483917)
              ·
                refine ⟨9836489191077684125056469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26230637842873824333483917 9836489191077684125056469)
                ·
                  refine ⟨230542715415883221681011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9836489191077684125056469 230542715415883221681011)
                  ·
                    rfl

theorem cell23_4040823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 7].length) (baseStart_4040823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040823 prefixEnd_4040823 := by exact prefixLift 4040823
  have htrace : WordTrace (prefixWord ++ tailWord_4040823) baseStart_4040823 baseEnd_4040823 := by
    simpa [prefixWord, tailWord_4040823, baseEnd_4040823] using wordTrace_append hprefix tailTrace_4040823
  have hstable : (prefixWord ++ tailWord_4040823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040823).length < 2 ^ (prefixWord ++ tailWord_4040823).sum := by decide
  have hdescent : baseEnd_4040823 < baseStart_4040823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040840 : List Nat := [2, 1, 3, 4, 1, 1, 2, 2, 7]
def baseStart_4040840 : Nat := 118140960795 + 4040840 * 2 ^ 59
def prefixEnd_4040840 : Nat := 4983230072969 + 3 ^ 40 * 4040840 * 2
def baseEnd_4040840 : Nat := 230543685323786158735169

theorem tailTrace_4040840 : CollatzResearch.WordTrace tailWord_4040840 prefixEnd_4040840 230543685323786158735169 := by
  unfold tailWord_4040840
  simp only [CollatzResearch.WordTrace]
  refine ⟨73690771340367137686903987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98254361787156183582538649 73690771340367137686903987)
  ·
    refine ⟨110536157010550706530355981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73690771340367137686903987 110536157010550706530355981)
    ·
      refine ⟨41451058878956514948883493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110536157010550706530355981 41451058878956514948883493)
      ·
        refine ⟨7772073539804346552915655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41451058878956514948883493 7772073539804346552915655)
        ·
          refine ⟨11658110309706519829373483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7772073539804346552915655 11658110309706519829373483)
          ·
            refine ⟨17487165464559779744060225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11658110309706519829373483 17487165464559779744060225)
            ·
              refine ⟨13115374098419834808045169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17487165464559779744060225 13115374098419834808045169)
              ·
                refine ⟨9836530573814876106033877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13115374098419834808045169 9836530573814876106033877)
                ·
                  refine ⟨230543685323786158735169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9836530573814876106033877 230543685323786158735169)
                  ·
                    rfl

theorem cell23_4040840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 7].length) (baseStart_4040840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040840 prefixEnd_4040840 := by exact prefixLift 4040840
  have htrace : WordTrace (prefixWord ++ tailWord_4040840) baseStart_4040840 baseEnd_4040840 := by
    simpa [prefixWord, tailWord_4040840, baseEnd_4040840] using wordTrace_append hprefix tailTrace_4040840
  have hstable : (prefixWord ++ tailWord_4040840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040840).length < 2 ^ (prefixWord ++ tailWord_4040840).sum := by decide
  have hdescent : baseEnd_4040840 < baseStart_4040840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040853 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 1, 7]
def baseStart_4040853 : Nat := 118140960795 + 4040853 * 2 ^ 59
def prefixEnd_4040853 : Nat := 4983230072969 + 3 ^ 40 * 4040853 * 2
def baseEnd_4040853 : Nat := 691633281054194625917987

theorem tailTrace_4040853 : CollatzResearch.WordTrace tailWord_4040853 prefixEnd_4040853 691633281054194625917987 := by
  unfold tailWord_4040853
  simp only [CollatzResearch.WordTrace]
  refine ⟨147382016829687178594031213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98254677886458119062687475 147382016829687178594031213)
  ·
    refine ⟨55268256311132691972761705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147382016829687178594031213 55268256311132691972761705)
    ·
      refine ⟨41451192233349518979571279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55268256311132691972761705 41451192233349518979571279)
      ·
        refine ⟨62176788350024278469356919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41451192233349518979571279 62176788350024278469356919)
        ·
          refine ⟨93265182525036417704035379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62176788350024278469356919 93265182525036417704035379)
          ·
            refine ⟨139897773787554626556053069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93265182525036417704035379 139897773787554626556053069)
            ·
              refine ⟨52461665170332984958519901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139897773787554626556053069 52461665170332984958519901)
              ·
                refine ⟨19673124438874869359444963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52461665170332984958519901 19673124438874869359444963)
                ·
                  refine ⟨29509686658312304039167445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19673124438874869359444963 29509686658312304039167445)
                  ·
                    refine ⟨691633281054194625917987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29509686658312304039167445 691633281054194625917987)
                    ·
                      rfl

theorem cell23_4040853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_4040853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040853 prefixEnd_4040853 := by exact prefixLift 4040853
  have htrace : WordTrace (prefixWord ++ tailWord_4040853) baseStart_4040853 baseEnd_4040853 := by
    simpa [prefixWord, tailWord_4040853, baseEnd_4040853] using wordTrace_append hprefix tailTrace_4040853
  have hstable : (prefixWord ++ tailWord_4040853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040853).length < 2 ^ (prefixWord ++ tailWord_4040853).sum := by decide
  have hdescent : baseEnd_4040853 < baseStart_4040853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040874 : List Nat := [3, 1, 5, 1, 2, 2, 1, 1, 7]
def baseStart_4040874 : Nat := 118140960795 + 4040874 * 2 ^ 59
def prefixEnd_4040874 : Nat := 4983230072969 + 3 ^ 40 * 4040874 * 2
def baseEnd_4040874 : Nat := 230545625139592032843485

theorem tailTrace_4040874 : CollatzResearch.WordTrace tailWord_4040874 prefixEnd_4040874 230545625139592032843485 := by
  unfold tailWord_4040874
  simp only [CollatzResearch.WordTrace]
  refine ⟨36845695690652774795136419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98255188508407399453697117 36845695690652774795136419)
  ·
    refine ⟨55268543535979162192704629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36845695690652774795136419 55268543535979162192704629)
    ·
      refine ⟨5181425956498046455566059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55268543535979162192704629 5181425956498046455566059)
      ·
        refine ⟨7772138934747069683349089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5181425956498046455566059 7772138934747069683349089)
        ·
          refine ⟨5829104201060302262511817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7772138934747069683349089 5829104201060302262511817)
          ·
            refine ⟨4371828150795226696883863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5829104201060302262511817 4371828150795226696883863)
            ·
              refine ⟨6557742226192840045325795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4371828150795226696883863 6557742226192840045325795)
              ·
                refine ⟨9836613339289260067988693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6557742226192840045325795 9836613339289260067988693)
                ·
                  refine ⟨230545625139592032843485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9836613339289260067988693 230545625139592032843485)
                  ·
                    rfl

theorem cell23_4040874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 7].length) (baseStart_4040874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040874 prefixEnd_4040874 := by exact prefixLift 4040874
  have htrace : WordTrace (prefixWord ++ tailWord_4040874) baseStart_4040874 baseEnd_4040874 := by
    simpa [prefixWord, tailWord_4040874, baseEnd_4040874] using wordTrace_append hprefix tailTrace_4040874
  have hstable : (prefixWord ++ tailWord_4040874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040874).length < 2 ^ (prefixWord ++ tailWord_4040874).sum := by decide
  have hdescent : baseEnd_4040874 < baseStart_4040874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040885 : List Nat := [1, 3, 3, 4, 1, 2, 2, 1, 2, 2, 2]
def baseStart_4040885 : Nat := 118140960795 + 4040885 * 2 ^ 59
def prefixEnd_4040885 : Nat := 4983230072969 + 3 ^ 40 * 4040885 * 2
def baseEnd_4040885 : Nat := 2074916274543527752553815

theorem tailTrace_4040885 : CollatzResearch.WordTrace tailWord_4040885 prefixEnd_4040885 2074916274543527752553815 := by
  unfold tailWord_4040885
  simp only [CollatzResearch.WordTrace]
  refine ⟨147383183965571248059196109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98255455977047498706130739 147383183965571248059196109)
  ·
    refine ⟨55268693987089218022198541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147383183965571248059196109 55268693987089218022198541)
    ·
      refine ⟨20725760245158456758324453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55268693987089218022198541 20725760245158456758324453)
      ·
        refine ⟨3886080045967210642185835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20725760245158456758324453 3886080045967210642185835)
        ·
          refine ⟨5829120068950815963278753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3886080045967210642185835 5829120068950815963278753)
          ·
            refine ⟨4371840051713111972459065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5829120068950815963278753 4371840051713111972459065)
            ·
              refine ⟨3278880038784833979344299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4371840051713111972459065 3278880038784833979344299)
              ·
                refine ⟨4918320058177250969016449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3278880038784833979344299 4918320058177250969016449)
                ·
                  refine ⟨3688740043632938226762337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4918320058177250969016449 3688740043632938226762337)
                  ·
                    refine ⟨2766555032724703670071753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3688740043632938226762337 2766555032724703670071753)
                    ·
                      refine ⟨2074916274543527752553815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766555032724703670071753 2074916274543527752553815)
                      ·
                        rfl

theorem cell23_4040885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_4040885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040885 prefixEnd_4040885 := by exact prefixLift 4040885
  have htrace : WordTrace (prefixWord ++ tailWord_4040885) baseStart_4040885 baseEnd_4040885 := by
    simpa [prefixWord, tailWord_4040885, baseEnd_4040885] using wordTrace_append hprefix tailTrace_4040885
  have hstable : (prefixWord ++ tailWord_4040885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040885).length < 2 ^ (prefixWord ++ tailWord_4040885).sum := by decide
  have hdescent : baseEnd_4040885 < baseStart_4040885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040903 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_4040903 : Nat := 118140960795 + 4040903 * 2 ^ 59
def prefixEnd_4040903 : Nat := 4983230072969 + 3 ^ 40 * 4040903 * 2
def baseEnd_4040903 : Nat := 2074925517195308682128731

theorem tailTrace_4040903 : CollatzResearch.WordTrace tailWord_4040903 prefixEnd_4040903 2074925517195308682128731 := by
  unfold tailWord_4040903
  simp only [CollatzResearch.WordTrace]
  refine ⟨147383840479506037133351363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98255893653004024755567575 147383840479506037133351363)
  ·
    refine ⟨221075760719259055700027045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147383840479506037133351363 221075760719259055700027045)
    ·
      refine ⟨41451705134861072943755071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221075760719259055700027045 41451705134861072943755071)
      ·
        refine ⟨62177557702291609415632607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41451705134861072943755071 62177557702291609415632607)
        ·
          refine ⟨93266336553437414123448911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62177557702291609415632607 93266336553437414123448911)
          ·
            refine ⟨139899504830156121185173367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93266336553437414123448911 139899504830156121185173367)
            ·
              refine ⟨209849257245234181777760051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139899504830156121185173367 209849257245234181777760051)
              ·
                refine ⟨314773885867851272666640077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209849257245234181777760051 314773885867851272666640077)
                ·
                  refine ⟨118040207200444227249990029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314773885867851272666640077 118040207200444227249990029)
                  ·
                    refine ⟨44265077700166585218746261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118040207200444227249990029 44265077700166585218746261)
                    ·
                      refine ⟨2074925517195308682128731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44265077700166585218746261 2074925517195308682128731)
                      ·
                        rfl

theorem cell23_4040903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_4040903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040903 prefixEnd_4040903 := by exact prefixLift 4040903
  have htrace : WordTrace (prefixWord ++ tailWord_4040903) baseStart_4040903 baseEnd_4040903 := by
    simpa [prefixWord, tailWord_4040903, baseEnd_4040903] using wordTrace_append hprefix tailTrace_4040903
  have hstable : (prefixWord ++ tailWord_4040903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040903).length < 2 ^ (prefixWord ++ tailWord_4040903).sum := by decide
  have hdescent : baseEnd_4040903 < baseStart_4040903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040913 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 10]
def baseStart_4040913 : Nat := 118140960795 + 4040913 * 2 ^ 59
def prefixEnd_4040913 : Nat := 4983230072969 + 3 ^ 40 * 4040913 * 2
def baseEnd_4040913 : Nat := 230547850222428182555965

theorem tailTrace_4040913 : CollatzResearch.WordTrace tailWord_4040913 prefixEnd_4040913 230547850222428182555965 := by
  unfold tailWord_4040913
  simp only [CollatzResearch.WordTrace]
  refine ⟨147384205209469808841215393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98256136806313205894143595 147384205209469808841215393)
  ·
    refine ⟨110538153907102356630911545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147384205209469808841215393 110538153907102356630911545)
    ·
      refine ⟨82903615430326767473183659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110538153907102356630911545 82903615430326767473183659)
      ·
        refine ⟨124355423145490151209775489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82903615430326767473183659 124355423145490151209775489)
        ·
          refine ⟨93266567359117613407331617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124355423145490151209775489 93266567359117613407331617)
          ·
            refine ⟨69949925519338210055498713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93266567359117613407331617 69949925519338210055498713)
            ·
              refine ⟨52462444139503657541624035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69949925519338210055498713 52462444139503657541624035)
              ·
                refine ⟨78693666209255486312436053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52462444139503657541624035 78693666209255486312436053)
                ·
                  refine ⟨230547850222428182555965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 78693666209255486312436053 230547850222428182555965)
                  ·
                    rfl

theorem cell23_4040913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 10].length) (baseStart_4040913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040913 prefixEnd_4040913 := by exact prefixLift 4040913
  have htrace : WordTrace (prefixWord ++ tailWord_4040913) baseStart_4040913 baseEnd_4040913 := by
    simpa [prefixWord, tailWord_4040913, baseEnd_4040913] using wordTrace_append hprefix tailTrace_4040913
  have hstable : (prefixWord ++ tailWord_4040913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040913).length < 2 ^ (prefixWord ++ tailWord_4040913).sum := by decide
  have hdescent : baseEnd_4040913 < baseStart_4040913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040960 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 3, 5]
def baseStart_4040960 : Nat := 118140960795 + 4040960 * 2 ^ 59
def prefixEnd_4040960 : Nat := 4983230072969 + 3 ^ 40 * 4040960 * 2
def baseEnd_4040960 : Nat := 691651595197538319705323

theorem tailTrace_4040960 : CollatzResearch.WordTrace tailWord_4040960 prefixEnd_4040960 691651595197538319705323 := by
  unfold tailWord_4040960
  simp only [CollatzResearch.WordTrace]
  refine ⟨73692959720149767934088167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98257279626866357245450889 73692959720149767934088167)
  ·
    refine ⟨110539439580224651901132251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73692959720149767934088167 110539439580224651901132251)
    ·
      refine ⟨165809159370336977851698377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110539439580224651901132251 165809159370336977851698377)
      ·
        refine ⟨124356869527752733388773783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165809159370336977851698377 124356869527752733388773783)
        ·
          refine ⟨186535304291629100083160675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124356869527752733388773783 186535304291629100083160675)
          ·
            refine ⟨279802956437443650124741013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186535304291629100083160675 279802956437443650124741013)
            ·
              refine ⟨13115763583005171099597235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 279802956437443650124741013 13115763583005171099597235)
              ·
                refine ⟨19673645374507756649395853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13115763583005171099597235 19673645374507756649395853)
                ·
                  refine ⟨7377617015440408743523445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19673645374507756649395853 7377617015440408743523445)
                  ·
                    refine ⟨691651595197538319705323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7377617015440408743523445 691651595197538319705323)
                    ·
                      rfl

theorem cell23_4040960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 3, 5].length) (baseStart_4040960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040960 prefixEnd_4040960 := by exact prefixLift 4040960
  have htrace : WordTrace (prefixWord ++ tailWord_4040960) baseStart_4040960 baseEnd_4040960 := by
    simpa [prefixWord, tailWord_4040960, baseEnd_4040960] using wordTrace_append hprefix tailTrace_4040960
  have hstable : (prefixWord ++ tailWord_4040960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040960).length < 2 ^ (prefixWord ++ tailWord_4040960).sum := by decide
  have hdescent : baseEnd_4040960 < baseStart_4040960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040977 : List Nat := [1, 2, 2, 1, 1, 6, 1, 3, 1, 5]
def baseStart_4040977 : Nat := 118140960795 + 4040977 * 2 ^ 59
def prefixEnd_4040977 : Nat := 4983230072969 + 3 ^ 40 * 4040977 * 2
def baseEnd_4040977 : Nat := 691654504921247130867797

theorem tailTrace_4040977 : CollatzResearch.WordTrace tailWord_4040977 prefixEnd_4040977 691654504921247130867797 := by
  unfold tailWord_4040977
  simp only [CollatzResearch.WordTrace]
  refine ⟨147386539481237947771545185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98257692987491965181030123 147386539481237947771545185)
  ·
    refine ⟨110539904610928460828658889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147386539481237947771545185 110539904610928460828658889)
    ·
      refine ⟨82904928458196345621494167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110539904610928460828658889 82904928458196345621494167)
      ·
        refine ⟨124357392687294518432241251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82904928458196345621494167 124357392687294518432241251)
        ·
          refine ⟨186536089030941777648361877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124357392687294518432241251 186536089030941777648361877)
          ·
            refine ⟨8743879173325395827266963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 186536089030941777648361877 8743879173325395827266963)
            ·
              refine ⟨13115818759988093740900445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8743879173325395827266963 13115818759988093740900445)
              ·
                refine ⟨4918432034995535152837667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13115818759988093740900445 4918432034995535152837667)
                ·
                  refine ⟨7377648052493302729256501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4918432034995535152837667 7377648052493302729256501)
                  ·
                    refine ⟨691654504921247130867797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7377648052493302729256501 691654504921247130867797)
                    ·
                      rfl

theorem cell23_4040977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_4040977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040977 prefixEnd_4040977 := by exact prefixLift 4040977
  have htrace : WordTrace (prefixWord ++ tailWord_4040977) baseStart_4040977 baseEnd_4040977 := by
    simpa [prefixWord, tailWord_4040977, baseEnd_4040977] using wordTrace_append hprefix tailTrace_4040977
  have hstable : (prefixWord ++ tailWord_4040977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040977).length < 2 ^ (prefixWord ++ tailWord_4040977).sum := by decide
  have hdescent : baseEnd_4040977 < baseStart_4040977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040991 : List Nat := [1, 1, 2, 4, 3, 1, 2, 4, 1, 1, 3]
def baseStart_4040991 : Nat := 118140960795 + 4040991 * 2 ^ 59
def prefixEnd_4040991 : Nat := 4983230072969 + 3 ^ 40 * 4040991 * 2
def baseEnd_4040991 : Nat := 2074970703492904337828327

theorem tailTrace_4040991 : CollatzResearch.WordTrace tailWord_4040991 prefixEnd_4040991 2074970703492904337828327 := by
  unfold tailWord_4040991
  simp only [CollatzResearch.WordTrace]
  refine ⟨147387050103187228162554827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98258033402124818775036551 147387050103187228162554827)
  ·
    refine ⟨221080575154780842243832241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147387050103187228162554827 221080575154780842243832241)
    ·
      refine ⟨165810431366085631682874181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221080575154780842243832241 165810431366085631682874181)
      ·
        refine ⟨31089455881141055940538909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165810431366085631682874181 31089455881141055940538909)
        ·
          refine ⟨11658545955427895977702091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31089455881141055940538909 11658545955427895977702091)
          ·
            refine ⟨17487818933141843966553137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11658545955427895977702091 17487818933141843966553137)
            ·
              refine ⟨13115864199856382974914853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17487818933141843966553137 13115864199856382974914853)
              ·
                refine ⟨2459224537473071807796535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13115864199856382974914853 2459224537473071807796535)
                ·
                  refine ⟨3688836806209607711694803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2459224537473071807796535 3688836806209607711694803)
                  ·
                    refine ⟨5533255209314411567542205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3688836806209607711694803 5533255209314411567542205)
                    ·
                      refine ⟨2074970703492904337828327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5533255209314411567542205 2074970703492904337828327)
                      ·
                        rfl

theorem cell23_4040991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_4040991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4040991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4040991 prefixEnd_4040991 := by exact prefixLift 4040991
  have htrace : WordTrace (prefixWord ++ tailWord_4040991) baseStart_4040991 baseEnd_4040991 := by
    simpa [prefixWord, tailWord_4040991, baseEnd_4040991] using wordTrace_append hprefix tailTrace_4040991
  have hstable : (prefixWord ++ tailWord_4040991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040991).length < 2 ^ (prefixWord ++ tailWord_4040991).sum := by decide
  have hdescent : baseEnd_4040991 < baseStart_4040991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041007 : List Nat := [1, 1, 2, 1, 2, 1, 4, 5, 2, 4]
def baseStart_4041007 : Nat := 118140960795 + 4041007 * 2 ^ 59
def prefixEnd_4041007 : Nat := 4983230072969 + 3 ^ 40 * 4041007 * 2
def baseEnd_4041007 : Nat := 691659639727792091742751

theorem tailTrace_4041007 : CollatzResearch.WordTrace tailWord_4041007 prefixEnd_4041007 691659639727792091742751 := by
  unfold tailWord_4041007
  simp only [CollatzResearch.WordTrace]
  refine ⟨147387633671129262895137275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98258422447419508596758183 147387633671129262895137275)
  ·
    refine ⟨221081450506693894342705913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147387633671129262895137275 221081450506693894342705913)
    ·
      refine ⟨165811087880020420757029435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221081450506693894342705913 165811087880020420757029435)
      ·
        refine ⟨248716631820030631135544153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165811087880020420757029435 248716631820030631135544153)
        ·
          refine ⟨186537473865022973351658115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248716631820030631135544153 186537473865022973351658115)
          ·
            refine ⟨279806210797534460027487173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186537473865022973351658115 279806210797534460027487173)
            ·
              refine ⟨52463664524537711255153845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279806210797534460027487173 52463664524537711255153845)
              ·
                refine ⟨4918468549175410430170673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52463664524537711255153845 4918468549175410430170673)
                ·
                  refine ⟨3688851411881557822628005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4918468549175410430170673 3688851411881557822628005)
                  ·
                    refine ⟨691659639727792091742751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3688851411881557822628005 691659639727792091742751)
                    ·
                      rfl

theorem cell23_4041007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 4].length) (baseStart_4041007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041007 prefixEnd_4041007 := by exact prefixLift 4041007
  have htrace : WordTrace (prefixWord ++ tailWord_4041007) baseStart_4041007 baseEnd_4041007 := by
    simpa [prefixWord, tailWord_4041007, baseEnd_4041007] using wordTrace_append hprefix tailTrace_4041007
  have hstable : (prefixWord ++ tailWord_4041007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041007).length < 2 ^ (prefixWord ++ tailWord_4041007).sum := by decide
  have hdescent : baseEnd_4041007 < baseStart_4041007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041020 : List Nat := [2, 2, 2, 2, 1, 2, 3, 9]
def baseStart_4041020 : Nat := 118140960795 + 4041020 * 2 ^ 59
def prefixEnd_4041020 : Nat := 4983230072969 + 3 ^ 40 * 4041020 * 2
def baseEnd_4041020 : Nat := 76851318312292026828359

theorem tailTrace_4041020 : CollatzResearch.WordTrace tailWord_4041020 prefixEnd_4041020 76851318312292026828359 := by
  unfold tailWord_4041020
  simp only [CollatzResearch.WordTrace]
  refine ⟨73694053910041083057680257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98258738546721444076907009 73694053910041083057680257)
  ·
    refine ⟨55270540432530812293260193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73694053910041083057680257 55270540432530812293260193)
    ·
      refine ⟨41452905324398109219945145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55270540432530812293260193 41452905324398109219945145)
      ·
        refine ⟨31089678993298581914958859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41452905324398109219945145 31089678993298581914958859)
        ·
          refine ⟨46634518489947872872438289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31089678993298581914958859 46634518489947872872438289)
          ·
            refine ⟨34975888867460904654328717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46634518489947872872438289 34975888867460904654328717)
            ·
              refine ⟨13115958325297839245373269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34975888867460904654328717 13115958325297839245373269)
              ·
                refine ⟨76851318312292026828359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13115958325297839245373269 76851318312292026828359)
                ·
                  rfl

theorem cell23_4041020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 9].length) (baseStart_4041020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041020 prefixEnd_4041020 := by exact prefixLift 4041020
  have htrace : WordTrace (prefixWord ++ tailWord_4041020) baseStart_4041020 baseEnd_4041020 := by
    simpa [prefixWord, tailWord_4041020, baseEnd_4041020] using wordTrace_append hprefix tailTrace_4041020
  have hstable : (prefixWord ++ tailWord_4041020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041020).length < 2 ^ (prefixWord ++ tailWord_4041020).sum := by decide
  have hdescent : baseEnd_4041020 < baseStart_4041020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041025 : List Nat := [1, 2, 5, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_4041025 : Nat := 118140960795 + 4041025 * 2 ^ 59
def prefixEnd_4041025 : Nat := 4983230072969 + 3 ^ 40 * 4041025 * 2
def baseEnd_4041025 : Nat := 2074988161835157204803171

theorem tailTrace_4041025 : CollatzResearch.WordTrace tailWord_4041025 prefixEnd_4041025 2074988161835157204803171 := by
  unfold tailWord_4041025
  simp only [CollatzResearch.WordTrace]
  refine ⟨147388290185064051969292529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98258860123376034646195019 147388290185064051969292529)
  ·
    refine ⟨110541217638798038976969397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147388290185064051969292529 110541217638798038976969397)
    ·
      refine ⟨10363239153637316154090881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110541217638798038976969397 10363239153637316154090881)
      ·
        refine ⟨7772429365227987115568161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10363239153637316154090881 7772429365227987115568161)
        ·
          refine ⟨5829322023920990336676121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7772429365227987115568161 5829322023920990336676121)
          ·
            refine ⟨4371991517940742752507091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5829322023920990336676121 4371991517940742752507091)
            ·
              refine ⟨6557987276911114128760637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4371991517940742752507091 6557987276911114128760637)
              ·
                refine ⟨2459245228841667798285239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6557987276911114128760637 2459245228841667798285239)
                ·
                  refine ⟨3688867843262501697427859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2459245228841667798285239 3688867843262501697427859)
                  ·
                    refine ⟨5533301764893752546141789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3688867843262501697427859 5533301764893752546141789)
                    ·
                      refine ⟨2074988161835157204803171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5533301764893752546141789 2074988161835157204803171)
                      ·
                        rfl

theorem cell23_4041025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_4041025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041025 prefixEnd_4041025 := by exact prefixLift 4041025
  have htrace : WordTrace (prefixWord ++ tailWord_4041025) baseStart_4041025 baseEnd_4041025 := by
    simpa [prefixWord, tailWord_4041025, baseEnd_4041025] using wordTrace_append hprefix tailTrace_4041025
  have hstable : (prefixWord ++ tailWord_4041025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041025).length < 2 ^ (prefixWord ++ tailWord_4041025).sum := by decide
  have hdescent : baseEnd_4041025 < baseStart_4041025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041050 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 2, 7]
def baseStart_4041050 : Nat := 118140960795 + 4041050 * 2 ^ 59
def prefixEnd_4041050 : Nat := 4983230072969 + 3 ^ 40 * 4041050 * 2
def baseEnd_4041050 : Nat := 691666999617173202330185

theorem tailTrace_4041050 : CollatzResearch.WordTrace tailWord_4041050 prefixEnd_4041050 691666999617173202330185 := by
  unfold tailWord_4041050
  simp only [CollatzResearch.WordTrace]
  refine ⟨36847300502493370309738151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98259468006648987492635069 36847300502493370309738151)
  ·
    refine ⟨55270950753740055464607227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36847300502493370309738151 55270950753740055464607227)
    ·
      refine ⟨82906426130610083196910841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55270950753740055464607227 82906426130610083196910841)
      ·
        refine ⟨62179819597957562397683131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82906426130610083196910841 62179819597957562397683131)
        ·
          refine ⟨93269729396936343596524697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62179819597957562397683131 93269729396936343596524697)
          ·
            refine ⟨69952297047702257697393523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93269729396936343596524697 69952297047702257697393523)
            ·
              refine ⟨104928445571553386546090285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69952297047702257697393523 104928445571553386546090285)
              ·
                refine ⟨39348167089332519954783857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104928445571553386546090285 39348167089332519954783857)
                ·
                  refine ⟨29511125316999389966087893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39348167089332519954783857 29511125316999389966087893)
                  ·
                    refine ⟨691666999617173202330185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29511125316999389966087893 691666999617173202330185)
                    ·
                      rfl

theorem cell23_4041050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_4041050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041050 prefixEnd_4041050 := by exact prefixLift 4041050
  have htrace : WordTrace (prefixWord ++ tailWord_4041050) baseStart_4041050 baseEnd_4041050 := by
    simpa [prefixWord, tailWord_4041050, baseEnd_4041050] using wordTrace_append hprefix tailTrace_4041050
  have hstable : (prefixWord ++ tailWord_4041050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041050).length < 2 ^ (prefixWord ++ tailWord_4041050).sum := by decide
  have hdescent : baseEnd_4041050 < baseStart_4041050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041057 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 1, 9, 2]
def baseStart_4041057 : Nat := 118140960795 + 4041057 * 2 ^ 59
def prefixEnd_4041057 : Nat := 4983230072969 + 3 ^ 40 * 4041057 * 2
def baseEnd_4041057 : Nat := 2075004593216101079603023

theorem tailTrace_4041057 : CollatzResearch.WordTrace tailWord_4041057 prefixEnd_4041057 2075004593216101079603023 := by
  unfold tailWord_4041057
  simp only [CollatzResearch.WordTrace]
  refine ⟨147389457320948121434457425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98259638213965414289638283 147389457320948121434457425)
  ·
    refine ⟨110542092990711091075843069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147389457320948121434457425 110542092990711091075843069)
    ·
      refine ⟨41453284871516659153441151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110542092990711091075843069 41453284871516659153441151)
      ·
        refine ⟨62179927307274988730161727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41453284871516659153441151 62179927307274988730161727)
        ·
          refine ⟨93269890960912483095242591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62179927307274988730161727 93269890960912483095242591)
          ·
            refine ⟨139904836441368724642863887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93269890960912483095242591 139904836441368724642863887)
            ·
              refine ⟨209857254662053086964295831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139904836441368724642863887 209857254662053086964295831)
              ·
                refine ⟨314785881993079630446443747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209857254662053086964295831 314785881993079630446443747)
                ·
                  refine ⟨472178822989619445669665621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314785881993079630446443747 472178822989619445669665621)
                  ·
                    refine ⟨2766672790954801439470697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 472178822989619445669665621 2766672790954801439470697)
                    ·
                      refine ⟨2075004593216101079603023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766672790954801439470697 2075004593216101079603023)
                      ·
                        rfl

theorem cell23_4041057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_4041057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041057 prefixEnd_4041057 := by exact prefixLift 4041057
  have htrace : WordTrace (prefixWord ++ tailWord_4041057) baseStart_4041057 baseEnd_4041057 := by
    simpa [prefixWord, tailWord_4041057, baseEnd_4041057] using wordTrace_append hprefix tailTrace_4041057
  have hstable : (prefixWord ++ tailWord_4041057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041057).length < 2 ^ (prefixWord ++ tailWord_4041057).sum := by decide
  have hdescent : baseEnd_4041057 < baseStart_4041057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041058 : List Nat := [3, 3, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_4041058 : Nat := 118140960795 + 4041058 * 2 ^ 59
def prefixEnd_4041058 : Nat := 4983230072969 + 3 ^ 40 * 4041058 * 2
def baseEnd_4041058 : Nat := 691668368898918525230173

theorem tailTrace_4041058 : CollatzResearch.WordTrace tailWord_4041058 prefixEnd_4041058 691668368898918525230173 := by
  unfold tailWord_4041058
  simp only [CollatzResearch.WordTrace]
  refine ⟨36847373448486124651310957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98259662529296332403495885 36847373448486124651310957)
  ·
    refine ⟨13817765043182296744241609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36847373448486124651310957 13817765043182296744241609)
    ·
      refine ⟨10363323782386722558181207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13817765043182296744241609 10363323782386722558181207)
      ·
        refine ⟨15544985673580083837271811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10363323782386722558181207 15544985673580083837271811)
        ·
          refine ⟨23317478510370125755907717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15544985673580083837271811 23317478510370125755907717)
          ·
            refine ⟨4372027220694398579232697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23317478510370125755907717 4372027220694398579232697)
            ·
              refine ⟨3279020415520798934424523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4372027220694398579232697 3279020415520798934424523)
              ·
                refine ⟨4918530623281198401636785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279020415520798934424523 4918530623281198401636785)
                ·
                  refine ⟨3688897967460898801227589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4918530623281198401636785 3688897967460898801227589)
                  ·
                    refine ⟨691668368898918525230173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3688897967460898801227589 691668368898918525230173)
                    ·
                      rfl

theorem cell23_4041058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_4041058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041058 prefixEnd_4041058 := by exact prefixLift 4041058
  have htrace : WordTrace (prefixWord ++ tailWord_4041058) baseStart_4041058 baseEnd_4041058 := by
    simpa [prefixWord, tailWord_4041058, baseEnd_4041058] using wordTrace_append hprefix tailTrace_4041058
  have hstable : (prefixWord ++ tailWord_4041058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041058).length < 2 ^ (prefixWord ++ tailWord_4041058).sum := by decide
  have hdescent : baseEnd_4041058 < baseStart_4041058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041068 : List Nat := [2, 2, 1, 1, 7, 1, 1, 2, 1, 2, 3]
def baseStart_4041068 : Nat := 118140960795 + 4041068 * 2 ^ 59
def prefixEnd_4041068 : Nat := 4983230072969 + 3 ^ 40 * 4041068 * 2
def baseEnd_4041068 : Nat := 2075010241503300536565473

theorem tailTrace_4041068 : CollatzResearch.WordTrace tailWord_4041068 prefixEnd_4041068 2075010241503300536565473 := by
  unfold tailWord_4041068
  simp only [CollatzResearch.WordTrace]
  refine ⟨73694929261954135156553929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98259905682605513542071905 73694929261954135156553929)
  ·
    refine ⟨55271196946465601367415447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73694929261954135156553929 55271196946465601367415447)
    ·
      refine ⟨82906795419698402051123171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55271196946465601367415447 82906795419698402051123171)
      ·
        refine ⟨124360193129547603076684757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82906795419698402051123171 124360193129547603076684757)
        ·
          refine ⟨2914692026473771947109799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 124360193129547603076684757 2914692026473771947109799)
          ·
            refine ⟨4372038039710657920664699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2914692026473771947109799 4372038039710657920664699)
            ·
              refine ⟨6558057059565986880997049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4372038039710657920664699 6558057059565986880997049)
              ·
                refine ⟨4918542794674490160747787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6558057059565986880997049 4918542794674490160747787)
                ·
                  refine ⟨7377814192011735241121681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4918542794674490160747787 7377814192011735241121681)
                  ·
                    refine ⟨5533360644008801430841261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7377814192011735241121681 5533360644008801430841261)
                    ·
                      refine ⟨2075010241503300536565473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5533360644008801430841261 2075010241503300536565473)
                      ·
                        rfl

theorem cell23_4041068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 1, 2, 3].length) (baseStart_4041068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041068 prefixEnd_4041068 := by exact prefixLift 4041068
  have htrace : WordTrace (prefixWord ++ tailWord_4041068) baseStart_4041068 baseEnd_4041068 := by
    simpa [prefixWord, tailWord_4041068, baseEnd_4041068] using wordTrace_append hprefix tailTrace_4041068
  have hstable : (prefixWord ++ tailWord_4041068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041068).length < 2 ^ (prefixWord ++ tailWord_4041068).sum := by decide
  have hdescent : baseEnd_4041068 < baseStart_4041068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041127 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 9]
def baseStart_4041127 : Nat := 118140960795 + 4041127 * 2 ^ 59
def prefixEnd_4041127 : Nat := 4983230072969 + 3 ^ 40 * 4041127 * 2
def baseEnd_4041127 : Nat := 230560059651323978414189

theorem tailTrace_4041127 : CollatzResearch.WordTrace tailWord_4041127 prefixEnd_4041127 230560059651323978414189 := by
  unfold tailWord_4041127
  simp only [CollatzResearch.WordTrace]
  refine ⟨147392010430694523389505635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98261340287129682259670423 147392010430694523389505635)
  ·
    refine ⟨221088015646041785084258453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147392010430694523389505635 221088015646041785084258453)
    ·
      refine ⟨10363500733408208675824615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 221088015646041785084258453 10363500733408208675824615)
      ·
        refine ⟨15545251100112313013736923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10363500733408208675824615 15545251100112313013736923)
        ·
          refine ⟨23317876650168469520605385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15545251100112313013736923 23317876650168469520605385)
          ·
            refine ⟨17488407487626352140454039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23317876650168469520605385 17488407487626352140454039)
            ·
              refine ⟨26232611231439528210681059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17488407487626352140454039 26232611231439528210681059)
              ·
                refine ⟨39348916847159292316021589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26232611231439528210681059 39348916847159292316021589)
                ·
                  refine ⟨230560059651323978414189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39348916847159292316021589 230560059651323978414189)
                  ·
                    rfl

theorem cell23_4041127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 9].length) (baseStart_4041127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041127 prefixEnd_4041127 := by exact prefixLift 4041127
  have htrace : WordTrace (prefixWord ++ tailWord_4041127) baseStart_4041127 baseEnd_4041127 := by
    simpa [prefixWord, tailWord_4041127, baseEnd_4041127] using wordTrace_append hprefix tailTrace_4041127
  have hstable : (prefixWord ++ tailWord_4041127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041127).length < 2 ^ (prefixWord ++ tailWord_4041127).sum := by decide
  have hdescent : baseEnd_4041127 < baseStart_4041127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041174 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_4041174 : Nat := 118140960795 + 4041174 * 2 ^ 59
def prefixEnd_4041174 : Nat := 4983230072969 + 3 ^ 40 * 4041174 * 2
def baseEnd_4041174 : Nat := 691688223484225707279995

theorem tailTrace_4041174 : CollatzResearch.WordTrace tailWord_4041174 prefixEnd_4041174 691688223484225707279995 := by
  unfold tailWord_4041174
  simp only [CollatzResearch.WordTrace]
  refine ⟨9212107791345265651029161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98262483107682833610977717 9212107791345265651029161)
  ·
    refine ⟨6909080843508949238271871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9212107791345265651029161 6909080843508949238271871)
    ·
      refine ⟨10363621265263423857407807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6909080843508949238271871 10363621265263423857407807)
      ·
        refine ⟨15545431897895135786111711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10363621265263423857407807 15545431897895135786111711)
        ·
          refine ⟨23318147846842703679167567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15545431897895135786111711 23318147846842703679167567)
          ·
            refine ⟨34977221770264055518751351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23318147846842703679167567 34977221770264055518751351)
            ·
              refine ⟨52465832655396083278127027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34977221770264055518751351 52465832655396083278127027)
              ·
                refine ⟨78698748983094124917190541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52465832655396083278127027 78698748983094124917190541)
                ·
                  refine ⟨29512030868660296843946453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78698748983094124917190541 29512030868660296843946453)
                  ·
                    refine ⟨691688223484225707279995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29512030868660296843946453 691688223484225707279995)
                    ·
                      rfl

theorem cell23_4041174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_4041174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041174 prefixEnd_4041174 := by exact prefixLift 4041174
  have htrace : WordTrace (prefixWord ++ tailWord_4041174) baseStart_4041174 baseEnd_4041174 := by
    simpa [prefixWord, tailWord_4041174, baseEnd_4041174] using wordTrace_append hprefix tailTrace_4041174
  have hstable : (prefixWord ++ tailWord_4041174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041174).length < 2 ^ (prefixWord ++ tailWord_4041174).sum := by decide
  have hdescent : baseEnd_4041174 < baseStart_4041174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041177 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 3, 3, 4]
def baseStart_4041177 : Nat := 118140960795 + 4041177 * 2 ^ 59
def prefixEnd_4041177 : Nat := 4983230072969 + 3 ^ 40 * 4041177 * 2
def baseEnd_4041177 : Nat := 2075066210894640610102471

theorem tailTrace_4041177 : CollatzResearch.WordTrace tailWord_4041177 prefixEnd_4041177 2075066210894640610102471 := by
  unfold tailWord_4041177
  simp only [CollatzResearch.WordTrace]
  refine ⟨147393834080513381928825785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98262556053675587952550523 147393834080513381928825785)
  ·
    refine ⟨110545375560385036446619339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147393834080513381928825785 110545375560385036446619339)
    ·
      refine ⟨165818063340577554669929009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110545375560385036446619339 165818063340577554669929009)
      ·
        refine ⟨124363547505433166002446757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165818063340577554669929009 124363547505433166002446757)
        ·
          refine ⟨23318165157268718625458767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124363547505433166002446757 23318165157268718625458767)
          ·
            refine ⟨34977247735903077938188151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23318165157268718625458767 34977247735903077938188151)
            ·
              refine ⟨52465871603854616907282227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34977247735903077938188151 52465871603854616907282227)
              ·
                refine ⟨78698807405781925360923341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52465871603854616907282227 78698807405781925360923341)
                ·
                  refine ⟨29512052777168222010346253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78698807405781925360923341 29512052777168222010346253)
                  ·
                    refine ⟨11067019791438083253879845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29512052777168222010346253 11067019791438083253879845)
                    ·
                      refine ⟨2075066210894640610102471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11067019791438083253879845 2075066210894640610102471)
                      ·
                        rfl

theorem cell23_4041177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_4041177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041177 prefixEnd_4041177 := by exact prefixLift 4041177
  have htrace : WordTrace (prefixWord ++ tailWord_4041177) baseStart_4041177 baseEnd_4041177 := by
    simpa [prefixWord, tailWord_4041177, baseEnd_4041177] using wordTrace_append hprefix tailTrace_4041177
  have hstable : (prefixWord ++ tailWord_4041177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041177).length < 2 ^ (prefixWord ++ tailWord_4041177).sum := by decide
  have hdescent : baseEnd_4041177 < baseStart_4041177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041194 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_4041194 : Nat := 118140960795 + 4041194 * 2 ^ 59
def prefixEnd_4041194 : Nat := 4983230072969 + 3 ^ 40 * 4041194 * 2
def baseEnd_4041194 : Nat := 2075074940065767043589893

theorem tailTrace_4041194 : CollatzResearch.WordTrace tailWord_4041194 prefixEnd_4041194 2075074940065767043589893 := by
  unfold tailWord_4041194
  simp only [CollatzResearch.WordTrace]
  refine ⟨36848613530362948458048659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98262969414301195888129757 36848613530362948458048659)
  ·
    refine ⟨55272920295544422687072989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36848613530362948458048659 55272920295544422687072989)
    ·
      refine ⟨20727345110829158507652371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55272920295544422687072989 20727345110829158507652371)
      ·
        refine ⟨31091017666243737761478557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20727345110829158507652371 31091017666243737761478557)
        ·
          refine ⟨11659131624841401660554459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31091017666243737761478557 11659131624841401660554459)
          ·
            refine ⟨17488697437262102490831689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11659131624841401660554459 17488697437262102490831689)
            ·
              refine ⟨13116523077946576868123767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17488697437262102490831689 13116523077946576868123767)
              ·
                refine ⟨19674784616919865302185651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13116523077946576868123767 19674784616919865302185651)
                ·
                  refine ⟨29512176925379797953278477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19674784616919865302185651 29512176925379797953278477)
                  ·
                    refine ⟨11067066347017424232479429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29512176925379797953278477 11067066347017424232479429)
                    ·
                      refine ⟨2075074940065767043589893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11067066347017424232479429 2075074940065767043589893)
                      ·
                        rfl

theorem cell23_4041194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_4041194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041194 prefixEnd_4041194 := by exact prefixLift 4041194
  have htrace : WordTrace (prefixWord ++ tailWord_4041194) baseStart_4041194 baseEnd_4041194 := by
    simpa [prefixWord, tailWord_4041194, baseEnd_4041194] using wordTrace_append hprefix tailTrace_4041194
  have hstable : (prefixWord ++ tailWord_4041194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041194).length < 2 ^ (prefixWord ++ tailWord_4041194).sum := by decide
  have hdescent : baseEnd_4041194 < baseStart_4041194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041221 : List Nat := [1, 3, 1, 1, 2, 2, 2, 6, 1, 4]
def baseStart_4041221 : Nat := 118140960795 + 4041221 * 2 ^ 59
def prefixEnd_4041221 : Nat := 4983230072969 + 3 ^ 40 * 4041221 * 2
def baseEnd_4041221 : Nat := 691696268014479479317423

theorem tailTrace_4041221 : CollatzResearch.WordTrace tailWord_4041221 prefixEnd_4041221 691696268014479479317423 := by
  unfold tailWord_4041221
  simp only [CollatzResearch.WordTrace]
  refine ⟨147395438892353977443427517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98263625928235984962285011 147395438892353977443427517)
  ·
    refine ⟨55273289584632741541285319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147395438892353977443427517 55273289584632741541285319)
    ·
      refine ⟨82909934376949112311927979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55273289584632741541285319 82909934376949112311927979)
      ·
        refine ⟨124364901565423668467891969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82909934376949112311927979 124364901565423668467891969)
        ·
          refine ⟨93273676174067751350918977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124364901565423668467891969 93273676174067751350918977)
          ·
            refine ⟨69955257130550813513189233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93273676174067751350918977 69955257130550813513189233)
            ·
              refine ⟨52466442847913110134891925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69955257130550813513189233 52466442847913110134891925)
              ·
                refine ⟨2459364508495927037573059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52466442847913110134891925 2459364508495927037573059)
                ·
                  refine ⟨3689046762743890556359589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2459364508495927037573059 3689046762743890556359589)
                  ·
                    refine ⟨691696268014479479317423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3689046762743890556359589 691696268014479479317423)
                    ·
                      rfl

theorem cell23_4041221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 1, 4].length) (baseStart_4041221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041221 prefixEnd_4041221 := by exact prefixLift 4041221
  have htrace : WordTrace (prefixWord ++ tailWord_4041221) baseStart_4041221 baseEnd_4041221 := by
    simpa [prefixWord, tailWord_4041221, baseEnd_4041221] using wordTrace_append hprefix tailTrace_4041221
  have hstable : (prefixWord ++ tailWord_4041221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041221).length < 2 ^ (prefixWord ++ tailWord_4041221).sum := by decide
  have hdescent : baseEnd_4041221 < baseStart_4041221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041248 : List Nat := [2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 3]
def baseStart_4041248 : Nat := 118140960795 + 4041248 * 2 ^ 59
def prefixEnd_4041248 : Nat := 4983230072969 + 3 ^ 40 * 4041248 * 2
def baseEnd_4041248 : Nat := 2075102668021109832314645

theorem tailTrace_4041248 : CollatzResearch.WordTrace tailWord_4041248 prefixEnd_4041248 2075102668021109832314645 := by
  unfold tailWord_4041248
  simp only [CollatzResearch.WordTrace]
  refine ⟨73698211831628080527330199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98264282442170774036440265 73698211831628080527330199)
  ·
    refine ⟨110547317747442120790995299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73698211831628080527330199 110547317747442120790995299)
    ·
      refine ⟨165820976621163181186492949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110547317747442120790995299 165820976621163181186492949)
      ·
        refine ⟨7772858279117024118116857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165820976621163181186492949 7772858279117024118116857)
        ·
          refine ⟨5829643709337768088587643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7772858279117024118116857 5829643709337768088587643)
          ·
            refine ⟨8744465564006652132881465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5829643709337768088587643 8744465564006652132881465)
            ·
              refine ⟨6558349173004989099661099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8744465564006652132881465 6558349173004989099661099)
              ·
                refine ⟨9837523759507483649491649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6558349173004989099661099 9837523759507483649491649)
                ·
                  refine ⟨7378142819630612737118737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9837523759507483649491649 7378142819630612737118737)
                  ·
                    refine ⟨5533607114722959552839053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7378142819630612737118737 5533607114722959552839053)
                    ·
                      refine ⟨2075102668021109832314645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5533607114722959552839053 2075102668021109832314645)
                      ·
                        rfl

theorem cell23_4041248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_4041248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041248 prefixEnd_4041248 := by exact prefixLift 4041248
  have htrace : WordTrace (prefixWord ++ tailWord_4041248) baseStart_4041248 baseEnd_4041248 := by
    simpa [prefixWord, tailWord_4041248, baseEnd_4041248] using wordTrace_append hprefix tailTrace_4041248
  have hstable : (prefixWord ++ tailWord_4041248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041248).length < 2 ^ (prefixWord ++ tailWord_4041248).sum := by decide
  have hdescent : baseEnd_4041248 < baseStart_4041248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041264 : List Nat := [2, 1, 1, 1, 2, 3, 2, 5, 1, 5]
def baseStart_4041264 : Nat := 118140960795 + 4041264 * 2 ^ 59
def prefixEnd_4041264 : Nat := 4983230072969 + 3 ^ 40 * 4041264 * 2
def baseEnd_4041264 : Nat := 691703627903860589904857

theorem tailTrace_4041264 : CollatzResearch.WordTrace tailWord_4041264 prefixEnd_4041264 691703627903860589904857 := by
  unfold tailWord_4041264
  simp only [CollatzResearch.WordTrace]
  refine ⟨73698503615599097893621423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98264671487465463858161897 73698503615599097893621423)
  ·
    refine ⟨110547755423398646840432135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73698503615599097893621423 110547755423398646840432135)
    ·
      refine ⟨165821633135097970260648203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110547755423398646840432135 165821633135097970260648203)
      ·
        refine ⟨248732449702646955390972305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165821633135097970260648203 248732449702646955390972305)
        ·
          refine ⟨186549337276985216543229229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248732449702646955390972305 186549337276985216543229229)
          ·
            refine ⟨69956001478869456203710961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186549337276985216543229229 69956001478869456203710961)
            ·
              refine ⟨52467001109152092152783221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69956001478869456203710961 52467001109152092152783221)
              ·
                refine ⟨4918781353983008639323427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52467001109152092152783221 4918781353983008639323427)
                ·
                  refine ⟨7378172030974512958985141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4918781353983008639323427 7378172030974512958985141)
                  ·
                    refine ⟨691703627903860589904857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7378172030974512958985141 691703627903860589904857)
                    ·
                      rfl

theorem cell23_4041264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 1, 5].length) (baseStart_4041264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041264 prefixEnd_4041264 := by exact prefixLift 4041264
  have htrace : WordTrace (prefixWord ++ tailWord_4041264) baseStart_4041264 baseEnd_4041264 := by
    simpa [prefixWord, tailWord_4041264, baseEnd_4041264] using wordTrace_append hprefix tailTrace_4041264
  have hstable : (prefixWord ++ tailWord_4041264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041264).length < 2 ^ (prefixWord ++ tailWord_4041264).sum := by decide
  have hdescent : baseEnd_4041264 < baseStart_4041264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041271 : List Nat := [1, 1, 3, 1, 2, 3, 1, 4, 2, 3, 2]
def baseStart_4041271 : Nat := 118140960795 + 4041271 * 2 ^ 59
def prefixEnd_4041271 : Nat := 4983230072969 + 3 ^ 40 * 4041271 * 2
def baseEnd_4041271 : Nat := 2075114478076163242327039

theorem tailTrace_4041271 : CollatzResearch.WordTrace tailWord_4041271 prefixEnd_4041271 2075114478076163242327039 := by
  unfold tailWord_4041271
  simp only [CollatzResearch.WordTrace]
  refine ⟨147397262542172835982747667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98264841694781890655165111 147397262542172835982747667)
  ·
    refine ⟨221095893813259253974121501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147397262542172835982747667 221095893813259253974121501)
    ·
      refine ⟨82910960179972220240295563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221095893813259253974121501 82910960179972220240295563)
      ·
        refine ⟨124366440269958330360443345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82910960179972220240295563 124366440269958330360443345)
        ·
          refine ⟨93274830202468747770332509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124366440269958330360443345 93274830202468747770332509)
          ·
            refine ⟨34978061325925780413874691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93274830202468747770332509 34978061325925780413874691)
            ·
              refine ⟨52467091988888670620812037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34978061325925780413874691 52467091988888670620812037)
              ·
                refine ⟨9837579747916625741402257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52467091988888670620812037 9837579747916625741402257)
                ·
                  refine ⟨7378184810937469306051693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9837579747916625741402257 7378184810937469306051693)
                  ·
                    refine ⟨2766819304101550989769385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7378184810937469306051693 2766819304101550989769385)
                    ·
                      refine ⟨2075114478076163242327039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766819304101550989769385 2075114478076163242327039)
                      ·
                        rfl

theorem cell23_4041271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 3, 2].length) (baseStart_4041271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041271 prefixEnd_4041271 := by exact prefixLift 4041271
  have htrace : WordTrace (prefixWord ++ tailWord_4041271) baseStart_4041271 baseEnd_4041271 := by
    simpa [prefixWord, tailWord_4041271, baseEnd_4041271] using wordTrace_append hprefix tailTrace_4041271
  have hstable : (prefixWord ++ tailWord_4041271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041271).length < 2 ^ (prefixWord ++ tailWord_4041271).sum := by decide
  have hdescent : baseEnd_4041271 < baseStart_4041271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041294 : List Nat := [4, 1, 1, 1, 1, 2, 3, 3, 1, 6]
def baseStart_4041294 : Nat := 118140960795 + 4041294 * 2 ^ 59
def prefixEnd_4041294 : Nat := 4983230072969 + 3 ^ 40 * 4041294 * 2
def baseEnd_4041294 : Nat := 691708762710405550779811

theorem tailTrace_4041294 : CollatzResearch.WordTrace tailWord_4041294 prefixEnd_4041294 691708762710405550779811 := by
  unfold tailWord_4041294
  simp only [CollatzResearch.WordTrace]
  refine ⟨18424762677636188863854367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98265400947393007273889957 18424762677636188863854367)
  ·
    refine ⟨27637144016454283295781551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18424762677636188863854367 27637144016454283295781551)
    ·
      refine ⟨41455716024681424943672327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27637144016454283295781551 41455716024681424943672327)
      ·
        refine ⟨62183574037022137415508491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41455716024681424943672327 62183574037022137415508491)
        ·
          refine ⟨93275361055533206123262737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62183574037022137415508491 93275361055533206123262737)
          ·
            refine ⟨69956520791649904592447053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93275361055533206123262737 69956520791649904592447053)
            ·
              refine ⟨26233695296868714222167645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69956520791649904592447053 26233695296868714222167645)
              ·
                refine ⟨9837635736325767833312867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26233695296868714222167645 9837635736325767833312867)
                ·
                  refine ⟨14756453604488651749969301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9837635736325767833312867 14756453604488651749969301)
                  ·
                    refine ⟨691708762710405550779811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14756453604488651749969301 691708762710405550779811)
                    ·
                      rfl

theorem cell23_4041294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_4041294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041294 prefixEnd_4041294 := by exact prefixLift 4041294
  have htrace : WordTrace (prefixWord ++ tailWord_4041294) baseStart_4041294 baseEnd_4041294 := by
    simpa [prefixWord, tailWord_4041294, baseEnd_4041294] using wordTrace_append hprefix tailTrace_4041294
  have hstable : (prefixWord ++ tailWord_4041294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041294).length < 2 ^ (prefixWord ++ tailWord_4041294).sum := by decide
  have hdescent : baseEnd_4041294 < baseStart_4041294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041335 : List Nat := [1, 1, 3, 1, 1, 3, 4, 4, 1, 2, 2]
def baseStart_4041335 : Nat := 118140960795 + 4041335 * 2 ^ 59
def prefixEnd_4041335 : Nat := 4983230072969 + 3 ^ 40 * 4041335 * 2
def baseEnd_4041335 : Nat := 2075147340838050991926745

theorem tailTrace_4041335 : CollatzResearch.WordTrace tailWord_4041335 prefixEnd_4041335 2075147340838050991926745 := by
  unfold tailWord_4041335
  simp only [CollatzResearch.WordTrace]
  refine ⟨147399596813940974913077459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98266397875960649942051639 147399596813940974913077459)
  ·
    refine ⟨221099395220911462369616189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147399596813940974913077459 221099395220911462369616189)
    ·
      refine ⟨82912273207841798388606071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221099395220911462369616189 82912273207841798388606071)
      ·
        refine ⟨124368409811762697582909107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82912273207841798388606071 124368409811762697582909107)
        ·
          refine ⟨186552614717644046374363661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124368409811762697582909107 186552614717644046374363661)
          ·
            refine ⟨69957230519116517390386373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186552614717644046374363661 69957230519116517390386373)
            ·
              refine ⟨13116980722334347010697445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69957230519116517390386373 13116980722334347010697445)
              ·
                refine ⟨2459433885437690064505771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13116980722334347010697445 2459433885437690064505771)
                ·
                  refine ⟨3689150828156535096758657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2459433885437690064505771 3689150828156535096758657)
                  ·
                    refine ⟨2766863121117401322568993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3689150828156535096758657 2766863121117401322568993)
                    ·
                      refine ⟨2075147340838050991926745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766863121117401322568993 2075147340838050991926745)
                      ·
                        rfl

theorem cell23_4041335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 1, 2, 2].length) (baseStart_4041335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041335 prefixEnd_4041335 := by exact prefixLift 4041335
  have htrace : WordTrace (prefixWord ++ tailWord_4041335) baseStart_4041335 baseEnd_4041335 := by
    simpa [prefixWord, tailWord_4041335, baseEnd_4041335] using wordTrace_append hprefix tailTrace_4041335
  have hstable : (prefixWord ++ tailWord_4041335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041335).length < 2 ^ (prefixWord ++ tailWord_4041335).sum := by decide
  have hdescent : baseEnd_4041335 < baseStart_4041335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041348 : List Nat := [2, 3, 2, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_4041348 : Nat := 118140960795 + 4041348 * 2 ^ 59
def prefixEnd_4041348 : Nat := 4983230072969 + 3 ^ 40 * 4041348 * 2
def baseEnd_4041348 : Nat := 2075154016086559441064185

theorem tailTrace_4041348 : CollatzResearch.WordTrace tailWord_4041348 prefixEnd_4041348 2075154016086559441064185 := by
  unfold tailWord_4041348
  simp only [CollatzResearch.WordTrace]
  refine ⟨73700035481446939066650349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98266713975262585422200465 73700035481446939066650349)
  ·
    refine ⟨27637513305542602149993881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73700035481446939066650349 27637513305542602149993881)
    ·
      refine ⟨20728134979156951612495411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27637513305542602149993881 20728134979156951612495411)
      ·
        refine ⟨31092202468735427418743117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20728134979156951612495411 31092202468735427418743117)
        ·
          refine ⟨11659575925775785282028669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31092202468735427418743117 11659575925775785282028669)
          ·
            refine ⟨4372340972165919480760751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11659575925775785282028669 4372340972165919480760751)
            ·
              refine ⟨6558511458248879221141127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4372340972165919480760751 6558511458248879221141127)
              ·
                refine ⟨9837767187373318831711691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6558511458248879221141127 9837767187373318831711691)
                ·
                  refine ⟨14756650781059978247567537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9837767187373318831711691 14756650781059978247567537)
                  ·
                    refine ⟨11067488085794983685675653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14756650781059978247567537 11067488085794983685675653)
                    ·
                      refine ⟨2075154016086559441064185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11067488085794983685675653 2075154016086559441064185)
                      ·
                        rfl

theorem cell23_4041348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_4041348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041348 prefixEnd_4041348 := by exact prefixLift 4041348
  have htrace : WordTrace (prefixWord ++ tailWord_4041348) baseStart_4041348 baseEnd_4041348 := by
    simpa [prefixWord, tailWord_4041348, baseEnd_4041348] using wordTrace_append hprefix tailTrace_4041348
  have hstable : (prefixWord ++ tailWord_4041348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041348).length < 2 ^ (prefixWord ++ tailWord_4041348).sum := by decide
  have hdescent : baseEnd_4041348 < baseStart_4041348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041361 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 7, 3, 2]
def baseStart_4041361 : Nat := 118140960795 + 4041361 * 2 ^ 59
def prefixEnd_4041361 : Nat := 4983230072969 + 3 ^ 40 * 4041361 * 2
def baseEnd_4041361 : Nat := 2075160691335067890201625

theorem tailTrace_4041361 : CollatzResearch.WordTrace tailWord_4041361 prefixEnd_4041361 2075160691335067890201625 := by
  unfold tailWord_4041361
  simp only [CollatzResearch.WordTrace]
  refine ⟨147400545111846781353523937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98267030074564520902349291 147400545111846781353523937)
  ·
    refine ⟨110550408833885086015142953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147400545111846781353523937 110550408833885086015142953)
    ·
      refine ⟨82912806625413814511357215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110550408833885086015142953 82912806625413814511357215)
      ·
        refine ⟨124369209938120721767035823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82912806625413814511357215 124369209938120721767035823)
        ·
          refine ⟨186553814907181082650553735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124369209938120721767035823 186553814907181082650553735)
          ·
            refine ⟨279830722360771623975830603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186553814907181082650553735 279830722360771623975830603)
            ·
              refine ⟨419746083541157435963745905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279830722360771623975830603 419746083541157435963745905)
              ·
                refine ⟨314809562655868076972809429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419746083541157435963745905 314809562655868076972809429)
                ·
                  refine ⟨7378349124746908054050221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 314809562655868076972809429 7378349124746908054050221)
                  ·
                    refine ⟨2766880921780090520268833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7378349124746908054050221 2766880921780090520268833)
                    ·
                      refine ⟨2075160691335067890201625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766880921780090520268833 2075160691335067890201625)
                      ·
                        rfl

theorem cell23_4041361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 3, 2].length) (baseStart_4041361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041361 prefixEnd_4041361 := by exact prefixLift 4041361
  have htrace : WordTrace (prefixWord ++ tailWord_4041361) baseStart_4041361 baseEnd_4041361 := by
    simpa [prefixWord, tailWord_4041361, baseEnd_4041361] using wordTrace_append hprefix tailTrace_4041361
  have hstable : (prefixWord ++ tailWord_4041361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041361).length < 2 ^ (prefixWord ++ tailWord_4041361).sum := by decide
  have hdescent : baseEnd_4041361 < baseStart_4041361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041386 : List Nat := [3, 1, 5, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_4041386 : Nat := 118140960795 + 4041386 * 2 ^ 59
def prefixEnd_4041386 : Nat := 4983230072969 + 3 ^ 40 * 4041386 * 2
def baseEnd_4041386 : Nat := 2075173528351430292389011

theorem tailTrace_4041386 : CollatzResearch.WordTrace tailWord_4041386 prefixEnd_4041386 2075173528351430292389011 := by
  unfold tailWord_4041386
  simp only [CollatzResearch.WordTrace]
  refine ⟨36850364234189052655796003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98267637957837473748789341 36850364234189052655796003)
  ·
    refine ⟨55275546351283578983694005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36850364234189052655796003 55275546351283578983694005)
    ·
      refine ⟨5182082470432835529721313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55275546351283578983694005 5182082470432835529721313)
      ·
        refine ⟨3886561852824626647290985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5182082470432835529721313 3886561852824626647290985)
        ·
          refine ⟨2914921389618469985468239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3886561852824626647290985 2914921389618469985468239)
          ·
            refine ⟨4372382084427704978202359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2914921389618469985468239 4372382084427704978202359)
            ·
              refine ⟨6558573126641557467303539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4372382084427704978202359 6558573126641557467303539)
              ·
                refine ⟨9837859689962336200955309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6558573126641557467303539 9837859689962336200955309)
                ·
                  refine ⟨3689197383735876075358241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9837859689962336200955309 3689197383735876075358241)
                  ·
                    refine ⟨2766898037801907056518681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3689197383735876075358241 2766898037801907056518681)
                    ·
                      refine ⟨2075173528351430292389011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766898037801907056518681 2075173528351430292389011)
                      ·
                        rfl

theorem cell23_4041386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_4041386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041386 prefixEnd_4041386 := by exact prefixLift 4041386
  have htrace : WordTrace (prefixWord ++ tailWord_4041386) baseStart_4041386 baseEnd_4041386 := by
    simpa [prefixWord, tailWord_4041386, baseEnd_4041386] using wordTrace_append hprefix tailTrace_4041386
  have hstable : (prefixWord ++ tailWord_4041386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041386).length < 2 ^ (prefixWord ++ tailWord_4041386).sum := by decide
  have hdescent : baseEnd_4041386 < baseStart_4041386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041394 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_4041394 : Nat := 118140960795 + 4041394 * 2 ^ 59
def prefixEnd_4041394 : Nat := 4983230072969 + 3 ^ 40 * 4041394 * 2
def baseEnd_4041394 : Nat := 2075177636196666261088973

theorem tailTrace_4041394 : CollatzResearch.WordTrace tailWord_4041394 prefixEnd_4041394 2075177636196666261088973 := by
  unfold tailWord_4041394
  simp only [CollatzResearch.WordTrace]
  refine ⟨36850437180181806997368809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98267832480484818659650157 36850437180181806997368809)
  ·
    refine ⟨27637827885136355248026607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36850437180181806997368809 27637827885136355248026607)
    ·
      refine ⟨41456741827704532872039911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27637827885136355248026607 41456741827704532872039911)
      ·
        refine ⟨62185112741556799308059867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41456741827704532872039911 62185112741556799308059867)
        ·
          refine ⟨93277669112335198962089801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62185112741556799308059867 93277669112335198962089801)
          ·
            refine ⟨69958251834251399221567351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93277669112335198962089801 69958251834251399221567351)
            ·
              refine ⟨104937377751377098832351027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69958251834251399221567351 104937377751377098832351027)
              ·
                refine ⟨157406066627065648248526541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104937377751377098832351027 157406066627065648248526541)
                ·
                  refine ⟨59027274985149618093197453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157406066627065648248526541 59027274985149618093197453)
                  ·
                    refine ⟨22135228119431106784949045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59027274985149618093197453 22135228119431106784949045)
                    ·
                      refine ⟨2075177636196666261088973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22135228119431106784949045 2075177636196666261088973)
                      ·
                        rfl

theorem cell23_4041394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_4041394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041394 prefixEnd_4041394 := by exact prefixLift 4041394
  have htrace : WordTrace (prefixWord ++ tailWord_4041394) baseStart_4041394 baseEnd_4041394 := by
    simpa [prefixWord, tailWord_4041394, baseEnd_4041394] using wordTrace_append hprefix tailTrace_4041394
  have hstable : (prefixWord ++ tailWord_4041394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041394).length < 2 ^ (prefixWord ++ tailWord_4041394).sum := by decide
  have hdescent : baseEnd_4041394 < baseStart_4041394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041412 : List Nat := [2, 3, 3, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_4041412 : Nat := 118140960795 + 4041412 * 2 ^ 59
def prefixEnd_4041412 : Nat := 4983230072969 + 3 ^ 40 * 4041412 * 2
def baseEnd_4041412 : Nat := 2075186878848447190663891

theorem tailTrace_4041412 : CollatzResearch.WordTrace tailWord_4041412 prefixEnd_4041412 2075186878848447190663891 := by
  unfold tailWord_4041412
  simp only [CollatzResearch.WordTrace]
  refine ⟨73701202617331008531815245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98268270156441344709086993 73701202617331008531815245)
  ·
    refine ⟨27637950981499128199430717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73701202617331008531815245 27637950981499128199430717)
    ·
      refine ⟨10364231618062173074786519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27637950981499128199430717 10364231618062173074786519)
      ·
        refine ⟨15546347427093259612179779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10364231618062173074786519 15546347427093259612179779)
        ·
          refine ⟨23319521140639889418269669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15546347427093259612179779 23319521140639889418269669)
          ·
            refine ⟨4372410213869979265925563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23319521140639889418269669 4372410213869979265925563)
            ·
              refine ⟨6558615320804968898888345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4372410213869979265925563 6558615320804968898888345)
              ·
                refine ⟨4918961490603726674166259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6558615320804968898888345 4918961490603726674166259)
                ·
                  refine ⟨7378442235905590011249389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4918961490603726674166259 7378442235905590011249389)
                  ·
                    refine ⟨2766915838464596254218521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7378442235905590011249389 2766915838464596254218521)
                    ·
                      refine ⟨2075186878848447190663891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766915838464596254218521 2075186878848447190663891)
                      ·
                        rfl

theorem cell23_4041412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_4041412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041412 prefixEnd_4041412 := by exact prefixLift 4041412
  have htrace : WordTrace (prefixWord ++ tailWord_4041412) baseStart_4041412 baseEnd_4041412 := by
    simpa [prefixWord, tailWord_4041412, baseEnd_4041412] using wordTrace_append hprefix tailTrace_4041412
  have hstable : (prefixWord ++ tailWord_4041412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041412).length < 2 ^ (prefixWord ++ tailWord_4041412).sum := by decide
  have hdescent : baseEnd_4041412 < baseStart_4041412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041429 : List Nat := [1, 3, 2, 5, 1, 1, 3, 1, 1, 3, 2]
def baseStart_4041429 : Nat := 118140960795 + 4041429 * 2 ^ 59
def prefixEnd_4041429 : Nat := 4983230072969 + 3 ^ 40 * 4041429 * 2
def baseEnd_4041429 : Nat := 2075195608019573624151313

theorem tailTrace_4041429 : CollatzResearch.WordTrace tailWord_4041429 prefixEnd_4041429 2075195608019573624151313 := by
  unfold tailWord_4041429
  simp only [CollatzResearch.WordTrace]
  refine ⟨147403025275600428966999341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98268683517066952644666227 147403025275600428966999341)
  ·
    refine ⟨55276134478350160862624753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147403025275600428966999341 55276134478350160862624753)
    ·
      refine ⟨41457100858762620646968565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55276134478350160862624753 41457100858762620646968565)
      ·
        refine ⟨3886603205508995685653303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41457100858762620646968565 3886603205508995685653303)
        ·
          refine ⟨5829904808263493528479955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3886603205508995685653303 5829904808263493528479955)
          ·
            refine ⟨8744857212395240292719933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5829904808263493528479955 8744857212395240292719933)
            ·
              refine ⟨3279321454648215109769975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8744857212395240292719933 3279321454648215109769975)
              ·
                refine ⟨4918982181972322664654963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279321454648215109769975 4918982181972322664654963)
                ·
                  refine ⟨7378473272958483996982445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4918982181972322664654963 7378473272958483996982445)
                  ·
                    refine ⟨2766927477359431498868417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7378473272958483996982445 2766927477359431498868417)
                    ·
                      refine ⟨2075195608019573624151313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766927477359431498868417 2075195608019573624151313)
                      ·
                        rfl

theorem cell23_4041429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_4041429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041429 prefixEnd_4041429 := by exact prefixLift 4041429
  have htrace : WordTrace (prefixWord ++ tailWord_4041429) baseStart_4041429 baseEnd_4041429 := by
    simpa [prefixWord, tailWord_4041429, baseEnd_4041429] using wordTrace_append hprefix tailTrace_4041429
  have hstable : (prefixWord ++ tailWord_4041429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041429).length < 2 ^ (prefixWord ++ tailWord_4041429).sum := by decide
  have hdescent : baseEnd_4041429 < baseStart_4041429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041458 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 2, 3, 3]
def baseStart_4041458 : Nat := 118140960795 + 4041458 * 2 ^ 59
def prefixEnd_4041458 : Nat := 4983230072969 + 3 ^ 40 * 4041458 * 2
def baseEnd_4041458 : Nat := 2075210498958554010688679

theorem tailTrace_4041458 : CollatzResearch.WordTrace tailWord_4041458 prefixEnd_4041458 2075210498958554010688679 := by
  unfold tailWord_4041458
  simp only [CollatzResearch.WordTrace]
  refine ⟨36851020748123841729951257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98269388661663577946536685 36851020748123841729951257)
  ·
    refine ⟨27638265561092881297463443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36851020748123841729951257 27638265561092881297463443)
    ·
      refine ⟨41457398341639321946195165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27638265561092881297463443 41457398341639321946195165)
      ·
        refine ⟨15546524378114745729823187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41457398341639321946195165 15546524378114745729823187)
        ·
          refine ⟨23319786567172118594734781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15546524378114745729823187 23319786567172118594734781)
          ·
            refine ⟨8744919962689544473025543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23319786567172118594734781 8744919962689544473025543)
            ·
              refine ⟨13117379944034316709538315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8744919962689544473025543 13117379944034316709538315)
              ·
                refine ⟨19676069916051475064307473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13117379944034316709538315 19676069916051475064307473)
                ·
                  refine ⟨14757052437038606298230605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19676069916051475064307473 14757052437038606298230605)
                  ·
                    refine ⟨5533894663889477361836477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14757052437038606298230605 5533894663889477361836477)
                    ·
                      refine ⟨2075210498958554010688679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5533894663889477361836477 2075210498958554010688679)
                      ·
                        rfl

theorem cell23_4041458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_4041458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041458 prefixEnd_4041458 := by exact prefixLift 4041458
  have htrace : WordTrace (prefixWord ++ tailWord_4041458) baseStart_4041458 baseEnd_4041458 := by
    simpa [prefixWord, tailWord_4041458, baseEnd_4041458] using wordTrace_append hprefix tailTrace_4041458
  have hstable : (prefixWord ++ tailWord_4041458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041458).length < 2 ^ (prefixWord ++ tailWord_4041458).sum := by decide
  have hdescent : baseEnd_4041458 < baseStart_4041458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041491 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 5, 4]
def baseStart_4041491 : Nat := 118140960795 + 4041491 * 2 ^ 59
def prefixEnd_4041491 : Nat := 4983230072969 + 3 ^ 40 * 4041491 * 2
def baseEnd_4041491 : Nat := 691742481273384127192009

theorem tailTrace_4041491 : CollatzResearch.WordTrace tailWord_4041491 prefixEnd_4041491 691742481273384127192009 := by
  unfold tailWord_4041491
  simp only [CollatzResearch.WordTrace]
  refine ⟨147405286601375813555756327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98270191067583875703837551 147405286601375813555756327)
  ·
    refine ⟨221107929902063720333634491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147405286601375813555756327 221107929902063720333634491)
    ·
      refine ⟨331661894853095580500451737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221107929902063720333634491 331661894853095580500451737)
      ·
        refine ⟨248746421139821685375338803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331661894853095580500451737 248746421139821685375338803)
        ·
          refine ⟨373119631709732528063008205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248746421139821685375338803 373119631709732528063008205)
          ·
            refine ⟨139919861891149698023628077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373119631709732528063008205 139919861891149698023628077)
            ·
              refine ⟨52469948209181136758860529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139919861891149698023628077 52469948209181136758860529)
              ·
                refine ⟨39352461156885852569145397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52469948209181136758860529 39352461156885852569145397)
                ·
                  refine ⟨3689293233458048678357381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39352461156885852569145397 3689293233458048678357381)
                  ·
                    refine ⟨691742481273384127192009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3689293233458048678357381 691742481273384127192009)
                    ·
                      rfl

theorem cell23_4041491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 4].length) (baseStart_4041491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041491 prefixEnd_4041491 := by exact prefixLift 4041491
  have htrace : WordTrace (prefixWord ++ tailWord_4041491) baseStart_4041491 baseEnd_4041491 := by
    simpa [prefixWord, tailWord_4041491, baseEnd_4041491] using wordTrace_append hprefix tailTrace_4041491
  have hstable : (prefixWord ++ tailWord_4041491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041491).length < 2 ^ (prefixWord ++ tailWord_4041491).sum := by decide
  have hdescent : baseEnd_4041491 < baseStart_4041491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041498 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2]
def baseStart_4041498 : Nat := 118140960795 + 4041498 * 2 ^ 59
def prefixEnd_4041498 : Nat := 4983230072969 + 3 ^ 40 * 4041498 * 2
def baseEnd_4041498 : Nat := 2075231038184733854188495

theorem tailTrace_4041498 : CollatzResearch.WordTrace tailWord_4041498 prefixEnd_4041498 2075231038184733854188495 := by
  unfold tailWord_4041498
  simp only [CollatzResearch.WordTrace]
  refine ⟨36851385478087613437815287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98270361274900302500840765 36851385478087613437815287)
  ·
    refine ⟨55277078217131420156722931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36851385478087613437815287 55277078217131420156722931)
    ·
      refine ⟨82915617325697130235084397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55277078217131420156722931 82915617325697130235084397)
      ·
        refine ⟨31093356497136423838156649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82915617325697130235084397 31093356497136423838156649)
        ·
          refine ⟨23320017372852317878617487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31093356497136423838156649 23320017372852317878617487)
          ·
            refine ⟨34980026059278476817926231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23320017372852317878617487 34980026059278476817926231)
            ·
              refine ⟨52470039088917715226889347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34980026059278476817926231 52470039088917715226889347)
              ·
                refine ⟨78705058633376572840334021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52470039088917715226889347 78705058633376572840334021)
                ·
                  refine ⟨14757198493758107407562629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78705058633376572840334021 14757198493758107407562629)
                  ·
                    refine ⟨2766974717579645138917993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14757198493758107407562629 2766974717579645138917993)
                    ·
                      refine ⟨2075231038184733854188495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2766974717579645138917993 2075231038184733854188495)
                      ·
                        rfl

theorem cell23_4041498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_4041498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041498 prefixEnd_4041498 := by exact prefixLift 4041498
  have htrace : WordTrace (prefixWord ++ tailWord_4041498) baseStart_4041498 baseEnd_4041498 := by
    simpa [prefixWord, tailWord_4041498, baseEnd_4041498] using wordTrace_append hprefix tailTrace_4041498
  have hstable : (prefixWord ++ tailWord_4041498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041498).length < 2 ^ (prefixWord ++ tailWord_4041498).sum := by decide
  have hdescent : baseEnd_4041498 < baseStart_4041498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041585 : List Nat := [1, 2, 2, 2, 1, 6, 1, 2, 1, 5]
def baseStart_4041585 : Nat := 118140960795 + 4041585 * 2 ^ 59
def prefixEnd_4041585 : Nat := 4983230072969 + 3 ^ 40 * 4041585 * 2
def baseEnd_4041585 : Nat := 691758570333891671266865

theorem tailTrace_4041585 : CollatzResearch.WordTrace tailWord_4041585 prefixEnd_4041585 691758570333891671266865 := by
  unfold tailWord_4041585
  simp only [CollatzResearch.WordTrace]
  refine ⟨147408715063035267609678209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98272476708690178406452139 147408715063035267609678209)
  ·
    refine ⟨110556536297276450707258657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147408715063035267609678209 110556536297276450707258657)
    ·
      refine ⟨82917402222957338030443993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110556536297276450707258657 82917402222957338030443993)
      ·
        refine ⟨62188051667218003522832995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82917402222957338030443993 62188051667218003522832995)
        ·
          refine ⟨93282077500827005284249493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62188051667218003522832995 93282077500827005284249493)
          ·
            refine ⟨4372597382851265872699195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93282077500827005284249493 4372597382851265872699195)
            ·
              refine ⟨6558896074276898809048793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4372597382851265872699195 6558896074276898809048793)
              ·
                refine ⟨4919172055707674106786595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6558896074276898809048793 4919172055707674106786595)
                ·
                  refine ⟨7378758083561511160179893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4919172055707674106786595 7378758083561511160179893)
                  ·
                    refine ⟨691758570333891671266865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7378758083561511160179893 691758570333891671266865)
                    ·
                      rfl

theorem cell23_4041585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_4041585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041585 prefixEnd_4041585 := by exact prefixLift 4041585
  have htrace : WordTrace (prefixWord ++ tailWord_4041585) baseStart_4041585 baseEnd_4041585 := by
    simpa [prefixWord, tailWord_4041585, baseEnd_4041585] using wordTrace_append hprefix tailTrace_4041585
  have hstable : (prefixWord ++ tailWord_4041585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041585).length < 2 ^ (prefixWord ++ tailWord_4041585).sum := by decide
  have hdescent : baseEnd_4041585 < baseStart_4041585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041591 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 5]
def baseStart_4041591 : Nat := 118140960795 + 4041591 * 2 ^ 59
def prefixEnd_4041591 : Nat := 4983230072969 + 3 ^ 40 * 4041591 * 2
def baseEnd_4041591 : Nat := 2075278791885601990325567

theorem tailTrace_4041591 : CollatzResearch.WordTrace tailWord_4041591 prefixEnd_4041591 2075278791885601990325567 := by
  unfold tailWord_4041591
  simp only [CollatzResearch.WordTrace]
  refine ⟨147408933901013530634396627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98272622600675687089597751 147408933901013530634396627)
  ·
    refine ⟨221113400851520295951594941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147408933901013530634396627 221113400851520295951594941)
    ·
      refine ⟨82917525319320110981848103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221113400851520295951594941 82917525319320110981848103)
      ·
        refine ⟨124376287978980166472772155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82917525319320110981848103 124376287978980166472772155)
        ·
          refine ⟨186564431968470249709158233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124376287978980166472772155 186564431968470249709158233)
          ·
            refine ⟨139923323976352687281868675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186564431968470249709158233 139923323976352687281868675)
            ·
              refine ⟨209884985964529030922803013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139923323976352687281868675 209884985964529030922803013)
              ·
                refine ⟨39353434868349193298025565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209884985964529030922803013 39353434868349193298025565)
                ·
                  refine ⟨14757538075630947486759587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39353434868349193298025565 14757538075630947486759587)
                  ·
                    refine ⟨22136307113446421230139381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14757538075630947486759587 22136307113446421230139381)
                    ·
                      refine ⟨2075278791885601990325567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22136307113446421230139381 2075278791885601990325567)
                      ·
                        rfl

theorem cell23_4041591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_4041591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041591 prefixEnd_4041591 := by exact prefixLift 4041591
  have htrace : WordTrace (prefixWord ++ tailWord_4041591) baseStart_4041591 baseEnd_4041591 := by
    simpa [prefixWord, tailWord_4041591, baseEnd_4041591] using wordTrace_append hprefix tailTrace_4041591
  have hstable : (prefixWord ++ tailWord_4041591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041591).length < 2 ^ (prefixWord ++ tailWord_4041591).sum := by decide
  have hdescent : baseEnd_4041591 < baseStart_4041591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041639 : List Nat := [1, 1, 6, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_4041639 : Nat := 118140960795 + 4041639 * 2 ^ 59
def prefixEnd_4041639 : Nat := 4983230072969 + 3 ^ 40 * 4041639 * 2
def baseEnd_4041639 : Nat := 2075303438957017802525347

theorem tailTrace_4041639 : CollatzResearch.WordTrace tailWord_4041639 prefixEnd_4041639 2075303438957017802525347 := by
  unfold tailWord_4041639
  simp only [CollatzResearch.WordTrace]
  refine ⟨147410684604839634832143971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98273789736559756554762647 147410684604839634832143971)
  ·
    refine ⟨221116026907259452248215957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147410684604839634832143971 221116026907259452248215957)
    ·
      refine ⟨10364813761277786824135123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 221116026907259452248215957 10364813761277786824135123)
      ·
        refine ⟨15547220641916680236202685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10364813761277786824135123 15547220641916680236202685)
        ·
          refine ⟨5830207740718755088576007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15547220641916680236202685 5830207740718755088576007)
          ·
            refine ⟨8745311611078132632864011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5830207740718755088576007 8745311611078132632864011)
            ·
              refine ⟨13117967416617198949296017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8745311611078132632864011 13117967416617198949296017)
              ·
                refine ⟨9838475562462899211972013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13117967416617198949296017 9838475562462899211972013)
                ·
                  refine ⟨3689428335923587204489505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9838475562462899211972013 3689428335923587204489505)
                  ·
                    refine ⟨2767071251942690403367129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3689428335923587204489505 2767071251942690403367129)
                    ·
                      refine ⟨2075303438957017802525347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2767071251942690403367129 2075303438957017802525347)
                      ·
                        rfl

theorem cell23_4041639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_4041639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041639 prefixEnd_4041639 := by exact prefixLift 4041639
  have htrace : WordTrace (prefixWord ++ tailWord_4041639) baseStart_4041639 baseEnd_4041639 := by
    simpa [prefixWord, tailWord_4041639, baseEnd_4041639] using wordTrace_append hprefix tailTrace_4041639
  have hstable : (prefixWord ++ tailWord_4041639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041639).length < 2 ^ (prefixWord ++ tailWord_4041639).sum := by decide
  have hdescent : baseEnd_4041639 < baseStart_4041639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041641 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 2, 7]
def baseStart_4041641 : Nat := 118140960795 + 4041641 * 2 ^ 59
def prefixEnd_4041641 : Nat := 4983230072969 + 3 ^ 40 * 4041641 * 2
def baseEnd_4041641 : Nat := 691768155306108931566779

theorem tailTrace_4041641 : CollatzResearch.WordTrace tailWord_4041641 prefixEnd_4041641 691768155306108931566779 := by
  unfold tailWord_4041641
  simp only [CollatzResearch.WordTrace]
  refine ⟨147410757550832389173716777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98273838367221592782477851 147410757550832389173716777)
  ·
    refine ⟨110558068163124291880287583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147410757550832389173716777 110558068163124291880287583)
    ·
      refine ⟨165837102244686437820431375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110558068163124291880287583 165837102244686437820431375)
      ·
        refine ⟨248755653367029656730647063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165837102244686437820431375 248755653367029656730647063)
        ·
          refine ⟨373133480050544485095970595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248755653367029656730647063 373133480050544485095970595)
          ·
            refine ⟨559700220075816727643955893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373133480050544485095970595 559700220075816727643955893)
            ·
              refine ⟨52471895632107818216620865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 559700220075816727643955893 52471895632107818216620865)
              ·
                refine ⟨39353921724080863662465649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52471895632107818216620865 39353921724080863662465649)
                ·
                  refine ⟨29515441293060647746849237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39353921724080863662465649 29515441293060647746849237)
                  ·
                    refine ⟨691768155306108931566779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29515441293060647746849237 691768155306108931566779)
                    ·
                      rfl

theorem cell23_4041641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 7].length) (baseStart_4041641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041641 prefixEnd_4041641 := by exact prefixLift 4041641
  have htrace : WordTrace (prefixWord ++ tailWord_4041641) baseStart_4041641 baseEnd_4041641 := by
    simpa [prefixWord, tailWord_4041641, baseEnd_4041641] using wordTrace_append hprefix tailTrace_4041641
  have hstable : (prefixWord ++ tailWord_4041641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041641).length < 2 ^ (prefixWord ++ tailWord_4041641).sum := by decide
  have hdescent : baseEnd_4041641 < baseStart_4041641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041652 : List Nat := [2, 5, 2, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_4041652 : Nat := 118140960795 + 4041652 * 2 ^ 59
def prefixEnd_4041652 : Nat := 4983230072969 + 3 ^ 40 * 4041652 * 2
def baseEnd_4041652 : Nat := 2075310114205526251662787

theorem tailTrace_4041652 : CollatzResearch.WordTrace tailWord_4041652 prefixEnd_4041652 2075310114205526251662787 := by
  unfold tailWord_4041652
  simp only [CollatzResearch.WordTrace]
  refine ⟨73705579376896269026183605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98274105835861692034911473 73705579376896269026183605)
  ·
    refine ⟨6909898066584025221204713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73705579376896269026183605 6909898066584025221204713)
    ·
      refine ⟨5182423549938018915903535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6909898066584025221204713 5182423549938018915903535)
      ·
        refine ⟨7773635324907028373855303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5182423549938018915903535 7773635324907028373855303)
        ·
          refine ⟨11660452987360542560782955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7773635324907028373855303 11660452987360542560782955)
          ·
            refine ⟨17490679481040813841174433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11660452987360542560782955 17490679481040813841174433)
            ·
              refine ⟨13118009610780610380880825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17490679481040813841174433 13118009610780610380880825)
              ·
                refine ⟨9838507208085457785660619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13118009610780610380880825 9838507208085457785660619)
                ·
                  refine ⟨14757760812128186678490929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9838507208085457785660619 14757760812128186678490929)
                  ·
                    refine ⟨11068320609096140008868197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14757760812128186678490929 11068320609096140008868197)
                    ·
                      refine ⟨2075310114205526251662787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11068320609096140008868197 2075310114205526251662787)
                      ·
                        rfl

theorem cell23_4041652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_4041652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041652 prefixEnd_4041652 := by exact prefixLift 4041652
  have htrace : WordTrace (prefixWord ++ tailWord_4041652) baseStart_4041652 baseEnd_4041652 := by
    simpa [prefixWord, tailWord_4041652, baseEnd_4041652] using wordTrace_append hprefix tailTrace_4041652
  have hstable : (prefixWord ++ tailWord_4041652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041652).length < 2 ^ (prefixWord ++ tailWord_4041652).sum := by decide
  have hdescent : baseEnd_4041652 < baseStart_4041652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041672 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 4, 1, 3]
def baseStart_4041672 : Nat := 118140960795 + 4041672 * 2 ^ 59
def prefixEnd_4041672 : Nat := 4983230072969 + 3 ^ 40 * 4041672 * 2
def baseEnd_4041672 : Nat := 2075320383818616173412695

theorem tailTrace_4041672 : CollatzResearch.WordTrace tailWord_4041672 prefixEnd_4041672 2075320383818616173412695 := by
  unfold tailWord_4041672
  simp only [CollatzResearch.WordTrace]
  refine ⟨73705944106860040734047635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98274592142480054312063513 73705944106860040734047635)
  ·
    refine ⟨110558916160290061101071453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73705944106860040734047635 110558916160290061101071453)
    ·
      refine ⟨41459593560108772912901795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110558916160290061101071453 41459593560108772912901795)
      ·
        refine ⟨62189390340163159369352693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41459593560108772912901795 62189390340163159369352693)
        ·
          refine ⟨5830255344390296190876815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62189390340163159369352693 5830255344390296190876815)
          ·
            refine ⟨8745383016585444286315223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5830255344390296190876815 8745383016585444286315223)
            ·
              refine ⟨13118074524878166429472835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8745383016585444286315223 13118074524878166429472835)
              ·
                refine ⟨19677111787317249644209253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13118074524878166429472835 19677111787317249644209253)
                ·
                  refine ⟨3689458460121984308289235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19677111787317249644209253 3689458460121984308289235)
                  ·
                    refine ⟨5534187690182976462433853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3689458460121984308289235 5534187690182976462433853)
                    ·
                      refine ⟨2075320383818616173412695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5534187690182976462433853 2075320383818616173412695)
                      ·
                        rfl

theorem cell23_4041672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_4041672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041672 prefixEnd_4041672 := by exact prefixLift 4041672
  have htrace : WordTrace (prefixWord ++ tailWord_4041672) baseStart_4041672 baseEnd_4041672 := by
    simpa [prefixWord, tailWord_4041672, baseEnd_4041672] using wordTrace_append hprefix tailTrace_4041672
  have hstable : (prefixWord ++ tailWord_4041672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041672).length < 2 ^ (prefixWord ++ tailWord_4041672).sum := by decide
  have hdescent : baseEnd_4041672 < baseStart_4041672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041688 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 2, 6]
def baseStart_4041688 : Nat := 118140960795 + 4041688 * 2 ^ 59
def prefixEnd_4041688 : Nat := 4983230072969 + 3 ^ 40 * 4041688 * 2
def baseEnd_4041688 : Nat := 691776199836362703604207

theorem tailTrace_4041688 : CollatzResearch.WordTrace tailWord_4041688 prefixEnd_4041688 691776199836362703604207 := by
  unfold tailWord_4041688
  simp only [CollatzResearch.WordTrace]
  refine ⟨73706235890831058100338859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98274981187774744133785145 73706235890831058100338859)
  ·
    refine ⟨110559353836246587150508289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73706235890831058100338859 110559353836246587150508289)
    ·
      refine ⟨82919515377184940362881217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110559353836246587150508289 82919515377184940362881217)
      ·
        refine ⟨62189636532888705272160913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82919515377184940362881217 62189636532888705272160913)
        ·
          refine ⟨46642227399666528954120685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62189636532888705272160913 46642227399666528954120685)
          ·
            refine ⟨17490835274874948357795257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46642227399666528954120685 17490835274874948357795257)
            ·
              refine ⟨13118126456156211268346443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17490835274874948357795257 13118126456156211268346443)
              ·
                refine ⟨19677189684234316902519665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13118126456156211268346443 19677189684234316902519665)
                ·
                  refine ⟨14757892263175737676889749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19677189684234316902519665 14757892263175737676889749)
                  ·
                    refine ⟨691776199836362703604207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14757892263175737676889749 691776199836362703604207)
                    ·
                      rfl

theorem cell23_4041688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_4041688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041688 prefixEnd_4041688 := by exact prefixLift 4041688
  have htrace : WordTrace (prefixWord ++ tailWord_4041688) baseStart_4041688 baseEnd_4041688 := by
    simpa [prefixWord, tailWord_4041688, baseEnd_4041688] using wordTrace_append hprefix tailTrace_4041688
  have hstable : (prefixWord ++ tailWord_4041688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041688).length < 2 ^ (prefixWord ++ tailWord_4041688).sum := by decide
  have hdescent : baseEnd_4041688 < baseStart_4041688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041689 : List Nat := [1, 2, 1, 2, 5, 2, 3, 1, 2, 1, 3]
def baseStart_4041689 : Nat := 118140960795 + 4041689 * 2 ^ 59
def prefixEnd_4041689 : Nat := 4983230072969 + 3 ^ 40 * 4041689 * 2
def baseEnd_4041689 : Nat := 2075329112989742606900117

theorem tailTrace_4041689 : CollatzResearch.WordTrace tailWord_4041689 prefixEnd_4041689 2075329112989742606900117 := by
  unfold tailWord_4041689
  simp only [CollatzResearch.WordTrace]
  refine ⟨147412508254658493371464121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98275005503105662247642747 147412508254658493371464121)
  ·
    refine ⟨110559381190993870028598091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147412508254658493371464121 110559381190993870028598091)
    ·
      refine ⟨165839071786490805042897137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110559381190993870028598091 165839071786490805042897137)
      ·
        refine ⟨124379303839868103782172853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165839071786490805042897137 124379303839868103782172853)
        ·
          refine ⟨11660559734987634729578705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124379303839868103782172853 11660559734987634729578705)
          ·
            refine ⟨8745419801240726047184029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11660559734987634729578705 8745419801240726047184029)
            ·
              refine ⟨3279532425465272267694011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8745419801240726047184029 3279532425465272267694011)
              ·
                refine ⟨4919298638197908401541017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279532425465272267694011 4919298638197908401541017)
                ·
                  refine ⟨3689473978648431301155763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4919298638197908401541017 3689473978648431301155763)
                  ·
                    refine ⟨5534210967972646951733645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3689473978648431301155763 5534210967972646951733645)
                    ·
                      refine ⟨2075329112989742606900117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5534210967972646951733645 2075329112989742606900117)
                      ·
                        rfl

theorem cell23_4041689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 2, 1, 3].length) (baseStart_4041689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041689 prefixEnd_4041689 := by exact prefixLift 4041689
  have htrace : WordTrace (prefixWord ++ tailWord_4041689) baseStart_4041689 baseEnd_4041689 := by
    simpa [prefixWord, tailWord_4041689, baseEnd_4041689] using wordTrace_append hprefix tailTrace_4041689
  have hstable : (prefixWord ++ tailWord_4041689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041689).length < 2 ^ (prefixWord ++ tailWord_4041689).sum := by decide
  have hdescent : baseEnd_4041689 < baseStart_4041689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041765 : List Nat := [1, 3, 1, 2, 2, 2, 4, 1, 2, 5]
def baseStart_4041765 : Nat := 118140960795 + 4041765 * 2 ^ 59
def prefixEnd_4041765 : Nat := 4983230072969 + 3 ^ 40 * 4041765 * 2
def baseEnd_4041765 : Nat := 691789379173161436516589

theorem tailTrace_4041765 : CollatzResearch.WordTrace tailWord_4041765 prefixEnd_4041765 691789379173161436516589 := by
  unfold tailWord_4041765
  simp only [CollatzResearch.WordTrace]
  refine ⟨147415280202383158351230749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98276853468255438900820499 147415280202383158351230749)
  ·
    refine ⟨55280730075893684381711531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147415280202383158351230749 55280730075893684381711531)
    ·
      refine ⟨82921095113840526572567297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55280730075893684381711531 82921095113840526572567297)
      ·
        refine ⟨62190821335380394929425473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82921095113840526572567297 62190821335380394929425473)
        ·
          refine ⟨46643116001535296197069105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62190821335380394929425473 46643116001535296197069105)
          ·
            refine ⟨34982337001151472147801829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46643116001535296197069105 34982337001151472147801829)
            ·
              refine ⟨6559188187715901027712843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34982337001151472147801829 6559188187715901027712843)
              ·
                refine ⟨9838782281573851541569265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6559188187715901027712843 9838782281573851541569265)
                ·
                  refine ⟨7379086711180388656176949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9838782281573851541569265 7379086711180388656176949)
                  ·
                    refine ⟨691789379173161436516589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7379086711180388656176949 691789379173161436516589)
                    ·
                      rfl

theorem cell23_4041765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_4041765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041765 prefixEnd_4041765 := by exact prefixLift 4041765
  have htrace : WordTrace (prefixWord ++ tailWord_4041765) baseStart_4041765 baseEnd_4041765 := by
    simpa [prefixWord, tailWord_4041765, baseEnd_4041765] using wordTrace_append hprefix tailTrace_4041765
  have hstable : (prefixWord ++ tailWord_4041765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041765).length < 2 ^ (prefixWord ++ tailWord_4041765).sum := by decide
  have hdescent : baseEnd_4041765 < baseStart_4041765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041782 : List Nat := [5, 1, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_4041782 : Nat := 118140960795 + 4041782 * 2 ^ 59
def prefixEnd_4041782 : Nat := 4983230072969 + 3 ^ 40 * 4041782 * 2
def baseEnd_4041782 : Nat := 691792288896870247679063

theorem tailTrace_4041782 : CollatzResearch.WordTrace tailWord_4041782 prefixEnd_4041782 691792288896870247679063 := by
  unfold tailWord_4041782
  simp only [CollatzResearch.WordTrace]
  refine ⟨9213493765207598140912475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98277266828881046836399733 9213493765207598140912475)
  ·
    refine ⟨13820240647811397211368713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9213493765207598140912475 13820240647811397211368713)
    ·
      refine ⟨10365180485858547908526535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13820240647811397211368713 10365180485858547908526535)
      ·
        refine ⟨15547770728787821862789803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10365180485858547908526535 15547770728787821862789803)
        ·
          refine ⟨23321656093181732794184705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15547770728787821862789803 23321656093181732794184705)
          ·
            refine ⟨17491242069886299595638529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23321656093181732794184705 17491242069886299595638529)
            ·
              refine ⟨13118431552414724696728897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17491242069886299595638529 13118431552414724696728897)
              ·
                refine ⟨9838823664311043522546673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13118431552414724696728897 9838823664311043522546673)
                ·
                  refine ⟨7379117748233282641910005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9838823664311043522546673 7379117748233282641910005)
                  ·
                    refine ⟨691792288896870247679063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7379117748233282641910005 691792288896870247679063)
                    ·
                      rfl

theorem cell23_4041782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_4041782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041782 prefixEnd_4041782 := by exact prefixLift 4041782
  have htrace : WordTrace (prefixWord ++ tailWord_4041782) baseStart_4041782 baseEnd_4041782 := by
    simpa [prefixWord, tailWord_4041782, baseEnd_4041782] using wordTrace_append hprefix tailTrace_4041782
  have hstable : (prefixWord ++ tailWord_4041782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041782).length < 2 ^ (prefixWord ++ tailWord_4041782).sum := by decide
  have hdescent : baseEnd_4041782 < baseStart_4041782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041795 : List Nat := [1, 1, 1, 3, 1, 2, 4, 3, 3, 4]
def baseStart_4041795 : Nat := 118140960795 + 4041795 * 2 ^ 59
def prefixEnd_4041795 : Nat := 4983230072969 + 3 ^ 40 * 4041795 * 2
def baseEnd_4041795 : Nat := 691794513979706397391543

theorem tailTrace_4041795 : CollatzResearch.WordTrace tailWord_4041795 prefixEnd_4041795 691794513979706397391543 := by
  unfold tailWord_4041795
  simp only [CollatzResearch.WordTrace]
  refine ⟨147416374392274473474822839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98277582928182982316548559 147416374392274473474822839)
  ·
    refine ⟨221124561588411710212234259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147416374392274473474822839 221124561588411710212234259)
    ·
      refine ⟨331686842382617565318351389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221124561588411710212234259 331686842382617565318351389)
      ·
        refine ⟨124382565893481586994381771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331686842382617565318351389 124382565893481586994381771)
        ·
          refine ⟨186573848840222380491572657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124382565893481586994381771 186573848840222380491572657)
          ·
            refine ⟨139930386630166785368679493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186573848840222380491572657 139930386630166785368679493)
            ·
              refine ⟨26236947493156272256627405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139930386630166785368679493 26236947493156272256627405)
              ·
                refine ⟨9838855309933602096235277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26236947493156272256627405 9838855309933602096235277)
                ·
                  refine ⟨3689570741225100786088229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9838855309933602096235277 3689570741225100786088229)
                  ·
                    refine ⟨691794513979706397391543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3689570741225100786088229 691794513979706397391543)
                    ·
                      rfl

theorem cell23_4041795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 4].length) (baseStart_4041795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041795 prefixEnd_4041795 := by exact prefixLift 4041795
  have htrace : WordTrace (prefixWord ++ tailWord_4041795) baseStart_4041795 baseEnd_4041795 := by
    simpa [prefixWord, tailWord_4041795, baseEnd_4041795] using wordTrace_append hprefix tailTrace_4041795
  have hstable : (prefixWord ++ tailWord_4041795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041795).length < 2 ^ (prefixWord ++ tailWord_4041795).sum := by decide
  have hdescent : baseEnd_4041795 < baseStart_4041795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041829 : List Nat := [1, 3, 1, 3, 2, 1, 4, 3, 1, 4]
def baseStart_4041829 : Nat := 118140960795 + 4041829 * 2 ^ 59
def prefixEnd_4041829 : Nat := 4983230072969 + 3 ^ 40 * 4041829 * 2
def baseEnd_4041829 : Nat := 691800333427124019716491

theorem tailTrace_4041829 : CollatzResearch.WordTrace tailWord_4041829 prefixEnd_4041829 691800333427124019716491 := by
  unfold tailWord_4041829
  simp only [CollatzResearch.WordTrace]
  refine ⟨147417614474151297281560541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98278409649434198187707027 147417614474151297281560541)
  ·
    refine ⟨55281605427806736480585203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147417614474151297281560541 55281605427806736480585203)
    ·
      refine ⟨82922408141710104720877805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55281605427806736480585203 82922408141710104720877805)
      ·
        refine ⟨31095903053141289270329177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82922408141710104720877805 31095903053141289270329177)
        ·
          refine ⟨23321927289855966952746883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31095903053141289270329177 23321927289855966952746883)
          ·
            refine ⟨34982890934783950429120325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23321927289855966952746883 34982890934783950429120325)
            ·
              refine ⟨6559292050271990705460061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34982890934783950429120325 6559292050271990705460061)
              ·
                refine ⟨2459734518851996514547523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6559292050271990705460061 2459734518851996514547523)
                ·
                  refine ⟨3689601778277994771821285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2459734518851996514547523 3689601778277994771821285)
                  ·
                    refine ⟨691800333427124019716491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3689601778277994771821285 691800333427124019716491)
                    ·
                      rfl

theorem cell23_4041829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 1, 4].length) (baseStart_4041829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041829 prefixEnd_4041829 := by exact prefixLift 4041829
  have htrace : WordTrace (prefixWord ++ tailWord_4041829) baseStart_4041829 baseEnd_4041829 := by
    simpa [prefixWord, tailWord_4041829, baseEnd_4041829] using wordTrace_append hprefix tailTrace_4041829
  have hstable : (prefixWord ++ tailWord_4041829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041829).length < 2 ^ (prefixWord ++ tailWord_4041829).sum := by decide
  have hdescent : baseEnd_4041829 < baseStart_4041829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041875 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 4]
def baseStart_4041875 : Nat := 118140960795 + 4041875 * 2 ^ 59
def prefixEnd_4041875 : Nat := 4983230072969 + 3 ^ 40 * 4041875 * 2
def baseEnd_4041875 : Nat := 2075424620391478879174261

theorem tailTrace_4041875 : CollatzResearch.WordTrace tailWord_4041875 prefixEnd_4041875 2075424620391478879174261 := by
  unfold tailWord_4041875
  simp only [CollatzResearch.WordTrace]
  refine ⟨147419292231984647137735079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98279528154656431425156719 147419292231984647137735079)
  ·
    refine ⟨221128938347976970706602619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147419292231984647137735079 221128938347976970706602619)
    ·
      refine ⟨331693407521965456059903929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221128938347976970706602619 331693407521965456059903929)
      ·
        refine ⟨248770055641474092044927947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331693407521965456059903929 248770055641474092044927947)
        ·
          refine ⟨373155083462211138067391921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248770055641474092044927947 373155083462211138067391921)
          ·
            refine ⟨279866312596658353550543941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373155083462211138067391921 279866312596658353550543941)
            ·
              refine ⟨52474933611873441290726989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279866312596658353550543941 52474933611873441290726989)
              ·
                refine ⟨19678100104452540484022621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52474933611873441290726989 19678100104452540484022621)
                ·
                  refine ⟨7379287539169702681508483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19678100104452540484022621 7379287539169702681508483)
                  ·
                    refine ⟨11068931308754554022262725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7379287539169702681508483 11068931308754554022262725)
                    ·
                      refine ⟨2075424620391478879174261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11068931308754554022262725 2075424620391478879174261)
                      ·
                        rfl

theorem cell23_4041875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 4].length) (baseStart_4041875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041875 prefixEnd_4041875 := by exact prefixLift 4041875
  have htrace : WordTrace (prefixWord ++ tailWord_4041875) baseStart_4041875 baseEnd_4041875 := by
    simpa [prefixWord, tailWord_4041875, baseEnd_4041875] using wordTrace_append hprefix tailTrace_4041875
  have hstable : (prefixWord ++ tailWord_4041875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041875).length < 2 ^ (prefixWord ++ tailWord_4041875).sum := by decide
  have hdescent : baseEnd_4041875 < baseStart_4041875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041885 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 3, 6]
def baseStart_4041885 : Nat := 118140960795 + 4041885 * 2 ^ 59
def prefixEnd_4041885 : Nat := 4983230072969 + 3 ^ 40 * 4041885 * 2
def baseEnd_4041885 : Nat := 691809918399341280016405

theorem tailTrace_4041885 : CollatzResearch.WordTrace tailWord_4041885 prefixEnd_4041885 691809918399341280016405 := by
  unfold tailWord_4041885
  simp only [CollatzResearch.WordTrace]
  refine ⟨147419656961948418845599109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98279771307965612563732739 147419656961948418845599109)
  ·
    refine ⟨27641185680365328533549833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147419656961948418845599109 27641185680365328533549833)
    ·
      refine ⟨20730889260273996400162375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27641185680365328533549833 20730889260273996400162375)
      ·
        refine ⟨31096333890410994600243563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20730889260273996400162375 31096333890410994600243563)
        ·
          refine ⟨46644500835616491900365345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31096333890410994600243563 46644500835616491900365345)
          ·
            refine ⟨34983375626712368925274009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46644500835616491900365345 34983375626712368925274009)
            ·
              refine ⟨26237531720034276693955507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34983375626712368925274009 26237531720034276693955507)
              ·
                refine ⟨39356297580051415040933261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26237531720034276693955507 39356297580051415040933261)
                ·
                  refine ⟨14758611592519280640349973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39356297580051415040933261 14758611592519280640349973)
                  ·
                    refine ⟨691809918399341280016405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14758611592519280640349973 691809918399341280016405)
                    ·
                      rfl

theorem cell23_4041885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_4041885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041885 prefixEnd_4041885 := by exact prefixLift 4041885
  have htrace : WordTrace (prefixWord ++ tailWord_4041885) baseStart_4041885 baseEnd_4041885 := by
    simpa [prefixWord, tailWord_4041885, baseEnd_4041885] using wordTrace_append hprefix tailTrace_4041885
  have hstable : (prefixWord ++ tailWord_4041885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041885).length < 2 ^ (prefixWord ++ tailWord_4041885).sum := by decide
  have hdescent : baseEnd_4041885 < baseStart_4041885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041910 : List Nat := [5, 1, 3, 2, 2, 1, 2, 1, 6]
def baseStart_4041910 : Nat := 118140960795 + 4041910 * 2 ^ 59
def prefixEnd_4041910 : Nat := 4983230072969 + 3 ^ 40 * 4041910 * 2
def baseEnd_4041910 : Nat := 230604732468265138026289

theorem tailTrace_4041910 : CollatzResearch.WordTrace tailWord_4041910 prefixEnd_4041910 230604732468265138026289 := by
  unfold tailWord_4041910
  simp only [CollatzResearch.WordTrace]
  refine ⟨9213785549178615507203699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98280379191238565410172789 9213785549178615507203699)
  ·
    refine ⟨13820678323767923260805549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9213785549178615507203699 13820678323767923260805549)
    ·
      refine ⟨5182754371412971222802081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13820678323767923260805549 5182754371412971222802081)
      ·
        refine ⟨3887065778559728417101561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5182754371412971222802081 3887065778559728417101561)
        ·
          refine ⟨2915299333919796312826171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3887065778559728417101561 2915299333919796312826171)
          ·
            refine ⟨4372949000879694469239257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2915299333919796312826171 4372949000879694469239257)
            ·
              refine ⟨3279711750659770851929443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4372949000879694469239257 3279711750659770851929443)
              ·
                refine ⟨4919567625989656277894165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279711750659770851929443 4919567625989656277894165)
                ·
                  refine ⟨230604732468265138026289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4919567625989656277894165 230604732468265138026289)
                  ·
                    rfl

theorem cell23_4041910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_4041910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041910 prefixEnd_4041910 := by exact prefixLift 4041910
  have htrace : WordTrace (prefixWord ++ tailWord_4041910) baseStart_4041910 baseEnd_4041910 := by
    simpa [prefixWord, tailWord_4041910, baseEnd_4041910] using wordTrace_append hprefix tailTrace_4041910
  have hstable : (prefixWord ++ tailWord_4041910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041910).length < 2 ^ (prefixWord ++ tailWord_4041910).sum := by decide
  have hdescent : baseEnd_4041910 < baseStart_4041910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041919 : List Nat := [1, 1, 2, 2, 2, 2, 6, 1, 2, 4]
def baseStart_4041919 : Nat := 118140960795 + 4041919 * 2 ^ 59
def prefixEnd_4041919 : Nat := 4983230072969 + 3 ^ 40 * 4041919 * 2
def baseEnd_4041919 : Nat := 691815737846758902341353

theorem tailTrace_4041919 : CollatzResearch.WordTrace tailWord_4041919 prefixEnd_4041919 691815737846758902341353 := by
  unfold tailWord_4041919
  simp only [CollatzResearch.WordTrace]
  refine ⟨147420897043825242652336811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98280598029216828434891207 147420897043825242652336811)
  ·
    refine ⟨221131345565737863978505217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147420897043825242652336811 221131345565737863978505217)
    ·
      refine ⟨165848509174303397983878913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221131345565737863978505217 165848509174303397983878913)
      ·
        refine ⟨124386381880727548487909185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165848509174303397983878913 124386381880727548487909185)
        ·
          refine ⟨93289786410545661365931889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124386381880727548487909185 93289786410545661365931889)
          ·
            refine ⟨69967339807909246024448917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93289786410545661365931889 69967339807909246024448917)
            ·
              refine ⟨3279719053495745907396043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69967339807909246024448917 3279719053495745907396043)
              ·
                refine ⟨4919578580243618861094065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279719053495745907396043 4919578580243618861094065)
                ·
                  refine ⟨3689683935182714145820549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4919578580243618861094065 3689683935182714145820549)
                  ·
                    refine ⟨691815737846758902341353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3689683935182714145820549 691815737846758902341353)
                    ·
                      rfl

theorem cell23_4041919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 2, 4].length) (baseStart_4041919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041919 prefixEnd_4041919 := by exact prefixLift 4041919
  have htrace : WordTrace (prefixWord ++ tailWord_4041919) baseStart_4041919 baseEnd_4041919 := by
    simpa [prefixWord, tailWord_4041919, baseEnd_4041919] using wordTrace_append hprefix tailTrace_4041919
  have hstable : (prefixWord ++ tailWord_4041919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041919).length < 2 ^ (prefixWord ++ tailWord_4041919).sum := by decide
  have hdescent : baseEnd_4041919 < baseStart_4041919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4041975 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 2, 6]
def baseStart_4041975 : Nat := 118140960795 + 4041975 * 2 ^ 59
def prefixEnd_4041975 : Nat := 4983230072969 + 3 ^ 40 * 4041975 * 2
def baseEnd_4041975 : Nat := 691825322818976162641267

theorem tailTrace_4041975 : CollatzResearch.WordTrace tailWord_4041975 prefixEnd_4041975 691825322818976162641267 := by
  unfold tailWord_4041975
  simp only [CollatzResearch.WordTrace]
  refine ⟨147422939531622364216375379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98281959687748242810916919 147422939531622364216375379)
  ·
    refine ⟨221134409297433546324563069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147422939531622364216375379 221134409297433546324563069)
    ·
      refine ⟨82925403486537579871711151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221134409297433546324563069 82925403486537579871711151)
      ·
        refine ⟨124388105229806369807566727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82925403486537579871711151 124388105229806369807566727)
        ·
          refine ⟨186582157844709554711350091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124388105229806369807566727 186582157844709554711350091)
          ·
            refine ⟨279873236767064332067025137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186582157844709554711350091 279873236767064332067025137)
            ·
              refine ⟨209904927575298249050268853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279873236767064332067025137 209904927575298249050268853)
              ·
                refine ⟨19678586960184210848462705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209904927575298249050268853 19678586960184210848462705)
                ·
                  refine ⟨14758940220138158136347029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19678586960184210848462705 14758940220138158136347029)
                  ·
                    refine ⟨691825322818976162641267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14758940220138158136347029 691825322818976162641267)
                    ·
                      rfl

theorem cell23_4041975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_4041975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4041975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4041975 prefixEnd_4041975 := by exact prefixLift 4041975
  have htrace : WordTrace (prefixWord ++ tailWord_4041975) baseStart_4041975 baseEnd_4041975 := by
    simpa [prefixWord, tailWord_4041975, baseEnd_4041975] using wordTrace_append hprefix tailTrace_4041975
  have hstable : (prefixWord ++ tailWord_4041975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4041975).length < 2 ^ (prefixWord ++ tailWord_4041975).sum := by decide
  have hdescent : baseEnd_4041975 < baseStart_4041975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4041975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042005 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 11]
def baseStart_4042005 : Nat := 118140960795 + 4042005 * 2 ^ 59
def prefixEnd_4042005 : Nat := 4983230072969 + 3 ^ 40 * 4042005 * 2
def baseEnd_4042005 : Nat := 230610152541840374505407

theorem tailTrace_4042005 : CollatzResearch.WordTrace tailWord_4042005 prefixEnd_4042005 230610152541840374505407 := by
  unfold tailWord_4042005
  simp only [CollatzResearch.WordTrace]
  refine ⟨147424033721513679339967469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98282689147675786226644979 147424033721513679339967469)
  ·
    refine ⟨55284012645567629752487801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147424033721513679339967469 55284012645567629752487801)
    ·
      refine ⟨41463009484175722314365851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55284012645567629752487801 41463009484175722314365851)
      ·
        refine ⟨62194514226263583471548777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41463009484175722314365851 62194514226263583471548777)
        ·
          refine ⟨46645885669697687603661583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62194514226263583471548777 46645885669697687603661583)
          ·
            refine ⟨69968828504546531405492375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46645885669697687603661583 69968828504546531405492375)
            ·
              refine ⟨104953242756819797108238563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69968828504546531405492375 104953242756819797108238563)
              ·
                refine ⟨157429864135229695662357845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104953242756819797108238563 157429864135229695662357845)
                ·
                  refine ⟨230610152541840374505407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 157429864135229695662357845 230610152541840374505407)
                  ·
                    rfl

theorem cell23_4042005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 11].length) (baseStart_4042005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042005 prefixEnd_4042005 := by exact prefixLift 4042005
  have htrace : WordTrace (prefixWord ++ tailWord_4042005) baseStart_4042005 baseEnd_4042005 := by
    simpa [prefixWord, tailWord_4042005, baseEnd_4042005] using wordTrace_append hprefix tailTrace_4042005
  have hstable : (prefixWord ++ tailWord_4042005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042005).length < 2 ^ (prefixWord ++ tailWord_4042005).sum := by decide
  have hdescent : baseEnd_4042005 < baseStart_4042005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042012 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_4042012 : Nat := 118140960795 + 4042012 * 2 ^ 59
def prefixEnd_4042012 : Nat := 4983230072969 + 3 ^ 40 * 4042012 * 2
def baseEnd_4042012 : Nat := 2075494967241144843161131

theorem tailTrace_4042012 : CollatzResearch.WordTrace tailWord_4042012 prefixEnd_4042012 2075494967241144843161131 := by
  unfold tailWord_4042012
  simp only [CollatzResearch.WordTrace]
  refine ⟨73712144516244159767736145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98282859354992213023648193 73712144516244159767736145)
  ·
    refine ⟨55284108387183119825802109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73712144516244159767736145 55284108387183119825802109)
    ·
      refine ⟨20731540645193669934675791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55284108387183119825802109 20731540645193669934675791)
      ·
        refine ⟨31097310967790504902013687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20731540645193669934675791 31097310967790504902013687)
        ·
          refine ⟨46645966451685757353020531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31097310967790504902013687 46645966451685757353020531)
          ·
            refine ⟨69968949677528636029530797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46645966451685757353020531 69968949677528636029530797)
            ·
              refine ⟨26238356129073238511074049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69968949677528636029530797 26238356129073238511074049)
              ·
                refine ⟨19678767096804928883305537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26238356129073238511074049 19678767096804928883305537)
                ·
                  refine ⟨14759075322603696662479153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19678767096804928883305537 14759075322603696662479153)
                  ·
                    refine ⟨11069306491952772496859365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14759075322603696662479153 11069306491952772496859365)
                    ·
                      refine ⟨2075494967241144843161131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11069306491952772496859365 2075494967241144843161131)
                      ·
                        rfl

theorem cell23_4042012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_4042012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042012 prefixEnd_4042012 := by exact prefixLift 4042012
  have htrace : WordTrace (prefixWord ++ tailWord_4042012) baseStart_4042012 baseEnd_4042012 := by
    simpa [prefixWord, tailWord_4042012, baseEnd_4042012] using wordTrace_append hprefix tailTrace_4042012
  have hstable : (prefixWord ++ tailWord_4042012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042012).length < 2 ^ (prefixWord ++ tailWord_4042012).sum := by decide
  have hdescent : baseEnd_4042012 < baseStart_4042012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042032 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 3]
def baseStart_4042032 : Nat := 118140960795 + 4042032 * 2 ^ 59
def prefixEnd_4042032 : Nat := 4983230072969 + 3 ^ 40 * 4042032 * 2
def baseEnd_4042032 : Nat := 2075505236854234764911039

theorem tailTrace_4042032 : CollatzResearch.WordTrace tailWord_4042032 prefixEnd_4042032 2075505236854234764911039 := by
  unfold tailWord_4042032
  simp only [CollatzResearch.WordTrace]
  refine ⟨73712509246207931475600175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98283345661610575300800233 73712509246207931475600175)
  ·
    refine ⟨110568763869311897213400263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73712509246207931475600175 110568763869311897213400263)
    ·
      refine ⟨165853145803967845820100395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110568763869311897213400263 165853145803967845820100395)
      ·
        refine ⟨248779718705951768730150593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165853145803967845820100395 248779718705951768730150593)
        ·
          refine ⟨186584789029463826547612945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248779718705951768730150593 186584789029463826547612945)
          ·
            refine ⟨139938591772097869910709709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186584789029463826547612945 139938591772097869910709709)
            ·
              refine ⟨52476971914536701216516141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139938591772097869910709709 52476971914536701216516141)
              ·
                refine ⟨19678864467951262956193553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52476971914536701216516141 19678864467951262956193553)
                ·
                  refine ⟨14759148350963447217145165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19678864467951262956193553 14759148350963447217145165)
                  ·
                    refine ⟨5534680631611292706429437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14759148350963447217145165 5534680631611292706429437)
                    ·
                      refine ⟨2075505236854234764911039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5534680631611292706429437 2075505236854234764911039)
                      ·
                        rfl

theorem cell23_4042032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 3].length) (baseStart_4042032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042032 prefixEnd_4042032 := by exact prefixLift 4042032
  have htrace : WordTrace (prefixWord ++ tailWord_4042032) baseStart_4042032 baseEnd_4042032 := by
    simpa [prefixWord, tailWord_4042032, baseEnd_4042032] using wordTrace_append hprefix tailTrace_4042032
  have hstable : (prefixWord ++ tailWord_4042032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042032).length < 2 ^ (prefixWord ++ tailWord_4042032).sum := by decide
  have hdescent : baseEnd_4042032 < baseStart_4042032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042062 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_4042062 : Nat := 118140960795 + 4042062 * 2 ^ 59
def prefixEnd_4042062 : Nat := 4983230072969 + 3 ^ 40 * 4042062 * 2
def baseEnd_4042062 : Nat := 2075520641273869647535901

theorem tailTrace_4042062 : CollatzResearch.WordTrace tailWord_4042062 prefixEnd_4042062 2075520641273869647535901 := by
  unfold tailWord_4042062
  simp only [CollatzResearch.WordTrace]
  refine ⟨18428264085288397259349055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98284075121538118716528293 18428264085288397259349055)
  ·
    refine ⟨27642396127932595889023583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18428264085288397259349055 27642396127932595889023583)
    ·
      refine ⟨41463594191898893833535375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27642396127932595889023583 41463594191898893833535375)
      ·
        refine ⟨62195391287848340750303063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41463594191898893833535375 62195391287848340750303063)
        ·
          refine ⟨93293086931772511125454595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62195391287848340750303063 93293086931772511125454595)
          ·
            refine ⟨139939630397658766688181893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93293086931772511125454595 139939630397658766688181893)
            ·
              refine ⟨26238680699561018754034105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139939630397658766688181893 26238680699561018754034105)
              ·
                refine ⟨19679010524670764065525579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26238680699561018754034105 19679010524670764065525579)
                ·
                  refine ⟨29518515787006146098288369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19679010524670764065525579 29518515787006146098288369)
                  ·
                    refine ⟨22138886840254609573716277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29518515787006146098288369 22138886840254609573716277)
                    ·
                      refine ⟨2075520641273869647535901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22138886840254609573716277 2075520641273869647535901)
                      ·
                        rfl

theorem cell23_4042062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_4042062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042062 prefixEnd_4042062 := by exact prefixLift 4042062
  have htrace : WordTrace (prefixWord ++ tailWord_4042062) baseStart_4042062 baseEnd_4042062 := by
    simpa [prefixWord, tailWord_4042062, baseEnd_4042062] using wordTrace_append hprefix tailTrace_4042062
  have hstable : (prefixWord ++ tailWord_4042062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042062).length < 2 ^ (prefixWord ++ tailWord_4042062).sum := by decide
  have hdescent : baseEnd_4042062 < baseStart_4042062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042069 : List Nat := [1, 3, 2, 2, 3, 2, 1, 2, 2, 5]
def baseStart_4042069 : Nat := 118140960795 + 4042069 * 2 ^ 59
def prefixEnd_4042069 : Nat := 4983230072969 + 3 ^ 40 * 4042069 * 2
def baseEnd_4042069 : Nat := 691841411879483706716123

theorem tailTrace_4042069 : CollatzResearch.WordTrace tailWord_4042069 prefixEnd_4042069 691841411879483706716123 := by
  unfold tailWord_4042069
  simp only [CollatzResearch.WordTrace]
  refine ⟨147426367993281818270297261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98284245328854545513531507 147426367993281818270297261)
  ·
    refine ⟨55284887997480681851361473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147426367993281818270297261 55284887997480681851361473)
    ·
      refine ⟨41463665998110511388521105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55284887997480681851361473 41463665998110511388521105)
      ·
        refine ⟨31097749498582883541390829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41463665998110511388521105 31097749498582883541390829)
        ·
          refine ⟨11661656061968581328021561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31097749498582883541390829 11661656061968581328021561)
          ·
            refine ⟨8746242046476435996016171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11661656061968581328021561 8746242046476435996016171)
            ·
              refine ⟨13119363069714653994024257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8746242046476435996016171 13119363069714653994024257)
              ·
                refine ⟨9839522302285990495518193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13119363069714653994024257 9839522302285990495518193)
                ·
                  refine ⟨7379641726714492871638645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9839522302285990495518193 7379641726714492871638645)
                  ·
                    refine ⟨691841411879483706716123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7379641726714492871638645 691841411879483706716123)
                    ·
                      rfl

theorem cell23_4042069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_4042069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042069 prefixEnd_4042069 := by exact prefixLift 4042069
  have htrace : WordTrace (prefixWord ++ tailWord_4042069) baseStart_4042069 baseEnd_4042069 := by
    simpa [prefixWord, tailWord_4042069, baseEnd_4042069] using wordTrace_append hprefix tailTrace_4042069
  have hstable : (prefixWord ++ tailWord_4042069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042069).length < 2 ^ (prefixWord ++ tailWord_4042069).sum := by decide
  have hdescent : baseEnd_4042069 < baseStart_4042069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042133 : List Nat := [1, 3, 2, 1, 1, 2, 6, 2, 1, 4]
def baseStart_4042133 : Nat := 118140960795 + 4042133 * 2 ^ 59
def prefixEnd_4042133 : Nat := 4983230072969 + 3 ^ 40 * 4042133 * 2
def baseEnd_4042133 : Nat := 691852366133446289916025

theorem tailTrace_4042133 : CollatzResearch.WordTrace tailWord_4042133 prefixEnd_4042133 691852366133446289916025 := by
  unfold tailWord_4042133
  simp only [CollatzResearch.WordTrace]
  refine ⟨147428702265049957200627053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98285801510033304800418035 147428702265049957200627053)
  ·
    refine ⟨55285763349393733950235145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147428702265049957200627053 55285763349393733950235145)
    ·
      refine ⟨41464322512045300462676359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55285763349393733950235145 41464322512045300462676359)
      ·
        refine ⟨62196483768067950694014539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41464322512045300462676359 62196483768067950694014539)
        ·
          refine ⟨93294725652101926041021809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62196483768067950694014539 93294725652101926041021809)
          ·
            refine ⟨69971044239076444530766357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93294725652101926041021809 69971044239076444530766357)
            ·
              refine ⟨3279892698706708337379673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69971044239076444530766357 3279892698706708337379673)
              ·
                refine ⟨2459919524030031253034755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3279892698706708337379673 2459919524030031253034755)
                ·
                  refine ⟨3689879286045046879552133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2459919524030031253034755 3689879286045046879552133)
                  ·
                    refine ⟨691852366133446289916025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3689879286045046879552133 691852366133446289916025)
                    ·
                      rfl

theorem cell23_4042133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_4042133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042133 prefixEnd_4042133 := by exact prefixLift 4042133
  have htrace : WordTrace (prefixWord ++ tailWord_4042133) baseStart_4042133 baseEnd_4042133 := by
    simpa [prefixWord, tailWord_4042133, baseEnd_4042133] using wordTrace_append hprefix tailTrace_4042133
  have hstable : (prefixWord ++ tailWord_4042133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042133).length < 2 ^ (prefixWord ++ tailWord_4042133).sum := by decide
  have hdescent : baseEnd_4042133 < baseStart_4042133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042176 : List Nat := [2, 1, 1, 2, 3, 1, 6, 1, 1, 5]
def baseStart_4042176 : Nat := 118140960795 + 4042176 * 2 ^ 59
def prefixEnd_4042176 : Nat := 4983230072969 + 3 ^ 40 * 4042176 * 2
def baseEnd_4042176 : Nat := 691859726022827400503459

theorem tailTrace_4042176 : CollatzResearch.WordTrace tailWord_4042176 prefixEnd_4042176 691859726022827400503459 := by
  unfold tailWord_4042176
  simp only [CollatzResearch.WordTrace]
  refine ⟨73715135301947087772221191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98286847069262783696294921 73715135301947087772221191)
  ·
    refine ⟨110572702952920631658331787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73715135301947087772221191 110572702952920631658331787)
    ·
      refine ⟨165859054429380947487497681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110572702952920631658331787 165859054429380947487497681)
      ·
        refine ⟨124394290822035710615623261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165859054429380947487497681 124394290822035710615623261)
        ·
          refine ⟨46647859058263391480858723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124394290822035710615623261 46647859058263391480858723)
          ·
            refine ⟨69971788587395087221288085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46647859058263391480858723 69971788587395087221288085)
            ·
              refine ⟨3279927590034144713497879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69971788587395087221288085 3279927590034144713497879)
              ·
                refine ⟨4919891385051217070246819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279927590034144713497879 4919891385051217070246819)
                ·
                  refine ⟨7379837077576825605370229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4919891385051217070246819 7379837077576825605370229)
                  ·
                    refine ⟨691859726022827400503459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7379837077576825605370229 691859726022827400503459)
                    ·
                      rfl

theorem cell23_4042176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 1, 5].length) (baseStart_4042176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042176 prefixEnd_4042176 := by exact prefixLift 4042176
  have htrace : WordTrace (prefixWord ++ tailWord_4042176) baseStart_4042176 baseEnd_4042176 := by
    simpa [prefixWord, tailWord_4042176, baseEnd_4042176] using wordTrace_append hprefix tailTrace_4042176
  have hstable : (prefixWord ++ tailWord_4042176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042176).length < 2 ^ (prefixWord ++ tailWord_4042176).sum := by decide
  have hdescent : baseEnd_4042176 < baseStart_4042176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042192 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 6]
def baseStart_4042192 : Nat := 118140960795 + 4042192 * 2 ^ 59
def prefixEnd_4042192 : Nat := 4983230072969 + 3 ^ 40 * 4042192 * 2
def baseEnd_4042192 : Nat := 2075587393758954138910303

theorem tailTrace_4042192 : CollatzResearch.WordTrace tailWord_4042192 prefixEnd_4042192 2075587393758954138910303 := by
  unfold tailWord_4042192
  simp only [CollatzResearch.WordTrace]
  refine ⟨73715427085918105138512415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98287236114557473518016553 73715427085918105138512415)
  ·
    refine ⟨110573140628877157707768623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73715427085918105138512415 110573140628877157707768623)
    ·
      refine ⟨165859710943315736561652935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110573140628877157707768623 165859710943315736561652935)
      ·
        refine ⟨248789566414973604842479403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165859710943315736561652935 248789566414973604842479403)
        ·
          refine ⟨373184349622460407263719105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248789566414973604842479403 373184349622460407263719105)
          ·
            refine ⟨279888262216845305447789329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373184349622460407263719105 279888262216845305447789329)
            ·
              refine ⟨209916196662633979085841997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279888262216845305447789329 209916196662633979085841997)
              ·
                refine ⟨78718573748487742157190749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209916196662633979085841997 78718573748487742157190749)
                ·
                  refine ⟨29519465155682903308946531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78718573748487742157190749 29519465155682903308946531)
                  ·
                    refine ⟨44279197733524354963419797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29519465155682903308946531 44279197733524354963419797)
                    ·
                      refine ⟨2075587393758954138910303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44279197733524354963419797 2075587393758954138910303)
                      ·
                        rfl

theorem cell23_4042192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_4042192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042192 prefixEnd_4042192 := by exact prefixLift 4042192
  have htrace : WordTrace (prefixWord ++ tailWord_4042192) baseStart_4042192 baseEnd_4042192 := by
    simpa [prefixWord, tailWord_4042192, baseEnd_4042192] using wordTrace_append hprefix tailTrace_4042192
  have hstable : (prefixWord ++ tailWord_4042192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042192).length < 2 ^ (prefixWord ++ tailWord_4042192).sum := by decide
  have hdescent : baseEnd_4042192 < baseStart_4042192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042199 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 3]
def baseStart_4042199 : Nat := 118140960795 + 4042199 * 2 ^ 59
def prefixEnd_4042199 : Nat := 4983230072969 + 3 ^ 40 * 4042199 * 2
def baseEnd_4042199 : Nat := 2075590988123535611522771

theorem tailTrace_4042199 : CollatzResearch.WordTrace tailWord_4042199 prefixEnd_4042199 2075590988123535611522771 := by
  unfold tailWord_4042199
  simp only [CollatzResearch.WordTrace]
  refine ⟨147431109482810850472529651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98287406321873900315019767 147431109482810850472529651)
  ·
    refine ⟨221146664224216275708794477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147431109482810850472529651 221146664224216275708794477)
    ·
      refine ⟨82929999084081103390797929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221146664224216275708794477 82929999084081103390797929)
      ·
        refine ⟨62197499313060827543098447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82929999084081103390797929 62197499313060827543098447)
        ·
          refine ⟨93296248969591241314647671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62197499313060827543098447 93296248969591241314647671)
          ·
            refine ⟨139944373454386861971971507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93296248969591241314647671 139944373454386861971971507)
            ·
              refine ⟨209916560181580292957957261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139944373454386861971971507 209916560181580292957957261)
              ·
                refine ⟨78718710068092609859233973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209916560181580292957957261 78718710068092609859233973)
                ·
                  refine ⟨7379879068883682174303185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78718710068092609859233973 7379879068883682174303185)
                  ·
                    refine ⟨5534909301662761630727389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7379879068883682174303185 5534909301662761630727389)
                    ·
                      refine ⟨2075590988123535611522771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5534909301662761630727389 2075590988123535611522771)
                      ·
                        rfl

theorem cell23_4042199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_4042199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042199 prefixEnd_4042199 := by exact prefixLift 4042199
  have htrace : WordTrace (prefixWord ++ tailWord_4042199) baseStart_4042199 baseEnd_4042199 := by
    simpa [prefixWord, tailWord_4042199, baseEnd_4042199] using wordTrace_append hprefix tailTrace_4042199
  have hstable : (prefixWord ++ tailWord_4042199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042199).length < 2 ^ (prefixWord ++ tailWord_4042199).sum := by decide
  have hdescent : baseEnd_4042199 < baseStart_4042199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042209 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_4042209 : Nat := 118140960795 + 4042209 * 2 ^ 59
def prefixEnd_4042209 : Nat := 4983230072969 + 3 ^ 40 * 4042209 * 2
def baseEnd_4042209 : Nat := 2075596122930080572397725

theorem tailTrace_4042209 : CollatzResearch.WordTrace tailWord_4042209 prefixEnd_4042209 2075596122930080572397725 := by
  unfold tailWord_4042209
  simp only [CollatzResearch.WordTrace]
  refine ⟨147431474212774622180393681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98287649475183081453595787 147431474212774622180393681)
  ·
    refine ⟨110573605659580966635295261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147431474212774622180393681 110573605659580966635295261)
    ·
      refine ⟨41465102122342862488235723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110573605659580966635295261 41465102122342862488235723)
      ·
        refine ⟨62197653183514293732353585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41465102122342862488235723 62197653183514293732353585)
        ·
          refine ⟨46648239887635720299265189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62197653183514293732353585 46648239887635720299265189)
          ·
            refine ⟨8746544978931697556112223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46648239887635720299265189 8746544978931697556112223)
            ·
              refine ⟨13119817468397546334168335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8746544978931697556112223 13119817468397546334168335)
              ·
                refine ⟨19679726202596319501252503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13119817468397546334168335 19679726202596319501252503)
                ·
                  refine ⟨29519589303894479251878755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19679726202596319501252503 29519589303894479251878755)
                  ·
                    refine ⟨44279383955841718877818133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29519589303894479251878755 44279383955841718877818133)
                    ·
                      refine ⟨2075596122930080572397725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44279383955841718877818133 2075596122930080572397725)
                      ·
                        rfl

theorem cell23_4042209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_4042209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042209 prefixEnd_4042209 := by exact prefixLift 4042209
  have htrace : WordTrace (prefixWord ++ tailWord_4042209) baseStart_4042209 baseEnd_4042209 := by
    simpa [prefixWord, tailWord_4042209, baseEnd_4042209] using wordTrace_append hprefix tailTrace_4042209
  have hstable : (prefixWord ++ tailWord_4042209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042209).length < 2 ^ (prefixWord ++ tailWord_4042209).sum := by decide
  have hdescent : baseEnd_4042209 < baseStart_4042209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042213 : List Nat := [1, 3, 1, 5, 1, 2, 2, 2, 1, 1, 4]
def baseStart_4042213 : Nat := 118140960795 + 4042213 * 2 ^ 59
def prefixEnd_4042213 : Nat := 4983230072969 + 3 ^ 40 * 4042213 * 2
def baseEnd_4042213 : Nat := 2075598176852698556747707

theorem tailTrace_4042213 : CollatzResearch.WordTrace tailWord_4042213 prefixEnd_4042213 2075598176852698556747707 := by
  unfold tailWord_4042213
  simp only [CollatzResearch.WordTrace]
  refine ⟨147431620104760130863539293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98287746736506753909026195 147431620104760130863539293)
  ·
    refine ⟨55286857539285049073827235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147431620104760130863539293 55286857539285049073827235)
    ·
      refine ⟨82930286308927573610740853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55286857539285049073827235 82930286308927573610740853)
      ·
        refine ⟨7774714341461960026006955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82930286308927573610740853 7774714341461960026006955)
        ·
          refine ⟨11662071512192940039010433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7774714341461960026006955 11662071512192940039010433)
          ·
            refine ⟨8746553634144705029257825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11662071512192940039010433 8746553634144705029257825)
            ·
              refine ⟨6559915225608528771943369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8746553634144705029257825 6559915225608528771943369)
              ·
                refine ⟨4919936419206396578957527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6559915225608528771943369 4919936419206396578957527)
                ·
                  refine ⟨7379904628809594868436291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4919936419206396578957527 7379904628809594868436291)
                  ·
                    refine ⟨11069856943214392302654437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7379904628809594868436291 11069856943214392302654437)
                    ·
                      refine ⟨2075598176852698556747707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11069856943214392302654437 2075598176852698556747707)
                      ·
                        rfl

theorem cell23_4042213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_4042213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042213 prefixEnd_4042213 := by exact prefixLift 4042213
  have htrace : WordTrace (prefixWord ++ tailWord_4042213) baseStart_4042213 baseEnd_4042213 := by
    simpa [prefixWord, tailWord_4042213, baseEnd_4042213] using wordTrace_append hprefix tailTrace_4042213
  have hstable : (prefixWord ++ tailWord_4042213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042213).length < 2 ^ (prefixWord ++ tailWord_4042213).sum := by decide
  have hdescent : baseEnd_4042213 < baseStart_4042213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042273 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 3, 3, 2]
def baseStart_4042273 : Nat := 118140960795 + 4042273 * 2 ^ 59
def prefixEnd_4042273 : Nat := 4983230072969 + 3 ^ 40 * 4042273 * 2
def baseEnd_4042273 : Nat := 2075628985691968321997431

theorem tailTrace_4042273 : CollatzResearch.WordTrace tailWord_4042273 prefixEnd_4042273 2075628985691968321997431 := by
  unfold tailWord_4042273
  simp only [CollatzResearch.WordTrace]
  refine ⟨147433808484542761110723473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98289205656361840740482315 147433808484542761110723473)
  ·
    refine ⟨110575356363407070833042605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147433808484542761110723473 110575356363407070833042605)
    ·
      refine ⟨41465758636277651562390977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110575356363407070833042605 41465758636277651562390977)
      ·
        refine ⟨31099318977208238671793233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41465758636277651562390977 31099318977208238671793233)
        ·
          refine ⟨23324489232906179003844925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31099318977208238671793233 23324489232906179003844925)
          ·
            refine ⟨8746683462339817126441847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23324489232906179003844925 8746683462339817126441847)
            ·
              refine ⟨13120025193509725689662771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8746683462339817126441847 13120025193509725689662771)
              ·
                refine ⟨19680037790264588534494157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13120025193509725689662771 19680037790264588534494157)
                ·
                  refine ⟨7380014171349220700435309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19680037790264588534494157 7380014171349220700435309)
                  ·
                    refine ⟨2767505314255957762663241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7380014171349220700435309 2767505314255957762663241)
                    ·
                      refine ⟨2075628985691968321997431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2767505314255957762663241 2075628985691968321997431)
                      ·
                        rfl

theorem cell23_4042273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_4042273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042273 prefixEnd_4042273 := by exact prefixLift 4042273
  have htrace : WordTrace (prefixWord ++ tailWord_4042273) baseStart_4042273 baseEnd_4042273 := by
    simpa [prefixWord, tailWord_4042273, baseEnd_4042273] using wordTrace_append hprefix tailTrace_4042273
  have hstable : (prefixWord ++ tailWord_4042273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042273).length < 2 ^ (prefixWord ++ tailWord_4042273).sum := by decide
  have hdescent : baseEnd_4042273 < baseStart_4042273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042309 : List Nat := [1, 3, 1, 1, 1, 4, 2, 3, 7]
def baseStart_4042309 : Nat := 118140960795 + 4042309 * 2 ^ 59
def prefixEnd_4042309 : Nat := 4983230072969 + 3 ^ 40 * 4042309 * 2
def baseEnd_4042309 : Nat := 230627496777281131238585

theorem tailTrace_4042309 : CollatzResearch.WordTrace tailWord_4042309 prefixEnd_4042309 230627496777281131238585 := by
  unfold tailWord_4042309
  simp only [CollatzResearch.WordTrace]
  refine ⟨147435121512412339259033981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98290081008274892839355987 147435121512412339259033981)
  ·
    refine ⟨55288170567154627222137743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147435121512412339259033981 55288170567154627222137743)
    ·
      refine ⟨82932255850731940833206615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55288170567154627222137743 82932255850731940833206615)
      ·
        refine ⟨124398383776097911249809923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82932255850731940833206615 124398383776097911249809923)
        ·
          refine ⟨186597575664146866874714885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124398383776097911249809923 186597575664146866874714885)
          ·
            refine ⟨34987045437027537539009041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186597575664146866874714885 34987045437027537539009041)
            ·
              refine ⟨26240284077770653154256781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34987045437027537539009041 26240284077770653154256781)
              ·
                refine ⟨9840106529163994932846293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26240284077770653154256781 9840106529163994932846293)
                ·
                  refine ⟨230627496777281131238585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9840106529163994932846293 230627496777281131238585)
                  ·
                    rfl

theorem cell23_4042309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 7].length) (baseStart_4042309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042309 prefixEnd_4042309 := by exact prefixLift 4042309
  have htrace : WordTrace (prefixWord ++ tailWord_4042309) baseStart_4042309 baseEnd_4042309 := by
    simpa [prefixWord, tailWord_4042309, baseEnd_4042309] using wordTrace_append hprefix tailTrace_4042309
  have hstable : (prefixWord ++ tailWord_4042309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042309).length < 2 ^ (prefixWord ++ tailWord_4042309).sum := by decide
  have hdescent : baseEnd_4042309 < baseStart_4042309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042316 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 2, 2, 4]
def baseStart_4042316 : Nat := 118140960795 + 4042316 * 2 ^ 59
def prefixEnd_4042316 : Nat := 4983230072969 + 3 ^ 40 * 4042316 * 2
def baseEnd_4042316 : Nat := 2075651065360111653759733

theorem tailTrace_4042316 : CollatzResearch.WordTrace tailWord_4042316 prefixEnd_4042316 2075651065360111653759733 := by
  unfold tailWord_4042316
  simp only [CollatzResearch.WordTrace]
  refine ⟨73717688411693489727269401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98290251215591319636359201 73717688411693489727269401)
  ·
    refine ⟨55288266308770117295452051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73717688411693489727269401 55288266308770117295452051)
    ·
      refine ⟨82932399463155175943178077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55288266308770117295452051 82932399463155175943178077)
      ·
        refine ⟨31099649798683190978691779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82932399463155175943178077 31099649798683190978691779)
        ·
          refine ⟨46649474698024786468037669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31099649798683190978691779 46649474698024786468037669)
          ·
            refine ⟨8746776505879647462757063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46649474698024786468037669 8746776505879647462757063)
            ·
              refine ⟨13120164758819471194135595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8746776505879647462757063 13120164758819471194135595)
              ·
                refine ⟨19680247138229206791203393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13120164758819471194135595 19680247138229206791203393)
                ·
                  refine ⟨14760185353671905093402545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19680247138229206791203393 14760185353671905093402545)
                  ·
                    refine ⟨11070139015253928820051909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14760185353671905093402545 11070139015253928820051909)
                    ·
                      refine ⟨2075651065360111653759733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11070139015253928820051909 2075651065360111653759733)
                      ·
                        rfl

theorem cell23_4042316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_4042316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042316 prefixEnd_4042316 := by exact prefixLift 4042316
  have htrace : WordTrace (prefixWord ++ tailWord_4042316) baseStart_4042316 baseEnd_4042316 := by
    simpa [prefixWord, tailWord_4042316, baseEnd_4042316] using wordTrace_append hprefix tailTrace_4042316
  have hstable : (prefixWord ++ tailWord_4042316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042316).length < 2 ^ (prefixWord ++ tailWord_4042316).sum := by decide
  have hdescent : baseEnd_4042316 < baseStart_4042316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042443 : List Nat := [1, 1, 1, 1, 3, 2, 1, 6, 3, 1, 3]
def baseStart_4042443 : Nat := 118140960795 + 4042443 * 2 ^ 59
def prefixEnd_4042443 : Nat := 4983230072969 + 3 ^ 40 * 4042443 * 2
def baseEnd_4042443 : Nat := 2075716277403232656871649

theorem tailTrace_4042443 : CollatzResearch.WordTrace tailWord_4042443 prefixEnd_4042443 2075716277403232656871649 := by
  unfold tailWord_4042443
  simp only [CollatzResearch.WordTrace]
  refine ⟨147440008893926880144411983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98293339262617920096274655 147440008893926880144411983)
  ·
    refine ⟨221160013340890320216617975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147440008893926880144411983 221160013340890320216617975)
    ·
      refine ⟨331740020011335480324926963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221160013340890320216617975 331740020011335480324926963)
      ·
        refine ⟨497610030017003220487390445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331740020011335480324926963 497610030017003220487390445)
        ·
          refine ⟨186603761256376207682771417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 497610030017003220487390445 186603761256376207682771417)
          ·
            refine ⟨139952820942282155762078563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186603761256376207682771417 139952820942282155762078563)
            ·
              refine ⟨209929231413423233643117845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139952820942282155762078563 209929231413423233643117845)
              ·
                refine ⟨9840432722504214077021149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 209929231413423233643117845 9840432722504214077021149)
                ·
                  refine ⟨3690162270939080278882931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9840432722504214077021149 3690162270939080278882931)
                  ·
                    refine ⟨5535243406408620418324397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3690162270939080278882931 5535243406408620418324397)
                    ·
                      refine ⟨2075716277403232656871649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5535243406408620418324397 2075716277403232656871649)
                      ·
                        rfl

theorem cell23_4042443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 1, 3].length) (baseStart_4042443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042443 prefixEnd_4042443 := by exact prefixLift 4042443
  have htrace : WordTrace (prefixWord ++ tailWord_4042443) baseStart_4042443 baseEnd_4042443 := by
    simpa [prefixWord, tailWord_4042443, baseEnd_4042443] using wordTrace_append hprefix tailTrace_4042443
  have hstable : (prefixWord ++ tailWord_4042443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042443).length < 2 ^ (prefixWord ++ tailWord_4042443).sum := by decide
  have hdescent : baseEnd_4042443 < baseStart_4042443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042471 : List Nat := [1, 1, 5, 4, 1, 2, 2, 2, 1, 4]
def baseStart_4042471 : Nat := 118140960795 + 4042471 * 2 ^ 59
def prefixEnd_4042471 : Nat := 4983230072969 + 3 ^ 40 * 4042471 * 2
def baseEnd_4042471 : Nat := 691910218287186182440507

theorem tailTrace_4042471 : CollatzResearch.WordTrace tailWord_4042471 prefixEnd_4042471 691910218287186182440507 := by
  unfold tailWord_4042471
  simp only [CollatzResearch.WordTrace]
  refine ⟨147441030137825440926431267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98294020091883627284287511 147441030137825440926431267)
  ·
    refine ⟨221161545206738161389646901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147441030137825440926431267 221161545206738161389646901)
    ·
      refine ⟨20733894863131702630279397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221161545206738161389646901 20733894863131702630279397)
      ·
        refine ⟨3887605286837194243177387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20733894863131702630279397 3887605286837194243177387)
        ·
          refine ⟨5831407930255791364766081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3887605286837194243177387 5831407930255791364766081)
          ·
            refine ⟨4373555947691843523574561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5831407930255791364766081 4373555947691843523574561)
            ·
              refine ⟨3280166960768882642680921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4373555947691843523574561 3280166960768882642680921)
              ·
                refine ⟨2460125220576661982010691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3280166960768882642680921 2460125220576661982010691)
                ·
                  refine ⟨3690187830864992973016037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460125220576661982010691 3690187830864992973016037)
                  ·
                    refine ⟨691910218287186182440507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3690187830864992973016037 691910218287186182440507)
                    ·
                      rfl

theorem cell23_4042471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_4042471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042471 prefixEnd_4042471 := by exact prefixLift 4042471
  have htrace : WordTrace (prefixWord ++ tailWord_4042471) baseStart_4042471 baseEnd_4042471 := by
    simpa [prefixWord, tailWord_4042471, baseEnd_4042471] using wordTrace_append hprefix tailTrace_4042471
  have hstable : (prefixWord ++ tailWord_4042471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042471).length < 2 ^ (prefixWord ++ tailWord_4042471).sum := by decide
  have hdescent : baseEnd_4042471 < baseStart_4042471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042496 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 4]
def baseStart_4042496 : Nat := 118140960795 + 4042496 * 2 ^ 59
def prefixEnd_4042496 : Nat := 4983230072969 + 3 ^ 40 * 4042496 * 2
def baseEnd_4042496 : Nat := 2075743491877920949508905

theorem tailTrace_4042496 : CollatzResearch.WordTrace tailWord_4042496 prefixEnd_4042496 2075743491877920949508905 := by
  unfold tailWord_4042496
  simp only [CollatzResearch.WordTrace]
  refine ⟨73720970981367435098045671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98294627975156580130727561 73720970981367435098045671)
  ·
    refine ⟨110581456472051152647068507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73720970981367435098045671 110581456472051152647068507)
    ·
      refine ⟨165872184708076728970602761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110581456472051152647068507 165872184708076728970602761)
      ·
        refine ⟨124404138531057546727952071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165872184708076728970602761 124404138531057546727952071)
        ·
          refine ⟨186606207796586320091928107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124404138531057546727952071 186606207796586320091928107)
          ·
            refine ⟨279909311694879480137892161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186606207796586320091928107 279909311694879480137892161)
            ·
              refine ⟨209931983771159610103419121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279909311694879480137892161 209931983771159610103419121)
              ·
                refine ⟨157448987828369707577564341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209931983771159610103419121 157448987828369707577564341)
                ·
                  refine ⟨14760842608909660085396657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157448987828369707577564341 14760842608909660085396657)
                  ·
                    refine ⟨11070631956682245064047493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14760842608909660085396657 11070631956682245064047493)
                    ·
                      refine ⟨2075743491877920949508905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11070631956682245064047493 2075743491877920949508905)
                      ·
                        rfl

theorem cell23_4042496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_4042496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042496 prefixEnd_4042496 := by exact prefixLift 4042496
  have htrace : WordTrace (prefixWord ++ tailWord_4042496) baseStart_4042496 baseEnd_4042496 := by
    simpa [prefixWord, tailWord_4042496, baseEnd_4042496] using wordTrace_append hprefix tailTrace_4042496
  have hstable : (prefixWord ++ tailWord_4042496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042496).length < 2 ^ (prefixWord ++ tailWord_4042496).sum := by decide
  have hdescent : baseEnd_4042496 < baseStart_4042496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042514 : List Nat := [3, 2, 4, 1, 1, 3, 2, 1, 1, 5]
def baseStart_4042514 : Nat := 118140960795 + 4042514 * 2 ^ 59
def prefixEnd_4042514 : Nat := 4983230072969 + 3 ^ 40 * 4042514 * 2
def baseEnd_4042514 : Nat := 691917578176567293027941

theorem tailTrace_4042514 : CollatzResearch.WordTrace tailWord_4042514 prefixEnd_4042514 691917578176567293027941 := by
  unfold tailWord_4042514
  simp only [CollatzResearch.WordTrace]
  refine ⟨36860649619167414817561649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98295065651113106180164397 36860649619167414817561649)
  ·
    refine ⟨27645487214375561113171237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36860649619167414817561649 27645487214375561113171237)
    ·
      refine ⟨5183528852695417708719607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27645487214375561113171237 5183528852695417708719607)
      ·
        refine ⟨7775293279043126563079411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5183528852695417708719607 7775293279043126563079411)
        ·
          refine ⟨11662939918564689844619117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7775293279043126563079411 11662939918564689844619117)
          ·
            refine ⟨4373602469461758691732169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11662939918564689844619117 4373602469461758691732169)
            ·
              refine ⟨3280201852096319018799127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4373602469461758691732169 3280201852096319018799127)
              ·
                refine ⟨4920302778144478528198691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3280201852096319018799127 4920302778144478528198691)
                ·
                  refine ⟨7380454167216717792298037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4920302778144478528198691 7380454167216717792298037)
                  ·
                    refine ⟨691917578176567293027941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7380454167216717792298037 691917578176567293027941)
                    ·
                      rfl

theorem cell23_4042514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_4042514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042514 prefixEnd_4042514 := by exact prefixLift 4042514
  have htrace : WordTrace (prefixWord ++ tailWord_4042514) baseStart_4042514 baseEnd_4042514 := by
    simpa [prefixWord, tailWord_4042514, baseEnd_4042514] using wordTrace_append hprefix tailTrace_4042514
  have hstable : (prefixWord ++ tailWord_4042514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042514).length < 2 ^ (prefixWord ++ tailWord_4042514).sum := by decide
  have hdescent : baseEnd_4042514 < baseStart_4042514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042517 : List Nat := [1, 3, 2, 1, 2, 5, 2, 1, 1, 1, 4]
def baseStart_4042517 : Nat := 118140960795 + 4042517 * 2 ^ 59
def prefixEnd_4042517 : Nat := 4983230072969 + 3 ^ 40 * 4042517 * 2
def baseEnd_4042517 : Nat := 2075754274971665367346309

theorem tailTrace_4042517 : CollatzResearch.WordTrace tailWord_4042517 prefixEnd_4042517 2075754274971665367346309 := by
  unfold tailWord_4042517
  simp only [CollatzResearch.WordTrace]
  refine ⟨147442707895658790782605805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98295138597105860521737203 147442707895658790782605805)
  ·
    refine ⟨55291015460872046543477177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147442707895658790782605805 55291015460872046543477177)
    ·
      refine ⟨41468261595654034907607883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55291015460872046543477177 41468261595654034907607883)
      ·
        refine ⟨62202392393481052361411825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41468261595654034907607883 62202392393481052361411825)
        ·
          refine ⟨46651794295110789271058869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62202392393481052361411825 46651794295110789271058869)
          ·
            refine ⟨4373605715166636494161769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46651794295110789271058869 4373605715166636494161769)
            ·
              refine ⟨3280204286374977370621327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4373605715166636494161769 3280204286374977370621327)
              ·
                refine ⟨4920306429562466055931991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3280204286374977370621327 4920306429562466055931991)
                ·
                  refine ⟨7380459644343699083897987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4920306429562466055931991 7380459644343699083897987)
                  ·
                    refine ⟨11070689466515548625846981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7380459644343699083897987 11070689466515548625846981)
                    ·
                      refine ⟨2075754274971665367346309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11070689466515548625846981 2075754274971665367346309)
                      ·
                        rfl

theorem cell23_4042517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_4042517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042517 prefixEnd_4042517 := by exact prefixLift 4042517
  have htrace : WordTrace (prefixWord ++ tailWord_4042517) baseStart_4042517 baseEnd_4042517 := by
    simpa [prefixWord, tailWord_4042517, baseEnd_4042517] using wordTrace_append hprefix tailTrace_4042517
  have hstable : (prefixWord ++ tailWord_4042517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042517).length < 2 ^ (prefixWord ++ tailWord_4042517).sum := by decide
  have hdescent : baseEnd_4042517 < baseStart_4042517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042547 : List Nat := [1, 1, 1, 2, 8, 1, 1, 1, 1, 2, 4]
def baseStart_4042547 : Nat := 118140960795 + 4042547 * 2 ^ 59
def prefixEnd_4042547 : Nat := 4983230072969 + 3 ^ 40 * 4042547 * 2
def baseEnd_4042547 : Nat := 2075769679391300249971171

theorem tailTrace_4042547 : CollatzResearch.WordTrace tailWord_4042547 prefixEnd_4042547 2075769679391300249971171 := by
  unfold tailWord_4042547
  simp only [CollatzResearch.WordTrace]
  refine ⟨147443802085550105906197895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98295868057033403937465263 147443802085550105906197895)
  ·
    refine ⟨221165703128325158859296843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147443802085550105906197895 221165703128325158859296843)
    ·
      refine ⟨331748554692487738288945265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221165703128325158859296843 331748554692487738288945265)
      ·
        refine ⟨248811416019365803716708949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331748554692487738288945265 248811416019365803716708949)
        ·
          refine ⟨2915758781476943012305183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 248811416019365803716708949 2915758781476943012305183)
          ·
            refine ⟨4373638172215414518457775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2915758781476943012305183 4373638172215414518457775)
            ·
              refine ⟨6560457258323121777686663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4373638172215414518457775 6560457258323121777686663)
              ·
                refine ⟨9840685887484682666529995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6560457258323121777686663 9840685887484682666529995)
                ·
                  refine ⟨14761028831227023999794993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9840685887484682666529995 14761028831227023999794993)
                  ·
                    refine ⟨11070771623420267999846245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14761028831227023999794993 11070771623420267999846245)
                    ·
                      refine ⟨2075769679391300249971171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11070771623420267999846245 2075769679391300249971171)
                      ·
                        rfl

theorem cell23_4042547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 1, 2, 4].length) (baseStart_4042547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042547 prefixEnd_4042547 := by exact prefixLift 4042547
  have htrace : WordTrace (prefixWord ++ tailWord_4042547) baseStart_4042547 baseEnd_4042547 := by
    simpa [prefixWord, tailWord_4042547, baseEnd_4042547] using wordTrace_append hprefix tailTrace_4042547
  have hstable : (prefixWord ++ tailWord_4042547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042547).length < 2 ^ (prefixWord ++ tailWord_4042547).sum := by decide
  have hdescent : baseEnd_4042547 < baseStart_4042547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042577 : List Nat := [1, 2, 2, 1, 5, 1, 2, 3, 1, 3, 2]
def baseStart_4042577 : Nat := 118140960795 + 4042577 * 2 ^ 59
def prefixEnd_4042577 : Nat := 4983230072969 + 3 ^ 40 * 4042577 * 2
def baseEnd_4042577 : Nat := 2075785083810935132596033

theorem tailTrace_4042577 : CollatzResearch.WordTrace tailWord_4042577 prefixEnd_4042577 2075785083810935132596033 := by
  unfold tailWord_4042577
  simp only [CollatzResearch.WordTrace]
  refine ⟨147444896275441421029789985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98296597516960947353193323 147444896275441421029789985)
  ·
    refine ⟨110583672206581065772342489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147444896275441421029789985 110583672206581065772342489)
    ·
      refine ⟨82937754154935799329256867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110583672206581065772342489 82937754154935799329256867)
      ·
        refine ⟨124406631232403698993885301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82937754154935799329256867 124406631232403698993885301)
        ·
          refine ⟨11663121678037846780676747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124406631232403698993885301 11663121678037846780676747)
          ·
            refine ⟨17494682517056770171015121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11663121678037846780676747 17494682517056770171015121)
            ·
              refine ⟨13121011887792577628261341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17494682517056770171015121 13121011887792577628261341)
              ·
                refine ⟨4920379457922216610598003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13121011887792577628261341 4920379457922216610598003)
                ·
                  refine ⟨7380569186883324915897005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4920379457922216610598003 7380569186883324915897005)
                  ·
                    refine ⟨2767713445081246843461377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7380569186883324915897005 2767713445081246843461377)
                    ·
                      refine ⟨2075785083810935132596033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2767713445081246843461377 2075785083810935132596033)
                      ·
                        rfl

theorem cell23_4042577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 3, 2].length) (baseStart_4042577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042577 prefixEnd_4042577 := by exact prefixLift 4042577
  have htrace : WordTrace (prefixWord ++ tailWord_4042577) baseStart_4042577 baseEnd_4042577 := by
    simpa [prefixWord, tailWord_4042577, baseEnd_4042577] using wordTrace_append hprefix tailTrace_4042577
  have hstable : (prefixWord ++ tailWord_4042577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042577).length < 2 ^ (prefixWord ++ tailWord_4042577).sum := by decide
  have hdescent : baseEnd_4042577 < baseStart_4042577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042593 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 2, 4, 3]
def baseStart_4042593 : Nat := 118140960795 + 4042593 * 2 ^ 59
def prefixEnd_4042593 : Nat := 4983230072969 + 3 ^ 40 * 4042593 * 2
def baseEnd_4042593 : Nat := 2075793299501407069995959

theorem tailTrace_4042593 : CollatzResearch.WordTrace tailWord_4042593 prefixEnd_4042593 2075793299501407069995959 := by
  unfold tailWord_4042593
  simp only [CollatzResearch.WordTrace]
  refine ⟨147445479843383455762372433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98296986562255637174914955 147445479843383455762372433)
  ·
    refine ⟨110584109882537591821779325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147445479843383455762372433 110584109882537591821779325)
    ·
      refine ⟨41469041205951596933167247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110584109882537591821779325 41469041205951596933167247)
      ·
        refine ⟨62203561808927395399750871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41469041205951596933167247 62203561808927395399750871)
        ·
          refine ⟨93305342713391093099626307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62203561808927395399750871 93305342713391093099626307)
          ·
            refine ⟨139958014070086639649439461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93305342713391093099626307 139958014070086639649439461)
            ·
              refine ⟨26242127638141244934269899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139958014070086639649439461 26242127638141244934269899)
              ·
                refine ⟨39363191457211867401404849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26242127638141244934269899 39363191457211867401404849)
                ·
                  refine ⟨29522393592908900551053637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39363191457211867401404849 29522393592908900551053637)
                  ·
                    refine ⟨5535448798670418853322557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29522393592908900551053637 5535448798670418853322557)
                    ·
                      refine ⟨2075793299501407069995959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5535448798670418853322557 2075793299501407069995959)
                      ·
                        rfl

theorem cell23_4042593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_4042593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042593 prefixEnd_4042593 := by exact prefixLift 4042593
  have htrace : WordTrace (prefixWord ++ tailWord_4042593) baseStart_4042593 baseEnd_4042593 := by
    simpa [prefixWord, tailWord_4042593, baseEnd_4042593] using wordTrace_append hprefix tailTrace_4042593
  have hstable : (prefixWord ++ tailWord_4042593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042593).length < 2 ^ (prefixWord ++ tailWord_4042593).sum := by decide
  have hdescent : baseEnd_4042593 < baseStart_4042593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042613 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 9]
def baseStart_4042613 : Nat := 118140960795 + 4042613 * 2 ^ 59
def prefixEnd_4042613 : Nat := 4983230072969 + 3 ^ 40 * 4042613 * 2
def baseEnd_4042613 : Nat := 230644841012721887971763

theorem tailTrace_4042613 : CollatzResearch.WordTrace tailWord_4042613 prefixEnd_4042613 230644841012721887971763 := by
  unfold tailWord_4042613
  simp only [CollatzResearch.WordTrace]
  refine ⟨147446209303310999178100493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98297472868873999452066995 147446209303310999178100493)
  ·
    refine ⟨55292328488741624691787685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147446209303310999178100493 55292328488741624691787685)
    ·
      refine ⟨10367311591639054629710191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55292328488741624691787685 10367311591639054629710191)
      ·
        refine ⟨15550967387458581944565287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10367311591639054629710191 15550967387458581944565287)
        ·
          refine ⟨23326451081187872916847931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15550967387458581944565287 23326451081187872916847931)
          ·
            refine ⟨34989676621781809375271897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23326451081187872916847931 34989676621781809375271897)
            ·
              refine ⟨26242257466336357031453923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34989676621781809375271897 26242257466336357031453923)
              ·
                refine ⟨39363386199504535547180885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26242257466336357031453923 39363386199504535547180885)
                ·
                  refine ⟨230644841012721887971763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39363386199504535547180885 230644841012721887971763)
                  ·
                    rfl

theorem cell23_4042613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 9].length) (baseStart_4042613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042613 prefixEnd_4042613 := by exact prefixLift 4042613
  have htrace : WordTrace (prefixWord ++ tailWord_4042613) baseStart_4042613 baseEnd_4042613 := by
    simpa [prefixWord, tailWord_4042613, baseEnd_4042613] using wordTrace_append hprefix tailTrace_4042613
  have hstable : (prefixWord ++ tailWord_4042613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042613).length < 2 ^ (prefixWord ++ tailWord_4042613).sum := by decide
  have hdescent : baseEnd_4042613 < baseStart_4042613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042623 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 3]
def baseStart_4042623 : Nat := 118140960795 + 4042623 * 2 ^ 59
def prefixEnd_4042623 : Nat := 4983230072969 + 3 ^ 40 * 4042623 * 2
def baseEnd_4042623 : Nat := 2075808703921041952620821

theorem tailTrace_4042623 : CollatzResearch.WordTrace tailWord_4042623 prefixEnd_4042623 2075808703921041952620821 := by
  unfold tailWord_4042623
  simp only [CollatzResearch.WordTrace]
  refine ⟨147446574033274770885964523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98297716022183180590643015 147446574033274770885964523)
  ·
    refine ⟨221169861049912156328946785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147446574033274770885964523 221169861049912156328946785)
    ·
      refine ⟨165877395787434117246710089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221169861049912156328946785 165877395787434117246710089)
      ·
        refine ⟨124408046840575587935032567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165877395787434117246710089 124408046840575587935032567)
        ·
          refine ⟨186612070260863381902548851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124408046840575587935032567 186612070260863381902548851)
          ·
            refine ⟨279918105391295072853823277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186612070260863381902548851 279918105391295072853823277)
            ·
              refine ⟨104969289521735652320183729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279918105391295072853823277 104969289521735652320183729)
              ·
                refine ⟨78726967141301739240137797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104969289521735652320183729 78726967141301739240137797)
                ·
                  refine ⟨14761306338994076107525837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78726967141301739240137797 14761306338994076107525837)
                  ·
                    refine ⟨5535489877122778540322189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14761306338994076107525837 5535489877122778540322189)
                    ·
                      refine ⟨2075808703921041952620821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5535489877122778540322189 2075808703921041952620821)
                      ·
                        rfl

theorem cell23_4042623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_4042623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042623 prefixEnd_4042623 := by exact prefixLift 4042623
  have htrace : WordTrace (prefixWord ++ tailWord_4042623) baseStart_4042623 baseEnd_4042623 := by
    simpa [prefixWord, tailWord_4042623, baseEnd_4042623] using wordTrace_append hprefix tailTrace_4042623
  have hstable : (prefixWord ++ tailWord_4042623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042623).length < 2 ^ (prefixWord ++ tailWord_4042623).sum := by decide
  have hdescent : baseEnd_4042623 < baseStart_4042623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042647 : List Nat := [1, 1, 3, 3, 1, 3, 4, 2, 5]
def baseStart_4042647 : Nat := 118140960795 + 4042647 * 2 ^ 59
def prefixEnd_4042647 : Nat := 4983230072969 + 3 ^ 40 * 4042647 * 2
def baseEnd_4042647 : Nat := 230646780828527762080079

theorem tailTrace_4042647 : CollatzResearch.WordTrace tailWord_4042647 prefixEnd_4042647 230646780828527762080079 := by
  unfold tailWord_4042647
  simp only [CollatzResearch.WordTrace]
  refine ⟨147447449385187822984838195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98298299590125215323225463 147447449385187822984838195)
  ·
    refine ⟨221171174077781734477257293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147447449385187822984838195 221171174077781734477257293)
    ·
      refine ⟨82939190279168150428971485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221171174077781734477257293 82939190279168150428971485)
      ·
        refine ⟨31102196354688056410864307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82939190279168150428971485 31102196354688056410864307)
        ·
          refine ⟨46653294532032084616296461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31102196354688056410864307 46653294532032084616296461)
          ·
            refine ⟨17494985449512031731111173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46653294532032084616296461 17494985449512031731111173)
            ·
              refine ⟨3280309771783505949583345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17494985449512031731111173 3280309771783505949583345)
              ·
                refine ⟨2460232328837629462187509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3280309771783505949583345 2460232328837629462187509)
                ·
                  refine ⟨230646780828527762080079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2460232328837629462187509 230646780828527762080079)
                  ·
                    rfl

theorem cell23_4042647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 5].length) (baseStart_4042647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042647 prefixEnd_4042647 := by exact prefixLift 4042647
  have htrace : WordTrace (prefixWord ++ tailWord_4042647) baseStart_4042647 baseEnd_4042647 := by
    simpa [prefixWord, tailWord_4042647, baseEnd_4042647] using wordTrace_append hprefix tailTrace_4042647
  have hstable : (prefixWord ++ tailWord_4042647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042647).length < 2 ^ (prefixWord ++ tailWord_4042647).sum := by decide
  have hdescent : baseEnd_4042647 < baseStart_4042647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042654 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_4042654 : Nat := 118140960795 + 4042654 * 2 ^ 59
def prefixEnd_4042654 : Nat := 4983230072969 + 3 ^ 40 * 4042654 * 2
def baseEnd_4042654 : Nat := 2075824621821331331333179

theorem tailTrace_4042654 : CollatzResearch.WordTrace tailWord_4042654 prefixEnd_4042654 2075824621821331331333179 := by
  unfold tailWord_4042654
  simp only [CollatzResearch.WordTrace]
  refine ⟨18430963087020307897542877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98298469797441642120228677 18430963087020307897542877)
  ·
    refine ⟨6911611157632615461578579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18430963087020307897542877 6911611157632615461578579)
    ·
      refine ⟨10367416736448923192367869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6911611157632615461578579 10367416736448923192367869)
      ·
        refine ⟨3887781276168346197137951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10367416736448923192367869 3887781276168346197137951)
        ·
          refine ⟨5831671914252519295706927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3887781276168346197137951 5831671914252519295706927)
          ·
            refine ⟨8747507871378778943560391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5831671914252519295706927 8747507871378778943560391)
            ·
              refine ⟨13121261807068168415340587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8747507871378778943560391 13121261807068168415340587)
              ·
                refine ⟨19681892710602252623010881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13121261807068168415340587 19681892710602252623010881)
                ·
                  refine ⟨14761419532951689467258161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19681892710602252623010881 14761419532951689467258161)
                  ·
                    refine ⟨11071064649713767100443621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14761419532951689467258161 11071064649713767100443621)
                    ·
                      refine ⟨2075824621821331331333179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11071064649713767100443621 2075824621821331331333179)
                      ·
                        rfl

theorem cell23_4042654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_4042654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042654 prefixEnd_4042654 := by exact prefixLift 4042654
  have htrace : WordTrace (prefixWord ++ tailWord_4042654) baseStart_4042654 baseEnd_4042654 := by
    simpa [prefixWord, tailWord_4042654, baseEnd_4042654] using wordTrace_append hprefix tailTrace_4042654
  have hstable : (prefixWord ++ tailWord_4042654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042654).length < 2 ^ (prefixWord ++ tailWord_4042654).sum := by decide
  have hdescent : baseEnd_4042654 < baseStart_4042654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042657 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 2, 3, 3]
def baseStart_4042657 : Nat := 118140960795 + 4042657 * 2 ^ 59
def prefixEnd_4042657 : Nat := 4983230072969 + 3 ^ 40 * 4042657 * 2
def baseEnd_4042657 : Nat := 2075826162263294819595665

theorem tailTrace_4042657 : CollatzResearch.WordTrace tailWord_4042657 prefixEnd_4042657 2075826162263294819595665 := by
  unfold tailWord_4042657
  simp only [CollatzResearch.WordTrace]
  refine ⟨147447814115151594692702225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98298542743434396461801483 147447814115151594692702225)
  ·
    refine ⟨110585860586363696019526669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147447814115151594692702225 110585860586363696019526669)
    ·
      refine ⟨41469697719886386007322501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110585860586363696019526669 41469697719886386007322501)
      ·
        refine ⟨7775568322478697376372969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41469697719886386007322501 7775568322478697376372969)
        ·
          refine ⟨5831676241859023032279727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7775568322478697376372969 5831676241859023032279727)
          ·
            refine ⟨8747514362788534548419591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5831676241859023032279727 8747514362788534548419591)
            ·
              refine ⟨13121271544182801822629387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8747514362788534548419591 13121271544182801822629387)
              ·
                refine ⟨19681907316274202733944081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13121271544182801822629387 19681907316274202733944081)
                ·
                  refine ⟨14761430487205652050458061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19681907316274202733944081 14761430487205652050458061)
                  ·
                    refine ⟨5535536432702119518921773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14761430487205652050458061 5535536432702119518921773)
                    ·
                      refine ⟨2075826162263294819595665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5535536432702119518921773 2075826162263294819595665)
                      ·
                        rfl

theorem cell23_4042657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_4042657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042657 prefixEnd_4042657 := by exact prefixLift 4042657
  have htrace : WordTrace (prefixWord ++ tailWord_4042657) baseStart_4042657 baseEnd_4042657 := by
    simpa [prefixWord, tailWord_4042657, baseEnd_4042657] using wordTrace_append hprefix tailTrace_4042657
  have hstable : (prefixWord ++ tailWord_4042657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042657).length < 2 ^ (prefixWord ++ tailWord_4042657).sum := by decide
  have hdescent : baseEnd_4042657 < baseStart_4042657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042677 : List Nat := [1, 3, 3, 2, 1, 4, 1, 1, 2, 5]
def baseStart_4042677 : Nat := 118140960795 + 4042677 * 2 ^ 59
def prefixEnd_4042677 : Nat := 4983230072969 + 3 ^ 40 * 4042677 * 2
def baseEnd_4042677 : Nat := 691945477292128247115191

theorem tailTrace_4042677 : CollatzResearch.WordTrace tailWord_4042677 prefixEnd_4042677 691945477292128247115191 := by
  unfold tailWord_4042677
  simp only [CollatzResearch.WordTrace]
  refine ⟨147448543575079138108430285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98299029050052758738953523 147448543575079138108430285)
  ·
    refine ⟨55293203840654676790661357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147448543575079138108430285 55293203840654676790661357)
    ·
      refine ⟨20734951440245503796498009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55293203840654676790661357 20734951440245503796498009)
      ·
        refine ⟨15551213580184127847373507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20734951440245503796498009 15551213580184127847373507)
        ·
          refine ⟨23326820370276191771060261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15551213580184127847373507 23326820370276191771060261)
          ·
            refine ⟨4373778819426785957073799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23326820370276191771060261 4373778819426785957073799)
            ·
              refine ⟨6560668229140178935610699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4373778819426785957073799 6560668229140178935610699)
              ·
                refine ⟨9841002343710268403416049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6560668229140178935610699 9841002343710268403416049)
                ·
                  refine ⟨7380751757782701302562037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9841002343710268403416049 7380751757782701302562037)
                  ·
                    refine ⟨691945477292128247115191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7380751757782701302562037 691945477292128247115191)
                    ·
                      rfl

theorem cell23_4042677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_4042677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042677 prefixEnd_4042677 := by exact prefixLift 4042677
  have htrace : WordTrace (prefixWord ++ tailWord_4042677) baseStart_4042677 baseEnd_4042677 := by
    simpa [prefixWord, tailWord_4042677, baseEnd_4042677] using wordTrace_append hprefix tailTrace_4042677
  have hstable : (prefixWord ++ tailWord_4042677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042677).length < 2 ^ (prefixWord ++ tailWord_4042677).sum := by decide
  have hdescent : baseEnd_4042677 < baseStart_4042677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042680 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 1, 6, 2]
def baseStart_4042680 : Nat := 118140960795 + 4042680 * 2 ^ 59
def prefixEnd_4042680 : Nat := 4983230072969 + 3 ^ 40 * 4042680 * 2
def baseEnd_4042680 : Nat := 2075837972318348229608059

theorem tailTrace_4042680 : CollatzResearch.WordTrace tailWord_4042680 prefixEnd_4042680 2075837972318348229608059 := by
  unfold tailWord_4042680
  simp only [CollatzResearch.WordTrace]
  refine ⟨73724326497034134810394747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98299101996045513080526329 73724326497034134810394747)
  ·
    refine ⟨110586489745551202215592121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73724326497034134810394747 110586489745551202215592121)
    ·
      refine ⟨82939867309163401661694091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110586489745551202215592121 82939867309163401661694091)
      ·
        refine ⟨124409800963745102492541137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82939867309163401661694091 124409800963745102492541137)
        ·
          refine ⟨93307350722808826869405853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124409800963745102492541137 93307350722808826869405853)
          ·
            refine ⟨34990256521053310076027195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93307350722808826869405853 34990256521053310076027195)
            ·
              refine ⟨52485384781579965114040793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34990256521053310076027195 52485384781579965114040793)
              ·
                refine ⟨39364038586184973835530595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52485384781579965114040793 39364038586184973835530595)
                ·
                  refine ⟨59046057879277460753295893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39364038586184973835530595 59046057879277460753295893)
                  ·
                    refine ⟨2767783963091130972810745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59046057879277460753295893 2767783963091130972810745)
                    ·
                      refine ⟨2075837972318348229608059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2767783963091130972810745 2075837972318348229608059)
                      ·
                        rfl

theorem cell23_4042680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 6, 2].length) (baseStart_4042680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042680 prefixEnd_4042680 := by exact prefixLift 4042680
  have htrace : WordTrace (prefixWord ++ tailWord_4042680) baseStart_4042680 baseEnd_4042680 := by
    simpa [prefixWord, tailWord_4042680, baseEnd_4042680] using wordTrace_append hprefix tailTrace_4042680
  have hstable : (prefixWord ++ tailWord_4042680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042680).length < 2 ^ (prefixWord ++ tailWord_4042680).sum := by decide
  have hdescent : baseEnd_4042680 < baseStart_4042680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042703 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 8]
def baseStart_4042703 : Nat := 118140960795 + 4042703 * 2 ^ 59
def prefixEnd_4042703 : Nat := 4983230072969 + 3 ^ 40 * 4042703 * 2
def baseEnd_4042703 : Nat := 230649975819266848846717

theorem tailTrace_4042703 : CollatzResearch.WordTrace tailWord_4042703 prefixEnd_4042703 230649975819266848846717 := by
  unfold tailWord_4042703
  simp only [CollatzResearch.WordTrace]
  refine ⟨147449491872984944548876763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98299661248656629699251175 147449491872984944548876763)
  ·
    refine ⟨221174237809477416823315145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147449491872984944548876763 221174237809477416823315145)
    ·
      refine ⟨165880678357108062617486359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221174237809477416823315145 165880678357108062617486359)
      ·
        refine ⟨248821017535662093926229539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165880678357108062617486359 248821017535662093926229539)
        ·
          refine ⟨373231526303493140889344309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248821017535662093926229539 373231526303493140889344309)
          ·
            refine ⟨34990455590952481958376029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 373231526303493140889344309 34990455590952481958376029)
            ·
              refine ⟨13121420846607180734391011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34990455590952481958376029 13121420846607180734391011)
              ·
                refine ⟨19682131269910771101586517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13121420846607180734391011 19682131269910771101586517)
                ·
                  refine ⟨230649975819266848846717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19682131269910771101586517 230649975819266848846717)
                  ·
                    rfl

theorem cell23_4042703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 8].length) (baseStart_4042703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042703 prefixEnd_4042703 := by exact prefixLift 4042703
  have htrace : WordTrace (prefixWord ++ tailWord_4042703) baseStart_4042703 baseEnd_4042703 := by
    simpa [prefixWord, tailWord_4042703, baseEnd_4042703] using wordTrace_append hprefix tailTrace_4042703
  have hstable : (prefixWord ++ tailWord_4042703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042703).length < 2 ^ (prefixWord ++ tailWord_4042703).sum := by decide
  have hdescent : baseEnd_4042703 < baseStart_4042703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042730 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_4042730 : Nat := 118140960795 + 4042730 * 2 ^ 59
def prefixEnd_4042730 : Nat := 4983230072969 + 3 ^ 40 * 4042730 * 2
def baseEnd_4042730 : Nat := 2075863646351073033982829

theorem tailTrace_4042730 : CollatzResearch.WordTrace tailWord_4042730 prefixEnd_4042730 2075863646351073033982829 := by
  unfold tailWord_4042730
  simp only [CollatzResearch.WordTrace]
  refine ⟨36862619160971782040027411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98300317762591418773406429 36862619160971782040027411)
  ·
    refine ⟨55293928741457673060041117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36862619160971782040027411 55293928741457673060041117)
    ·
      refine ⟨20735223278046627397515419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55293928741457673060041117 20735223278046627397515419)
      ·
        refine ⟨31102834917069941096273129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20735223278046627397515419 31102834917069941096273129)
        ·
          refine ⟨23327126187802455822204847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31102834917069941096273129 23327126187802455822204847)
          ·
            refine ⟨34990689281703683733307271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23327126187802455822204847 34990689281703683733307271)
            ·
              refine ⟨52486033922555525599960907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34990689281703683733307271 52486033922555525599960907)
              ·
                refine ⟨78729050883833288399941361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52486033922555525599960907 78729050883833288399941361)
                ·
                  refine ⟨59046788162874966299956021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78729050883833288399941361 59046788162874966299956021)
                  ·
                    refine ⟨5535636390269528090620877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59046788162874966299956021 5535636390269528090620877)
                    ·
                      refine ⟨2075863646351073033982829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5535636390269528090620877 2075863646351073033982829)
                      ·
                        rfl

theorem cell23_4042730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_4042730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042730 prefixEnd_4042730 := by exact prefixLift 4042730
  have htrace : WordTrace (prefixWord ++ tailWord_4042730) baseStart_4042730 baseEnd_4042730 := by
    simpa [prefixWord, tailWord_4042730, baseEnd_4042730] using wordTrace_append hprefix tailTrace_4042730
  have hstable : (prefixWord ++ tailWord_4042730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042730).length < 2 ^ (prefixWord ++ tailWord_4042730).sum := by decide
  have hdescent : baseEnd_4042730 < baseStart_4042730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042757 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 4, 3, 2]
def baseStart_4042757 : Nat := 118140960795 + 4042757 * 2 ^ 59
def prefixEnd_4042757 : Nat := 4983230072969 + 3 ^ 40 * 4042757 * 2
def baseEnd_4042757 : Nat := 2075877510328744428345205

theorem tailTrace_4042757 : CollatzResearch.WordTrace tailWord_4042757 prefixEnd_4042757 2075877510328744428345205 := by
  unfold tailWord_4042757
  simp only [CollatzResearch.WordTrace]
  refine ⟨147451461414789311771342525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98300974276526207847561683 147451461414789311771342525)
  ·
    refine ⟨55294298030545991914253447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147451461414789311771342525 55294298030545991914253447)
    ·
      refine ⟨82941447045818987871380171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55294298030545991914253447 82941447045818987871380171)
      ·
        refine ⟨124412170568728481807070257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82941447045818987871380171 124412170568728481807070257)
        ·
          refine ⟨93309127926546361355302693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124412170568728481807070257 93309127926546361355302693)
          ·
            refine ⟨17495461486227442754119255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93309127926546361355302693 17495461486227442754119255)
            ·
              refine ⟨26243192229341164131178883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17495461486227442754119255 26243192229341164131178883)
              ·
                refine ⟨39364788344011746196768325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26243192229341164131178883 39364788344011746196768325)
                ·
                  refine ⟨7380897814502202411894061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39364788344011746196768325 7380897814502202411894061)
                  ·
                    refine ⟨2767836680438325904460273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7380897814502202411894061 2767836680438325904460273)
                    ·
                      refine ⟨2075877510328744428345205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2767836680438325904460273 2075877510328744428345205)
                      ·
                        rfl

theorem cell23_4042757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 3, 2].length) (baseStart_4042757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042757 prefixEnd_4042757 := by exact prefixLift 4042757
  have htrace : WordTrace (prefixWord ++ tailWord_4042757) baseStart_4042757 baseEnd_4042757 := by
    simpa [prefixWord, tailWord_4042757, baseEnd_4042757] using wordTrace_append hprefix tailTrace_4042757
  have hstable : (prefixWord ++ tailWord_4042757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042757).length < 2 ^ (prefixWord ++ tailWord_4042757).sum := by decide
  have hdescent : baseEnd_4042757 < baseStart_4042757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042800 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 4]
def baseStart_4042800 : Nat := 118140960795 + 4042800 * 2 ^ 59
def prefixEnd_4042800 : Nat := 4983230072969 + 3 ^ 40 * 4042800 * 2
def baseEnd_4042800 : Nat := 2075899589996887760107507

theorem tailTrace_4042800 : CollatzResearch.WordTrace tailWord_4042800 prefixEnd_4042800 2075899589996887760107507 := by
  unfold tailWord_4042800
  simp only [CollatzResearch.WordTrace]
  refine ⟨73726514876816765057578927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98302019835755686743438569 73726514876816765057578927)
  ·
    refine ⟨110589772315225147586368391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73726514876816765057578927 110589772315225147586368391)
    ·
      refine ⟨165884658472837721379552587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110589772315225147586368391 165884658472837721379552587)
      ·
        refine ⟨248826987709256582069328881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165884658472837721379552587 248826987709256582069328881)
        ·
          refine ⟨186620240781942436551996661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248826987709256582069328881 186620240781942436551996661)
          ·
            refine ⟨17495647573307103426749687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186620240781942436551996661 17495647573307103426749687)
            ·
              refine ⟨26243471359960655140124531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17495647573307103426749687 26243471359960655140124531)
              ·
                refine ⟨39365207039940982710186797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26243471359960655140124531 39365207039940982710186797)
                ·
                  refine ⟨14761952639977868516320049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39365207039940982710186797 14761952639977868516320049)
                  ·
                    refine ⟨11071464479983401387240037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14761952639977868516320049 11071464479983401387240037)
                    ·
                      refine ⟨2075899589996887760107507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11071464479983401387240037 2075899589996887760107507)
                      ·
                        rfl

theorem cell23_4042800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_4042800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042800 prefixEnd_4042800 := by exact prefixLift 4042800
  have htrace : WordTrace (prefixWord ++ tailWord_4042800) baseStart_4042800 baseEnd_4042800 := by
    simpa [prefixWord, tailWord_4042800, baseEnd_4042800] using wordTrace_append hprefix tailTrace_4042800
  have hstable : (prefixWord ++ tailWord_4042800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042800).length < 2 ^ (prefixWord ++ tailWord_4042800).sum := by decide
  have hdescent : baseEnd_4042800 < baseStart_4042800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042807 : List Nat := [1, 1, 3, 1, 2, 2, 2, 5, 1, 2, 3]
def baseStart_4042807 : Nat := 118140960795 + 4042807 * 2 ^ 59
def prefixEnd_4042807 : Nat := 4983230072969 + 3 ^ 40 * 4042807 * 2
def baseEnd_4042807 : Nat := 2075903184361469232719975

theorem tailTrace_4042807 : CollatzResearch.WordTrace tailWord_4042807 prefixEnd_4042807 2075903184361469232719975 := by
  unfold tailWord_4042807
  simp only [CollatzResearch.WordTrace]
  refine ⟨147453285064608170310662675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98302190043072113540441783 147453285064608170310662675)
  ·
    refine ⟨221179927596912255465994013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147453285064608170310662675 221179927596912255465994013)
    ·
      refine ⟨82942472848842095799747755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221179927596912255465994013 82942472848842095799747755)
      ·
        refine ⟨124413709273263143699621633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82942472848842095799747755 124413709273263143699621633)
        ·
          refine ⟨93310281954947357774716225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124413709273263143699621633 93310281954947357774716225)
          ·
            refine ⟨69982711466210518331037169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93310281954947357774716225 69982711466210518331037169)
            ·
              refine ⟨52487033599657888748277877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69982711466210518331037169 52487033599657888748277877)
              ·
                refine ⟨4920659399967927070151051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52487033599657888748277877 4920659399967927070151051)
                ·
                  refine ⟨7380989099951890605226577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4920659399967927070151051 7380989099951890605226577)
                  ·
                    refine ⟨5535741824963917953919933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7380989099951890605226577 5535741824963917953919933)
                    ·
                      refine ⟨2075903184361469232719975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5535741824963917953919933 2075903184361469232719975)
                      ·
                        rfl

theorem cell23_4042807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 2, 3].length) (baseStart_4042807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042807 prefixEnd_4042807 := by exact prefixLift 4042807
  have htrace : WordTrace (prefixWord ++ tailWord_4042807) baseStart_4042807 baseEnd_4042807 := by
    simpa [prefixWord, tailWord_4042807, baseEnd_4042807] using wordTrace_append hprefix tailTrace_4042807
  have hstable : (prefixWord ++ tailWord_4042807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042807).length < 2 ^ (prefixWord ++ tailWord_4042807).sum := by decide
  have hdescent : baseEnd_4042807 < baseStart_4042807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042834 : List Nat := [3, 2, 2, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_4042834 : Nat := 118140960795 + 4042834 * 2 ^ 59
def prefixEnd_4042834 : Nat := 4983230072969 + 3 ^ 40 * 4042834 * 2
def baseEnd_4042834 : Nat := 2075917048339140627082351

theorem tailTrace_4042834 : CollatzResearch.WordTrace tailWord_4042834 prefixEnd_4042834 2075917048339140627082351 := by
  unfold tailWord_4042834
  simp only [CollatzResearch.WordTrace]
  refine ⟨36863567458877588480473889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98302846557006902614597037 36863567458877588480473889)
  ·
    refine ⟨27647675594158191360355417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36863567458877588480473889 27647675594158191360355417)
    ·
      refine ⟨20735756695618643520266563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27647675594158191360355417 20735756695618643520266563)
      ·
        refine ⟨31103635043427965280399845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20735756695618643520266563 31103635043427965280399845)
        ·
          refine ⟨5831931570642743490074971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31103635043427965280399845 5831931570642743490074971)
          ·
            refine ⟨8747897355964115235112457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5831931570642743490074971 8747897355964115235112457)
            ·
              refine ⟨6560923016973086426334343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8747897355964115235112457 6560923016973086426334343)
              ·
                refine ⟨9841384525459629639501515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6560923016973086426334343 9841384525459629639501515)
                ·
                  refine ⟨14762076788189444459252273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9841384525459629639501515 14762076788189444459252273)
                  ·
                    refine ⟨11071557591142083344439205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14762076788189444459252273 11071557591142083344439205)
                    ·
                      refine ⟨2075917048339140627082351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11071557591142083344439205 2075917048339140627082351)
                      ·
                        rfl

theorem cell23_4042834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_4042834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042834 prefixEnd_4042834 := by exact prefixLift 4042834
  have htrace : WordTrace (prefixWord ++ tailWord_4042834) baseStart_4042834 baseEnd_4042834 := by
    simpa [prefixWord, tailWord_4042834, baseEnd_4042834] using wordTrace_append hprefix tailTrace_4042834
  have hstable : (prefixWord ++ tailWord_4042834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042834).length < 2 ^ (prefixWord ++ tailWord_4042834).sum := by decide
  have hdescent : baseEnd_4042834 < baseStart_4042834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042837 : List Nat := [1, 3, 2, 2, 1, 3, 1, 3, 1, 3, 3]
def baseStart_4042837 : Nat := 118140960795 + 4042837 * 2 ^ 59
def prefixEnd_4042837 : Nat := 4983230072969 + 3 ^ 40 * 4042837 * 2
def baseEnd_4042837 : Nat := 2075918588781104115344837

theorem tailTrace_4042837 : CollatzResearch.WordTrace tailWord_4042837 prefixEnd_4042837 2075918588781104115344837 := by
  unfold tailWord_4042837
  simp only [CollatzResearch.WordTrace]
  refine ⟨147454379254499485434254765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98302919502999656956169843 147454379254499485434254765)
  ·
    refine ⟨55295392220437307037845537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147454379254499485434254765 55295392220437307037845537)
    ·
      refine ⟨41471544165327980278384153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55295392220437307037845537 41471544165327980278384153)
      ·
        refine ⟨31103658123995985208788115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41471544165327980278384153 31103658123995985208788115)
        ·
          refine ⟨46655487185993977813182173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31103658123995985208788115 46655487185993977813182173)
          ·
            refine ⟨17495807694747741679943315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46655487185993977813182173 17495807694747741679943315)
            ·
              refine ⟨26243711542121612519914973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17495807694747741679943315 26243711542121612519914973)
              ·
                refine ⟨9841391828295604694968115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26243711542121612519914973 9841391828295604694968115)
                ·
                  refine ⟨14762087742443407042452173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9841391828295604694968115 14762087742443407042452173)
                  ·
                    refine ⟨5535782903416277640919565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14762087742443407042452173 5535782903416277640919565)
                    ·
                      refine ⟨2075918588781104115344837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5535782903416277640919565 2075918588781104115344837)
                      ·
                        rfl

theorem cell23_4042837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_4042837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042837 prefixEnd_4042837 := by exact prefixLift 4042837
  have htrace : WordTrace (prefixWord ++ tailWord_4042837) baseStart_4042837 baseEnd_4042837 := by
    simpa [prefixWord, tailWord_4042837, baseEnd_4042837] using wordTrace_append hprefix tailTrace_4042837
  have hstable : (prefixWord ++ tailWord_4042837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042837).length < 2 ^ (prefixWord ++ tailWord_4042837).sum := by decide
  have hdescent : baseEnd_4042837 < baseStart_4042837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042838 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_4042838 : Nat := 118140960795 + 4042838 * 2 ^ 59
def prefixEnd_4042838 : Nat := 4983230072969 + 3 ^ 40 * 4042838 * 2
def baseEnd_4042838 : Nat := 2075919102261758611432333

theorem tailTrace_4042838 : CollatzResearch.WordTrace tailWord_4042838 prefixEnd_4042838 2075919102261758611432333 := by
  unfold tailWord_4042838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9215900982968491412815073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98302943818330575070027445 9215900982968491412815073)
  ·
    refine ⟨6911925737226368559611305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9215900982968491412815073 6911925737226368559611305)
    ·
      refine ⟨5183944302919776419708479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6911925737226368559611305 5183944302919776419708479)
      ·
        refine ⟨7775916454379664629562719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5183944302919776419708479 7775916454379664629562719)
        ·
          refine ⟨11663874681569496944344079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7775916454379664629562719 11663874681569496944344079)
          ·
            refine ⟨17495812022354245416516119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11663874681569496944344079 17495812022354245416516119)
            ·
              refine ⟨26243718033531368124774179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17495812022354245416516119 26243718033531368124774179)
              ·
                refine ⟨39365577050297052187161269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26243718033531368124774179 39365577050297052187161269)
                ·
                  refine ⟨3690522848465348642546369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39365577050297052187161269 3690522848465348642546369)
                  ·
                    refine ⟨2767892136349011481909777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3690522848465348642546369 2767892136349011481909777)
                    ·
                      refine ⟨2075919102261758611432333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2767892136349011481909777 2075919102261758611432333)
                      ·
                        rfl

theorem cell23_4042838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_4042838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042838 prefixEnd_4042838 := by exact prefixLift 4042838
  have htrace : WordTrace (prefixWord ++ tailWord_4042838) baseStart_4042838 baseEnd_4042838 := by
    simpa [prefixWord, tailWord_4042838, baseEnd_4042838] using wordTrace_append hprefix tailTrace_4042838
  have hstable : (prefixWord ++ tailWord_4042838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042838).length < 2 ^ (prefixWord ++ tailWord_4042838).sum := by decide
  have hdescent : baseEnd_4042838 < baseStart_4042838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042858 : List Nat := [3, 1, 3, 2, 3, 2, 2, 1, 1, 2, 3]
def baseStart_4042858 : Nat := 118140960795 + 4042858 * 2 ^ 59
def prefixEnd_4042858 : Nat := 4983230072969 + 3 ^ 40 * 4042858 * 2
def baseEnd_4042858 : Nat := 2075929371874848533182241

theorem tailTrace_4042858 : CollatzResearch.WordTrace tailWord_4042858 prefixEnd_4042858 2075929371874848533182241 := by
  unfold tailWord_4042858
  simp only [CollatzResearch.WordTrace]
  refine ⟨36863786296855851505192307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98303430124948937347179485 36863786296855851505192307)
  ·
    refine ⟨55295679445283777257788461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36863786296855851505192307 55295679445283777257788461)
    ·
      refine ⟨20735879791981416471670673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55295679445283777257788461 20735879791981416471670673)
      ·
        refine ⟨15551909843986062353753005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20735879791981416471670673 15551909843986062353753005)
        ·
          refine ⟨5831966191494773382657377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15551909843986062353753005 5831966191494773382657377)
          ·
            refine ⟨4373974643621080036993033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5831966191494773382657377 4373974643621080036993033)
            ·
              refine ⟨3280480982715810027744775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4373974643621080036993033 3280480982715810027744775)
              ·
                refine ⟨4920721474073715041617163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3280480982715810027744775 4920721474073715041617163)
                ·
                  refine ⟨7381082211110572562425745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4920721474073715041617163 7381082211110572562425745)
                  ·
                    refine ⟨5535811658332929421819309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7381082211110572562425745 5535811658332929421819309)
                    ·
                      refine ⟨2075929371874848533182241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5535811658332929421819309 2075929371874848533182241)
                      ·
                        rfl

theorem cell23_4042858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_4042858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042858 prefixEnd_4042858 := by exact prefixLift 4042858
  have htrace : WordTrace (prefixWord ++ tailWord_4042858) baseStart_4042858 baseEnd_4042858 := by
    simpa [prefixWord, tailWord_4042858, baseEnd_4042858] using wordTrace_append hprefix tailTrace_4042858
  have hstable : (prefixWord ++ tailWord_4042858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042858).length < 2 ^ (prefixWord ++ tailWord_4042858).sum := by decide
  have hdescent : baseEnd_4042858 < baseStart_4042858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042871 : List Nat := [1, 1, 3, 1, 1, 7, 1, 2, 2, 1, 3]
def baseStart_4042871 : Nat := 118140960795 + 4042871 * 2 ^ 59
def prefixEnd_4042871 : Nat := 4983230072969 + 3 ^ 40 * 4042871 * 2
def baseEnd_4042871 : Nat := 2075936047123356982319681

theorem tailTrace_4042871 : CollatzResearch.WordTrace tailWord_4042871 prefixEnd_4042871 2075936047123356982319681 := by
  unfold tailWord_4042871
  simp only [CollatzResearch.WordTrace]
  refine ⟨147455619336376309240992467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98303746224250872827328311 147455619336376309240992467)
  ·
    refine ⟨221183429004564463861488701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147455619336376309240992467 221183429004564463861488701)
    ·
      refine ⟨82943785876711673948058263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221183429004564463861488701 82943785876711673948058263)
      ·
        refine ⟨124415678815067510922087395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82943785876711673948058263 124415678815067510922087395)
        ·
          refine ⟨186623518222601266383131093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124415678815067510922087395 186623518222601266383131093)
          ·
            refine ⟨4373988708342217180854635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 186623518222601266383131093 4373988708342217180854635)
            ·
              refine ⟨6560983062513325771281953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4373988708342217180854635 6560983062513325771281953)
              ·
                refine ⟨4920737296884994328461465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6560983062513325771281953 4920737296884994328461465)
                ·
                  refine ⟨3690552972663745746346099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4920737296884994328461465 3690552972663745746346099)
                  ·
                    refine ⟨5535829458995618619519149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3690552972663745746346099 5535829458995618619519149)
                    ·
                      refine ⟨2075936047123356982319681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5535829458995618619519149 2075936047123356982319681)
                      ·
                        rfl

theorem cell23_4042871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 1, 3].length) (baseStart_4042871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042871 prefixEnd_4042871 := by exact prefixLift 4042871
  have htrace : WordTrace (prefixWord ++ tailWord_4042871) baseStart_4042871 baseEnd_4042871 := by
    simpa [prefixWord, tailWord_4042871, baseEnd_4042871] using wordTrace_append hprefix tailTrace_4042871
  have hstable : (prefixWord ++ tailWord_4042871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042871).length < 2 ^ (prefixWord ++ tailWord_4042871).sum := by decide
  have hdescent : baseEnd_4042871 < baseStart_4042871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042880 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 5]
def baseStart_4042880 : Nat := 118140960795 + 4042880 * 2 ^ 59
def prefixEnd_4042880 : Nat := 4983230072969 + 3 ^ 40 * 4042880 * 2
def baseEnd_4042880 : Nat := 2075940668449247447107139

theorem tailTrace_4042880 : CollatzResearch.WordTrace tailWord_4042880 prefixEnd_4042880 2075940668449247447107139 := by
  unfold tailWord_4042880
  simp only [CollatzResearch.WordTrace]
  refine ⟨73727973796671851889035047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98303965062229135852046729 73727973796671851889035047)
  ·
    refine ⟨110591960695007777833552571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73727973796671851889035047 110591960695007777833552571)
    ·
      refine ⟨165887941042511666750328857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110591960695007777833552571 165887941042511666750328857)
      ·
        refine ⟨124415955781883750062746643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165887941042511666750328857 124415955781883750062746643)
        ·
          refine ⟨186623933672825625094119965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124415955781883750062746643 186623933672825625094119965)
          ·
            refine ⟨69983975127309609410294987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186623933672825625094119965 69983975127309609410294987)
            ·
              refine ⟨104975962690964414115442481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69983975127309609410294987 104975962690964414115442481)
              ·
                refine ⟨78731972018223310586581861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104975962690964414115442481 78731972018223310586581861)
                ·
                  refine ⟨14762244753416870734984099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78731972018223310586581861 14762244753416870734984099)
                  ·
                    refine ⟨22143367130125306102476149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14762244753416870734984099 22143367130125306102476149)
                    ·
                      refine ⟨2075940668449247447107139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22143367130125306102476149 2075940668449247447107139)
                      ·
                        rfl

theorem cell23_4042880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_4042880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042880 prefixEnd_4042880 := by exact prefixLift 4042880
  have htrace : WordTrace (prefixWord ++ tailWord_4042880) baseStart_4042880 baseEnd_4042880 := by
    simpa [prefixWord, tailWord_4042880, baseEnd_4042880] using wordTrace_append hprefix tailTrace_4042880
  have hstable : (prefixWord ++ tailWord_4042880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042880).length < 2 ^ (prefixWord ++ tailWord_4042880).sum := by decide
  have hdescent : baseEnd_4042880 < baseStart_4042880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042888 : List Nat := [2, 1, 3, 4, 1, 2, 3, 1, 2, 1, 3]
def baseStart_4042888 : Nat := 118140960795 + 4042888 * 2 ^ 59
def prefixEnd_4042888 : Nat := 4983230072969 + 3 ^ 40 * 4042888 * 2
def baseEnd_4042888 : Nat := 2075944776294483415807103

theorem tailTrace_4042888 : CollatzResearch.WordTrace tailWord_4042888 prefixEnd_4042888 2075944776294483415807103 := by
  unfold tailWord_4042888
  simp only [CollatzResearch.WordTrace]
  refine ⟨73728119688657360572180659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98304159584876480762907545 73728119688657360572180659)
  ·
    refine ⟨110592179532986040858270989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73728119688657360572180659 110592179532986040858270989)
    ·
      refine ⟨41472067324869765321851621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110592179532986040858270989 41472067324869765321851621)
      ·
        refine ⟨7776012623413080997847179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41472067324869765321851621 7776012623413080997847179)
        ·
          refine ⟨11664018935119621496770769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7776012623413080997847179 11664018935119621496770769)
          ·
            refine ⟨8748014201339716122578077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11664018935119621496770769 8748014201339716122578077)
            ·
              refine ⟨3280505325502393545966779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8748014201339716122578077 3280505325502393545966779)
              ·
                refine ⟨4920757988253590318950169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3280505325502393545966779 4920757988253590318950169)
                ·
                  refine ⟨3690568491190192739212627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4920757988253590318950169 3690568491190192739212627)
                  ·
                    refine ⟨5535852736785289108818941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3690568491190192739212627 5535852736785289108818941)
                    ·
                      refine ⟨2075944776294483415807103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5535852736785289108818941 2075944776294483415807103)
                      ·
                        rfl

theorem cell23_4042888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_4042888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042888 prefixEnd_4042888 := by exact prefixLift 4042888
  have htrace : WordTrace (prefixWord ++ tailWord_4042888) baseStart_4042888 baseEnd_4042888 := by
    simpa [prefixWord, tailWord_4042888, baseEnd_4042888] using wordTrace_append hprefix tailTrace_4042888
  have hstable : (prefixWord ++ tailWord_4042888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042888).length < 2 ^ (prefixWord ++ tailWord_4042888).sum := by decide
  have hdescent : baseEnd_4042888 < baseStart_4042888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042911 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 4, 2, 2]
def baseStart_4042911 : Nat := 118140960795 + 4042911 * 2 ^ 59
def prefixEnd_4042911 : Nat := 4983230072969 + 3 ^ 40 * 4042911 * 2
def baseEnd_4042911 : Nat := 2075956586349536825819497

theorem tailTrace_4042911 : CollatzResearch.WordTrace tailWord_4042911 prefixEnd_4042911 2075956586349536825819497 := by
  unfold tailWord_4042911
  simp only [CollatzResearch.WordTrace]
  refine ⟨147457078256231396072448587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98304718837487597381632391 147457078256231396072448587)
  ·
    refine ⟨221185617384347094108672881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147457078256231396072448587 221185617384347094108672881)
    ·
      refine ⟨165889213038260320581504661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221185617384347094108672881 165889213038260320581504661)
      ·
        refine ⟨7776056861168452527258031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165889213038260320581504661 7776056861168452527258031)
        ·
          refine ⟨11664085291752678790887047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7776056861168452527258031 11664085291752678790887047)
          ·
            refine ⟨17496127937629018186330571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11664085291752678790887047 17496127937629018186330571)
            ·
              refine ⟨26244191906443527279495857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17496127937629018186330571 26244191906443527279495857)
              ·
                refine ⟨19683143929832645459621893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26244191906443527279495857 19683143929832645459621893)
                ·
                  refine ⟨3690589486843621023679105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19683143929832645459621893 3690589486843621023679105)
                  ·
                    refine ⟨2767942115132715767759329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3690589486843621023679105 2767942115132715767759329)
                    ·
                      refine ⟨2075956586349536825819497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2767942115132715767759329 2075956586349536825819497)
                      ·
                        rfl

theorem cell23_4042911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_4042911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042911 prefixEnd_4042911 := by exact prefixLift 4042911
  have htrace : WordTrace (prefixWord ++ tailWord_4042911) baseStart_4042911 baseEnd_4042911 := by
    simpa [prefixWord, tailWord_4042911, baseEnd_4042911] using wordTrace_append hprefix tailTrace_4042911
  have hstable : (prefixWord ++ tailWord_4042911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042911).length < 2 ^ (prefixWord ++ tailWord_4042911).sum := by decide
  have hdescent : baseEnd_4042911 < baseStart_4042911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042914 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_4042914 : Nat := 118140960795 + 4042914 * 2 ^ 59
def prefixEnd_4042914 : Nat := 4983230072969 + 3 ^ 40 * 4042914 * 2
def baseEnd_4042914 : Nat := 2075958126791500314081983

theorem tailTrace_4042914 : CollatzResearch.WordTrace tailWord_4042914 prefixEnd_4042914 2075958126791500314081983 := by
  unfold tailWord_4042914
  simp only [CollatzResearch.WordTrace]
  refine ⟨36864296918805131896201949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98304791783480351723205197 36864296918805131896201949)
  ·
    refine ⟨13824111344551924461075731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36864296918805131896201949 13824111344551924461075731)
    ·
      refine ⟨20736167016827886691613597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13824111344551924461075731 20736167016827886691613597)
      ·
        refine ⟨7776062631310457509355099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20736167016827886691613597 7776062631310457509355099)
        ·
          refine ⟨11664093946965686264032649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7776062631310457509355099 11664093946965686264032649)
          ·
            refine ⟨8748070460224264698024487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11664093946965686264032649 8748070460224264698024487)
            ·
              refine ⟨13122105690336397047036731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8748070460224264698024487 13122105690336397047036731)
              ·
                refine ⟨19683158535504595570555097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13122105690336397047036731 19683158535504595570555097)
                ·
                  refine ⟨14762368901628446677916323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19683158535504595570555097 14762368901628446677916323)
                  ·
                    refine ⟨22143553352442670016874485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14762368901628446677916323 22143553352442670016874485)
                    ·
                      refine ⟨2075958126791500314081983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22143553352442670016874485 2075958126791500314081983)
                      ·
                        rfl

theorem cell23_4042914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_4042914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042914 prefixEnd_4042914 := by exact prefixLift 4042914
  have htrace : WordTrace (prefixWord ++ tailWord_4042914) baseStart_4042914 baseEnd_4042914 := by
    simpa [prefixWord, tailWord_4042914, baseEnd_4042914] using wordTrace_append hprefix tailTrace_4042914
  have hstable : (prefixWord ++ tailWord_4042914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042914).length < 2 ^ (prefixWord ++ tailWord_4042914).sum := by decide
  have hdescent : baseEnd_4042914 < baseStart_4042914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042945 : List Nat := [1, 2, 6, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_4042945 : Nat := 118140960795 + 4042945 * 2 ^ 59
def prefixEnd_4042945 : Nat := 4983230072969 + 3 ^ 40 * 4042945 * 2
def baseEnd_4042945 : Nat := 2075974044691789692794341

theorem tailTrace_4042945 : CollatzResearch.WordTrace tailWord_4042945 prefixEnd_4042945 2075974044691789692794341 := by
  unfold tailWord_4042945
  simp only [CollatzResearch.WordTrace]
  refine ⟨147458318338108219879186289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98305545558738813252790859 147458318338108219879186289)
  ·
    refine ⟨110593738753581164909389717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147458318338108219879186289 110593738753581164909389717)
    ·
      refine ⟨5184081504074117105127643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110593738753581164909389717 5184081504074117105127643)
      ·
        refine ⟨7776122256111175657691465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5184081504074117105127643 7776122256111175657691465)
        ·
          refine ⟨5832091692083381743268599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7776122256111175657691465 5832091692083381743268599)
          ·
            refine ⟨8748137538125072614902899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5832091692083381743268599 8748137538125072614902899)
            ·
              refine ⟨13122206307187608922354349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8748137538125072614902899 13122206307187608922354349)
              ·
                refine ⟨4920827365195353345882881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13122206307187608922354349 4920827365195353345882881)
                ·
                  refine ⟨3690620523896515009412161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4920827365195353345882881 3690620523896515009412161)
                  ·
                    refine ⟨2767965392922386257059121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3690620523896515009412161 2767965392922386257059121)
                    ·
                      refine ⟨2075974044691789692794341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2767965392922386257059121 2075974044691789692794341)
                      ·
                        rfl

theorem cell23_4042945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_4042945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042945 prefixEnd_4042945 := by exact prefixLift 4042945
  have htrace : WordTrace (prefixWord ++ tailWord_4042945) baseStart_4042945 baseEnd_4042945 := by
    simpa [prefixWord, tailWord_4042945, baseEnd_4042945] using wordTrace_append hprefix tailTrace_4042945
  have hstable : (prefixWord ++ tailWord_4042945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042945).length < 2 ^ (prefixWord ++ tailWord_4042945).sum := by decide
  have hdescent : baseEnd_4042945 < baseStart_4042945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4042984 : List Nat := [2, 1, 4, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_4042984 : Nat := 118140960795 + 4042984 * 2 ^ 59
def prefixEnd_4042984 : Nat := 4983230072969 + 3 ^ 40 * 4042984 * 2
def baseEnd_4042984 : Nat := 2075994070437315040206661

theorem tailTrace_4042984 : CollatzResearch.WordTrace tailWord_4042984 prefixEnd_4042984 2075994070437315040206661 := by
  unfold tailWord_4042984
  simp only [CollatzResearch.WordTrace]
  refine ⟨73729870392483464769928003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98306493856644619693237337 73729870392483464769928003)
  ·
    refine ⟨110594805588725197154892005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73729870392483464769928003 110594805588725197154892005)
    ·
      refine ⟨20736526047885974466542251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110594805588725197154892005 20736526047885974466542251)
      ·
        refine ⟨31104789071828961699813377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20736526047885974466542251 31104789071828961699813377)
        ·
          refine ⟨23328591803871721274860033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31104789071828961699813377 23328591803871721274860033)
          ·
            refine ⟨17496443852903790956145025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23328591803871721274860033 17496443852903790956145025)
            ·
              refine ⟨13122332889677843217108769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17496443852903790956145025 13122332889677843217108769)
              ·
                refine ⟨9841749667258382412831577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13122332889677843217108769 9841749667258382412831577)
                ·
                  refine ⟨7381312250443786809623683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9841749667258382412831577 7381312250443786809623683)
                  ·
                    refine ⟨11071968375665680214435525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7381312250443786809623683 11071968375665680214435525)
                    ·
                      refine ⟨2075994070437315040206661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11071968375665680214435525 2075994070437315040206661)
                      ·
                        rfl

theorem cell23_4042984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_4042984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4042984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4042984 prefixEnd_4042984 := by exact prefixLift 4042984
  have htrace : WordTrace (prefixWord ++ tailWord_4042984) baseStart_4042984 baseEnd_4042984 := by
    simpa [prefixWord, tailWord_4042984, baseEnd_4042984] using wordTrace_append hprefix tailTrace_4042984
  have hstable : (prefixWord ++ tailWord_4042984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4042984).length < 2 ^ (prefixWord ++ tailWord_4042984).sum := by decide
  have hdescent : baseEnd_4042984 < baseStart_4042984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4042984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043007 : List Nat := [1, 1, 2, 2, 1, 4, 1, 5, 6]
def baseStart_4043007 : Nat := 118140960795 + 4043007 * 2 ^ 59
def prefixEnd_4043007 : Nat := 4983230072969 + 3 ^ 40 * 4043007 * 2
def baseEnd_4043007 : Nat := 230667320054707605579895

theorem tailTrace_4043007 : CollatzResearch.WordTrace tailWord_4043007 prefixEnd_4043007 230667320054707605579895 := by
  unfold tailWord_4043007
  simp only [CollatzResearch.WordTrace]
  refine ⟨147460579663883604467943275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98307053109255736311962183 147460579663883604467943275)
  ·
    refine ⟨221190869495825406701914913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147460579663883604467943275 221190869495825406701914913)
    ·
      refine ⟨165893152121869055026436185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221190869495825406701914913 165893152121869055026436185)
      ·
        refine ⟨124419864091401791269827139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165893152121869055026436185 124419864091401791269827139)
        ·
          refine ⟨186629796137102686904740709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124419864091401791269827139 186629796137102686904740709)
          ·
            refine ⟨34993086775706753794638883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186629796137102686904740709 34993086775706753794638883)
            ·
              refine ⟨52489630163560130691958325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34993086775706753794638883 52489630163560130691958325)
              ·
                refine ⟨4920902827833762252371093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52489630163560130691958325 4920902827833762252371093)
                ·
                  refine ⟨230667320054707605579895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4920902827833762252371093 230667320054707605579895)
                  ·
                    rfl

theorem cell23_4043007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 6].length) (baseStart_4043007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043007 prefixEnd_4043007 := by exact prefixLift 4043007
  have htrace : WordTrace (prefixWord ++ tailWord_4043007) baseStart_4043007 baseEnd_4043007 := by
    simpa [prefixWord, tailWord_4043007, baseEnd_4043007] using wordTrace_append hprefix tailTrace_4043007
  have hstable : (prefixWord ++ tailWord_4043007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043007).length < 2 ^ (prefixWord ++ tailWord_4043007).sum := by decide
  have hdescent : baseEnd_4043007 < baseStart_4043007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043084 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 6, 4]
def baseStart_4043084 : Nat := 118140960795 + 4043084 * 2 ^ 59
def prefixEnd_4043084 : Nat := 4983230072969 + 3 ^ 40 * 4043084 * 2
def baseEnd_4043084 : Nat := 692015139500921549652067

theorem tailTrace_4043084 : CollatzResearch.WordTrace tailWord_4043084 prefixEnd_4043084 692015139500921549652067 := by
  unfold tailWord_4043084
  simp only [CollatzResearch.WordTrace]
  refine ⟨73731694042302323309248153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98308925389736431078997537 73731694042302323309248153)
  ·
    refine ⟨55298770531726742481936115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73731694042302323309248153 55298770531726742481936115)
    ·
      refine ⟨82948155797590113722904173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55298770531726742481936115 82948155797590113722904173)
      ·
        refine ⟨31105558424096292646089065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82948155797590113722904173 31105558424096292646089065)
        ·
          refine ⟨23329168818072219484566799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31105558424096292646089065 23329168818072219484566799)
          ·
            refine ⟨34993753227108329226850199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23329168818072219484566799 34993753227108329226850199)
            ·
              refine ⟨52490629840662493840275299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34993753227108329226850199 52490629840662493840275299)
              ·
                refine ⟨78735944760993740760412949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52490629840662493840275299 78735944760993740760412949)
                ·
                  refine ⟨3690747410671581598144357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78735944760993740760412949 3690747410671581598144357)
                  ·
                    refine ⟨692015139500921549652067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3690747410671581598144357 692015139500921549652067)
                    ·
                      rfl

theorem cell23_4043084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_4043084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043084 prefixEnd_4043084 := by exact prefixLift 4043084
  have htrace : WordTrace (prefixWord ++ tailWord_4043084) baseStart_4043084 baseEnd_4043084 := by
    simpa [prefixWord, tailWord_4043084, baseEnd_4043084] using wordTrace_append hprefix tailTrace_4043084
  have hstable : (prefixWord ++ tailWord_4043084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043084).length < 2 ^ (prefixWord ++ tailWord_4043084).sum := by decide
  have hdescent : baseEnd_4043084 < baseStart_4043084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043114 : List Nat := [3, 1, 3, 3, 1, 1, 1, 10]
def baseStart_4043114 : Nat := 118140960795 + 4043114 * 2 ^ 59
def prefixEnd_4043114 : Nat := 4983230072969 + 3 ^ 40 * 4043114 * 2
def baseEnd_4043114 : Nat := 76891141589718501169669

theorem tailTrace_4043114 : CollatzResearch.WordTrace tailWord_4043114 prefixEnd_4043114 76891141589718501169669 := by
  unfold tailWord_4043114
  simp only [CollatzResearch.WordTrace]
  refine ⟨36866120568623990435522099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98309654849663974494725597 36866120568623990435522099)
  ·
    refine ⟨55299180852935985653283149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36866120568623990435522099 55299180852935985653283149)
    ·
      refine ⟨20737192819850994619981181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55299180852935985653283149 20737192819850994619981181)
      ·
        refine ⟨7776447307444122982492943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20737192819850994619981181 7776447307444122982492943)
        ·
          refine ⟨11664670961166184473739415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7776447307444122982492943 11664670961166184473739415)
          ·
            refine ⟨17497006441749276710609123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11664670961166184473739415 17497006441749276710609123)
            ·
              refine ⟨26245509662623915065913685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17497006441749276710609123 26245509662623915065913685)
              ·
                refine ⟨76891141589718501169669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26245509662623915065913685 76891141589718501169669)
                ·
                  rfl

theorem cell23_4043114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 10].length) (baseStart_4043114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043114 prefixEnd_4043114 := by exact prefixLift 4043114
  have htrace : WordTrace (prefixWord ++ tailWord_4043114) baseStart_4043114 baseEnd_4043114 := by
    simpa [prefixWord, tailWord_4043114, baseEnd_4043114] using wordTrace_append hprefix tailTrace_4043114
  have hstable : (prefixWord ++ tailWord_4043114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043114).length < 2 ^ (prefixWord ++ tailWord_4043114).sum := by decide
  have hdescent : baseEnd_4043114 < baseStart_4043114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043127 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 4, 7]
def baseStart_4043127 : Nat := 118140960795 + 4043127 * 2 ^ 59
def prefixEnd_4043127 : Nat := 4983230072969 + 3 ^ 40 * 4043127 * 2
def baseEnd_4043127 : Nat := 692022499390302660239501

theorem tailTrace_4043127 : CollatzResearch.WordTrace tailWord_4043127 prefixEnd_4043127 692022499390302660239501 := by
  unfold tailWord_4043127
  simp only [CollatzResearch.WordTrace]
  refine ⟨147464956423448864962311635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98309970948965909974874423 147464956423448864962311635)
  ·
    refine ⟨221197434635173297443467453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147464956423448864962311635 221197434635173297443467453)
    ·
      refine ⟨82949037988189986541300295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221197434635173297443467453 82949037988189986541300295)
      ·
        refine ⟨124423556982284979811950443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82949037988189986541300295 124423556982284979811950443)
        ·
          refine ⟨186635335473427469717925665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124423556982284979811950443 186635335473427469717925665)
          ·
            refine ⟨139976501605070602288444249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186635335473427469717925665 139976501605070602288444249)
            ·
              refine ⟨104982376203802951716333187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139976501605070602288444249 104982376203802951716333187)
              ·
                refine ⟨157473564305704427574499781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104982376203802951716333187 157473564305704427574499781)
                ·
                  refine ⟨29526293307319580170218709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157473564305704427574499781 29526293307319580170218709)
                  ·
                    refine ⟨692022499390302660239501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29526293307319580170218709 692022499390302660239501)
                    ·
                      rfl

theorem cell23_4043127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_4043127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043127 prefixEnd_4043127 := by exact prefixLift 4043127
  have htrace : WordTrace (prefixWord ++ tailWord_4043127) baseStart_4043127 baseEnd_4043127 := by
    simpa [prefixWord, tailWord_4043127, baseEnd_4043127] using wordTrace_append hprefix tailTrace_4043127
  have hstable : (prefixWord ++ tailWord_4043127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043127).length < 2 ^ (prefixWord ++ tailWord_4043127).sum := by decide
  have hdescent : baseEnd_4043127 < baseStart_4043127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043198 : List Nat := [4, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2]
def baseStart_4043198 : Nat := 118140960795 + 4043198 * 2 ^ 59
def prefixEnd_4043198 : Nat := 4983230072969 + 3 ^ 40 * 4043198 * 2
def baseEnd_4043198 : Nat := 2076103955297377202930677

theorem tailTrace_4043198 : CollatzResearch.WordTrace tailWord_4043198 prefixEnd_4043198 2076103955297377202930677 := by
  unfold tailWord_4043198
  simp only [CollatzResearch.WordTrace]
  refine ⟨18433443250773955511018281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98311697337461096058764165 18433443250773955511018281)
  ·
    refine ⟨13825082438080466633263711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18433443250773955511018281 13825082438080466633263711)
    ·
      refine ⟨20737623657120699949895567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13825082438080466633263711 20737623657120699949895567)
      ·
        refine ⟨31106435485681049924843351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20737623657120699949895567 31106435485681049924843351)
        ·
          refine ⟨46659653228521574887265027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31106435485681049924843351 46659653228521574887265027)
          ·
            refine ⟨69989479842782362330897541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46659653228521574887265027 69989479842782362330897541)
            ·
              refine ⟨13123027470521692937043289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69989479842782362330897541 13123027470521692937043289)
              ·
                refine ⟨9842270602891269702782467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13123027470521692937043289 9842270602891269702782467)
                ·
                  refine ⟨14763405904336904554173701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9842270602891269702782467 14763405904336904554173701)
                  ·
                    refine ⟨2768138607063169603907569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14763405904336904554173701 2768138607063169603907569)
                    ·
                      refine ⟨2076103955297377202930677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2768138607063169603907569 2076103955297377202930677)
                      ·
                        rfl

theorem cell23_4043198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_4043198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043198 prefixEnd_4043198 := by exact prefixLift 4043198
  have htrace : WordTrace (prefixWord ++ tailWord_4043198) baseStart_4043198 baseEnd_4043198 := by
    simpa [prefixWord, tailWord_4043198, baseEnd_4043198] using wordTrace_append hprefix tailTrace_4043198
  have hstable : (prefixWord ++ tailWord_4043198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043198).length < 2 ^ (prefixWord ++ tailWord_4043198).sum := by decide
  have hdescent : baseEnd_4043198 < baseStart_4043198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043221 : List Nat := [1, 3, 2, 3, 1, 3, 2, 1, 7]
def baseStart_4043221 : Nat := 118140960795 + 4043221 * 2 ^ 59
def prefixEnd_4043221 : Nat := 4983230072969 + 3 ^ 40 * 4043221 * 2
def baseEnd_4043221 : Nat := 230679529483603401438119

theorem tailTrace_4043221 : CollatzResearch.WordTrace tailWord_4043221 prefixEnd_4043221 230679529483603401438119 := by
  unfold tailWord_4043221
  simp only [CollatzResearch.WordTrace]
  refine ⟨147468384885108319016233517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98312256590072212677489011 147468384885108319016233517)
  ·
    refine ⟨55300644331915619631087569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147468384885108319016233517 55300644331915619631087569)
    ·
      refine ⟨41475483248936714723315677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55300644331915619631087569 41475483248936714723315677)
      ·
        refine ⟨15553306218351268021243379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41475483248936714723315677 15553306218351268021243379)
        ·
          refine ⟨23329959327526902031865069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15553306218351268021243379 23329959327526902031865069)
          ·
            refine ⟨8748734747822588261949401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23329959327526902031865069 8748734747822588261949401)
            ·
              refine ⟨6561551060866941196462051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8748734747822588261949401 6561551060866941196462051)
              ·
                refine ⟨9842326591300411794693077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6561551060866941196462051 9842326591300411794693077)
                ·
                  refine ⟨230679529483603401438119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9842326591300411794693077 230679529483603401438119)
                  ·
                    rfl

theorem cell23_4043221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 7].length) (baseStart_4043221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043221 prefixEnd_4043221 := by exact prefixLift 4043221
  have htrace : WordTrace (prefixWord ++ tailWord_4043221) baseStart_4043221 baseEnd_4043221 := by
    simpa [prefixWord, tailWord_4043221, baseEnd_4043221] using wordTrace_append hprefix tailTrace_4043221
  have hstable : (prefixWord ++ tailWord_4043221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043221).length < 2 ^ (prefixWord ++ tailWord_4043221).sum := by decide
  have hdescent : baseEnd_4043221 < baseStart_4043221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043231 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 3]
def baseStart_4043231 : Nat := 118140960795 + 4043231 * 2 ^ 59
def prefixEnd_4043231 : Nat := 4983230072969 + 3 ^ 40 * 4043231 * 2
def baseEnd_4043231 : Nat := 2076120900158975573818025

theorem tailTrace_4043231 : CollatzResearch.WordTrace tailWord_4043231 prefixEnd_4043231 2076120900158975573818025 := by
  unfold tailWord_4043231
  simp only [CollatzResearch.WordTrace]
  refine ⟨147468749615072090724097547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98312499743381393816065031 147468749615072090724097547)
  ·
    refine ⟨221203124422608136086146321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147468749615072090724097547 221203124422608136086146321)
    ·
      refine ⟨165902343316956102064609741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221203124422608136086146321 165902343316956102064609741)
      ·
        refine ⟨62213378743858538274228653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165902343316956102064609741 62213378743858538274228653)
        ·
          refine ⟨23330017028946951852835745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62213378743858538274228653 23330017028946951852835745)
          ·
            refine ⟨17497512771710213889626809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23330017028946951852835745 17497512771710213889626809)
            ·
              refine ⟨13123134578782660417220107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17497512771710213889626809 13123134578782660417220107)
              ·
                refine ⟨19684701868173990625830161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13123134578782660417220107 19684701868173990625830161)
                ·
                  refine ⟨14763526401130492969372621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19684701868173990625830161 14763526401130492969372621)
                  ·
                    refine ⟨5536322400423934863514733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14763526401130492969372621 5536322400423934863514733)
                    ·
                      refine ⟨2076120900158975573818025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5536322400423934863514733 2076120900158975573818025)
                      ·
                        rfl

theorem cell23_4043231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_4043231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043231 prefixEnd_4043231 := by exact prefixLift 4043231
  have htrace : WordTrace (prefixWord ++ tailWord_4043231) baseStart_4043231 baseEnd_4043231 := by
    simpa [prefixWord, tailWord_4043231, baseEnd_4043231] using wordTrace_append hprefix tailTrace_4043231
  have hstable : (prefixWord ++ tailWord_4043231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043231).length < 2 ^ (prefixWord ++ tailWord_4043231).sum := by decide
  have hdescent : baseEnd_4043231 < baseStart_4043231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043268 : List Nat := [2, 3, 2, 3, 1, 2, 1, 2, 2, 5]
def baseStart_4043268 : Nat := 118140960795 + 4043268 * 2 ^ 59
def prefixEnd_4043268 : Nat := 4983230072969 + 3 ^ 40 * 4043268 * 2
def baseEnd_4043268 : Nat := 692046632981063976351785

theorem tailTrace_4043268 : CollatzResearch.WordTrace tailWord_4043268 prefixEnd_4043268 692046632981063976351785 := by
  unfold tailWord_4043268
  simp only [CollatzResearch.WordTrace]
  refine ⟨73735049557969023021597229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98313399410625364028796305 73735049557969023021597229)
  ·
    refine ⟨27650643584238383633098961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73735049557969023021597229 27650643584238383633098961)
    ·
      refine ⟨20737982688178787724824221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27650643584238383633098961 20737982688178787724824221)
      ·
        refine ⟨7776743508067045396809083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20737982688178787724824221 7776743508067045396809083)
        ·
          refine ⟨11665115262100568095213625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7776743508067045396809083 11665115262100568095213625)
          ·
            refine ⟨8748836446575426071410219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11665115262100568095213625 8748836446575426071410219)
            ·
              refine ⟨13123254669863139107115329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8748836446575426071410219 13123254669863139107115329)
              ·
                refine ⟨9842441002397354330336497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13123254669863139107115329 9842441002397354330336497)
                ·
                  refine ⟨7381830751798015747752373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9842441002397354330336497 7381830751798015747752373)
                  ·
                    refine ⟨692046632981063976351785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7381830751798015747752373 692046632981063976351785)
                    ·
                      rfl

theorem cell23_4043268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_4043268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043268 prefixEnd_4043268 := by exact prefixLift 4043268
  have htrace : WordTrace (prefixWord ++ tailWord_4043268) baseStart_4043268 baseEnd_4043268 := by
    simpa [prefixWord, tailWord_4043268, baseEnd_4043268] using wordTrace_append hprefix tailTrace_4043268
  have hstable : (prefixWord ++ tailWord_4043268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043268).length < 2 ^ (prefixWord ++ tailWord_4043268).sum := by decide
  have hdescent : baseEnd_4043268 < baseStart_4043268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043281 : List Nat := [1, 2, 2, 1, 1, 2, 2, 5, 3, 4]
def baseStart_4043281 : Nat := 118140960795 + 4043281 * 2 ^ 59
def prefixEnd_4043281 : Nat := 4983230072969 + 3 ^ 40 * 4043281 * 2
def baseEnd_4043281 : Nat := 692048858063900126064265

theorem tailTrace_4043281 : CollatzResearch.WordTrace tailWord_4043281 prefixEnd_4043281 692048858063900126064265 := by
  unfold tailWord_4043281
  simp only [CollatzResearch.WordTrace]
  refine ⟨147470573264890949263417697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98313715509927299508945131 147470573264890949263417697)
  ·
    refine ⟨110602929948668211947563273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147470573264890949263417697 110602929948668211947563273)
    ·
      refine ⟨82952197461501158960672455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110602929948668211947563273 82952197461501158960672455)
      ·
        refine ⟨124428296192251738441008683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82952197461501158960672455 124428296192251738441008683)
        ·
          refine ⟨186642444288377607661513025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124428296192251738441008683 186642444288377607661513025)
          ·
            refine ⟨139981833216283205746134769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186642444288377607661513025 139981833216283205746134769)
            ·
              refine ⟨104986374912212404309601077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139981833216283205746134769 104986374912212404309601077)
              ·
                refine ⟨9842472648019912904025101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104986374912212404309601077 9842472648019912904025101)
                ·
                  refine ⟨3690927243007467339009413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9842472648019912904025101 3690927243007467339009413)
                  ·
                    refine ⟨692048858063900126064265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3690927243007467339009413 692048858063900126064265)
                    ·
                      rfl

theorem cell23_4043281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_4043281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043281 prefixEnd_4043281 := by exact prefixLift 4043281
  have htrace : WordTrace (prefixWord ++ tailWord_4043281) baseStart_4043281 baseEnd_4043281 := by
    simpa [prefixWord, tailWord_4043281, baseEnd_4043281] using wordTrace_append hprefix tailTrace_4043281
  have hstable : (prefixWord ++ tailWord_4043281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043281).length < 2 ^ (prefixWord ++ tailWord_4043281).sum := by decide
  have hdescent : baseEnd_4043281 < baseStart_4043281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043365 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 1, 5, 2]
def baseStart_4043365 : Nat := 118140960795 + 4043365 * 2 ^ 59
def prefixEnd_4043365 : Nat := 4983230072969 + 3 ^ 40 * 4043365 * 2
def baseEnd_4043365 : Nat := 2076189706566678049542409

theorem tailTrace_4043365 : CollatzResearch.WordTrace tailWord_4043365 prefixEnd_4043365 2076189706566678049542409 := by
  unfold tailWord_4043365
  simp only [CollatzResearch.WordTrace]
  refine ⟨147473636996586631609475549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98315757997724421072983699 147473636996586631609475549)
  ·
    refine ⟨55302613873719986853553331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147473636996586631609475549 55302613873719986853553331)
    ·
      refine ⟨82953920810579980280329997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55302613873719986853553331 82953920810579980280329997)
      ·
        refine ⟨31107720303967492605123749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82953920810579980280329997 31107720303967492605123749)
        ·
          refine ⟨5832697556993904863460703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31107720303967492605123749 5832697556993904863460703)
          ·
            refine ⟨8749046335490857295191055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5832697556993904863460703 8749046335490857295191055)
            ·
              refine ⟨13123569503236285942786583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8749046335490857295191055 13123569503236285942786583)
              ·
                refine ⟨19685354254854428914179875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13123569503236285942786583 19685354254854428914179875)
                ·
                  refine ⟨29528031382281643371269813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19685354254854428914179875 29528031382281643371269813)
                  ·
                    refine ⟨2768252942088904066056545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29528031382281643371269813 2768252942088904066056545)
                    ·
                      refine ⟨2076189706566678049542409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2768252942088904066056545 2076189706566678049542409)
                      ·
                        rfl

theorem cell23_4043365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_4043365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043365 prefixEnd_4043365 := by exact prefixLift 4043365
  have htrace : WordTrace (prefixWord ++ tailWord_4043365) baseStart_4043365 baseEnd_4043365 := by
    simpa [prefixWord, tailWord_4043365, baseEnd_4043365] using wordTrace_append hprefix tailTrace_4043365
  have hstable : (prefixWord ++ tailWord_4043365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043365).length < 2 ^ (prefixWord ++ tailWord_4043365).sum := by decide
  have hdescent : baseEnd_4043365 < baseStart_4043365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043395 : List Nat := [1, 1, 1, 3, 3, 1, 3, 3, 3, 2, 2]
def baseStart_4043395 : Nat := 118140960795 + 4043395 * 2 ^ 59
def prefixEnd_4043395 : Nat := 4983230072969 + 3 ^ 40 * 4043395 * 2
def baseEnd_4043395 : Nat := 2076205110986312932167271

theorem tailTrace_4043395 : CollatzResearch.WordTrace tailWord_4043395 prefixEnd_4043395 2076205110986312932167271 := by
  unfold tailWord_4043395
  simp only [CollatzResearch.WordTrace]
  refine ⟨147474731186477946733067639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98316487457651964488711759 147474731186477946733067639)
  ·
    refine ⟨221212096779716920099601459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147474731186477946733067639 221212096779716920099601459)
    ·
      refine ⟨331818145169575380149402189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221212096779716920099601459 331818145169575380149402189)
      ·
        refine ⟨124431804438590767556025821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331818145169575380149402189 124431804438590767556025821)
        ·
          refine ⟨46661926664471537833509683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124431804438590767556025821 46661926664471537833509683)
          ·
            refine ⟨69992889996707306750264525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46661926664471537833509683 69992889996707306750264525)
            ·
              refine ⟨26247333748765240031349197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69992889996707306750264525 26247333748765240031349197)
              ·
                refine ⟨9842750155786965011755949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26247333748765240031349197 9842750155786965011755949)
                ·
                  refine ⟨3691031308420111879408481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9842750155786965011755949 3691031308420111879408481)
                  ·
                    refine ⟨2768273481315083909556361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3691031308420111879408481 2768273481315083909556361)
                    ·
                      refine ⟨2076205110986312932167271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2768273481315083909556361 2076205110986312932167271)
                      ·
                        rfl

theorem cell23_4043395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 2, 2].length) (baseStart_4043395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043395 prefixEnd_4043395 := by exact prefixLift 4043395
  have htrace : WordTrace (prefixWord ++ tailWord_4043395) baseStart_4043395 baseEnd_4043395 := by
    simpa [prefixWord, tailWord_4043395, baseEnd_4043395] using wordTrace_append hprefix tailTrace_4043395
  have hstable : (prefixWord ++ tailWord_4043395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043395).length < 2 ^ (prefixWord ++ tailWord_4043395).sum := by decide
  have hdescent : baseEnd_4043395 < baseStart_4043395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043412 : List Nat := [2, 4, 2, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_4043412 : Nat := 118140960795 + 4043412 * 2 ^ 59
def prefixEnd_4043412 : Nat := 4983230072969 + 3 ^ 40 * 4043412 * 2
def baseEnd_4043412 : Nat := 2076213840157439365654693

theorem tailTrace_4043412 : CollatzResearch.WordTrace tailWord_4043412 prefixEnd_4043412 2076213840157439365654693 := by
  unfold tailWord_4043412
  simp only [CollatzResearch.WordTrace]
  refine ⟨73737675613708179318218245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98316900818277572424290993 73737675613708179318218245)
  ·
    refine ⟨13825814177570283622165921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73737675613708179318218245 13825814177570283622165921)
    ·
      refine ⟨10369360633177712716624441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13825814177570283622165921 10369360633177712716624441)
      ·
        refine ⟨7777020474883284537468331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10369360633177712716624441 7777020474883284537468331)
        ·
          refine ⟨11665530712324926806202497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7777020474883284537468331 11665530712324926806202497)
          ·
            refine ⟨8749148034243695104651873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11665530712324926806202497 8749148034243695104651873)
            ·
              refine ⟨6561861025682771328488905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8749148034243695104651873 6561861025682771328488905)
              ·
                refine ⟨4921395769262078496366679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6561861025682771328488905 4921395769262078496366679)
                ·
                  refine ⟨7382093653893117744550019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4921395769262078496366679 7382093653893117744550019)
                  ·
                    refine ⟨11073140480839676616825029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7382093653893117744550019 11073140480839676616825029)
                    ·
                      refine ⟨2076213840157439365654693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11073140480839676616825029 2076213840157439365654693)
                      ·
                        rfl

theorem cell23_4043412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_4043412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043412 prefixEnd_4043412 := by exact prefixLift 4043412
  have htrace : WordTrace (prefixWord ++ tailWord_4043412) baseStart_4043412 baseEnd_4043412 := by
    simpa [prefixWord, tailWord_4043412, baseEnd_4043412] using wordTrace_append hprefix tailTrace_4043412
  have hstable : (prefixWord ++ tailWord_4043412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043412).length < 2 ^ (prefixWord ++ tailWord_4043412).sum := by decide
  have hdescent : baseEnd_4043412 < baseStart_4043412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043415 : List Nat := [1, 1, 3, 3, 2, 1, 4, 2, 1, 2, 3]
def baseStart_4043415 : Nat := 118140960795 + 4043415 * 2 ^ 59
def prefixEnd_4043415 : Nat := 4983230072969 + 3 ^ 40 * 4043415 * 2
def baseEnd_4043415 : Nat := 2076215380599402853917179

theorem tailTrace_4043415 : CollatzResearch.WordTrace tailWord_4043415 prefixEnd_4043415 2076215380599402853917179 := by
  unfold tailWord_4043415
  simp only [CollatzResearch.WordTrace]
  refine ⟨147475460646405490148795699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98316973764270326765863799 147475460646405490148795699)
  ·
    refine ⟨221213190969608235223193549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147475460646405490148795699 221213190969608235223193549)
    ·
      refine ⟨82954946613603088208697581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221213190969608235223193549 82954946613603088208697581)
      ·
        refine ⟨31108104980101158078261593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82954946613603088208697581 31108104980101158078261593)
        ·
          refine ⟨23331078735075868558696195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31108104980101158078261593 23331078735075868558696195)
          ·
            refine ⟨34996618102613802838044293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23331078735075868558696195 34996618102613802838044293)
            ·
              refine ⟨6561865894240088032133305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34996618102613802838044293 6561865894240088032133305)
              ·
                refine ⟨4921399420680066024099979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6561865894240088032133305 4921399420680066024099979)
                ·
                  refine ⟨7382099131020099036149969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4921399420680066024099979 7382099131020099036149969)
                  ·
                    refine ⟨5536574348265074277112477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7382099131020099036149969 5536574348265074277112477)
                    ·
                      refine ⟨2076215380599402853917179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5536574348265074277112477 2076215380599402853917179)
                      ·
                        rfl

theorem cell23_4043415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_4043415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043415 prefixEnd_4043415 := by exact prefixLift 4043415
  have htrace : WordTrace (prefixWord ++ tailWord_4043415) baseStart_4043415 baseEnd_4043415 := by
    simpa [prefixWord, tailWord_4043415, baseEnd_4043415] using wordTrace_append hprefix tailTrace_4043415
  have hstable : (prefixWord ++ tailWord_4043415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043415).length < 2 ^ (prefixWord ++ tailWord_4043415).sum := by decide
  have hdescent : baseEnd_4043415 < baseStart_4043415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043428 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 3, 3, 3]
def baseStart_4043428 : Nat := 118140960795 + 4043428 * 2 ^ 59
def prefixEnd_4043428 : Nat := 4983230072969 + 3 ^ 40 * 4043428 * 2
def baseEnd_4043428 : Nat := 2076222055847911303054619

theorem tailTrace_4043428 : CollatzResearch.WordTrace tailWord_4043428 prefixEnd_4043428 2076222055847911303054619 := by
  unfold tailWord_4043428
  simp only [CollatzResearch.WordTrace]
  refine ⟨73737967397679196684509469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98317289863572262246012625 73737967397679196684509469)
  ·
    refine ⟨27651737774129698756691051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73737967397679196684509469 27651737774129698756691051)
    ·
      refine ⟨41477606661194548135036577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27651737774129698756691051 41477606661194548135036577)
      ·
        refine ⟨31108204995895911101277433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41477606661194548135036577 31108204995895911101277433)
        ·
          refine ⟨23331153746921933325958075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31108204995895911101277433 23331153746921933325958075)
          ·
            refine ⟨34996730620382899988937113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23331153746921933325958075 34996730620382899988937113)
            ·
              refine ⟨26247547965287174991702835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34996730620382899988937113 26247547965287174991702835)
              ·
                refine ⟨39371321947930762487554253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26247547965287174991702835 39371321947930762487554253)
                ·
                  refine ⟨14764245730474035932832845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39371321947930762487554253 14764245730474035932832845)
                  ·
                    refine ⟨5536592148927763474812317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14764245730474035932832845 5536592148927763474812317)
                    ·
                      refine ⟨2076222055847911303054619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5536592148927763474812317 2076222055847911303054619)
                      ·
                        rfl

theorem cell23_4043428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_4043428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043428 prefixEnd_4043428 := by exact prefixLift 4043428
  have htrace : WordTrace (prefixWord ++ tailWord_4043428) baseStart_4043428 baseEnd_4043428 := by
    simpa [prefixWord, tailWord_4043428, baseEnd_4043428] using wordTrace_append hprefix tailTrace_4043428
  have hstable : (prefixWord ++ tailWord_4043428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043428).length < 2 ^ (prefixWord ++ tailWord_4043428).sum := by decide
  have hdescent : baseEnd_4043428 < baseStart_4043428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043489 : List Nat := [1, 2, 3, 1, 4, 2, 3, 1, 1, 3, 2]
def baseStart_4043489 : Nat := 118140960795 + 4043489 * 2 ^ 59
def prefixEnd_4043489 : Nat := 4983230072969 + 3 ^ 40 * 4043489 * 2
def baseEnd_4043489 : Nat := 2076253378167835564391839

theorem tailTrace_4043489 : CollatzResearch.WordTrace tailWord_4043489 prefixEnd_4043489 2076253378167835564391839 := by
  unfold tailWord_4043489
  simp only [CollatzResearch.WordTrace]
  refine ⟨147478159648137400786989521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98318773098758267191326347 147478159648137400786989521)
  ·
    refine ⟨110608619736103050590242141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147478159648137400786989521 110608619736103050590242141)
    ·
      refine ⟨41478232401038643971340803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110608619736103050590242141 41478232401038643971340803)
      ·
        refine ⟨62217348601557965957011205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41478232401038643971340803 62217348601557965957011205)
        ·
          refine ⟨11665752862792118616939601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62217348601557965957011205 11665752862792118616939601)
          ·
            refine ⟨8749314647094088962704701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11665752862792118616939601 8749314647094088962704701)
            ·
              refine ⟨3280992992660283361014263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8749314647094088962704701 3280992992660283361014263)
              ·
                refine ⟨4921489488990425041521395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3280992992660283361014263 4921489488990425041521395)
                ·
                  refine ⟨7382234233485637562282093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4921489488990425041521395 7382234233485637562282093)
                  ·
                    refine ⟨2768337837557114085855785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7382234233485637562282093 2768337837557114085855785)
                    ·
                      refine ⟨2076253378167835564391839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2768337837557114085855785 2076253378167835564391839)
                      ·
                        rfl

theorem cell23_4043489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_4043489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043489 prefixEnd_4043489 := by exact prefixLift 4043489
  have htrace : WordTrace (prefixWord ++ tailWord_4043489) baseStart_4043489 baseEnd_4043489 := by
    simpa [prefixWord, tailWord_4043489, baseEnd_4043489] using wordTrace_append hprefix tailTrace_4043489
  have hstable : (prefixWord ++ tailWord_4043489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043489).length < 2 ^ (prefixWord ++ tailWord_4043489).sum := by decide
  have hdescent : baseEnd_4043489 < baseStart_4043489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043498 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_4043498 : Nat := 118140960795 + 4043498 * 2 ^ 59
def prefixEnd_4043498 : Nat := 4983230072969 + 3 ^ 40 * 4043498 * 2
def baseEnd_4043498 : Nat := 2076257999493726029179297

theorem tailTrace_4043498 : CollatzResearch.WordTrace tailWord_4043498 prefixEnd_4043498 2076257999493726029179297 := by
  unfold tailWord_4043498
  simp only [CollatzResearch.WordTrace]
  refine ⟨36869621976276198831016787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98318991936736530216044765 36869621976276198831016787)
  ·
    refine ⟨55304432964414298246525181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36869621976276198831016787 55304432964414298246525181)
    ·
      refine ⟨20739162361655361842446943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55304432964414298246525181 20739162361655361842446943)
      ·
        refine ⟨31108743542483042763670415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20739162361655361842446943 31108743542483042763670415)
        ·
          refine ⟨46663115313724564145505623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31108743542483042763670415 46663115313724564145505623)
          ·
            refine ⟨69994672970586846218258435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46663115313724564145505623 69994672970586846218258435)
            ·
              refine ⟨104992009455880269327387653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69994672970586846218258435 104992009455880269327387653)
              ·
                refine ⟨19686001772977550498885185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104992009455880269327387653 19686001772977550498885185)
                ·
                  refine ⟨14764501329733162874163889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19686001772977550498885185 14764501329733162874163889)
                  ·
                    refine ⟨11073375997299872155622917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14764501329733162874163889 11073375997299872155622917)
                    ·
                      refine ⟨2076257999493726029179297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11073375997299872155622917 2076257999493726029179297)
                      ·
                        rfl

theorem cell23_4043498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_4043498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043498 prefixEnd_4043498 := by exact prefixLift 4043498
  have htrace : WordTrace (prefixWord ++ tailWord_4043498) baseStart_4043498 baseEnd_4043498 := by
    simpa [prefixWord, tailWord_4043498, baseEnd_4043498] using wordTrace_append hprefix tailTrace_4043498
  have hstable : (prefixWord ++ tailWord_4043498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043498).length < 2 ^ (prefixWord ++ tailWord_4043498).sum := by decide
  have hdescent : baseEnd_4043498 < baseStart_4043498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043511 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 8]
def baseStart_4043511 : Nat := 118140960795 + 4043511 * 2 ^ 59
def prefixEnd_4043511 : Nat := 4983230072969 + 3 ^ 40 * 4043511 * 2
def baseEnd_4043511 : Nat := 2076264674742234478316737

theorem tailTrace_4043511 : CollatzResearch.WordTrace tailWord_4043511 prefixEnd_4043511 2076264674742234478316737 := by
  unfold tailWord_4043511
  simp only [CollatzResearch.WordTrace]
  refine ⟨147478962054057698544290387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98319308036038465696193591 147478962054057698544290387)
  ·
    refine ⟨221218443081086547816435581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147478962054057698544290387 221218443081086547816435581)
    ·
      refine ⟨82956916155407455431163343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221218443081086547816435581 82956916155407455431163343)
      ·
        refine ⟨124435374233111183146745015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82956916155407455431163343 124435374233111183146745015)
        ·
          refine ⟨186653061349666774720117523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124435374233111183146745015 186653061349666774720117523)
          ·
            refine ⟨279979592024500162080176285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186653061349666774720117523 279979592024500162080176285)
            ·
              refine ⟨104992347009187560780066107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279979592024500162080176285 104992347009187560780066107)
              ·
                refine ⟨157488520513781341170099161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104992347009187560780066107 157488520513781341170099161)
                ·
                  refine ⟨118116390385336005877574371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157488520513781341170099161 118116390385336005877574371)
                  ·
                    refine ⟨177174585578004008816361557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118116390385336005877574371 177174585578004008816361557)
                    ·
                      refine ⟨2076264674742234478316737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 177174585578004008816361557 2076264674742234478316737)
                      ·
                        rfl

theorem cell23_4043511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_4043511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043511 prefixEnd_4043511 := by exact prefixLift 4043511
  have htrace : WordTrace (prefixWord ++ tailWord_4043511) baseStart_4043511 baseEnd_4043511 := by
    simpa [prefixWord, tailWord_4043511, baseEnd_4043511] using wordTrace_append hprefix tailTrace_4043511
  have hstable : (prefixWord ++ tailWord_4043511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043511).length < 2 ^ (prefixWord ++ tailWord_4043511).sum := by decide
  have hdescent : baseEnd_4043511 < baseStart_4043511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043575 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 2, 4, 2]
def baseStart_4043575 : Nat := 118140960795 + 4043575 * 2 ^ 59
def prefixEnd_4043575 : Nat := 4983230072969 + 3 ^ 40 * 4043575 * 2
def baseEnd_4043575 : Nat := 2076297537504122227916443

theorem tailTrace_4043575 : CollatzResearch.WordTrace tailWord_4043575 prefixEnd_4043575 2076297537504122227916443 := by
  unfold tailWord_4043575
  simp only [CollatzResearch.WordTrace]
  refine ⟨147481296325825837474620179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98320864217217224983080119 147481296325825837474620179)
  ·
    refine ⟨221221944488738756211930269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147481296325825837474620179 221221944488738756211930269)
    ·
      refine ⟨82958229183277033579473851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221221944488738756211930269 82958229183277033579473851)
      ·
        refine ⟨124437343774915550369210777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82958229183277033579473851 124437343774915550369210777)
        ·
          refine ⟨93328007831186662776908083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124437343774915550369210777 93328007831186662776908083)
          ·
            refine ⟨139992011746779994165362125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93328007831186662776908083 139992011746779994165362125)
            ·
              refine ⟨52497004405042497812010797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139992011746779994165362125 52497004405042497812010797)
              ·
                refine ⟨19686376651890936679504049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52497004405042497812010797 19686376651890936679504049)
                ·
                  refine ⟨14764782488918202509628037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19686376651890936679504049 14764782488918202509628037)
                  ·
                    refine ⟨2768396716672162970555257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14764782488918202509628037 2768396716672162970555257)
                    ·
                      refine ⟨2076297537504122227916443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2768396716672162970555257 2076297537504122227916443)
                      ·
                        rfl

theorem cell23_4043575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 4, 2].length) (baseStart_4043575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043575 prefixEnd_4043575 := by exact prefixLift 4043575
  have htrace : WordTrace (prefixWord ++ tailWord_4043575) baseStart_4043575 baseEnd_4043575 := by
    simpa [prefixWord, tailWord_4043575, baseEnd_4043575] using wordTrace_append hprefix tailTrace_4043575
  have hstable : (prefixWord ++ tailWord_4043575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043575).length < 2 ^ (prefixWord ++ tailWord_4043575).sum := by decide
  have hdescent : baseEnd_4043575 < baseStart_4043575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043612 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_4043612 : Nat := 118140960795 + 4043612 * 2 ^ 59
def prefixEnd_4043612 : Nat := 4983230072969 + 3 ^ 40 * 4043612 * 2
def baseEnd_4043612 : Nat := 2076316536288338583153773

theorem tailTrace_4043612 : CollatzResearch.WordTrace tailWord_4043612 prefixEnd_4043612 2076316536288338583153773 := by
  unfold tailWord_4043612
  simp only [CollatzResearch.WordTrace]
  refine ⟨73741322913345896396858545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98321763884461195195811393 73741322913345896396858545)
  ·
    refine ⟨55305992185009422297643909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73741322913345896396858545 55305992185009422297643909)
    ·
      refine ⟨10369873534689266680808233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55305992185009422297643909 10369873534689266680808233)
      ·
        refine ⟨7777405151016950010606175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10369873534689266680808233 7777405151016950010606175)
        ·
          refine ⟨11666107726525425015909263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7777405151016950010606175 11666107726525425015909263)
          ·
            refine ⟨17499161589788137523863895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11666107726525425015909263 17499161589788137523863895)
            ·
              refine ⟨26248742384682206285795843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17499161589788137523863895 26248742384682206285795843)
              ·
                refine ⟨39373113577023309428693765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26248742384682206285795843 39373113577023309428693765)
                ·
                  refine ⟨7382458795691870517880081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39373113577023309428693765 7382458795691870517880081)
                  ·
                    refine ⟨5536844096768902888410061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7382458795691870517880081 5536844096768902888410061)
                    ·
                      refine ⟨2076316536288338583153773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5536844096768902888410061 2076316536288338583153773)
                      ·
                        rfl

theorem cell23_4043612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_4043612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043612 prefixEnd_4043612 := by exact prefixLift 4043612
  have htrace : WordTrace (prefixWord ++ tailWord_4043612) baseStart_4043612 baseEnd_4043612 := by
    simpa [prefixWord, tailWord_4043612, baseEnd_4043612] using wordTrace_append hprefix tailTrace_4043612
  have hstable : (prefixWord ++ tailWord_4043612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043612).length < 2 ^ (prefixWord ++ tailWord_4043612).sum := by decide
  have hdescent : baseEnd_4043612 < baseStart_4043612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043635 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 3, 5, 2]
def baseStart_4043635 : Nat := 118140960795 + 4043635 * 2 ^ 59
def prefixEnd_4043635 : Nat := 4983230072969 + 3 ^ 40 * 4043635 * 2
def baseEnd_4043635 : Nat := 2076328346343391993166167

theorem tailTrace_4043635 : CollatzResearch.WordTrace tailWord_4043635 prefixEnd_4043635 2076328346343391993166167 := by
  unfold tailWord_4043635
  simp only [CollatzResearch.WordTrace]
  refine ⟨147483484705608467721804359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98322323137072311814536239 147483484705608467721804359)
  ·
    refine ⟨221225227058412701582706539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147483484705608467721804359 221225227058412701582706539)
    ·
      refine ⟨331837840587619052374059809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221225227058412701582706539 331837840587619052374059809)
      ·
        refine ⟨248878380440714289280544857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331837840587619052374059809 248878380440714289280544857)
        ·
          refine ⟨186658785330535716960408643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248878380440714289280544857 186658785330535716960408643)
          ·
            refine ⟨279988177995803575440612965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186658785330535716960408643 279988177995803575440612965)
            ·
              refine ⟨52497783374213170395114931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279988177995803575440612965 52497783374213170395114931)
              ·
                refine ⟨78746675061319755592672397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52497783374213170395114931 78746675061319755592672397)
                ·
                  refine ⟨29530003147994908347252149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78746675061319755592672397 29530003147994908347252149)
                  ·
                    refine ⟨2768437795124522657554889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29530003147994908347252149 2768437795124522657554889)
                    ·
                      refine ⟨2076328346343391993166167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2768437795124522657554889 2076328346343391993166167)
                      ·
                        rfl

theorem cell23_4043635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 5, 2].length) (baseStart_4043635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043635 prefixEnd_4043635 := by exact prefixLift 4043635
  have htrace : WordTrace (prefixWord ++ tailWord_4043635) baseStart_4043635 baseEnd_4043635 := by
    simpa [prefixWord, tailWord_4043635, baseEnd_4043635] using wordTrace_append hprefix tailTrace_4043635
  have hstable : (prefixWord ++ tailWord_4043635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043635).length < 2 ^ (prefixWord ++ tailWord_4043635).sum := by decide
  have hdescent : baseEnd_4043635 < baseStart_4043635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043646 : List Nat := [4, 2, 3, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_4043646 : Nat := 118140960795 + 4043646 * 2 ^ 59
def prefixEnd_4043646 : Nat := 4983230072969 + 3 ^ 40 * 4043646 * 2
def baseEnd_4043646 : Nat := 2076333994630591450128617

theorem tailTrace_4043646 : CollatzResearch.WordTrace tailWord_4043646 prefixEnd_4043646 2076333994630591450128617 := by
  unfold tailWord_4043646
  simp only [CollatzResearch.WordTrace]
  refine ⟨18435485738571077075056849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98322590605712411066969861 18435485738571077075056849)
  ·
    refine ⟨13826614303928307806292637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18435485738571077075056849 13826614303928307806292637)
    ·
      refine ⟨5184980363973115427359739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13826614303928307806292637 5184980363973115427359739)
      ·
        refine ⟨7777470545959673141039609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5184980363973115427359739 7777470545959673141039609)
        ·
          refine ⟨5833102909469754855779707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7777470545959673141039609 5833102909469754855779707)
          ·
            refine ⟨8749654364204632283669561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5833102909469754855779707 8749654364204632283669561)
            ·
              refine ⟨6562240773153474212752171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8749654364204632283669561 6562240773153474212752171)
              ·
                refine ⟨9843361159730211319128257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6562240773153474212752171 9843361159730211319128257)
                ·
                  refine ⟨7382520869797658489346193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9843361159730211319128257 7382520869797658489346193)
                  ·
                    refine ⟨5536890652348243867009645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7382520869797658489346193 5536890652348243867009645)
                    ·
                      refine ⟨2076333994630591450128617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5536890652348243867009645 2076333994630591450128617)
                      ·
                        rfl

theorem cell23_4043646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_4043646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043646 prefixEnd_4043646 := by exact prefixLift 4043646
  have htrace : WordTrace (prefixWord ++ tailWord_4043646) baseStart_4043646 baseEnd_4043646 := by
    simpa [prefixWord, tailWord_4043646, baseEnd_4043646] using wordTrace_append hprefix tailTrace_4043646
  have hstable : (prefixWord ++ tailWord_4043646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043646).length < 2 ^ (prefixWord ++ tailWord_4043646).sum := by decide
  have hdescent : baseEnd_4043646 < baseStart_4043646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043670 : List Nat := [5, 3, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_4043670 : Nat := 118140960795 + 4043670 * 2 ^ 59
def prefixEnd_4043670 : Nat := 4983230072969 + 3 ^ 40 * 4043670 * 2
def baseEnd_4043670 : Nat := 692115439388766452076169

theorem tailTrace_4043670 : CollatzResearch.WordTrace tailWord_4043670 prefixEnd_4043670 692115439388766452076169 := by
  unfold tailWord_4043670
  simp only [CollatzResearch.WordTrace]
  refine ⟨9217797578780104293708029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98323174173654445799552309 9217797578780104293708029)
  ·
    refine ⟨3456674092042539110140511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9217797578780104293708029 3456674092042539110140511)
    ·
      refine ⟨5185011138063808665210767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3456674092042539110140511 5185011138063808665210767)
      ·
        refine ⟨7777516707095712997816151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5185011138063808665210767 7777516707095712997816151)
        ·
          refine ⟨11666275060643569496724227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7777516707095712997816151 11666275060643569496724227)
          ·
            refine ⟨17499412590965354245086341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11666275060643569496724227 17499412590965354245086341)
            ·
              refine ⟨3281139860806003920953689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17499412590965354245086341 3281139860806003920953689)
              ·
                refine ⟨2460854895604502940715267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3281139860806003920953689 2460854895604502940715267)
                ·
                  refine ⟨3691282343406754411072901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460854895604502940715267 3691282343406754411072901)
                  ·
                    refine ⟨692115439388766452076169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3691282343406754411072901 692115439388766452076169)
                    ·
                      rfl

theorem cell23_4043670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_4043670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043670 prefixEnd_4043670 := by exact prefixLift 4043670
  have htrace : WordTrace (prefixWord ++ tailWord_4043670) baseStart_4043670 baseEnd_4043670 := by
    simpa [prefixWord, tailWord_4043670, baseEnd_4043670] using wordTrace_append hprefix tailTrace_4043670
  have hstable : (prefixWord ++ tailWord_4043670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043670).length < 2 ^ (prefixWord ++ tailWord_4043670).sum := by decide
  have hdescent : baseEnd_4043670 < baseStart_4043670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043682 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_4043682 : Nat := 118140960795 + 4043682 * 2 ^ 59
def prefixEnd_4043682 : Nat := 4983230072969 + 3 ^ 40 * 4043682 * 2
def baseEnd_4043682 : Nat := 2076352479934153309278451

theorem tailTrace_4043682 : CollatzResearch.WordTrace tailWord_4043682 prefixEnd_4043682 2076352479934153309278451 := by
  unfold tailWord_4043682
  simp only [CollatzResearch.WordTrace]
  refine ⟨36871299734109548687191325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98323465957625463165843533 36871299734109548687191325)
  ·
    refine ⟨13826737400291080757696747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36871299734109548687191325 13826737400291080757696747)
    ·
      refine ⟨20740106100436621136545121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13826737400291080757696747 20740106100436621136545121)
      ·
        refine ⟨15555079575327465852408841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20740106100436621136545121 15555079575327465852408841)
        ·
          refine ⟨11666309681495599389306631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15555079575327465852408841 11666309681495599389306631)
          ·
            refine ⟨17499464522243399083959947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11666309681495599389306631 17499464522243399083959947)
            ·
              refine ⟨26249196783365098625939921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17499464522243399083959947 26249196783365098625939921)
              ·
                refine ⟨19686897587523823969454941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26249196783365098625939921 19686897587523823969454941)
                ·
                  refine ⟨7382586595321433988545603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19686897587523823969454941 7382586595321433988545603)
                  ·
                    refine ⟨11073879892982150982818405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7382586595321433988545603 11073879892982150982818405)
                    ·
                      refine ⟨2076352479934153309278451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11073879892982150982818405 2076352479934153309278451)
                      ·
                        rfl

theorem cell23_4043682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_4043682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043682 prefixEnd_4043682 := by exact prefixLift 4043682
  have htrace : WordTrace (prefixWord ++ tailWord_4043682) baseStart_4043682 baseEnd_4043682 := by
    simpa [prefixWord, tailWord_4043682, baseEnd_4043682] using wordTrace_append hprefix tailTrace_4043682
  have hstable : (prefixWord ++ tailWord_4043682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043682).length < 2 ^ (prefixWord ++ tailWord_4043682).sum := by decide
  have hdescent : baseEnd_4043682 < baseStart_4043682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043716 : List Nat := [2, 3, 3, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_4043716 : Nat := 118140960795 + 4043716 * 2 ^ 59
def prefixEnd_4043716 : Nat := 4983230072969 + 3 ^ 40 * 4043716 * 2
def baseEnd_4043716 : Nat := 2076369938276406176253295

theorem tailTrace_4043716 : CollatzResearch.WordTrace tailWord_4043716 prefixEnd_4043716 2076369938276406176253295 := by
  unfold tailWord_4043716
  simp only [CollatzResearch.WordTrace]
  refine ⟨73743219509157509277751501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98324292678876679037002001 73743219509157509277751501)
  ·
    refine ⟨27653707315934065979156813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73743219509157509277751501 27653707315934065979156813)
    ·
      refine ⟨10370140243475274742183805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27653707315934065979156813 10370140243475274742183805)
      ·
        refine ⟨3888802591303228028318927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10370140243475274742183805 3888802591303228028318927)
        ·
          refine ⟨5833203886954842042478391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3888802591303228028318927 5833203886954842042478391)
          ·
            refine ⟨8749805830432263063717587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5833203886954842042478391 8749805830432263063717587)
            ·
              refine ⟨13124708745648394595576381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8749805830432263063717587 13124708745648394595576381)
              ·
                refine ⟨4921765779618147973341143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13124708745648394595576381 4921765779618147973341143)
                ·
                  refine ⟨7382648669427221960011715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4921765779618147973341143 7382648669427221960011715)
                  ·
                    refine ⟨11073973004140832940017573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7382648669427221960011715 11073973004140832940017573)
                    ·
                      refine ⟨2076369938276406176253295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11073973004140832940017573 2076369938276406176253295)
                      ·
                        rfl

theorem cell23_4043716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_4043716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043716 prefixEnd_4043716 := by exact prefixLift 4043716
  have htrace : WordTrace (prefixWord ++ tailWord_4043716) baseStart_4043716 baseEnd_4043716 := by
    simpa [prefixWord, tailWord_4043716, baseEnd_4043716] using wordTrace_append hprefix tailTrace_4043716
  have hstable : (prefixWord ++ tailWord_4043716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043716).length < 2 ^ (prefixWord ++ tailWord_4043716).sum := by decide
  have hdescent : baseEnd_4043716 < baseStart_4043716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043719 : List Nat := [1, 1, 4, 1, 1, 2, 6, 1, 1, 2, 3]
def baseStart_4043719 : Nat := 118140960795 + 4043719 * 2 ^ 59
def prefixEnd_4043719 : Nat := 4983230072969 + 3 ^ 40 * 4043719 * 2
def baseEnd_4043719 : Nat := 2076371478718369664515781

theorem tailTrace_4043719 : CollatzResearch.WordTrace tailWord_4043719 prefixEnd_4043719 2076371478718369664515781 := by
  unfold tailWord_4043719
  simp only [CollatzResearch.WordTrace]
  refine ⟨147486548437304150067862211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98324365624869433378574807 147486548437304150067862211)
  ·
    refine ⟨221229822655956225101793317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147486548437304150067862211 221229822655956225101793317)
    ·
      refine ⟨41480591747991792206586247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221229822655956225101793317 41480591747991792206586247)
      ·
        refine ⟨62220887621987688309879371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41480591747991792206586247 62220887621987688309879371)
        ·
          refine ⟨93331331432981532464819057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62220887621987688309879371 93331331432981532464819057)
          ·
            refine ⟨69998498574736149348614293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93331331432981532464819057 69998498574736149348614293)
            ·
              refine ⟨3281179620690757000716295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69998498574736149348614293 3281179620690757000716295)
              ·
                refine ⟨4921769431036135501074443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3281179620690757000716295 4921769431036135501074443)
                ·
                  refine ⟨7382654146554203251611665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4921769431036135501074443 7382654146554203251611665)
                  ·
                    refine ⟨5536990609915652438708749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7382654146554203251611665 5536990609915652438708749)
                    ·
                      refine ⟨2076371478718369664515781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5536990609915652438708749 2076371478718369664515781)
                      ·
                        rfl

theorem cell23_4043719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_4043719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043719 prefixEnd_4043719 := by exact prefixLift 4043719
  have htrace : WordTrace (prefixWord ++ tailWord_4043719) baseStart_4043719 baseEnd_4043719 := by
    simpa [prefixWord, tailWord_4043719, baseEnd_4043719] using wordTrace_append hprefix tailTrace_4043719
  have hstable : (prefixWord ++ tailWord_4043719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043719).length < 2 ^ (prefixWord ++ tailWord_4043719).sum := by decide
  have hdescent : baseEnd_4043719 < baseStart_4043719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043746 : List Nat := [3, 3, 3, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_4043746 : Nat := 118140960795 + 4043746 * 2 ^ 59
def prefixEnd_4043746 : Nat := 4983230072969 + 3 ^ 40 * 4043746 * 2
def baseEnd_4043746 : Nat := 2076385342696041058878157

theorem tailTrace_4043746 : CollatzResearch.WordTrace tailWord_4043746 prefixEnd_4043746 2076385342696041058878157 := by
  unfold tailWord_4043746
  simp only [CollatzResearch.WordTrace]
  refine ⟨36871883302051583419773773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98325022138804222452730061 36871883302051583419773773)
  ·
    refine ⟨13826956238269343782415165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36871883302051583419773773 13826956238269343782415165)
    ·
      refine ⟨5185108589351003918405687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13826956238269343782415165 5185108589351003918405687)
      ·
        refine ⟨7777662884026505877608531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5185108589351003918405687 7777662884026505877608531)
        ·
          refine ⟨11666494326039758816412797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7777662884026505877608531 11666494326039758816412797)
          ·
            refine ⟨4374935372264909556154799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11666494326039758816412797 4374935372264909556154799)
            ·
              refine ⟨6562403058397364334232199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4374935372264909556154799 6562403058397364334232199)
              ·
                refine ⟨9843604587596046501348299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6562403058397364334232199 9843604587596046501348299)
                ·
                  refine ⟨14765406881394069752022449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9843604587596046501348299 14765406881394069752022449)
                  ·
                    refine ⟨11074055161045552314016837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14765406881394069752022449 11074055161045552314016837)
                    ·
                      refine ⟨2076385342696041058878157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11074055161045552314016837 2076385342696041058878157)
                      ·
                        rfl

theorem cell23_4043746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_4043746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043746 prefixEnd_4043746 := by exact prefixLift 4043746
  have htrace : WordTrace (prefixWord ++ tailWord_4043746) baseStart_4043746 baseEnd_4043746 := by
    simpa [prefixWord, tailWord_4043746, baseEnd_4043746] using wordTrace_append hprefix tailTrace_4043746
  have hstable : (prefixWord ++ tailWord_4043746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043746).length < 2 ^ (prefixWord ++ tailWord_4043746).sum := by decide
  have hdescent : baseEnd_4043746 < baseStart_4043746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043759 : List Nat := [1, 1, 2, 1, 4, 3, 1, 4, 1, 3, 2]
def baseStart_4043759 : Nat := 118140960795 + 4043759 * 2 ^ 59
def prefixEnd_4043759 : Nat := 4983230072969 + 3 ^ 40 * 4043759 * 2
def baseEnd_4043759 : Nat := 2076392017944549508015597

theorem tailTrace_4043759 : CollatzResearch.WordTrace tailWord_4043759 prefixEnd_4043759 2076392017944549508015597 := by
  unfold tailWord_4043759
  simp only [CollatzResearch.WordTrace]
  refine ⟨147488007357159236899318331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98325338238106157932878887 147488007357159236899318331)
  ·
    refine ⟨221232011035738855348977497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147488007357159236899318331 221232011035738855348977497)
    ·
      refine ⟨165924008276804141511733123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221232011035738855348977497 165924008276804141511733123)
      ·
        refine ⟨248886012415206212267599685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165924008276804141511733123 248886012415206212267599685)
        ·
          refine ⟨46666127327851164800174941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248886012415206212267599685 46666127327851164800174941)
          ·
            refine ⟨17499797747944186800065603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46666127327851164800174941 17499797747944186800065603)
            ·
              refine ⟨26249696621916280200098405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17499797747944186800065603 26249696621916280200098405)
              ·
                refine ⟨4921818116609302537518451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26249696621916280200098405 4921818116609302537518451)
                ·
                  refine ⟨7382727174913953806277677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4921818116609302537518451 7382727174913953806277677)
                  ·
                    refine ⟨2768522690592732677354129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7382727174913953806277677 2768522690592732677354129)
                    ·
                      refine ⟨2076392017944549508015597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2768522690592732677354129 2076392017944549508015597)
                      ·
                        rfl

theorem cell23_4043759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 3, 2].length) (baseStart_4043759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043759 prefixEnd_4043759 := by exact prefixLift 4043759
  have htrace : WordTrace (prefixWord ++ tailWord_4043759) baseStart_4043759 baseEnd_4043759 := by
    simpa [prefixWord, tailWord_4043759, baseEnd_4043759] using wordTrace_append hprefix tailTrace_4043759
  have hstable : (prefixWord ++ tailWord_4043759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043759).length < 2 ^ (prefixWord ++ tailWord_4043759).sum := by decide
  have hdescent : baseEnd_4043759 < baseStart_4043759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043775 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 3]
def baseStart_4043775 : Nat := 118140960795 + 4043775 * 2 ^ 59
def prefixEnd_4043775 : Nat := 4983230072969 + 3 ^ 40 * 4043775 * 2
def baseEnd_4043775 : Nat := 2076400233635021445415523

theorem tailTrace_4043775 : CollatzResearch.WordTrace tailWord_4043775 prefixEnd_4043775 2076400233635021445415523 := by
  unfold tailWord_4043775
  simp only [CollatzResearch.WordTrace]
  refine ⟨147488590925101271631900779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98325727283400847754600519 147488590925101271631900779)
  ·
    refine ⟨221232886387651907447851169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147488590925101271631900779 221232886387651907447851169)
    ·
      refine ⟨165924664790738930585888377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221232886387651907447851169 165924664790738930585888377)
      ·
        refine ⟨124443498593054197939416283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165924664790738930585888377 124443498593054197939416283)
        ·
          refine ⟨186665247889581296909124425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124443498593054197939416283 186665247889581296909124425)
          ·
            refine ⟨139998935917185972681843319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186665247889581296909124425 139998935917185972681843319)
            ·
              refine ⟨209998403875778959022764979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139998935917185972681843319 209998403875778959022764979)
              ·
                refine ⟨314997605813668438534147469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209998403875778959022764979 314997605813668438534147469)
                ·
                  refine ⟨118124102180125664450305301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314997605813668438534147469 118124102180125664450305301)
                  ·
                    refine ⟨5537067289693390521108061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118124102180125664450305301 5537067289693390521108061)
                    ·
                      refine ⟨2076400233635021445415523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5537067289693390521108061 2076400233635021445415523)
                      ·
                        rfl

theorem cell23_4043775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_4043775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043775 prefixEnd_4043775 := by exact prefixLift 4043775
  have htrace : WordTrace (prefixWord ++ tailWord_4043775) baseStart_4043775 baseEnd_4043775 := by
    simpa [prefixWord, tailWord_4043775, baseEnd_4043775] using wordTrace_append hprefix tailTrace_4043775
  have hstable : (prefixWord ++ tailWord_4043775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043775).length < 2 ^ (prefixWord ++ tailWord_4043775).sum := by decide
  have hdescent : baseEnd_4043775 < baseStart_4043775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043785 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 4, 2, 4]
def baseStart_4043785 : Nat := 118140960795 + 4043785 * 2 ^ 59
def prefixEnd_4043785 : Nat := 4983230072969 + 3 ^ 40 * 4043785 * 2
def baseEnd_4043785 : Nat := 2076405368441566406290477

theorem tailTrace_4043785 : CollatzResearch.WordTrace tailWord_4043785 prefixEnd_4043785 2076405368441566406290477 := by
  unfold tailWord_4043785
  simp only [CollatzResearch.WordTrace]
  refine ⟨147488955655065043339764809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98325970436710028893176539 147488955655065043339764809)
  ·
    refine ⟨110616716741298782504823607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147488955655065043339764809 110616716741298782504823607)
    ·
      refine ⟨165925075111948173757235411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110616716741298782504823607 165925075111948173757235411)
      ·
        refine ⟨248887612667922260635853117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165925075111948173757235411 248887612667922260635853117)
        ·
          refine ⟨93332854750470847738444919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248887612667922260635853117 93332854750470847738444919)
          ·
            refine ⟨139999282125706271607667379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93332854750470847738444919 139999282125706271607667379)
            ·
              refine ⟨209998923188559407411501069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139999282125706271607667379 209998923188559407411501069)
              ·
                refine ⟨78749596195709777779312901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209998923188559407411501069 78749596195709777779312901)
                ·
                  refine ⟨14765549286695583333621169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78749596195709777779312901 14765549286695583333621169)
                  ·
                    refine ⟨11074161965021687500215877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14765549286695583333621169 11074161965021687500215877)
                    ·
                      refine ⟨2076405368441566406290477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11074161965021687500215877 2076405368441566406290477)
                      ·
                        rfl

theorem cell23_4043785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_4043785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043785 prefixEnd_4043785 := by exact prefixLift 4043785
  have htrace : WordTrace (prefixWord ++ tailWord_4043785) baseStart_4043785 baseEnd_4043785 := by
    simpa [prefixWord, tailWord_4043785, baseEnd_4043785] using wordTrace_append hprefix tailTrace_4043785
  have hstable : (prefixWord ++ tailWord_4043785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043785).length < 2 ^ (prefixWord ++ tailWord_4043785).sum := by decide
  have hdescent : baseEnd_4043785 < baseStart_4043785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043879 : List Nat := [1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_4043879 : Nat := 118140960795 + 4043879 * 2 ^ 59
def prefixEnd_4043879 : Nat := 4983230072969 + 3 ^ 40 * 4043879 * 2
def baseEnd_4043879 : Nat := 2076453635623089038515045

theorem tailTrace_4043879 : CollatzResearch.WordTrace tailWord_4043879 prefixEnd_4043879 2076453635623089038515045 := by
  unfold tailWord_4043879
  simp only [CollatzResearch.WordTrace]
  refine ⟨147492384116724497393686691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98328256077816331595791127 147492384116724497393686691)
  ·
    refine ⟨221238576175086746090530037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147492384116724497393686691 221238576175086746090530037)
    ·
      refine ⟨20741116516414382445987191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221238576175086746090530037 20741116516414382445987191)
      ·
        refine ⟨31111674774621573668980787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20741116516414382445987191 31111674774621573668980787)
        ·
          refine ⟨46667512161932360503471181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31111674774621573668980787 46667512161932360503471181)
          ·
            refine ⟨17500317060724635188801693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46667512161932360503471181 17500317060724635188801693)
            ·
              refine ⟨6562618897771738195800635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17500317060724635188801693 6562618897771738195800635)
              ·
                refine ⟨9843928346657607293700953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6562618897771738195800635 9843928346657607293700953)
                ·
                  refine ⟨7382946259993205470275715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9843928346657607293700953 7382946259993205470275715)
                  ·
                    refine ⟨11074419389989808205413573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7382946259993205470275715 11074419389989808205413573)
                    ·
                      refine ⟨2076453635623089038515045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11074419389989808205413573 2076453635623089038515045)
                      ·
                        rfl

theorem cell23_4043879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_4043879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043879 prefixEnd_4043879 := by exact prefixLift 4043879
  have htrace : WordTrace (prefixWord ++ tailWord_4043879) baseStart_4043879 baseEnd_4043879 := by
    simpa [prefixWord, tailWord_4043879, baseEnd_4043879] using wordTrace_append hprefix tailTrace_4043879
  have hstable : (prefixWord ++ tailWord_4043879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043879).length < 2 ^ (prefixWord ++ tailWord_4043879).sum := by decide
  have hdescent : baseEnd_4043879 < baseStart_4043879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4043939 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 6, 3, 2]
def baseStart_4043939 : Nat := 118140960795 + 4043939 * 2 ^ 59
def prefixEnd_4043939 : Nat := 4983230072969 + 3 ^ 40 * 4043939 * 2
def baseEnd_4043939 : Nat := 2076484444462358803764769

theorem tailTrace_4043939 : CollatzResearch.WordTrace tailWord_4043939 prefixEnd_4043939 2076484444462358803764769 := by
  unfold tailWord_4043939
  simp only [CollatzResearch.WordTrace]
  refine ⟨147494572496507127640870871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98329714997671418427247247 147494572496507127640870871)
  ·
    refine ⟨221241858744760691461306307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147494572496507127640870871 221241858744760691461306307)
    ·
      refine ⟨331862788117141037191959461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221241858744760691461306307 331862788117141037191959461)
      ·
        refine ⟨62224272771963944473492399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331862788117141037191959461 62224272771963944473492399)
        ·
          refine ⟨93336409157945916710238599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62224272771963944473492399 93336409157945916710238599)
          ·
            refine ⟨140004613736918875065357899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93336409157945916710238599 140004613736918875065357899)
            ·
              refine ⟨210006920605378312598036849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140004613736918875065357899 210006920605378312598036849)
              ·
                refine ⟨157505190454033734448527637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210006920605378312598036849 157505190454033734448527637)
                ·
                  refine ⟨7383055802532831302274733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157505190454033734448527637 7383055802532831302274733)
                  ·
                    refine ⟨2768645925949811738353025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7383055802532831302274733 2768645925949811738353025)
                    ·
                      refine ⟨2076484444462358803764769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2768645925949811738353025 2076484444462358803764769)
                      ·
                        rfl

theorem cell23_4043939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_4043939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4043939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4043939 prefixEnd_4043939 := by exact prefixLift 4043939
  have htrace : WordTrace (prefixWord ++ tailWord_4043939) baseStart_4043939 baseEnd_4043939 := by
    simpa [prefixWord, tailWord_4043939, baseEnd_4043939] using wordTrace_append hprefix tailTrace_4043939
  have hstable : (prefixWord ++ tailWord_4043939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4043939).length < 2 ^ (prefixWord ++ tailWord_4043939).sum := by decide
  have hdescent : baseEnd_4043939 < baseStart_4043939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4043939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044013 : List Nat := [1, 5, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_4044013 : Nat := 118140960795 + 4044013 * 2 ^ 59
def prefixEnd_4044013 : Nat := 4983230072969 + 3 ^ 40 * 4044013 * 2
def baseEnd_4044013 : Nat := 692174147343597171413143

theorem tailTrace_4044013 : CollatzResearch.WordTrace tailWord_4044013 prefixEnd_4044013 692174147343597171413143 := by
  unfold tailWord_4044013
  simp only [CollatzResearch.WordTrace]
  refine ⟨147497271498239038279064693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98331514332159358852709795 147497271498239038279064693)
  ·
    refine ⟨13827869202959909838662315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147497271498239038279064693 13827869202959909838662315)
    ·
      refine ⟨20741803804439864757993473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13827869202959909838662315 20741803804439864757993473)
      ·
        refine ⟨15556352853329898568495105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20741803804439864757993473 15556352853329898568495105)
        ·
          refine ⟨11667264639997423926371329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15556352853329898568495105 11667264639997423926371329)
          ·
            refine ⟨8750448479998067944778497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11667264639997423926371329 8750448479998067944778497)
            ·
              refine ⟨6562836359998550958583873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8750448479998067944778497 6562836359998550958583873)
              ·
                refine ⟨4922127269998913218937905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6562836359998550958583873 4922127269998913218937905)
                ·
                  refine ⟨3691595452499184914203429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4922127269998913218937905 3691595452499184914203429)
                  ·
                    refine ⟨692174147343597171413143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3691595452499184914203429 692174147343597171413143)
                    ·
                      rfl

theorem cell23_4044013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_4044013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044013 prefixEnd_4044013 := by exact prefixLift 4044013
  have htrace : WordTrace (prefixWord ++ tailWord_4044013) baseStart_4044013 baseEnd_4044013 := by
    simpa [prefixWord, tailWord_4044013, baseEnd_4044013] using wordTrace_append hprefix tailTrace_4044013
  have hstable : (prefixWord ++ tailWord_4044013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044013).length < 2 ^ (prefixWord ++ tailWord_4044013).sum := by decide
  have hdescent : baseEnd_4044013 < baseStart_4044013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044032 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 5]
def baseStart_4044032 : Nat := 118140960795 + 4044032 * 2 ^ 59
def prefixEnd_4044032 : Nat := 4983230072969 + 3 ^ 40 * 4044032 * 2
def baseEnd_4044032 : Nat := 2076532198163226939901841

theorem tailTrace_4044032 : CollatzResearch.WordTrace tailWord_4044032 prefixEnd_4044032 2076532198163226939901841 := by
  unfold tailWord_4044032
  simp only [CollatzResearch.WordTrace]
  refine ⟨73748982242585102262003175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98331976323446803016004233 73748982242585102262003175)
  ·
    refine ⟨110623473363877653393004763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73748982242585102262003175 110623473363877653393004763)
    ·
      refine ⟨165935210045816480089507145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110623473363877653393004763 165935210045816480089507145)
      ·
        refine ⟨124451407534362360067130359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165935210045816480089507145 124451407534362360067130359)
        ·
          refine ⟨186677111301543540100695539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124451407534362360067130359 186677111301543540100695539)
          ·
            refine ⟨280015666952315310151043309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186677111301543540100695539 280015666952315310151043309)
            ·
              refine ⟨105005875107118241306641241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280015666952315310151043309 105005875107118241306641241)
              ·
                refine ⟨78754406330338680979980931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105005875107118241306641241 78754406330338680979980931)
                ·
                  refine ⟨118131609495508021469971397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78754406330338680979980931 118131609495508021469971397)
                  ·
                    refine ⟨22149676780407754025619637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118131609495508021469971397 22149676780407754025619637)
                    ·
                      refine ⟨2076532198163226939901841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22149676780407754025619637 2076532198163226939901841)
                      ·
                        rfl

theorem cell23_4044032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_4044032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044032 prefixEnd_4044032 := by exact prefixLift 4044032
  have htrace : WordTrace (prefixWord ++ tailWord_4044032) baseStart_4044032 baseEnd_4044032 := by
    simpa [prefixWord, tailWord_4044032, baseEnd_4044032] using wordTrace_append hprefix tailTrace_4044032
  have hstable : (prefixWord ++ tailWord_4044032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044032).length < 2 ^ (prefixWord ++ tailWord_4044032).sum := by decide
  have hdescent : baseEnd_4044032 < baseStart_4044032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044036 : List Nat := [2, 3, 2, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_4044036 : Nat := 118140960795 + 4044036 * 2 ^ 59
def prefixEnd_4044036 : Nat := 4983230072969 + 3 ^ 40 * 4044036 * 2
def baseEnd_4044036 : Nat := 2076534252085844924251823

theorem tailTrace_4044036 : CollatzResearch.WordTrace tailWord_4044036 prefixEnd_4044036 2076534252085844924251823 := by
  unfold tailWord_4044036
  simp only [CollatzResearch.WordTrace]
  refine ⟨73749055188577856603575981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98332073584770475471434641 73749055188577856603575981)
  ·
    refine ⟨27655895695716696226340993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73749055188577856603575981 27655895695716696226340993)
    ·
      refine ⟨20741921771787522169755745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27655895695716696226340993 20741921771787522169755745)
      ·
        refine ⟨15556441328840641627316809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20741921771787522169755745 15556441328840641627316809)
        ·
          refine ⟨11667330996630481220487607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15556441328840641627316809 11667330996630481220487607)
          ·
            refine ⟨17500996494945721830731411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11667330996630481220487607 17500996494945721830731411)
            ·
              refine ⟨26251494742418582746097117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17500996494945721830731411 26251494742418582746097117)
              ·
                refine ⟨9844310528406968529786419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26251494742418582746097117 9844310528406968529786419)
                ·
                  refine ⟨14766465792610452794679629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9844310528406968529786419 14766465792610452794679629)
                  ·
                    refine ⟨5537424672228919798004861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14766465792610452794679629 5537424672228919798004861)
                    ·
                      refine ⟨2076534252085844924251823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5537424672228919798004861 2076534252085844924251823)
                      ·
                        rfl

theorem cell23_4044036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_4044036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044036 prefixEnd_4044036 := by exact prefixLift 4044036
  have htrace : WordTrace (prefixWord ++ tailWord_4044036) baseStart_4044036 baseEnd_4044036 := by
    simpa [prefixWord, tailWord_4044036, baseEnd_4044036] using wordTrace_append hprefix tailTrace_4044036
  have hstable : (prefixWord ++ tailWord_4044036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044036).length < 2 ^ (prefixWord ++ tailWord_4044036).sum := by decide
  have hdescent : baseEnd_4044036 < baseStart_4044036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044069 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 2, 6]
def baseStart_4044069 : Nat := 118140960795 + 4044069 * 2 ^ 59
def prefixEnd_4044069 : Nat := 4983230072969 + 3 ^ 40 * 4044069 * 2
def baseEnd_4044069 : Nat := 692183732315814431713057

theorem tailTrace_4044069 : CollatzResearch.WordTrace tailWord_4044069 prefixEnd_4044069 692183732315814431713057 := by
  unfold tailWord_4044069
  simp only [CollatzResearch.WordTrace]
  refine ⟨147499313986036159843103261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98332875990690773228735507 147499313986036159843103261)
  ·
    refine ⟨55312242744763559941163723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147499313986036159843103261 55312242744763559941163723)
    ·
      refine ⟨82968364117145339911745585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55312242744763559941163723 82968364117145339911745585)
      ·
        refine ⟨62226273087859004933809189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82968364117145339911745585 62226273087859004933809189)
        ·
          refine ⟨11667426203973563425089223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62226273087859004933809189 11667426203973563425089223)
          ·
            refine ⟨17501139305960345137633835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11667426203973563425089223 17501139305960345137633835)
            ·
              refine ⟨26251708958940517706450753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17501139305960345137633835 26251708958940517706450753)
              ·
                refine ⟨19688781719205388279838065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26251708958940517706450753 19688781719205388279838065)
                ·
                  refine ⟨14766586289404041209878549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19688781719205388279838065 14766586289404041209878549)
                  ·
                    refine ⟨692183732315814431713057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14766586289404041209878549 692183732315814431713057)
                    ·
                      rfl

theorem cell23_4044069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_4044069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044069 prefixEnd_4044069 := by exact prefixLift 4044069
  have htrace : WordTrace (prefixWord ++ tailWord_4044069) baseStart_4044069 baseEnd_4044069 := by
    simpa [prefixWord, tailWord_4044069, baseEnd_4044069] using wordTrace_append hprefix tailTrace_4044069
  have hstable : (prefixWord ++ tailWord_4044069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044069).length < 2 ^ (prefixWord ++ tailWord_4044069).sum := by decide
  have hdescent : baseEnd_4044069 < baseStart_4044069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044133 : List Nat := [1, 3, 1, 3, 1, 2, 5, 2, 5]
def baseStart_4044133 : Nat := 118140960795 + 4044133 * 2 ^ 59
def prefixEnd_4044133 : Nat := 4983230072969 + 3 ^ 40 * 4044133 * 2
def baseEnd_4044133 : Nat := 230731562189925671637653

theorem tailTrace_4044133 : CollatzResearch.WordTrace tailWord_4044133 prefixEnd_4044133 230731562189925671637653 := by
  unfold tailWord_4044133
  simp only [CollatzResearch.WordTrace]
  refine ⟨147501648257804298773433053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98334432171869532515622035 147501648257804298773433053)
  ·
    refine ⟨55313118096676612040037395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147501648257804298773433053 55313118096676612040037395)
    ·
      refine ⟨82969677145014918060056093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55313118096676612040037395 82969677145014918060056093)
      ·
        refine ⟨31113628929380594272521035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82969677145014918060056093 31113628929380594272521035)
        ·
          refine ⟨46670443394070891408781553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31113628929380594272521035 46670443394070891408781553)
          ·
            refine ⟨35002832545553168556586165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46670443394070891408781553 35002832545553168556586165)
            ·
              refine ⟨3281515551145609552179953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35002832545553168556586165 3281515551145609552179953)
              ·
                refine ⟨2461136663359207164134965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3281515551145609552179953 2461136663359207164134965)
                ·
                  refine ⟨230731562189925671637653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2461136663359207164134965 230731562189925671637653)
                  ·
                    rfl

theorem cell23_4044133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 5].length) (baseStart_4044133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044133 prefixEnd_4044133 := by exact prefixLift 4044133
  have htrace : WordTrace (prefixWord ++ tailWord_4044133) baseStart_4044133 baseEnd_4044133 := by
    simpa [prefixWord, tailWord_4044133, baseEnd_4044133] using wordTrace_append hprefix tailTrace_4044133
  have hstable : (prefixWord ++ tailWord_4044133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044133).length < 2 ^ (prefixWord ++ tailWord_4044133).sum := by decide
  have hdescent : baseEnd_4044133 < baseStart_4044133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044250 : List Nat := [3, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3]
def baseStart_4044250 : Nat := 118140960795 + 4044250 * 2 ^ 59
def prefixEnd_4044250 : Nat := 4983230072969 + 3 ^ 40 * 4044250 * 2
def baseEnd_4044250 : Nat := 2076644136945907086975839

theorem tailTrace_4044250 : CollatzResearch.WordTrace tailWord_4044250 prefixEnd_4044250 2076644136945907086975839 := by
  unfold tailWord_4044250
  simp only [CollatzResearch.WordTrace]
  refine ⟨36876478899595106938860551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98337277065586951836961469 36876478899595106938860551)
  ·
    refine ⟨55314718349392660408290827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36876478899595106938860551 55314718349392660408290827)
    ·
      refine ⟨82972077524088990612436241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55314718349392660408290827 82972077524088990612436241)
      ·
        refine ⟨62229058143066742959327181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82972077524088990612436241 62229058143066742959327181)
        ·
          refine ⟨23335896803650028609747693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62229058143066742959327181 23335896803650028609747693)
          ·
            refine ⟨8750961301368760728655385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23335896803650028609747693 8750961301368760728655385)
            ·
              refine ⟨6563220976026570546491539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8750961301368760728655385 6563220976026570546491539)
              ·
                refine ⟨9844831464039855819737309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6563220976026570546491539 9844831464039855819737309)
                ·
                  refine ⟨3691811799014945932401491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9844831464039855819737309 3691811799014945932401491)
                  ·
                    refine ⟨5537717698522418898602237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3691811799014945932401491 5537717698522418898602237)
                    ·
                      refine ⟨2076644136945907086975839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5537717698522418898602237 2076644136945907086975839)
                      ·
                        rfl

theorem cell23_4044250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_4044250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044250 prefixEnd_4044250 := by exact prefixLift 4044250
  have htrace : WordTrace (prefixWord ++ tailWord_4044250) baseStart_4044250 baseEnd_4044250 := by
    simpa [prefixWord, tailWord_4044250, baseEnd_4044250] using wordTrace_append hprefix tailTrace_4044250
  have hstable : (prefixWord ++ tailWord_4044250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044250).length < 2 ^ (prefixWord ++ tailWord_4044250).sum := by decide
  have hdescent : baseEnd_4044250 < baseStart_4044250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044256 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 4]
def baseStart_4044256 : Nat := 118140960795 + 4044256 * 2 ^ 59
def prefixEnd_4044256 : Nat := 4983230072969 + 3 ^ 40 * 4044256 * 2
def baseEnd_4044256 : Nat := 2076647217829834063500811

theorem tailTrace_4044256 : CollatzResearch.WordTrace tailWord_4044256 prefixEnd_4044256 2076647217829834063500811 := by
  unfold tailWord_4044256
  simp only [CollatzResearch.WordTrace]
  refine ⟨73753067218179345390080311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98337422957572460520107081 73753067218179345390080311)
  ·
    refine ⟨110629600827269018085120467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73753067218179345390080311 110629600827269018085120467)
    ·
      refine ⟨165944401240903527127680701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110629600827269018085120467 165944401240903527127680701)
      ·
        refine ⟨62229150465338822672880263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165944401240903527127680701 62229150465338822672880263)
        ·
          refine ⟨93343725698008234009320395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62229150465338822672880263 93343725698008234009320395)
          ·
            refine ⟨140015588547012351013980593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93343725698008234009320395 140015588547012351013980593)
            ·
              refine ⟨105011691410259263260485445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140015588547012351013980593 105011691410259263260485445)
              ·
                refine ⟨19689692139423611861341021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105011691410259263260485445 19689692139423611861341021)
                ·
                  refine ⟨7383634552283854448002883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19689692139423611861341021 7383634552283854448002883)
                  ·
                    refine ⟨11075451828425781672004325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7383634552283854448002883 11075451828425781672004325)
                    ·
                      refine ⟨2076647217829834063500811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11075451828425781672004325 2076647217829834063500811)
                      ·
                        rfl

theorem cell23_4044256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_4044256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044256 prefixEnd_4044256 := by exact prefixLift 4044256
  have htrace : WordTrace (prefixWord ++ tailWord_4044256) baseStart_4044256 baseEnd_4044256 := by
    simpa [prefixWord, tailWord_4044256, baseEnd_4044256] using wordTrace_append hprefix tailTrace_4044256
  have hstable : (prefixWord ++ tailWord_4044256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044256).length < 2 ^ (prefixWord ++ tailWord_4044256).sum := by decide
  have hdescent : baseEnd_4044256 < baseStart_4044256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044273 : List Nat := [1, 2, 2, 2, 3, 2, 1, 4, 1, 1, 4]
def baseStart_4044273 : Nat := 118140960795 + 4044273 * 2 ^ 59
def prefixEnd_4044273 : Nat := 4983230072969 + 3 ^ 40 * 4044273 * 2
def baseEnd_4044273 : Nat := 2076655947000960496988233

theorem tailTrace_4044273 : CollatzResearch.WordTrace tailWord_4044273 prefixEnd_4044273 2076655947000960496988233 := by
  unfold tailWord_4044273
  simp only [CollatzResearch.WordTrace]
  refine ⟨147506754477297102683529473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98337836318198068455686315 147506754477297102683529473)
  ·
    refine ⟨110630065857972827012647105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147506754477297102683529473 110630065857972827012647105)
    ·
      refine ⟨82972549393479620259485329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110630065857972827012647105 82972549393479620259485329)
      ·
        refine ⟨62229412045109715194613997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82972549393479620259485329 62229412045109715194613997)
        ·
          refine ⟨23336029516916143197980249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62229412045109715194613997 23336029516916143197980249)
          ·
            refine ⟨17502022137687107398485187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23336029516916143197980249 17502022137687107398485187)
            ·
              refine ⟨26253033206530661097727781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17502022137687107398485187 26253033206530661097727781)
              ·
                refine ⟨4922443726224498955823959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26253033206530661097727781 4922443726224498955823959)
                ·
                  refine ⟨7383665589336748433735939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4922443726224498955823959 7383665589336748433735939)
                  ·
                    refine ⟨11075498384005122650603909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7383665589336748433735939 11075498384005122650603909)
                    ·
                      refine ⟨2076655947000960496988233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11075498384005122650603909 2076655947000960496988233)
                      ·
                        rfl

theorem cell23_4044273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_4044273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044273 prefixEnd_4044273 := by exact prefixLift 4044273
  have htrace : WordTrace (prefixWord ++ tailWord_4044273) baseStart_4044273 baseEnd_4044273 := by
    simpa [prefixWord, tailWord_4044273, baseEnd_4044273] using wordTrace_append hprefix tailTrace_4044273
  have hstable : (prefixWord ++ tailWord_4044273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044273).length < 2 ^ (prefixWord ++ tailWord_4044273).sum := by decide
  have hdescent : baseEnd_4044273 < baseStart_4044273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044301 : List Nat := [1, 7, 1, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_4044301 : Nat := 118140960795 + 4044301 * 2 ^ 59
def prefixEnd_4044301 : Nat := 4983230072969 + 3 ^ 40 * 4044301 * 2
def baseEnd_4044301 : Nat := 2076670324459286387438105

theorem tailTrace_4044301 : CollatzResearch.WordTrace tailWord_4044301 prefixEnd_4044301 2076670324459286387438105 := by
  unfold tailWord_4044301
  simp only [CollatzResearch.WordTrace]
  refine ⟨147507775721195663465548757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98338517147463775643699171 147507775721195663465548757)
  ·
    refine ⟨3457213493465523362473799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 147507775721195663465548757 3457213493465523362473799)
    ·
      refine ⟨5185820240198285043710699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3457213493465523362473799 5185820240198285043710699)
      ·
        refine ⟨7778730360297427565566049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5185820240198285043710699 7778730360297427565566049)
        ·
          refine ⟨5834047770223070674174537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7778730360297427565566049 5834047770223070674174537)
          ·
            refine ⟨4375535827667303005630903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5834047770223070674174537 4375535827667303005630903)
            ·
              refine ⟨6563303741500954508446355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4375535827667303005630903 6563303741500954508446355)
              ·
                refine ⟨9844955612251431762669533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6563303741500954508446355 9844955612251431762669533)
                ·
                  refine ⟨3691858354594286911001075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9844955612251431762669533 3691858354594286911001075)
                  ·
                    refine ⟨5537787531891430366501613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3691858354594286911001075 5537787531891430366501613)
                    ·
                      refine ⟨2076670324459286387438105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5537787531891430366501613 2076670324459286387438105)
                      ·
                        rfl

theorem cell23_4044301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_4044301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044301 prefixEnd_4044301 := by exact prefixLift 4044301
  have htrace : WordTrace (prefixWord ++ tailWord_4044301) baseStart_4044301 baseEnd_4044301 := by
    simpa [prefixWord, tailWord_4044301, baseEnd_4044301] using wordTrace_append hprefix tailTrace_4044301
  have hstable : (prefixWord ++ tailWord_4044301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044301).length < 2 ^ (prefixWord ++ tailWord_4044301).sum := by decide
  have hdescent : baseEnd_4044301 < baseStart_4044301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044307 : List Nat := [1, 1, 1, 2, 1, 8, 1, 1, 3, 2, 2]
def baseStart_4044307 : Nat := 118140960795 + 4044307 * 2 ^ 59
def prefixEnd_4044307 : Nat := 4983230072969 + 3 ^ 40 * 4044307 * 2
def baseEnd_4044307 : Nat := 2076673405343213363963077

theorem tailTrace_4044307 : CollatzResearch.WordTrace tailWord_4044307 prefixEnd_4044307 2076673405343213363963077 := by
  unfold tailWord_4044307
  simp only [CollatzResearch.WordTrace]
  refine ⟨147507994559173926490267175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98338663039449284326844783 147507994559173926490267175)
  ·
    refine ⟨221261991838760889735400763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147507994559173926490267175 221261991838760889735400763)
    ·
      refine ⟨331892987758141334603101145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221261991838760889735400763 331892987758141334603101145)
      ·
        refine ⟨248919740818606000952325859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331892987758141334603101145 248919740818606000952325859)
        ·
          refine ⟨373379611227909001428488789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248919740818606000952325859 373379611227909001428488789)
          ·
            refine ⟨4375542319077058610490103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 373379611227909001428488789 4375542319077058610490103)
            ·
              refine ⟨6563313478615587915735155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4375542319077058610490103 6563313478615587915735155)
              ·
                refine ⟨9844970217923381873602733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6563313478615587915735155 9844970217923381873602733)
                ·
                  refine ⟨3691863831721268202601025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9844970217923381873602733 3691863831721268202601025)
                  ·
                    refine ⟨2768897873790951151950769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3691863831721268202601025 2768897873790951151950769)
                    ·
                      refine ⟨2076673405343213363963077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2768897873790951151950769 2076673405343213363963077)
                      ·
                        rfl

theorem cell23_4044307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 2, 2].length) (baseStart_4044307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044307 prefixEnd_4044307 := by exact prefixLift 4044307
  have htrace : WordTrace (prefixWord ++ tailWord_4044307) baseStart_4044307 baseEnd_4044307 := by
    simpa [prefixWord, tailWord_4044307, baseEnd_4044307] using wordTrace_append hprefix tailTrace_4044307
  have hstable : (prefixWord ++ tailWord_4044307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044307).length < 2 ^ (prefixWord ++ tailWord_4044307).sum := by decide
  have hdescent : baseEnd_4044307 < baseStart_4044307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044316 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_4044316 : Nat := 118140960795 + 4044316 * 2 ^ 59
def prefixEnd_4044316 : Nat := 4983230072969 + 3 ^ 40 * 4044316 * 2
def baseEnd_4044316 : Nat := 2076678026669103828750535

theorem tailTrace_4044316 : CollatzResearch.WordTrace tailWord_4044316 prefixEnd_4044316 2076678026669103828750535 := by
  unfold tailWord_4044316
  simp only [CollatzResearch.WordTrace]
  refine ⟨73754161408070660513672401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98338881877427547351563201 73754161408070660513672401)
  ·
    refine ⟨55315621056052995385254301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73754161408070660513672401 55315621056052995385254301)
    ·
      refine ⟨20743357896019873269470363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55315621056052995385254301 20743357896019873269470363)
      ·
        refine ⟨31115036844029809904205545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20743357896019873269470363 31115036844029809904205545)
        ·
          refine ⟨23336277633022357428154159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31115036844029809904205545 23336277633022357428154159)
          ·
            refine ⟨35004416449533536142231239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23336277633022357428154159 35004416449533536142231239)
            ·
              refine ⟨52506624674300304213346859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35004416449533536142231239 52506624674300304213346859)
              ·
                refine ⟨78759937011450456320020289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52506624674300304213346859 78759937011450456320020289)
                ·
                  refine ⟨59069952758587842240015217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78759937011450456320020289 59069952758587842240015217)
                  ·
                    refine ⟨44302464568940881680011413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59069952758587842240015217 44302464568940881680011413)
                    ·
                      refine ⟨2076678026669103828750535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44302464568940881680011413 2076678026669103828750535)
                      ·
                        rfl

theorem cell23_4044316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_4044316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044316 prefixEnd_4044316 := by exact prefixLift 4044316
  have htrace : WordTrace (prefixWord ++ tailWord_4044316) baseStart_4044316 baseEnd_4044316 := by
    simpa [prefixWord, tailWord_4044316, baseEnd_4044316] using wordTrace_append hprefix tailTrace_4044316
  have hstable : (prefixWord ++ tailWord_4044316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044316).length < 2 ^ (prefixWord ++ tailWord_4044316).sum := by decide
  have hdescent : baseEnd_4044316 < baseStart_4044316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044358 : List Nat := [6, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_4044358 : Nat := 118140960795 + 4044358 * 2 ^ 59
def prefixEnd_4044358 : Nat := 4983230072969 + 3 ^ 40 * 4044358 * 2
def baseEnd_4044358 : Nat := 2076699592856592664425343

theorem tailTrace_4044358 : CollatzResearch.WordTrace tailWord_4044358 prefixEnd_4044358 2076699592856592664425343 := by
  unfold tailWord_4044358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4609682958812161318761679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98339903121326108133582485 4609682958812161318761679)
  ·
    refine ⟨6914524438218241978142519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4609682958812161318761679 6914524438218241978142519)
    ·
      refine ⟨10371786657327362967213779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6914524438218241978142519 10371786657327362967213779)
      ·
        refine ⟨15557679985991044450820669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10371786657327362967213779 15557679985991044450820669)
        ·
          refine ⟨5834129994746641669057751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15557679985991044450820669 5834129994746641669057751)
          ·
            refine ⟨8751194992119962503586627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5834129994746641669057751 8751194992119962503586627)
            ·
              refine ⟨13126792488179943755379941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8751194992119962503586627 13126792488179943755379941)
              ·
                refine ⟨2461273591533739454133739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13126792488179943755379941 2461273591533739454133739)
                ·
                  refine ⟨3691910387300609181200609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2461273591533739454133739 3691910387300609181200609)
                  ·
                    refine ⟨2768932790475456885900457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3691910387300609181200609 2768932790475456885900457)
                    ·
                      refine ⟨2076699592856592664425343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2768932790475456885900457 2076699592856592664425343)
                      ·
                        rfl

theorem cell23_4044358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_4044358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044358 prefixEnd_4044358 := by exact prefixLift 4044358
  have htrace : WordTrace (prefixWord ++ tailWord_4044358) baseStart_4044358 baseEnd_4044358 := by
    simpa [prefixWord, tailWord_4044358, baseEnd_4044358] using wordTrace_append hprefix tailTrace_4044358
  have hstable : (prefixWord ++ tailWord_4044358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044358).length < 2 ^ (prefixWord ++ tailWord_4044358).sum := by decide
  have hdescent : baseEnd_4044358 < baseStart_4044358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044363 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 5, 4, 2]
def baseStart_4044363 : Nat := 118140960795 + 4044363 * 2 ^ 59
def prefixEnd_4044363 : Nat := 4983230072969 + 3 ^ 40 * 4044363 * 2
def baseEnd_4044363 : Nat := 2076702160259865144862819

theorem tailTrace_4044363 : CollatzResearch.WordTrace tailWord_4044363 prefixEnd_4044363 2076702160259865144862819 := by
  unfold tailWord_4044363
  simp only [CollatzResearch.WordTrace]
  refine ⟨147510037046971048054305743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98340024697980698702870495 147510037046971048054305743)
  ·
    refine ⟨221265055570456572081458615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147510037046971048054305743 221265055570456572081458615)
    ·
      refine ⟨331897583355684858122187923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221265055570456572081458615 331897583355684858122187923)
      ·
        refine ⟨497846375033527287183281885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331897583355684858122187923 497846375033527287183281885)
        ·
          refine ⟨186692390637572732693730707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 497846375033527287183281885 186692390637572732693730707)
          ·
            refine ⟨280038585956359099040596061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186692390637572732693730707 280038585956359099040596061)
            ·
              refine ⟨105014469733634662140223523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280038585956359099040596061 105014469733634662140223523)
              ·
                refine ⟨157521704600451993210335285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105014469733634662140223523 157521704600451993210335285)
                ·
                  refine ⟨14767659806292374363468933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157521704600451993210335285 14767659806292374363468933)
                  ·
                    refine ⟨2768936213679820193150425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14767659806292374363468933 2768936213679820193150425)
                    ·
                      refine ⟨2076702160259865144862819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2768936213679820193150425 2076702160259865144862819)
                      ·
                        rfl

theorem cell23_4044363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 4, 2].length) (baseStart_4044363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044363 prefixEnd_4044363 := by exact prefixLift 4044363
  have htrace : WordTrace (prefixWord ++ tailWord_4044363) baseStart_4044363 baseEnd_4044363 := by
    simpa [prefixWord, tailWord_4044363, baseEnd_4044363] using wordTrace_append hprefix tailTrace_4044363
  have hstable : (prefixWord ++ tailWord_4044363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044363).length < 2 ^ (prefixWord ++ tailWord_4044363).sum := by decide
  have hdescent : baseEnd_4044363 < baseStart_4044363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044396 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 7]
def baseStart_4044396 : Nat := 118140960795 + 4044396 * 2 ^ 59
def prefixEnd_4044396 : Nat := 4983230072969 + 3 ^ 40 * 4044396 * 2
def baseEnd_4044396 : Nat := 2076719105121463515750167

theorem tailTrace_4044396 : CollatzResearch.WordTrace tailWord_4044396 prefixEnd_4044396 2076719105121463515750167 := by
  unfold tailWord_4044396
  simp only [CollatzResearch.WordTrace]
  refine ⟨73755620327925747345128521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98340827103900996460171361 73755620327925747345128521)
  ·
    refine ⟨55316715245944310508846391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73755620327925747345128521 55316715245944310508846391)
    ·
      refine ⟨82975072868916465763269587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55316715245944310508846391 82975072868916465763269587)
      ·
        refine ⟨124462609303374698644904381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82975072868916465763269587 124462609303374698644904381)
        ·
          refine ⟨46673478488765511991839143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124462609303374698644904381 46673478488765511991839143)
          ·
            refine ⟨70010217733148267987758715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46673478488765511991839143 70010217733148267987758715)
            ·
              refine ⟨105015326599722401981638073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70010217733148267987758715 105015326599722401981638073)
              ·
                refine ⟨78761494949791801486228555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105015326599722401981638073 78761494949791801486228555)
                ·
                  refine ⟨118142242424687702229342833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78761494949791801486228555 118142242424687702229342833)
                  ·
                    refine ⟨88606681818515776672007125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118142242424687702229342833 88606681818515776672007125)
                    ·
                      refine ⟨2076719105121463515750167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88606681818515776672007125 2076719105121463515750167)
                      ·
                        rfl

theorem cell23_4044396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_4044396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044396 prefixEnd_4044396 := by exact prefixLift 4044396
  have htrace : WordTrace (prefixWord ++ tailWord_4044396) baseStart_4044396 baseEnd_4044396 := by
    simpa [prefixWord, tailWord_4044396, baseEnd_4044396] using wordTrace_append hprefix tailTrace_4044396
  have hstable : (prefixWord ++ tailWord_4044396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044396).length < 2 ^ (prefixWord ++ tailWord_4044396).sum := by decide
  have hdescent : baseEnd_4044396 < baseStart_4044396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044420 : List Nat := [2, 3, 2, 1, 4, 1, 2, 1, 7]
def baseStart_4044420 : Nat := 118140960795 + 4044420 * 2 ^ 59
def prefixEnd_4044420 : Nat := 4983230072969 + 3 ^ 40 * 4044420 * 2
def baseEnd_4044420 : Nat := 230747936517463491316673

theorem tailTrace_4044420 : CollatzResearch.WordTrace tailWord_4044420 prefixEnd_4044420 230747936517463491316673 := by
  unfold tailWord_4044420
  simp only [CollatzResearch.WordTrace]
  refine ⟨73756058003882273394565357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98341410671843031192753809 73756058003882273394565357)
  ·
    refine ⟨27658521751455852522962009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73756058003882273394565357 27658521751455852522962009)
    ·
      refine ⟨20743891313591889392221507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27658521751455852522962009 20743891313591889392221507)
      ·
        refine ⟨31115836970387834088332261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20743891313591889392221507 31115836970387834088332261)
        ·
          refine ⟨5834219431947718891562299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31115836970387834088332261 5834219431947718891562299)
          ·
            refine ⟨8751329147921578337343449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5834219431947718891562299 8751329147921578337343449)
            ·
              refine ⟨6563496860941183753007587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8751329147921578337343449 6563496860941183753007587)
              ·
                refine ⟨9845245291411775629511381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6563496860941183753007587 9845245291411775629511381)
                ·
                  refine ⟨230747936517463491316673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9845245291411775629511381 230747936517463491316673)
                  ·
                    rfl

theorem cell23_4044420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_4044420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044420 prefixEnd_4044420 := by exact prefixLift 4044420
  have htrace : WordTrace (prefixWord ++ tailWord_4044420) baseStart_4044420 baseEnd_4044420 := by
    simpa [prefixWord, tailWord_4044420, baseEnd_4044420] using wordTrace_append hprefix tailTrace_4044420
  have hstable : (prefixWord ++ tailWord_4044420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044420).length < 2 ^ (prefixWord ++ tailWord_4044420).sum := by decide
  have hdescent : baseEnd_4044420 < baseStart_4044420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044430 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3]
def baseStart_4044430 : Nat := 118140960795 + 4044430 * 2 ^ 59
def prefixEnd_4044430 : Nat := 4983230072969 + 3 ^ 40 * 4044430 * 2
def baseEnd_4044430 : Nat := 2076736563463716382725011

theorem tailTrace_4044430 : CollatzResearch.WordTrace tailWord_4044430 prefixEnd_4044430 2076736563463716382725011 := by
  unfold tailWord_4044430
  simp only [CollatzResearch.WordTrace]
  refine ⟨18439060092216039812124343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98341653825152212331329829 18439060092216039812124343)
  ·
    refine ⟨27658590138324059718186515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18439060092216039812124343 27658590138324059718186515)
    ·
      refine ⟨41487885207486089577279773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27658590138324059718186515 41487885207486089577279773)
      ·
        refine ⟨15557956952807283591479915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41487885207486089577279773 15557956952807283591479915)
        ·
          refine ⟨23336935429210925387219873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15557956952807283591479915 23336935429210925387219873)
          ·
            refine ⟨17502701571908194040414905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23336935429210925387219873 17502701571908194040414905)
            ·
              refine ⟨13127026178931145530311179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17502701571908194040414905 13127026178931145530311179)
              ·
                refine ⟨19690539268396718295466769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13127026178931145530311179 19690539268396718295466769)
                ·
                  refine ⟨14767904451297538721600077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19690539268396718295466769 14767904451297538721600077)
                  ·
                    refine ⟨5537964169236577020600029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14767904451297538721600077 5537964169236577020600029)
                    ·
                      refine ⟨2076736563463716382725011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5537964169236577020600029 2076736563463716382725011)
                      ·
                        rfl

theorem cell23_4044430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_4044430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044430 prefixEnd_4044430 := by exact prefixLift 4044430
  have htrace : WordTrace (prefixWord ++ tailWord_4044430) baseStart_4044430 baseEnd_4044430 := by
    simpa [prefixWord, tailWord_4044430, baseEnd_4044430] using wordTrace_append hprefix tailTrace_4044430
  have hstable : (prefixWord ++ tailWord_4044430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044430).length < 2 ^ (prefixWord ++ tailWord_4044430).sum := by decide
  have hdescent : baseEnd_4044430 < baseStart_4044430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044453 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 1, 3, 4]
def baseStart_4044453 : Nat := 118140960795 + 4044453 * 2 ^ 59
def prefixEnd_4044453 : Nat := 4983230072969 + 3 ^ 40 * 4044453 * 2
def baseEnd_4044453 : Nat := 2076748373518769792737405

theorem tailTrace_4044453 : CollatzResearch.WordTrace tailWord_4044453 prefixEnd_4044453 2076748373518769792737405 := by
  unfold tailWord_4044453
  simp only [CollatzResearch.WordTrace]
  refine ⟨147513319616644993425082013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98342213077763328950054675 147513319616644993425082013)
  ·
    refine ⟨55317494856241872534405755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147513319616644993425082013 55317494856241872534405755)
    ·
      refine ⟨82976242284362808801608633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55317494856241872534405755 82976242284362808801608633)
      ·
        refine ⟨62232181713272106601206475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82976242284362808801608633 62232181713272106601206475)
        ·
          refine ⟨93348272569908159901809713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62232181713272106601206475 93348272569908159901809713)
          ·
            refine ⟨70011204427431119926357285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93348272569908159901809713 70011204427431119926357285)
            ·
              refine ⟨13127100830143334986191991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70011204427431119926357285 13127100830143334986191991)
              ·
                refine ⟨19690651245215002479287987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13127100830143334986191991 19690651245215002479287987)
                ·
                  refine ⟨29535976867822503718931981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19690651245215002479287987 29535976867822503718931981)
                  ·
                    refine ⟨11075991325433438894599493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29535976867822503718931981 11075991325433438894599493)
                    ·
                      refine ⟨2076748373518769792737405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11075991325433438894599493 2076748373518769792737405)
                      ·
                        rfl

theorem cell23_4044453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_4044453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044453 prefixEnd_4044453 := by exact prefixLift 4044453
  have htrace : WordTrace (prefixWord ++ tailWord_4044453) baseStart_4044453 baseEnd_4044453 := by
    simpa [prefixWord, tailWord_4044453, baseEnd_4044453] using wordTrace_append hprefix tailTrace_4044453
  have hstable : (prefixWord ++ tailWord_4044453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044453).length < 2 ^ (prefixWord ++ tailWord_4044453).sum := by decide
  have hdescent : baseEnd_4044453 < baseStart_4044453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044482 : List Nat := [3, 5, 1, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_4044482 : Nat := 118140960795 + 4044482 * 2 ^ 59
def prefixEnd_4044482 : Nat := 4983230072969 + 3 ^ 40 * 4044482 * 2
def baseEnd_4044482 : Nat := 2076763264457750179274773

theorem tailTrace_4044482 : CollatzResearch.WordTrace tailWord_4044482 prefixEnd_4044482 2076763264457750179274773 := by
  unfold tailWord_4044482
  simp only [CollatzResearch.WordTrace]
  refine ⟨36878594333384982844471925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98342918222359954251925133 36878594333384982844471925)
  ·
    refine ⟨3457368218754842141669243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36878594333384982844471925 3457368218754842141669243)
    ·
      refine ⟨5186052328132263212503865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3457368218754842141669243 5186052328132263212503865)
      ·
        refine ⟨3889539246099197409377899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5186052328132263212503865 3889539246099197409377899)
        ·
          refine ⟨5834308869148796114066849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3889539246099197409377899 5834308869148796114066849)
          ·
            refine ⟨4375731651861597085550137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5834308869148796114066849 4375731651861597085550137)
            ·
              refine ⟨3281798738896197814162603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4375731651861597085550137 3281798738896197814162603)
              ·
                refine ⟨4922698108344296721243905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3281798738896197814162603 4922698108344296721243905)
                ·
                  refine ⟨3692023581258222540932929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4922698108344296721243905 3692023581258222540932929)
                  ·
                    refine ⟨2769017685943666905699697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3692023581258222540932929 2769017685943666905699697)
                    ·
                      refine ⟨2076763264457750179274773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2769017685943666905699697 2076763264457750179274773)
                      ·
                        rfl

theorem cell23_4044482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_4044482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044482 prefixEnd_4044482 := by exact prefixLift 4044482
  have htrace : WordTrace (prefixWord ++ tailWord_4044482) baseStart_4044482 baseEnd_4044482 := by
    simpa [prefixWord, tailWord_4044482, baseEnd_4044482] using wordTrace_append hprefix tailTrace_4044482
  have hstable : (prefixWord ++ tailWord_4044482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044482).length < 2 ^ (prefixWord ++ tailWord_4044482).sum := by decide
  have hdescent : baseEnd_4044482 < baseStart_4044482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044563 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 5]
def baseStart_4044563 : Nat := 118140960795 + 4044563 * 2 ^ 59
def prefixEnd_4044563 : Nat := 4983230072969 + 3 ^ 40 * 4044563 * 2
def baseEnd_4044563 : Nat := 2076804856390764362361899

theorem tailTrace_4044563 : CollatzResearch.WordTrace tailWord_4044563 prefixEnd_4044563 2076804856390764362361899 := by
  unfold tailWord_4044563
  simp only [CollatzResearch.WordTrace]
  refine ⟨147517331646246482211586343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98344887764164321474390895 147517331646246482211586343)
  ·
    refine ⟨221275997469369723317379515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147517331646246482211586343 221275997469369723317379515)
    ·
      refine ⟨331913996204054584976069273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221275997469369723317379515 331913996204054584976069273)
      ·
        refine ⟨248935497153040938732051955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331913996204054584976069273 248935497153040938732051955)
        ·
          refine ⟨373403245729561408098077933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248935497153040938732051955 373403245729561408098077933)
          ·
            refine ⟨140026217148585528036779225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373403245729561408098077933 140026217148585528036779225)
            ·
              refine ⟨105019662861439146027584419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140026217148585528036779225 105019662861439146027584419)
              ·
                refine ⟨157529494292158719041376629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105019662861439146027584419 157529494292158719041376629)
                ·
                  refine ⟨14768390089889879910129059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157529494292158719041376629 14768390089889879910129059)
                  ·
                    refine ⟨22152585134834819865193589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14768390089889879910129059 22152585134834819865193589)
                    ·
                      refine ⟨2076804856390764362361899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22152585134834819865193589 2076804856390764362361899)
                      ·
                        rfl

theorem cell23_4044563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_4044563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044563 prefixEnd_4044563 := by exact prefixLift 4044563
  have htrace : WordTrace (prefixWord ++ tailWord_4044563) baseStart_4044563 baseEnd_4044563 := by
    simpa [prefixWord, tailWord_4044563, baseEnd_4044563] using wordTrace_append hprefix tailTrace_4044563
  have hstable : (prefixWord ++ tailWord_4044563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044563).length < 2 ^ (prefixWord ++ tailWord_4044563).sum := by decide
  have hdescent : baseEnd_4044563 < baseStart_4044563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044570 : List Nat := [3, 1, 1, 3, 2, 2, 2, 2, 1, 6]
def baseStart_4044570 : Nat := 118140960795 + 4044570 * 2 ^ 59
def prefixEnd_4044570 : Nat := 4983230072969 + 3 ^ 40 * 4044570 * 2
def baseEnd_4044570 : Nat := 692269483585115278324789

theorem tailTrace_4044570 : CollatzResearch.WordTrace tailWord_4044570 prefixEnd_4044570 692269483585115278324789 := by
  unfold tailWord_4044570
  simp only [CollatzResearch.WordTrace]
  refine ⟨36879396739305280601772791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98345057971480748271394109 36879396739305280601772791)
  ·
    refine ⟨55319095108957920902659187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36879396739305280601772791 55319095108957920902659187)
    ·
      refine ⟨82978642663436881353988781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55319095108957920902659187 82978642663436881353988781)
      ·
        refine ⟨31116990998788830507745793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82978642663436881353988781 31116990998788830507745793)
        ·
          refine ⟨23337743249091622880809345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31116990998788830507745793 23337743249091622880809345)
          ·
            refine ⟨17503307436818717160607009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23337743249091622880809345 17503307436818717160607009)
            ·
              refine ⟨13127480577614037870455257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17503307436818717160607009 13127480577614037870455257)
              ·
                refine ⟨9845610433210528402841443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13127480577614037870455257 9845610433210528402841443)
                ·
                  refine ⟨14768415649815792604262165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9845610433210528402841443 14768415649815792604262165)
                  ·
                    refine ⟨692269483585115278324789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14768415649815792604262165 692269483585115278324789)
                    ·
                      rfl

theorem cell23_4044570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_4044570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044570 prefixEnd_4044570 := by exact prefixLift 4044570
  have htrace : WordTrace (prefixWord ++ tailWord_4044570) baseStart_4044570 baseEnd_4044570 := by
    simpa [prefixWord, tailWord_4044570, baseEnd_4044570] using wordTrace_append hprefix tailTrace_4044570
  have hstable : (prefixWord ++ tailWord_4044570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044570).length < 2 ^ (prefixWord ++ tailWord_4044570).sum := by decide
  have hdescent : baseEnd_4044570 < baseStart_4044570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044577 : List Nat := [1, 2, 3, 2, 1, 4, 1, 3, 1, 1, 4]
def baseStart_4044577 : Nat := 118140960795 + 4044577 * 2 ^ 59
def prefixEnd_4044577 : Nat := 4983230072969 + 3 ^ 40 * 4044577 * 2
def baseEnd_4044577 : Nat := 2076812045119927307586835

theorem tailTrace_4044577 : CollatzResearch.WordTrace tailWord_4044577 prefixEnd_4044577 2076812045119927307586835 := by
  unfold tailWord_4044577
  simp only [CollatzResearch.WordTrace]
  refine ⟨147517842268195762602595985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98345228178797175068397323 147517842268195762602595985)
  ·
    refine ⟨110638381701146821951946989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147517842268195762602595985 110638381701146821951946989)
    ·
      refine ⟨41489393137930058231980121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110638381701146821951946989 41489393137930058231980121)
      ·
        refine ⟨31117044853447543673985091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41489393137930058231980121 31117044853447543673985091)
        ·
          refine ⟨46675567280171315510977637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31117044853447543673985091 46675567280171315510977637)
          ·
            refine ⟨8751668865032121658308307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46675567280171315510977637 8751668865032121658308307)
            ·
              refine ⟨13127503297548182487462461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8751668865032121658308307 13127503297548182487462461)
              ·
                refine ⟨4922813736580568432798423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13127503297548182487462461 4922813736580568432798423)
                ·
                  refine ⟨7384220604870852649197635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4922813736580568432798423 7384220604870852649197635)
                  ·
                    refine ⟨11076330907306278973796453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7384220604870852649197635 11076330907306278973796453)
                    ·
                      refine ⟨2076812045119927307586835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11076330907306278973796453 2076812045119927307586835)
                      ·
                        rfl

theorem cell23_4044577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_4044577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044577 prefixEnd_4044577 := by exact prefixLift 4044577
  have htrace : WordTrace (prefixWord ++ tailWord_4044577) baseStart_4044577 baseEnd_4044577 := by
    simpa [prefixWord, tailWord_4044577, baseEnd_4044577] using wordTrace_append hprefix tailTrace_4044577
  have hstable : (prefixWord ++ tailWord_4044577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044577).length < 2 ^ (prefixWord ++ tailWord_4044577).sum := by decide
  have hdescent : baseEnd_4044577 < baseStart_4044577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
