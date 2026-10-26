import V185TrunkScan22Chunk465

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4154089 : List Nat := [1, 2, 1, 1, 1, 2, 8, 2, 4]
def baseStart_4154089 : Nat := 118140960795 + 4154089 * 2 ^ 59
def prefixEnd_4154089 : Nat := 4983230072969 + 3 ^ 40 * 4154089 * 2
def baseEnd_4154089 : Nat := 474009853012245075862933

theorem tailTrace_4154089 : CollatzResearch.WordTrace tailWord_4154089 prefixEnd_4154089 474009853012245075862933 := by
  unfold tailWord_4154089
  simp only [CollatzResearch.WordTrace]
  refine ⟨151512073047452489763161321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101008048698301659842107547 151512073047452489763161321)
  ·
    refine ⟨113634054785589367322370991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151512073047452489763161321 113634054785589367322370991)
    ·
      refine ⟨170451082178384050983556487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113634054785589367322370991 170451082178384050983556487)
      ·
        refine ⟨255676623267576076475334731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170451082178384050983556487 255676623267576076475334731)
        ·
          refine ⟨383514934901364114713002097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255676623267576076475334731 383514934901364114713002097)
          ·
            refine ⟨287636201176023086034751573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383514934901364114713002097 287636201176023086034751573)
            ·
              refine ⟨3370736732531520539469745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 287636201176023086034751573 3370736732531520539469745)
              ·
                refine ⟨2528052549398640404602309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3370736732531520539469745 2528052549398640404602309)
                ·
                  refine ⟨474009853012245075862933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2528052549398640404602309 474009853012245075862933)
                  ·
                    rfl

theorem cell22_4154089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 4].length) (baseStart_4154089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154089 prefixEnd_4154089 := by exact prefixLift 4154089
  have htrace : WordTrace (prefixWord ++ tailWord_4154089) baseStart_4154089 baseEnd_4154089 := by
    simpa [prefixWord, tailWord_4154089, baseEnd_4154089] using wordTrace_append hprefix tailTrace_4154089
  have hstable : (prefixWord ++ tailWord_4154089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154089).length < 2 ^ (prefixWord ++ tailWord_4154089).sum := by decide
  have hdescent : baseEnd_4154089 < baseStart_4154089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154102 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_4154102 : Nat := 118140960795 + 4154102 * 2 ^ 59
def prefixEnd_4154102 : Nat := 4983230072969 + 3 ^ 40 * 4154102 * 2
def baseEnd_4154102 : Nat := 1422034009202407527013759

theorem tailTrace_4154102 : CollatzResearch.WordTrace tailWord_4154102 prefixEnd_4154102 1422034009202407527013759 := by
  unfold tailWord_4154102
  simp only [CollatzResearch.WordTrace]
  refine ⟨9469534199775337061461535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101008364797603595322256373 9469534199775337061461535)
  ·
    refine ⟨14204301299663005592192303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9469534199775337061461535 14204301299663005592192303)
    ·
      refine ⟨21306451949494508388288455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14204301299663005592192303 21306451949494508388288455)
      ·
        refine ⟨31959677924241762582432683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21306451949494508388288455 31959677924241762582432683)
        ·
          refine ⟨47939516886362643873649025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31959677924241762582432683 47939516886362643873649025)
          ·
            refine ⟨35954637664771982905236769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47939516886362643873649025 35954637664771982905236769)
            ·
              refine ⟨26965978248578987178927577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35954637664771982905236769 26965978248578987178927577)
              ·
                refine ⟨20224483686434240384195683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26965978248578987178927577 20224483686434240384195683)
                ·
                  refine ⟨30336725529651360576293525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20224483686434240384195683 30336725529651360576293525)
                  ·
                    refine ⟨1422034009202407527013759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30336725529651360576293525 1422034009202407527013759)
                    ·
                      rfl

theorem cell22_4154102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_4154102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154102 prefixEnd_4154102 := by exact prefixLift 4154102
  have htrace : WordTrace (prefixWord ++ tailWord_4154102) baseStart_4154102 baseEnd_4154102 := by
    simpa [prefixWord, tailWord_4154102, baseEnd_4154102] using wordTrace_append hprefix tailTrace_4154102
  have hstable : (prefixWord ++ tailWord_4154102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154102).length < 2 ^ (prefixWord ++ tailWord_4154102).sum := by decide
  have hdescent : baseEnd_4154102 < baseStart_4154102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154119 : List Nat := [1, 1, 4, 4, 1, 1, 3, 1, 2, 4]
def baseStart_4154119 : Nat := 118140960795 + 4154119 * 2 ^ 59
def prefixEnd_4154119 : Nat := 4983230072969 + 3 ^ 40 * 4154119 * 2
def baseEnd_4154119 : Nat := 1422039828649825149338707

theorem tailTrace_4154119 : CollatzResearch.WordTrace tailWord_4154119 prefixEnd_4154119 1422039828649825149338707 := by
  unfold tailWord_4154119
  simp only [CollatzResearch.WordTrace]
  refine ⟨151513167237343804886753411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101008778158229203257835607 151513167237343804886753411)
  ·
    refine ⟨227269750856015707330130117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151513167237343804886753411 227269750856015707330130117)
    ·
      refine ⟨42613078285502945124399397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227269750856015707330130117 42613078285502945124399397)
      ·
        refine ⟨7989952178531802210824887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42613078285502945124399397 7989952178531802210824887)
        ·
          refine ⟨11984928267797703316237331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7989952178531802210824887 11984928267797703316237331)
          ·
            refine ⟨17977392401696554974355997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11984928267797703316237331 17977392401696554974355997)
            ·
              refine ⟨6741522150636208115383499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17977392401696554974355997 6741522150636208115383499)
              ·
                refine ⟨10112283225954312173075249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6741522150636208115383499 10112283225954312173075249)
                ·
                  refine ⟨7584212419465734129806437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10112283225954312173075249 7584212419465734129806437)
                  ·
                    refine ⟨1422039828649825149338707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7584212419465734129806437 1422039828649825149338707)
                    ·
                      rfl

theorem cell22_4154119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_4154119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154119 prefixEnd_4154119 := by exact prefixLift 4154119
  have htrace : WordTrace (prefixWord ++ tailWord_4154119) baseStart_4154119 baseEnd_4154119 := by
    simpa [prefixWord, tailWord_4154119, baseEnd_4154119] using wordTrace_append hprefix tailTrace_4154119
  have hstable : (prefixWord ++ tailWord_4154119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154119).length < 2 ^ (prefixWord ++ tailWord_4154119).sum := by decide
  have hdescent : baseEnd_4154119 < baseStart_4154119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154149 : List Nat := [1, 3, 1, 2, 3, 1, 4, 1, 3, 3]
def baseStart_4154149 : Nat := 118140960795 + 4154149 * 2 ^ 59
def prefixEnd_4154149 : Nat := 4983230072969 + 3 ^ 40 * 4154149 * 2
def baseEnd_4154149 : Nat := 1422050098262915071088615

theorem tailTrace_4154149 : CollatzResearch.WordTrace tailWord_4154149 prefixEnd_4154149 1422050098262915071088615 := by
  unfold tailWord_4154149
  simp only [CollatzResearch.WordTrace]
  refine ⟨151514261427235120010345501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101009507618156746673563667 151514261427235120010345501)
  ·
    refine ⟨56817848035213170003879563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151514261427235120010345501 56817848035213170003879563)
    ·
      refine ⟨85226772052819755005819345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56817848035213170003879563 85226772052819755005819345)
      ·
        refine ⟨63920079039614816254364509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85226772052819755005819345 63920079039614816254364509)
        ·
          refine ⟨23970029639855556095386691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63920079039614816254364509 23970029639855556095386691)
          ·
            refine ⟨35955044459783334143080037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23970029639855556095386691 35955044459783334143080037)
            ·
              refine ⟨6741570836209375151827507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35955044459783334143080037 6741570836209375151827507)
              ·
                refine ⟨10112356254314062727741261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6741570836209375151827507 10112356254314062727741261)
                ·
                  refine ⟨3792133595367773522902973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10112356254314062727741261 3792133595367773522902973)
                  ·
                    refine ⟨1422050098262915071088615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3792133595367773522902973 1422050098262915071088615)
                    ·
                      rfl

theorem cell22_4154149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_4154149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154149 prefixEnd_4154149 := by exact prefixLift 4154149
  have htrace : WordTrace (prefixWord ++ tailWord_4154149) baseStart_4154149 baseEnd_4154149 := by
    simpa [prefixWord, tailWord_4154149, baseEnd_4154149] using wordTrace_append hprefix tailTrace_4154149
  have hstable : (prefixWord ++ tailWord_4154149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154149).length < 2 ^ (prefixWord ++ tailWord_4154149).sum := by decide
  have hdescent : baseEnd_4154149 < baseStart_4154149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154237 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_4154237 : Nat := 118140960795 + 4154237 * 2 ^ 59
def prefixEnd_4154237 : Nat := 4983230072969 + 3 ^ 40 * 4154237 * 2
def baseEnd_4154237 : Nat := 1422080222461312174888345

theorem tailTrace_4154237 : CollatzResearch.WordTrace tailWord_4154237 prefixEnd_4154237 1422080222461312174888345 := by
  unfold tailWord_4154237
  simp only [CollatzResearch.WordTrace]
  refine ⟨151517471050916311039548965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101011647367277540693032643 151517471050916311039548965)
  ·
    refine ⟨28409525822046808319915431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151517471050916311039548965 28409525822046808319915431)
    ·
      refine ⟨42614288733070212479873147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28409525822046808319915431 42614288733070212479873147)
      ·
        refine ⟨63921433099605318719809721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42614288733070212479873147 63921433099605318719809721)
        ·
          refine ⟨47941074824703989039857291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63921433099605318719809721 47941074824703989039857291)
          ·
            refine ⟨71911612237055983559785937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47941074824703989039857291 71911612237055983559785937)
            ·
              refine ⟨53933709177791987669839453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71911612237055983559785937 53933709177791987669839453)
              ·
                refine ⟨20225140941671995376189795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53933709177791987669839453 20225140941671995376189795)
                ·
                  refine ⟨30337711412507993064284693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20225140941671995376189795 30337711412507993064284693)
                  ·
                    refine ⟨1422080222461312174888345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30337711412507993064284693 1422080222461312174888345)
                    ·
                      rfl

theorem cell22_4154237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_4154237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154237 prefixEnd_4154237 := by exact prefixLift 4154237
  have htrace : WordTrace (prefixWord ++ tailWord_4154237) baseStart_4154237 baseEnd_4154237 := by
    simpa [prefixWord, tailWord_4154237, baseEnd_4154237] using wordTrace_append hprefix tailTrace_4154237
  have hstable : (prefixWord ++ tailWord_4154237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154237).length < 2 ^ (prefixWord ++ tailWord_4154237).sum := by decide
  have hdescent : baseEnd_4154237 < baseStart_4154237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154258 : List Nat := [3, 2, 3, 2, 2, 1, 1, 4, 4]
def baseStart_4154258 : Nat := 118140960795 + 4154258 * 2 ^ 59
def prefixEnd_4154258 : Nat := 4983230072969 + 3 ^ 40 * 4154258 * 2
def baseEnd_4154258 : Nat := 474029137063491706704427

theorem tailTrace_4154258 : CollatzResearch.WordTrace tailWord_4154258 prefixEnd_4154258 474029137063491706704427 := by
  unfold tailWord_4154258
  simp only [CollatzResearch.WordTrace]
  refine ⟨37879559245960057906515857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101012157989226821084042285 37879559245960057906515857)
  ·
    refine ⟨28409669434470043429886893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37879559245960057906515857 28409669434470043429886893)
    ·
      refine ⟨10653626037926266286207585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28409669434470043429886893 10653626037926266286207585)
      ·
        refine ⟨7990219528444699714655689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10653626037926266286207585 7990219528444699714655689)
        ·
          refine ⟨5992664646333524785991767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7990219528444699714655689 5992664646333524785991767)
          ·
            refine ⟨8988996969500287178987651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5992664646333524785991767 8988996969500287178987651)
            ·
              refine ⟨13483495454250430768481477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8988996969500287178987651 13483495454250430768481477)
              ·
                refine ⟨2528155397671955769090277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13483495454250430768481477 2528155397671955769090277)
                ·
                  refine ⟨474029137063491706704427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2528155397671955769090277 474029137063491706704427)
                  ·
                    rfl

theorem cell22_4154258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_4154258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154258 prefixEnd_4154258 := by exact prefixLift 4154258
  have htrace : WordTrace (prefixWord ++ tailWord_4154258) baseStart_4154258 baseEnd_4154258 := by
    simpa [prefixWord, tailWord_4154258, baseEnd_4154258] using wordTrace_append hprefix tailTrace_4154258
  have hstable : (prefixWord ++ tailWord_4154258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154258).length < 2 ^ (prefixWord ++ tailWord_4154258).sum := by decide
  have hdescent : baseEnd_4154258 < baseStart_4154258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154284 : List Nat := [2, 2, 1, 1, 1, 1, 2, 6, 3, 3]
def baseStart_4154284 : Nat := 118140960795 + 4154284 * 2 ^ 59
def prefixEnd_4154284 : Nat := 4983230072969 + 3 ^ 40 * 4154284 * 2
def baseEnd_4154284 : Nat := 1422096311521819718963201

theorem tailTrace_4154284 : CollatzResearch.WordTrace tailWord_4154284 prefixEnd_4154284 1422096311521819718963201 := by
  unfold tailWord_4154284
  simp only [CollatzResearch.WordTrace]
  refine ⟨75759592640873019033254953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101012790187830692044339937 75759592640873019033254953)
  ·
    refine ⟨56819694480654764274941215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75759592640873019033254953 56819694480654764274941215)
    ·
      refine ⟨85229541720982146412411823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56819694480654764274941215 85229541720982146412411823)
      ·
        refine ⟨127844312581473219618617735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85229541720982146412411823 127844312581473219618617735)
        ·
          refine ⟨191766468872209829427926603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127844312581473219618617735 191766468872209829427926603)
          ·
            refine ⟨287649703308314744141889905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191766468872209829427926603 287649703308314744141889905)
            ·
              refine ⟨215737277481236058106417429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287649703308314744141889905 215737277481236058106417429)
              ·
                refine ⟨10112684881932940223738317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 215737277481236058106417429 10112684881932940223738317)
                ·
                  refine ⟨3792256830724852583901869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10112684881932940223738317 3792256830724852583901869)
                  ·
                    refine ⟨1422096311521819718963201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3792256830724852583901869 1422096311521819718963201)
                    ·
                      rfl

theorem cell22_4154284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_4154284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154284 prefixEnd_4154284 := by exact prefixLift 4154284
  have htrace : WordTrace (prefixWord ++ tailWord_4154284) baseStart_4154284 baseEnd_4154284 := by
    simpa [prefixWord, tailWord_4154284, baseEnd_4154284] using wordTrace_append hprefix tailTrace_4154284
  have hstable : (prefixWord ++ tailWord_4154284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154284).length < 2 ^ (prefixWord ++ tailWord_4154284).sum := by decide
  have hdescent : baseEnd_4154284 < baseStart_4154284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154294 : List Nat := [5, 1, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_4154294 : Nat := 118140960795 + 4154294 * 2 ^ 59
def prefixEnd_4154294 : Nat := 4983230072969 + 3 ^ 40 * 4154294 * 2
def baseEnd_4154294 : Nat := 1422099734726183026213171

theorem tailTrace_4154294 : CollatzResearch.WordTrace tailWord_4154294 prefixEnd_4154294 1422099734726183026213171 := by
  unfold tailWord_4154294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9469971875731863110898371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101013033341139873182915957 9469971875731863110898371)
  ·
    refine ⟨14204957813597794666347557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9469971875731863110898371 14204957813597794666347557)
    ·
      refine ⟨2663429590049586499940167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14204957813597794666347557 2663429590049586499940167)
      ·
        refine ⟨3995144385074379749910251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2663429590049586499940167 3995144385074379749910251)
        ·
          refine ⟨5992716577611569624865377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3995144385074379749910251 5992716577611569624865377)
          ·
            refine ⟨4494537433208677218649033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5992716577611569624865377 4494537433208677218649033)
            ·
              refine ⟨3370903074906507913986775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4494537433208677218649033 3370903074906507913986775)
              ·
                refine ⟨5056354612359761870980163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3370903074906507913986775 5056354612359761870980163)
                ·
                  refine ⟨7584531918539642806470245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5056354612359761870980163 7584531918539642806470245)
                  ·
                    refine ⟨1422099734726183026213171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7584531918539642806470245 1422099734726183026213171)
                    ·
                      rfl

theorem cell22_4154294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_4154294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154294 prefixEnd_4154294 := by exact prefixLift 4154294
  have htrace : WordTrace (prefixWord ++ tailWord_4154294) baseStart_4154294 baseEnd_4154294 := by
    simpa [prefixWord, tailWord_4154294, baseEnd_4154294] using wordTrace_append hprefix tailTrace_4154294
  have hstable : (prefixWord ++ tailWord_4154294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154294).length < 2 ^ (prefixWord ++ tailWord_4154294).sum := by decide
  have hdescent : baseEnd_4154294 < baseStart_4154294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154318 : List Nat := [4, 1, 1, 1, 2, 3, 2, 4, 1, 3]
def baseStart_4154318 : Nat := 118140960795 + 4154318 * 2 ^ 59
def prefixEnd_4154318 : Nat := 4983230072969 + 3 ^ 40 * 4154318 * 2
def baseEnd_4154318 : Nat := 1422107950416654963613097

theorem tailTrace_4154318 : CollatzResearch.WordTrace tailWord_4154318 prefixEnd_4154318 1422107950416654963613097 := by
  unfold tailWord_4154318
  simp only [CollatzResearch.WordTrace]
  refine ⟨18940053170452857734155951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101013616909081907915498405 18940053170452857734155951)
  ·
    refine ⟨28410079755679286601233927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18940053170452857734155951 28410079755679286601233927)
    ·
      refine ⟨42615119633518929901850891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28410079755679286601233927 42615119633518929901850891)
      ·
        refine ⟨63922679450278394852776337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42615119633518929901850891 63922679450278394852776337)
        ·
          refine ⟨47942009587708796139582253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63922679450278394852776337 47942009587708796139582253)
          ·
            refine ⟨17978253595390798552343345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47942009587708796139582253 17978253595390798552343345)
            ·
              refine ⟨13483690196543098914257509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17978253595390798552343345 13483690196543098914257509)
              ·
                refine ⟨2528191911851831046423283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13483690196543098914257509 2528191911851831046423283)
                ·
                  refine ⟨3792287867777746569634925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2528191911851831046423283 3792287867777746569634925)
                  ·
                    refine ⟨1422107950416654963613097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3792287867777746569634925 1422107950416654963613097)
                    ·
                      rfl

theorem cell22_4154318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_4154318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154318 prefixEnd_4154318 := by exact prefixLift 4154318
  have htrace : WordTrace (prefixWord ++ tailWord_4154318) baseStart_4154318 baseEnd_4154318 := by
    simpa [prefixWord, tailWord_4154318, baseEnd_4154318] using wordTrace_append hprefix tailTrace_4154318
  have hstable : (prefixWord ++ tailWord_4154318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154318).length < 2 ^ (prefixWord ++ tailWord_4154318).sum := by decide
  have hdescent : baseEnd_4154318 < baseStart_4154318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154327 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 2, 8]
def baseStart_4154327 : Nat := 118140960795 + 4154327 * 2 ^ 59
def prefixEnd_4154327 : Nat := 4983230072969 + 3 ^ 40 * 4154327 * 2
def baseEnd_4154327 : Nat := 1422111031300581940138069

theorem tailTrace_4154327 : CollatzResearch.WordTrace tailWord_4154327 prefixEnd_4154327 1422111031300581940138069 := by
  unfold tailWord_4154327
  simp only [CollatzResearch.WordTrace]
  refine ⟨151520753620590256410325235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101013835747060170940216823 151520753620590256410325235)
  ·
    refine ⟨227281130430885384615487853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151520753620590256410325235 227281130430885384615487853)
    ·
      refine ⟨85230423911582019230807945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227281130430885384615487853 85230423911582019230807945)
      ·
        refine ⟨63922817933686514423105959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85230423911582019230807945 63922817933686514423105959)
        ·
          refine ⟨95884226900529771634658939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63922817933686514423105959 95884226900529771634658939)
          ·
            refine ⟨143826340350794657451988409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95884226900529771634658939 143826340350794657451988409)
            ·
              refine ⟨107869755263095993088991307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143826340350794657451988409 107869755263095993088991307)
              ·
                refine ⟨161804632894643989633486961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107869755263095993088991307 161804632894643989633486961)
                ·
                  refine ⟨121353474670982992225115221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161804632894643989633486961 121353474670982992225115221)
                  ·
                    refine ⟨1422111031300581940138069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121353474670982992225115221 1422111031300581940138069)
                    ·
                      rfl

theorem cell22_4154327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_4154327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154327 prefixEnd_4154327 := by exact prefixLift 4154327
  have htrace : WordTrace (prefixWord ++ tailWord_4154327) baseStart_4154327 baseEnd_4154327 := by
    simpa [prefixWord, tailWord_4154327, baseEnd_4154327] using wordTrace_append hprefix tailTrace_4154327
  have hstable : (prefixWord ++ tailWord_4154327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154327).length < 2 ^ (prefixWord ++ tailWord_4154327).sum := by decide
  have hdescent : baseEnd_4154327 < baseStart_4154327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154329 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 2, 5]
def baseStart_4154329 : Nat := 118140960795 + 4154329 * 2 ^ 59
def prefixEnd_4154329 : Nat := 4983230072969 + 3 ^ 40 * 4154329 * 2
def baseEnd_4154329 : Nat := 1422111715941454601588063

theorem tailTrace_4154329 : CollatzResearch.WordTrace tailWord_4154329 prefixEnd_4154329 1422111715941454601588063 := by
  unfold tailWord_4154329
  simp only [CollatzResearch.WordTrace]
  refine ⟨151520826566583010751898041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101013884377722007167932027 151520826566583010751898041)
  ·
    refine ⟨113640619924937258063923531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151520826566583010751898041 113640619924937258063923531)
    ·
      refine ⟨170460929887405887095885297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113640619924937258063923531 170460929887405887095885297)
      ·
        refine ⟨127845697415554415321913973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170460929887405887095885297 127845697415554415321913973)
        ·
          refine ⟨11985534132708226436429435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127845697415554415321913973 11985534132708226436429435)
          ·
            refine ⟨17978301199062339654644153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11985534132708226436429435 17978301199062339654644153)
            ·
              refine ⟨13483725899296754740983115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17978301199062339654644153 13483725899296754740983115)
              ·
                refine ⟨20225588848945132111474673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13483725899296754740983115 20225588848945132111474673)
                ·
                  refine ⟨15169191636708849083606005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20225588848945132111474673 15169191636708849083606005)
                  ·
                    refine ⟨1422111715941454601588063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15169191636708849083606005 1422111715941454601588063)
                    ·
                      rfl

theorem cell22_4154329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_4154329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154329 prefixEnd_4154329 := by exact prefixLift 4154329
  have htrace : WordTrace (prefixWord ++ tailWord_4154329) baseStart_4154329 baseEnd_4154329 := by
    simpa [prefixWord, tailWord_4154329, baseEnd_4154329] using wordTrace_append hprefix tailTrace_4154329
  have hstable : (prefixWord ++ tailWord_4154329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154329).length < 2 ^ (prefixWord ++ tailWord_4154329).sum := by decide
  have hdescent : baseEnd_4154329 < baseStart_4154329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154344 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 3, 4]
def baseStart_4154344 : Nat := 118140960795 + 4154344 * 2 ^ 59
def prefixEnd_4154344 : Nat := 4983230072969 + 3 ^ 40 * 4154344 * 2
def baseEnd_4154344 : Nat := 1422116850747999562463017

theorem tailTrace_4154344 : CollatzResearch.WordTrace tailWord_4154344 prefixEnd_4154344 1422116850747999562463017 := by
  unfold tailWord_4154344
  simp only [CollatzResearch.WordTrace]
  refine ⟨75760686830764334156847043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101014249107685778875796057 75760686830764334156847043)
  ·
    refine ⟨113641030246146501235270565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75760686830764334156847043 113641030246146501235270565)
    ·
      refine ⟨21307693171152468981613231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113641030246146501235270565 21307693171152468981613231)
      ·
        refine ⟨31961539756728703472419847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21307693171152468981613231 31961539756728703472419847)
        ·
          refine ⟨47942309635093055208629771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31961539756728703472419847 47942309635093055208629771)
          ·
            refine ⟨71913464452639582812944657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47942309635093055208629771 71913464452639582812944657)
            ·
              refine ⟨53935098339479687109708493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71913464452639582812944657 53935098339479687109708493)
              ·
                refine ⟨20225661877304882666140685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53935098339479687109708493 20225661877304882666140685)
                ·
                  refine ⟨7584623203989330999802757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20225661877304882666140685 7584623203989330999802757)
                  ·
                    refine ⟨1422116850747999562463017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7584623203989330999802757 1422116850747999562463017)
                    ·
                      rfl

theorem cell22_4154344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_4154344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154344 prefixEnd_4154344 := by exact prefixLift 4154344
  have htrace : WordTrace (prefixWord ++ tailWord_4154344) baseStart_4154344 baseEnd_4154344 := by
    simpa [prefixWord, tailWord_4154344, baseEnd_4154344] using wordTrace_append hprefix tailTrace_4154344
  have hstable : (prefixWord ++ tailWord_4154344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154344).length < 2 ^ (prefixWord ++ tailWord_4154344).sum := by decide
  have hdescent : baseEnd_4154344 < baseStart_4154344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154376 : List Nat := [2, 1, 3, 2, 1, 5, 1, 1, 6]
def baseStart_4154376 : Nat := 118140960795 + 4154376 * 2 ^ 59
def prefixEnd_4154376 : Nat := 4983230072969 + 3 ^ 40 * 4154376 * 2
def baseEnd_4154376 : Nat := 474042601667320715220973

theorem tailTrace_4154376 : CollatzResearch.WordTrace tailWord_4154376 prefixEnd_4154376 474042601667320715220973 := by
  unfold tailWord_4154376
  simp only [CollatzResearch.WordTrace]
  refine ⟨75761270398706368889429491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101015027198275158519239321 75761270398706368889429491)
  ·
    refine ⟨113641905598059553334144237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75761270398706368889429491 113641905598059553334144237)
    ·
      refine ⟨42615714599272332500304089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113641905598059553334144237 42615714599272332500304089)
      ·
        refine ⟨31961785949454249375228067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42615714599272332500304089 31961785949454249375228067)
        ·
          refine ⟨47942678924181374062842101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31961785949454249375228067 47942678924181374062842101)
          ·
            refine ⟨4494626149142003818391447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47942678924181374062842101 4494626149142003818391447)
            ·
              refine ⟨6741939223713005727587171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4494626149142003818391447 6741939223713005727587171)
              ·
                refine ⟨10112908835569508591380757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6741939223713005727587171 10112908835569508591380757)
                ·
                  refine ⟨474042601667320715220973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10112908835569508591380757 474042601667320715220973)
                  ·
                    rfl

theorem cell22_4154376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 6].length) (baseStart_4154376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154376 prefixEnd_4154376 := by exact prefixLift 4154376
  have htrace : WordTrace (prefixWord ++ tailWord_4154376) baseStart_4154376 baseEnd_4154376 := by
    simpa [prefixWord, tailWord_4154376, baseEnd_4154376] using wordTrace_append hprefix tailTrace_4154376
  have hstable : (prefixWord ++ tailWord_4154376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154376).length < 2 ^ (prefixWord ++ tailWord_4154376).sum := by decide
  have hdescent : baseEnd_4154376 < baseStart_4154376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154438 : List Nat := [6, 1, 1, 1, 1, 2, 3, 7]
def baseStart_4154438 : Nat := 118140960795 + 4154438 * 2 ^ 59
def prefixEnd_4154438 : Nat := 4983230072969 + 3 ^ 40 * 4154438 * 2
def baseEnd_4154438 : Nat := 158016558763223850068081

theorem tailTrace_4154438 : CollatzResearch.WordTrace tailWord_4154438 prefixEnd_4154438 158016558763223850068081 := by
  unfold tailWord_4154438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4735150066349628823987999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101016534748792081578410645 4735150066349628823987999)
  ·
    refine ⟨7102725099524443235981999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4735150066349628823987999 7102725099524443235981999)
    ·
      refine ⟨10654087649286664853972999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7102725099524443235981999 10654087649286664853972999)
      ·
        refine ⟨15981131473929997280959499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10654087649286664853972999 15981131473929997280959499)
        ·
          refine ⟨23971697210894995921439249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15981131473929997280959499 23971697210894995921439249)
          ·
            refine ⟨17978772908171246941079437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23971697210894995921439249 17978772908171246941079437)
            ·
              refine ⟨6742039840564217602904789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17978772908171246941079437 6742039840564217602904789)
              ·
                refine ⟨158016558763223850068081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6742039840564217602904789 158016558763223850068081)
                ·
                  rfl

theorem cell22_4154438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_4154438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154438 prefixEnd_4154438 := by exact prefixLift 4154438
  have htrace : WordTrace (prefixWord ++ tailWord_4154438) baseStart_4154438 baseEnd_4154438 := by
    simpa [prefixWord, tailWord_4154438, baseEnd_4154438] using wordTrace_append hprefix tailTrace_4154438
  have hstable : (prefixWord ++ tailWord_4154438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154438).length < 2 ^ (prefixWord ++ tailWord_4154438).sum := by decide
  have hdescent : baseEnd_4154438 < baseStart_4154438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154464 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 1, 7]
def baseStart_4154464 : Nat := 118140960795 + 4154464 * 2 ^ 59
def prefixEnd_4154464 : Nat := 4983230072969 + 3 ^ 40 * 4154464 * 2
def baseEnd_4154464 : Nat := 1422157929200359249462649

theorem tailTrace_4154464 : CollatzResearch.WordTrace tailWord_4154464 prefixEnd_4154464 1422157929200359249462649 := by
  unfold tailWord_4154464
  simp only [CollatzResearch.WordTrace]
  refine ⟨75762875210546964404031223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101017166947395952538708297 75762875210546964404031223)
  ·
    refine ⟨113644312815820446606046835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75762875210546964404031223 113644312815820446606046835)
    ·
      refine ⟨170466469223730669909070253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113644312815820446606046835 170466469223730669909070253)
      ·
        refine ⟨63924925958899001215901345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170466469223730669909070253 63924925958899001215901345)
        ·
          refine ⟨47943694469174250911926009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63924925958899001215901345 47943694469174250911926009)
          ·
            refine ⟨35957770851880688183944507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47943694469174250911926009 35957770851880688183944507)
            ·
              refine ⟨53936656277821032275916761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35957770851880688183944507 53936656277821032275916761)
              ·
                refine ⟨40452492208365774206937571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53936656277821032275916761 40452492208365774206937571)
                ·
                  refine ⟨60678738312548661310406357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40452492208365774206937571 60678738312548661310406357)
                  ·
                    refine ⟨1422157929200359249462649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60678738312548661310406357 1422157929200359249462649)
                    ·
                      rfl

theorem cell22_4154464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_4154464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154464 prefixEnd_4154464 := by exact prefixLift 4154464
  have htrace : WordTrace (prefixWord ++ tailWord_4154464) baseStart_4154464 baseEnd_4154464 := by
    simpa [prefixWord, tailWord_4154464, baseEnd_4154464] using wordTrace_append hprefix tailTrace_4154464
  have hstable : (prefixWord ++ tailWord_4154464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154464).length < 2 ^ (prefixWord ++ tailWord_4154464).sum := by decide
  have hdescent : baseEnd_4154464 < baseStart_4154464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154556 : List Nat := [2, 2, 2, 3, 2, 1, 1, 9]
def baseStart_4154556 : Nat := 118140960795 + 4154556 * 2 ^ 59
def prefixEnd_4154556 : Nat := 4983230072969 + 3 ^ 40 * 4154556 * 2
def baseEnd_4154556 : Nat := 158021046964500186240263

theorem tailTrace_4154556 : CollatzResearch.WordTrace tailWord_4154556 prefixEnd_4154556 158021046964500186240263 := by
  unfold tailWord_4154556
  simp only [CollatzResearch.WordTrace]
  refine ⟨75764552968380314260205761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101019403957840419013607681 75764552968380314260205761)
  ·
    refine ⟨56823414726285235695154321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75764552968380314260205761 56823414726285235695154321)
    ·
      refine ⟨42617561044713926771365741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56823414726285235695154321 42617561044713926771365741)
      ·
        refine ⟨15981585391767722539262153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42617561044713926771365741 15981585391767722539262153)
        ·
          refine ⟨11986189043825791904446615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15981585391767722539262153 11986189043825791904446615)
          ·
            refine ⟨17979283565738687856669923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11986189043825791904446615 17979283565738687856669923)
            ·
              refine ⟨26968925348608031785004885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17979283565738687856669923 26968925348608031785004885)
              ·
                refine ⟨158021046964500186240263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26968925348608031785004885 158021046964500186240263)
                ·
                  rfl

theorem cell22_4154556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 9].length) (baseStart_4154556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154556 prefixEnd_4154556 := by exact prefixLift 4154556
  have htrace : WordTrace (prefixWord ++ tailWord_4154556) baseStart_4154556 baseEnd_4154556 := by
    simpa [prefixWord, tailWord_4154556, baseEnd_4154556] using wordTrace_append hprefix tailTrace_4154556
  have hstable : (prefixWord ++ tailWord_4154556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154556).length < 2 ^ (prefixWord ++ tailWord_4154556).sum := by decide
  have hdescent : baseEnd_4154556 < baseStart_4154556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154560 : List Nat := [2, 1, 1, 2, 6, 1, 1, 3, 2, 3]
def baseStart_4154560 : Nat := 118140960795 + 4154560 * 2 ^ 59
def prefixEnd_4154560 : Nat := 4983230072969 + 3 ^ 40 * 4154560 * 2
def baseEnd_4154560 : Nat := 1422190791962246999062355

theorem tailTrace_4154560 : CollatzResearch.WordTrace tailWord_4154560 prefixEnd_4154560 1422190791962246999062355 := by
  unfold tailWord_4154560
  simp only [CollatzResearch.WordTrace]
  refine ⟨75764625914373068601778567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101019501219164091469038089 75764625914373068601778567)
  ·
    refine ⟨113646938871559602902667851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75764625914373068601778567 113646938871559602902667851)
    ·
      refine ⟨170470408307339404354001777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113646938871559602902667851 170470408307339404354001777)
      ·
        refine ⟨127852806230504553265501333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170470408307339404354001777 127852806230504553265501333)
        ·
          refine ⟨5993100292054900934320375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 127852806230504553265501333 5993100292054900934320375)
          ·
            refine ⟨8989650438082351401480563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5993100292054900934320375 8989650438082351401480563)
            ·
              refine ⟨13484475657123527102220845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8989650438082351401480563 13484475657123527102220845)
              ·
                refine ⟨5056678371421322663332817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13484475657123527102220845 5056678371421322663332817)
                ·
                  refine ⟨3792508778565991997499613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5056678371421322663332817 3792508778565991997499613)
                  ·
                    refine ⟨1422190791962246999062355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3792508778565991997499613 1422190791962246999062355)
                    ·
                      rfl

theorem cell22_4154560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 2, 3].length) (baseStart_4154560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154560 prefixEnd_4154560 := by exact prefixLift 4154560
  have htrace : WordTrace (prefixWord ++ tailWord_4154560) baseStart_4154560 baseEnd_4154560 := by
    simpa [prefixWord, tailWord_4154560, baseEnd_4154560] using wordTrace_append hprefix tailTrace_4154560
  have hstable : (prefixWord ++ tailWord_4154560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154560).length < 2 ^ (prefixWord ++ tailWord_4154560).sum := by decide
  have hdescent : baseEnd_4154560 < baseStart_4154560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154845 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_4154845 : Nat := 118140960795 + 4154845 * 2 ^ 59
def prefixEnd_4154845 : Nat := 4983230072969 + 3 ^ 40 * 4154845 * 2
def baseEnd_4154845 : Nat := 1422288353286601255686481

theorem tailTrace_4154845 : CollatzResearch.WordTrace tailWord_4154845 prefixEnd_4154845 1422288353286601255686481 := by
  unfold tailWord_4154845
  simp only [CollatzResearch.WordTrace]
  refine ⟨151539646632713630877681989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101026431088475753918454659 151539646632713630877681989)
  ·
    refine ⟨28413683743633805789565373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151539646632713630877681989 28413683743633805789565373)
    ·
      refine ⟨10655131403862677171087015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28413683743633805789565373 10655131403862677171087015)
      ·
        refine ⟨15982697105794015756630523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10655131403862677171087015 15982697105794015756630523)
        ·
          refine ⟨23974045658691023634945785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15982697105794015756630523 23974045658691023634945785)
          ·
            refine ⟨17980534244018267726209339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23974045658691023634945785 17980534244018267726209339)
            ·
              refine ⟨26970801366027401589314009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17980534244018267726209339 26970801366027401589314009)
              ·
                refine ⟨20228101024520551191985507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26970801366027401589314009 20228101024520551191985507)
                ·
                  refine ⟨30342151536780826787978261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20228101024520551191985507 30342151536780826787978261)
                  ·
                    refine ⟨1422288353286601255686481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30342151536780826787978261 1422288353286601255686481)
                    ·
                      rfl

theorem cell22_4154845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_4154845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154845 prefixEnd_4154845 := by exact prefixLift 4154845
  have htrace : WordTrace (prefixWord ++ tailWord_4154845) baseStart_4154845 baseEnd_4154845 := by
    simpa [prefixWord, tailWord_4154845, baseEnd_4154845] using wordTrace_append hprefix tailTrace_4154845
  have hstable : (prefixWord ++ tailWord_4154845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154845).length < 2 ^ (prefixWord ++ tailWord_4154845).sum := by decide
  have hdescent : baseEnd_4154845 < baseStart_4154845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154873 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 1, 8]
def baseStart_4154873 : Nat := 118140960795 + 4154873 * 2 ^ 59
def prefixEnd_4154873 : Nat := 4983230072969 + 3 ^ 40 * 4154873 * 2
def baseEnd_4154873 : Nat := 1422297938258818515986395

theorem tailTrace_4154873 : CollatzResearch.WordTrace tailWord_4154873 prefixEnd_4154873 1422297938258818515986395 := by
  unfold tailWord_4154873
  simp only [CollatzResearch.WordTrace]
  refine ⟨151540667876612191659701273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101027111917741461106467515 151540667876612191659701273)
  ·
    refine ⟨113655500907459143744775955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151540667876612191659701273 113655500907459143744775955)
    ·
      refine ⟨170483251361188715617163933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113655500907459143744775955 170483251361188715617163933)
      ·
        refine ⟨63931219260445768356436475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170483251361188715617163933 63931219260445768356436475)
        ·
          refine ⟨95896828890668652534654713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63931219260445768356436475 95896828890668652534654713)
          ·
            refine ⟨71922621668001489400991035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95896828890668652534654713 71922621668001489400991035)
            ·
              refine ⟨107883932502002234101486553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71922621668001489400991035 107883932502002234101486553)
              ·
                refine ⟨80912949376501675576114915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107883932502002234101486553 80912949376501675576114915)
                ·
                  refine ⟨121369424064752513364172373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80912949376501675576114915 121369424064752513364172373)
                  ·
                    refine ⟨1422297938258818515986395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121369424064752513364172373 1422297938258818515986395)
                    ·
                      rfl

theorem cell22_4154873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_4154873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154873 prefixEnd_4154873 := by exact prefixLift 4154873
  have htrace : WordTrace (prefixWord ++ tailWord_4154873) baseStart_4154873 baseEnd_4154873 := by
    simpa [prefixWord, tailWord_4154873, baseEnd_4154873] using wordTrace_append hprefix tailTrace_4154873
  have hstable : (prefixWord ++ tailWord_4154873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154873).length < 2 ^ (prefixWord ++ tailWord_4154873).sum := by decide
  have hdescent : baseEnd_4154873 < baseStart_4154873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154984 : List Nat := [2, 1, 4, 3, 1, 1, 1, 5, 4]
def baseStart_4154984 : Nat := 118140960795 + 4154984 * 2 ^ 59
def prefixEnd_4154984 : Nat := 4983230072969 + 3 ^ 40 * 4154984 * 2
def baseEnd_4154984 : Nat := 474111978609083742153685

theorem tailTrace_4154984 : CollatzResearch.WordTrace tailWord_4154984 prefixEnd_4154984 474111978609083742153685 := by
  unfold tailWord_4154984
  simp only [CollatzResearch.WordTrace]
  refine ⟨75772358189605028808496003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101029810919473371744661337 75772358189605028808496003)
  ·
    refine ⟨113658537284407543212744005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75772358189605028808496003 113658537284407543212744005)
    ·
      refine ⟨21310975740826414352389501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113658537284407543212744005 21310975740826414352389501)
      ·
        refine ⟨7991615902809905382146063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21310975740826414352389501 7991615902809905382146063)
        ·
          refine ⟨11987423854214858073219095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7991615902809905382146063 11987423854214858073219095)
          ·
            refine ⟨17981135781322287109828643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11987423854214858073219095 17981135781322287109828643)
            ·
              refine ⟨26971703671983430664742965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17981135781322287109828643 26971703671983430664742965)
              ·
                refine ⟨2528597219248446624819653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26971703671983430664742965 2528597219248446624819653)
                ·
                  refine ⟨474111978609083742153685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2528597219248446624819653 474111978609083742153685)
                  ·
                    rfl

theorem cell22_4154984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 4].length) (baseStart_4154984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154984 prefixEnd_4154984 := by exact prefixLift 4154984
  have htrace : WordTrace (prefixWord ++ tailWord_4154984) baseStart_4154984 baseEnd_4154984 := by
    simpa [prefixWord, tailWord_4154984, baseEnd_4154984] using wordTrace_append hprefix tailTrace_4154984
  have hstable : (prefixWord ++ tailWord_4154984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154984).length < 2 ^ (prefixWord ++ tailWord_4154984).sum := by decide
  have hdescent : baseEnd_4154984 < baseStart_4154984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4154986 : List Nat := [3, 1, 3, 2, 1, 4, 2, 1, 1, 4]
def baseStart_4154986 : Nat := 118140960795 + 4154986 * 2 ^ 59
def prefixEnd_4154986 : Nat := 4983230072969 + 3 ^ 40 * 4154986 * 2
def baseEnd_4154986 : Nat := 1422336620468123887911049

theorem tailTrace_4154986 : CollatzResearch.WordTrace tailWord_4154986 prefixEnd_4154986 1422336620468123887911049 := by
  unfold tailWord_4154986
  simp only [CollatzResearch.WordTrace]
  refine ⟨37886197331300702989641203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101029859550135207972376541 37886197331300702989641203)
  ·
    refine ⟨56829295996951054484461805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37886197331300702989641203 56829295996951054484461805)
    ·
      refine ⟨21310985998856645431673177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56829295996951054484461805 21310985998856645431673177)
      ·
        refine ⟨15983239499142484073754883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21310985998856645431673177 15983239499142484073754883)
        ·
          refine ⟨23974859248713726110632325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15983239499142484073754883 23974859248713726110632325)
          ·
            refine ⟨4495286109133823645743561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23974859248713726110632325 4495286109133823645743561)
            ·
              refine ⟨3371464581850367734307671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4495286109133823645743561 3371464581850367734307671)
              ·
                refine ⟨5057196872775551601461507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3371464581850367734307671 5057196872775551601461507)
                ·
                  refine ⟨7585795309163327402192261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5057196872775551601461507 7585795309163327402192261)
                  ·
                    refine ⟨1422336620468123887911049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7585795309163327402192261 1422336620468123887911049)
                    ·
                      rfl

theorem cell22_4154986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_4154986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4154986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4154986 prefixEnd_4154986 := by exact prefixLift 4154986
  have htrace : WordTrace (prefixWord ++ tailWord_4154986) baseStart_4154986 baseEnd_4154986 := by
    simpa [prefixWord, tailWord_4154986, baseEnd_4154986] using wordTrace_append hprefix tailTrace_4154986
  have hstable : (prefixWord ++ tailWord_4154986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4154986).length < 2 ^ (prefixWord ++ tailWord_4154986).sum := by decide
  have hdescent : baseEnd_4154986 < baseStart_4154986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4154986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155016 : List Nat := [2, 1, 3, 5, 1, 2, 1, 1, 1, 5]
def baseStart_4155016 : Nat := 118140960795 + 4155016 * 2 ^ 59
def prefixEnd_4155016 : Nat := 4983230072969 + 3 ^ 40 * 4155016 * 2
def baseEnd_4155016 : Nat := 1422346890081213809660957

theorem tailTrace_4155016 : CollatzResearch.WordTrace tailWord_4155016 prefixEnd_4155016 1422346890081213809660957 := by
  unfold tailWord_4155016
  simp only [CollatzResearch.WordTrace]
  refine ⟨75772941757547063541078451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101030589010062751388104601 75772941757547063541078451)
  ·
    refine ⟨113659412636320595311617677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75772941757547063541078451 113659412636320595311617677)
    ·
      refine ⟨42622279738620223241856629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113659412636320595311617677 42622279738620223241856629)
      ·
        refine ⟨3995838725495645928924059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42622279738620223241856629 3995838725495645928924059)
        ·
          refine ⟨5993758088243468893386089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3995838725495645928924059 5993758088243468893386089)
          ·
            refine ⟨4495318566182601670039567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5993758088243468893386089 4495318566182601670039567)
            ·
              refine ⟨6742977849273902505059351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4495318566182601670039567 6742977849273902505059351)
              ·
                refine ⟨10114466773910853757589027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6742977849273902505059351 10114466773910853757589027)
                ·
                  refine ⟨15171700160866280636383541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10114466773910853757589027 15171700160866280636383541)
                  ·
                    refine ⟨1422346890081213809660957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15171700160866280636383541 1422346890081213809660957)
                    ·
                      rfl

theorem cell22_4155016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_4155016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155016 prefixEnd_4155016 := by exact prefixLift 4155016
  have htrace : WordTrace (prefixWord ++ tailWord_4155016) baseStart_4155016 baseEnd_4155016 := by
    simpa [prefixWord, tailWord_4155016, baseEnd_4155016] using wordTrace_append hprefix tailTrace_4155016
  have hstable : (prefixWord ++ tailWord_4155016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155016).length < 2 ^ (prefixWord ++ tailWord_4155016).sum := by decide
  have hdescent : baseEnd_4155016 < baseStart_4155016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155048 : List Nat := [2, 1, 7, 1, 1, 1, 1, 2, 2, 4]
def baseStart_4155048 : Nat := 118140960795 + 4155048 * 2 ^ 59
def prefixEnd_4155048 : Nat := 4983230072969 + 3 ^ 40 * 4155048 * 2
def baseEnd_4155048 : Nat := 1422357844335176392860859

theorem tailTrace_4155048 : CollatzResearch.WordTrace tailWord_4155048 prefixEnd_4155048 1422357844335176392860859 := by
  unfold tailWord_4155048
  simp only [CollatzResearch.WordTrace]
  refine ⟨75773525325489098273660899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101031367100652131031547865 75773525325489098273660899)
  ·
    refine ⟨113660287988233647410491349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75773525325489098273660899 113660287988233647410491349)
    ·
      refine ⟨2663912999724226111183391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 113660287988233647410491349 2663912999724226111183391)
      ·
        refine ⟨3995869499586339166775087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2663912999724226111183391 3995869499586339166775087)
        ·
          refine ⟨5993804249379508750162631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3995869499586339166775087 5993804249379508750162631)
          ·
            refine ⟨8990706374069263125243947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5993804249379508750162631 8990706374069263125243947)
            ·
              refine ⟨13486059561103894687865921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8990706374069263125243947 13486059561103894687865921)
              ·
                refine ⟨10114544670827921015899441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13486059561103894687865921 10114544670827921015899441)
                ·
                  refine ⟨7585908503120940761924581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10114544670827921015899441 7585908503120940761924581)
                  ·
                    refine ⟨1422357844335176392860859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7585908503120940761924581 1422357844335176392860859)
                    ·
                      rfl

theorem cell22_4155048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_4155048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155048 prefixEnd_4155048 := by exact prefixLift 4155048
  have htrace : WordTrace (prefixWord ++ tailWord_4155048) baseStart_4155048 baseEnd_4155048 := by
    simpa [prefixWord, tailWord_4155048, baseEnd_4155048] using wordTrace_append hprefix tailTrace_4155048
  have hstable : (prefixWord ++ tailWord_4155048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155048).length < 2 ^ (prefixWord ++ tailWord_4155048).sum := by decide
  have hdescent : baseEnd_4155048 < baseStart_4155048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155119 : List Nat := [1, 1, 2, 1, 5, 1, 3, 4, 4]
def baseStart_4155119 : Nat := 118140960795 + 4155119 * 2 ^ 59
def prefixEnd_4155119 : Nat := 4983230072969 + 3 ^ 40 * 4155119 * 2
def baseEnd_4155119 : Nat := 474127383028718624778547

theorem tailTrace_4155119 : CollatzResearch.WordTrace tailWord_4155119 prefixEnd_4155119 474127383028718624778547 := by
  unfold tailWord_4155119
  simp only [CollatzResearch.WordTrace]
  refine ⟨151549640233720975673156411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101033093489147317115437607 151549640233720975673156411)
  ·
    refine ⟨227324460350581463509734617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151549640233720975673156411 227324460350581463509734617)
    ·
      refine ⟨170493345262936097632300963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227324460350581463509734617 170493345262936097632300963)
      ·
        refine ⟨255740017894404146448451445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170493345262936097632300963 255740017894404146448451445)
        ·
          refine ⟨23975626677600388729542323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 255740017894404146448451445 23975626677600388729542323)
          ·
            refine ⟨35963440016400583094313485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23975626677600388729542323 35963440016400583094313485)
            ·
              refine ⟨13486290006150218660367557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35963440016400583094313485 13486290006150218660367557)
              ·
                refine ⟨2528679376153165998818917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13486290006150218660367557 2528679376153165998818917)
                ·
                  refine ⟨474127383028718624778547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2528679376153165998818917 474127383028718624778547)
                  ·
                    rfl

theorem cell22_4155119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 4].length) (baseStart_4155119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155119 prefixEnd_4155119 := by exact prefixLift 4155119
  have htrace : WordTrace (prefixWord ++ tailWord_4155119) baseStart_4155119 baseEnd_4155119 := by
    simpa [prefixWord, tailWord_4155119, baseEnd_4155119] using wordTrace_append hprefix tailTrace_4155119
  have hstable : (prefixWord ++ tailWord_4155119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155119).length < 2 ^ (prefixWord ++ tailWord_4155119).sum := by decide
  have hdescent : baseEnd_4155119 < baseStart_4155119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155132 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 1, 6]
def baseStart_4155132 : Nat := 118140960795 + 4155132 * 2 ^ 59
def prefixEnd_4155132 : Nat := 4983230072969 + 3 ^ 40 * 4155132 * 2
def baseEnd_4155132 : Nat := 1422386599251828173760601

theorem tailTrace_4155132 : CollatzResearch.WordTrace tailWord_4155132 prefixEnd_4155132 1422386599251828173760601 := by
  unfold tailWord_4155132
  simp only [CollatzResearch.WordTrace]
  refine ⟨75775057191336939446689825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101033409588449252595586433 75775057191336939446689825)
  ·
    refine ⟨56831292893502704585017369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75775057191336939446689825 56831292893502704585017369)
    ·
      refine ⟨42623469670127028438763027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56831292893502704585017369 42623469670127028438763027)
      ·
        refine ⟨63935204505190542658144541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42623469670127028438763027 63935204505190542658144541)
        ·
          refine ⟨23975701689446453496804203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63935204505190542658144541 23975701689446453496804203)
          ·
            refine ⟨35963552534169680245206305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23975701689446453496804203 35963552534169680245206305)
            ·
              refine ⟨26972664400627260183904729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35963552534169680245206305 26972664400627260183904729)
              ·
                refine ⟨20229498300470445137928547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26972664400627260183904729 20229498300470445137928547)
                ·
                  refine ⟨30344247450705667706892821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20229498300470445137928547 30344247450705667706892821)
                  ·
                    refine ⟨1422386599251828173760601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30344247450705667706892821 1422386599251828173760601)
                    ·
                      rfl

theorem cell22_4155132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_4155132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155132 prefixEnd_4155132 := by exact prefixLift 4155132
  have htrace : WordTrace (prefixWord ++ tailWord_4155132) baseStart_4155132 baseEnd_4155132 := by
    simpa [prefixWord, tailWord_4155132, baseEnd_4155132] using wordTrace_append hprefix tailTrace_4155132
  have hstable : (prefixWord ++ tailWord_4155132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155132).length < 2 ^ (prefixWord ++ tailWord_4155132).sum := by decide
  have hdescent : baseEnd_4155132 < baseStart_4155132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155207 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 1, 7]
def baseStart_4155207 : Nat := 118140960795 + 4155207 * 2 ^ 59
def prefixEnd_4155207 : Nat := 4983230072969 + 3 ^ 40 * 4155207 * 2
def baseEnd_4155207 : Nat := 1422412273284552978135371

theorem tailTrace_4155207 : CollatzResearch.WordTrace tailWord_4155207 prefixEnd_4155207 1422412273284552978135371 := by
  unfold tailWord_4155207
  simp only [CollatzResearch.WordTrace]
  refine ⟨151552849857402166702359875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101035233238268111134906583 151552849857402166702359875)
  ·
    refine ⟨227329274786103250053539813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151552849857402166702359875 227329274786103250053539813)
    ·
      refine ⟨42624239022394359385038715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227329274786103250053539813 42624239022394359385038715)
      ·
        refine ⟨63936358533591539077558073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42624239022394359385038715 63936358533591539077558073)
        ·
          refine ⟨47952268900193654308168555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63936358533591539077558073 47952268900193654308168555)
          ·
            refine ⟨71928403350290481462252833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47952268900193654308168555 71928403350290481462252833)
            ·
              refine ⟨53946302512717861096689625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71928403350290481462252833 53946302512717861096689625)
              ·
                refine ⟨40459726884538395822517219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53946302512717861096689625 40459726884538395822517219)
                ·
                  refine ⟨60689590326807593733775829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40459726884538395822517219 60689590326807593733775829)
                  ·
                    refine ⟨1422412273284552978135371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60689590326807593733775829 1422412273284552978135371)
                    ·
                      rfl

theorem cell22_4155207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_4155207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155207 prefixEnd_4155207 := by exact prefixLift 4155207
  have htrace : WordTrace (prefixWord ++ tailWord_4155207) baseStart_4155207 baseEnd_4155207 := by
    simpa [prefixWord, tailWord_4155207, baseEnd_4155207] using wordTrace_append hprefix tailTrace_4155207
  have hstable : (prefixWord ++ tailWord_4155207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155207).length < 2 ^ (prefixWord ++ tailWord_4155207).sum := by decide
  have hdescent : baseEnd_4155207 < baseStart_4155207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155239 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 3, 4]
def baseStart_4155239 : Nat := 118140960795 + 4155239 * 2 ^ 59
def prefixEnd_4155239 : Nat := 4983230072969 + 3 ^ 40 * 4155239 * 2
def baseEnd_4155239 : Nat := 1422423227538515561335273

theorem tailTrace_4155239 : CollatzResearch.WordTrace tailWord_4155239 prefixEnd_4155239 1422423227538515561335273 := by
  unfold tailWord_4155239
  simp only [CollatzResearch.WordTrace]
  refine ⟨151554016993286236167524771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101036011328857490778349847 151554016993286236167524771)
  ·
    refine ⟨227331025489929354251287157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151554016993286236167524771 227331025489929354251287157)
    ·
      refine ⟨21312283639680876961058171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227331025489929354251287157 21312283639680876961058171)
      ·
        refine ⟨31968425459521315441587257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21312283639680876961058171 31968425459521315441587257)
        ·
          refine ⟨23976319094640986581190443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31968425459521315441587257 23976319094640986581190443)
          ·
            refine ⟨35964478641961479871785665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23976319094640986581190443 35964478641961479871785665)
            ·
              refine ⟨26973358981471109903839249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35964478641961479871785665 26973358981471109903839249)
              ·
                refine ⟨20230019236103332427879437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26973358981471109903839249 20230019236103332427879437)
                ·
                  refine ⟨7586257213538749660454789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20230019236103332427879437 7586257213538749660454789)
                  ·
                    refine ⟨1422423227538515561335273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7586257213538749660454789 1422423227538515561335273)
                    ·
                      rfl

theorem cell22_4155239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_4155239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155239 prefixEnd_4155239 := by exact prefixLift 4155239
  have htrace : WordTrace (prefixWord ++ tailWord_4155239) baseStart_4155239 baseEnd_4155239 := by
    simpa [prefixWord, tailWord_4155239, baseEnd_4155239] using wordTrace_append hprefix tailTrace_4155239
  have hstable : (prefixWord ++ tailWord_4155239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155239).length < 2 ^ (prefixWord ++ tailWord_4155239).sum := by decide
  have hdescent : baseEnd_4155239 < baseStart_4155239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155269 : List Nat := [1, 3, 1, 1, 3, 2, 3, 2, 1, 5]
def baseStart_4155269 : Nat := 118140960795 + 4155269 * 2 ^ 59
def prefixEnd_4155269 : Nat := 4983230072969 + 3 ^ 40 * 4155269 * 2
def baseEnd_4155269 : Nat := 1422433497151605483085181

theorem tailTrace_4155269 : CollatzResearch.WordTrace tailWord_4155269 prefixEnd_4155269 1422433497151605483085181 := by
  unfold tailWord_4155269
  simp only [CollatzResearch.WordTrace]
  refine ⟨151555111183177551291116861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101036740788785034194077907 151555111183177551291116861)
  ·
    refine ⟨56833166693691581734168823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151555111183177551291116861 56833166693691581734168823)
    ·
      refine ⟨85249750040537372601253235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56833166693691581734168823 85249750040537372601253235)
      ·
        refine ⟨127874625060806058901879853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85249750040537372601253235 127874625060806058901879853)
        ·
          refine ⟨47952984397802272088204945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127874625060806058901879853 47952984397802272088204945)
          ·
            refine ⟨35964738298351704066153709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47952984397802272088204945 35964738298351704066153709)
            ·
              refine ⟨13486776861881889024807641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35964738298351704066153709 13486776861881889024807641)
              ·
                refine ⟨10115082646411416768605731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13486776861881889024807641 10115082646411416768605731)
                ·
                  refine ⟨15172623969617125152908597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10115082646411416768605731 15172623969617125152908597)
                  ·
                    refine ⟨1422433497151605483085181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15172623969617125152908597 1422433497151605483085181)
                    ·
                      rfl

theorem cell22_4155269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_4155269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155269 prefixEnd_4155269 := by exact prefixLift 4155269
  have htrace : WordTrace (prefixWord ++ tailWord_4155269) baseStart_4155269 baseEnd_4155269 := by
    simpa [prefixWord, tailWord_4155269, baseEnd_4155269] using wordTrace_append hprefix tailTrace_4155269
  have hstable : (prefixWord ++ tailWord_4155269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155269).length < 2 ^ (prefixWord ++ tailWord_4155269).sum := by decide
  have hdescent : baseEnd_4155269 < baseStart_4155269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155303 : List Nat := [1, 1, 6, 1, 2, 1, 2, 3, 2, 3]
def baseStart_4155303 : Nat := 118140960795 + 4155303 * 2 ^ 59
def prefixEnd_4155303 : Nat := 4983230072969 + 3 ^ 40 * 4155303 * 2
def baseEnd_4155303 : Nat := 1422445136046440727735077

theorem tailTrace_4155303 : CollatzResearch.WordTrace tailWord_4155303 prefixEnd_4155303 1422445136046440727735077 := by
  unfold tailWord_4155303
  simp only [CollatzResearch.WordTrace]
  refine ⟨151556351265054375097854563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101037567510036250065236375 151556351265054375097854563)
  ·
    refine ⟨227334526897581562646781845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151556351265054375097854563 227334526897581562646781845)
    ·
      refine ⟨10656305948324135749067899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 227334526897581562646781845 10656305948324135749067899)
      ·
        refine ⟨15984458922486203623601849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10656305948324135749067899 15984458922486203623601849)
        ·
          refine ⟨11988344191864652717701387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15984458922486203623601849 11988344191864652717701387)
          ·
            refine ⟨17982516287796979076552081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11988344191864652717701387 17982516287796979076552081)
            ·
              refine ⟨13486887215847734307414061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17982516287796979076552081 13486887215847734307414061)
              ·
                refine ⟨5057582705942900365280273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13486887215847734307414061 5057582705942900365280273)
                ·
                  refine ⟨3793187029457175273960205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5057582705942900365280273 3793187029457175273960205)
                  ·
                    refine ⟨1422445136046440727735077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3793187029457175273960205 1422445136046440727735077)
                    ·
                      rfl

theorem cell22_4155303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_4155303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155303 prefixEnd_4155303 := by exact prefixLift 4155303
  have htrace : WordTrace (prefixWord ++ tailWord_4155303) baseStart_4155303 baseEnd_4155303 := by
    simpa [prefixWord, tailWord_4155303, baseEnd_4155303] using wordTrace_append hprefix tailTrace_4155303
  have hstable : (prefixWord ++ tailWord_4155303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155303).length < 2 ^ (prefixWord ++ tailWord_4155303).sum := by decide
  have hdescent : baseEnd_4155303 < baseStart_4155303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155348 : List Nat := [2, 4, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_4155348 : Nat := 118140960795 + 4155348 * 2 ^ 59
def prefixEnd_4155348 : Nat := 4983230072969 + 3 ^ 40 * 4155348 * 2
def baseEnd_4155348 : Nat := 1422460540466075610359939

theorem tailTrace_4155348 : CollatzResearch.WordTrace tailWord_4155348 prefixEnd_4155348 1422460540466075610359939 := by
  unfold tailWord_4155348
  simp only [CollatzResearch.WordTrace]
  refine ⟨75778996274945673891621349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101038661699927565188828465 75778996274945673891621349)
  ·
    refine ⟨14208561801552313854679003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75778996274945673891621349 14208561801552313854679003)
    ·
      refine ⟨21312842702328470782018505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14208561801552313854679003 21312842702328470782018505)
      ·
        refine ⟨15984632026746353086513879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21312842702328470782018505 15984632026746353086513879)
        ·
          refine ⟨23976948040119529629770819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15984632026746353086513879 23976948040119529629770819)
          ·
            refine ⟨35965422060179294444656229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23976948040119529629770819 35965422060179294444656229)
            ·
              refine ⟨6743516636283617708373043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35965422060179294444656229 6743516636283617708373043)
              ·
                refine ⟨10115274954425426562559565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6743516636283617708373043 10115274954425426562559565)
                ·
                  refine ⟨3793228107909534960959837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10115274954425426562559565 3793228107909534960959837)
                  ·
                    refine ⟨1422460540466075610359939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3793228107909534960959837 1422460540466075610359939)
                    ·
                      rfl

theorem cell22_4155348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_4155348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155348 prefixEnd_4155348 := by exact prefixLift 4155348
  have htrace : WordTrace (prefixWord ++ tailWord_4155348) baseStart_4155348 baseEnd_4155348 := by
    simpa [prefixWord, tailWord_4155348, baseEnd_4155348] using wordTrace_append hprefix tailTrace_4155348
  have hstable : (prefixWord ++ tailWord_4155348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155348).length < 2 ^ (prefixWord ++ tailWord_4155348).sum := by decide
  have hdescent : baseEnd_4155348 < baseStart_4155348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155389 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 8]
def baseStart_4155389 : Nat := 118140960795 + 4155389 * 2 ^ 59
def prefixEnd_4155389 : Nat := 4983230072969 + 3 ^ 40 * 4155389 * 2
def baseEnd_4155389 : Nat := 474158191867988390028271

theorem tailTrace_4155389 : CollatzResearch.WordTrace tailWord_4155389 prefixEnd_4155389 474158191867988390028271 := by
  unfold tailWord_4155389
  simp only [CollatzResearch.WordTrace]
  refine ⟨151559487942742811785485221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101039658628495207856990147 151559487942742811785485221)
  ·
    refine ⟨28417403989264277209778479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151559487942742811785485221 28417403989264277209778479)
    ·
      refine ⟨42626105983896415814667719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28417403989264277209778479 42626105983896415814667719)
      ·
        refine ⟨63939158975844623722001579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42626105983896415814667719 63939158975844623722001579)
        ·
          refine ⟨95908738463766935583002369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63939158975844623722001579 95908738463766935583002369)
          ·
            refine ⟨71931553847825201687251777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95908738463766935583002369 71931553847825201687251777)
            ·
              refine ⟨53948665385868901265438833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71931553847825201687251777 53948665385868901265438833)
              ·
                refine ⟨40461499039401675949079125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53948665385868901265438833 40461499039401675949079125)
                ·
                  refine ⟨474158191867988390028271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40461499039401675949079125 474158191867988390028271)
                  ·
                    rfl

theorem cell22_4155389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_4155389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155389 prefixEnd_4155389 := by exact prefixLift 4155389
  have htrace : WordTrace (prefixWord ++ tailWord_4155389) baseStart_4155389 baseEnd_4155389 := by
    simpa [prefixWord, tailWord_4155389, baseEnd_4155389] using wordTrace_append hprefix tailTrace_4155389
  have hstable : (prefixWord ++ tailWord_4155389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155389).length < 2 ^ (prefixWord ++ tailWord_4155389).sum := by decide
  have hdescent : baseEnd_4155389 < baseStart_4155389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155419 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 1, 6]
def baseStart_4155419 : Nat := 118140960795 + 4155419 * 2 ^ 59
def prefixEnd_4155419 : Nat := 4983230072969 + 3 ^ 40 * 4155419 * 2
def baseEnd_4155419 : Nat := 1422484845217055091834721

theorem tailTrace_4155419 : CollatzResearch.WordTrace tailWord_4155419 prefixEnd_4155419 1422484845217055091834721 := by
  unfold tailWord_4155419
  simp only [CollatzResearch.WordTrace]
  refine ⟨151560582132634126909077311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101040388088422751272718207 151560582132634126909077311)
  ·
    refine ⟨227340873198951190363615967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151560582132634126909077311 227340873198951190363615967)
    ·
      refine ⟨341011309798426785545423951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227340873198951190363615967 341011309798426785545423951)
      ·
        refine ⟨511516964697640178318135927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341011309798426785545423951 511516964697640178318135927)
        ·
          refine ⟨767275447046460267477203891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511516964697640178318135927 767275447046460267477203891)
          ·
            refine ⟨1150913170569690401215805837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767275447046460267477203891 1150913170569690401215805837)
            ·
              refine ⟨431592438963633900455927189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1150913170569690401215805837 431592438963633900455927189)
              ·
                refine ⟨20230895576420339083871587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 431592438963633900455927189 20230895576420339083871587)
                ·
                  refine ⟨30346343364630508625807381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20230895576420339083871587 30346343364630508625807381)
                  ·
                    refine ⟨1422484845217055091834721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30346343364630508625807381 1422484845217055091834721)
                    ·
                      rfl

theorem cell22_4155419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 6].length) (baseStart_4155419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155419 prefixEnd_4155419 := by exact prefixLift 4155419
  have htrace : WordTrace (prefixWord ++ tailWord_4155419) baseStart_4155419 baseEnd_4155419 := by
    simpa [prefixWord, tailWord_4155419, baseEnd_4155419] using wordTrace_append hprefix tailTrace_4155419
  have hstable : (prefixWord ++ tailWord_4155419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155419).length < 2 ^ (prefixWord ++ tailWord_4155419).sum := by decide
  have hdescent : baseEnd_4155419 < baseStart_4155419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155425 : List Nat := [1, 2, 3, 2, 4, 2, 1, 2, 1, 4]
def baseStart_4155425 : Nat := 118140960795 + 4155425 * 2 ^ 59
def prefixEnd_4155425 : Nat := 4983230072969 + 3 ^ 40 * 4155425 * 2
def baseEnd_4155425 : Nat := 1422486899139673076184703

theorem tailTrace_4155425 : CollatzResearch.WordTrace tailWord_4155425 prefixEnd_4155425 1422486899139673076184703 := by
  unfold tailWord_4155425
  simp only [CollatzResearch.WordTrace]
  refine ⟨151560800970612389933795729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101040533980408259955863819 151560800970612389933795729)
  ·
    refine ⟨113670600727959292450346797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151560800970612389933795729 113670600727959292450346797)
    ·
      refine ⟨42626475272984734668880049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113670600727959292450346797 42626475272984734668880049)
      ·
        refine ⟨31969856454738551001660037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42626475272984734668880049 31969856454738551001660037)
        ·
          refine ⟨5994348085263478312811257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31969856454738551001660037 5994348085263478312811257)
          ·
            refine ⟨4495761063947608734608443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5994348085263478312811257 4495761063947608734608443)
            ·
              refine ⟨6743641595921413101912665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4495761063947608734608443 6743641595921413101912665)
              ·
                refine ⟨5057731196941059826434499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6743641595921413101912665 5057731196941059826434499)
                ·
                  refine ⟨7586596795411589739651749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5057731196941059826434499 7586596795411589739651749)
                  ·
                    refine ⟨1422486899139673076184703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7586596795411589739651749 1422486899139673076184703)
                    ·
                      rfl

theorem cell22_4155425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_4155425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155425 prefixEnd_4155425 := by exact prefixLift 4155425
  have htrace : WordTrace (prefixWord ++ tailWord_4155425) baseStart_4155425 baseEnd_4155425 := by
    simpa [prefixWord, tailWord_4155425, baseEnd_4155425] using wordTrace_append hprefix tailTrace_4155425
  have hstable : (prefixWord ++ tailWord_4155425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155425).length < 2 ^ (prefixWord ++ tailWord_4155425).sum := by decide
  have hdescent : baseEnd_4155425 < baseStart_4155425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155438 : List Nat := [4, 1, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_4155438 : Nat := 118140960795 + 4155438 * 2 ^ 59
def prefixEnd_4155438 : Nat := 4983230072969 + 3 ^ 40 * 4155438 * 2
def baseEnd_4155438 : Nat := 1422491349305345375609663

theorem tailTrace_4155438 : CollatzResearch.WordTrace tailWord_4155438 prefixEnd_4155438 1422491349305345375609663 := by
  unfold tailWord_4155438
  simp only [CollatzResearch.WordTrace]
  refine ⟨18945159389945661644252371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101040850079710195436012645 18945159389945661644252371)
  ·
    refine ⟨28417739084918492466378557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18945159389945661644252371 28417739084918492466378557)
    ·
      refine ⟨10656652156844434674891959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28417739084918492466378557 10656652156844434674891959)
      ·
        refine ⟨15984978235266652012337939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10656652156844434674891959 15984978235266652012337939)
        ·
          refine ⟨23977467352899978018506909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15984978235266652012337939 23977467352899978018506909)
          ·
            refine ⟨8991550257337491756940091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23977467352899978018506909 8991550257337491756940091)
            ·
              refine ⟨13487325386006237635410137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8991550257337491756940091 13487325386006237635410137)
              ·
                refine ⟨10115494039504678226557603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13487325386006237635410137 10115494039504678226557603)
                ·
                  refine ⟨15173241059257017339836405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10115494039504678226557603 15173241059257017339836405)
                  ·
                    refine ⟨1422491349305345375609663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15173241059257017339836405 1422491349305345375609663)
                    ·
                      rfl

theorem cell22_4155438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_4155438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155438 prefixEnd_4155438 := by exact prefixLift 4155438
  have htrace : WordTrace (prefixWord ++ tailWord_4155438) baseStart_4155438 baseEnd_4155438 := by
    simpa [prefixWord, tailWord_4155438, baseEnd_4155438] using wordTrace_append hprefix tailTrace_4155438
  have hstable : (prefixWord ++ tailWord_4155438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155438).length < 2 ^ (prefixWord ++ tailWord_4155438).sum := by decide
  have hdescent : baseEnd_4155438 < baseStart_4155438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155457 : List Nat := [1, 2, 5, 1, 2, 3, 2, 2, 4]
def baseStart_4155457 : Nat := 118140960795 + 4155457 * 2 ^ 59
def prefixEnd_4155457 : Nat := 4983230072969 + 3 ^ 40 * 4155457 * 2
def baseEnd_4155457 : Nat := 474165951131211886461535

theorem tailTrace_4155457 : CollatzResearch.WordTrace tailWord_4155457 prefixEnd_4155457 474165951131211886461535 := by
  unfold tailWord_4155457
  simp only [CollatzResearch.WordTrace]
  refine ⟨151561968106496459398960625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101041312070997639599307083 151561968106496459398960625)
  ·
    refine ⟨113671476079872344549220469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151561968106496459398960625 113671476079872344549220469)
    ·
      refine ⟨10656700882488032301489419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113671476079872344549220469 10656700882488032301489419)
      ·
        refine ⟨15985051323732048452234129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10656700882488032301489419 15985051323732048452234129)
        ·
          refine ⟨11988788492799036339175597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15985051323732048452234129 11988788492799036339175597)
          ·
            refine ⟨4495795684799638627190849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11988788492799036339175597 4495795684799638627190849)
            ·
              refine ⟨3371846763599728970393137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4495795684799638627190849 3371846763599728970393137)
              ·
                refine ⟨2528885072699796727794853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3371846763599728970393137 2528885072699796727794853)
                ·
                  refine ⟨474165951131211886461535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2528885072699796727794853 474165951131211886461535)
                  ·
                    rfl

theorem cell22_4155457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 4].length) (baseStart_4155457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155457 prefixEnd_4155457 := by exact prefixLift 4155457
  have htrace : WordTrace (prefixWord ++ tailWord_4155457) baseStart_4155457 baseEnd_4155457 := by
    simpa [prefixWord, tailWord_4155457, baseEnd_4155457] using wordTrace_append hprefix tailTrace_4155457
  have hstable : (prefixWord ++ tailWord_4155457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155457).length < 2 ^ (prefixWord ++ tailWord_4155457).sum := by decide
  have hdescent : baseEnd_4155457 < baseStart_4155457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155485 : List Nat := [1, 4, 4, 1, 1, 2, 3, 6]
def baseStart_4155485 : Nat := 118140960795 + 4155485 * 2 ^ 59
def prefixEnd_4155485 : Nat := 4983230072969 + 3 ^ 40 * 4155485 * 2
def baseEnd_4155485 : Nat := 158056382040650324409391

theorem tailTrace_4155485 : CollatzResearch.WordTrace tailWord_4155485 prefixEnd_4155485 158056382040650324409391 := by
  unfold tailWord_4155485
  simp only [CollatzResearch.WordTrace]
  refine ⟨151562989350395020180979909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101041992900263346787319939 151562989350395020180979909)
  ·
    refine ⟨28418060503199066283933733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151562989350395020180979909 28418060503199066283933733)
    ·
      refine ⟨5328386344349824928237575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28418060503199066283933733 5328386344349824928237575)
      ·
        refine ⟨7992579516524737392356363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5328386344349824928237575 7992579516524737392356363)
        ·
          refine ⟨11988869274787106088534545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7992579516524737392356363 11988869274787106088534545)
          ·
            refine ⟨8991651956090329566400909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11988869274787106088534545 8991651956090329566400909)
            ·
              refine ⟨3371869483533873587400341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8991651956090329566400909 3371869483533873587400341)
              ·
                refine ⟨158056382040650324409391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3371869483533873587400341 158056382040650324409391)
                ·
                  rfl

theorem cell22_4155485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 6].length) (baseStart_4155485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155485 prefixEnd_4155485 := by exact prefixLift 4155485
  have htrace : WordTrace (prefixWord ++ tailWord_4155485) baseStart_4155485 baseEnd_4155485 := by
    simpa [prefixWord, tailWord_4155485, baseEnd_4155485] using wordTrace_append hprefix tailTrace_4155485
  have hstable : (prefixWord ++ tailWord_4155485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155485).length < 2 ^ (prefixWord ++ tailWord_4155485).sum := by decide
  have hdescent : baseEnd_4155485 < baseStart_4155485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155500 : List Nat := [2, 2, 1, 1, 3, 3, 1, 5, 1, 3]
def baseStart_4155500 : Nat := 118140960795 + 4155500 * 2 ^ 59
def prefixEnd_4155500 : Nat := 4983230072969 + 3 ^ 40 * 4155500 * 2
def baseEnd_4155500 : Nat := 1422512573172397880559473

theorem tailTrace_4155500 : CollatzResearch.WordTrace tailWord_4155500 prefixEnd_4155500 1422512573172397880559473 := by
  unfold tailWord_4155500
  simp only [CollatzResearch.WordTrace]
  refine ⟨75781768222670338871387977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101042357630227118495183969 75781768222670338871387977)
  ·
    refine ⟨56836326167002754153540983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75781768222670338871387977 56836326167002754153540983)
    ·
      refine ⟨85254489250504131230311475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56836326167002754153540983 85254489250504131230311475)
      ·
        refine ⟨127881733875756196845467213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85254489250504131230311475 127881733875756196845467213)
        ·
          refine ⟨47955650203408573817050205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127881733875756196845467213 47955650203408573817050205)
          ·
            refine ⟨17983368826278215181393827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47955650203408573817050205 17983368826278215181393827)
            ·
              refine ⟨26975053239417322772090741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17983368826278215181393827 26975053239417322772090741)
              ·
                refine ⟨2528911241195374009883507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26975053239417322772090741 2528911241195374009883507)
                ·
                  refine ⟨3793366861793061014825261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2528911241195374009883507 3793366861793061014825261)
                  ·
                    refine ⟨1422512573172397880559473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3793366861793061014825261 1422512573172397880559473)
                    ·
                      rfl

theorem cell22_4155500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 1, 3].length) (baseStart_4155500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155500 prefixEnd_4155500 := by exact prefixLift 4155500
  have htrace : WordTrace (prefixWord ++ tailWord_4155500) baseStart_4155500 baseEnd_4155500 := by
    simpa [prefixWord, tailWord_4155500, baseEnd_4155500] using wordTrace_append hprefix tailTrace_4155500
  have hstable : (prefixWord ++ tailWord_4155500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155500).length < 2 ^ (prefixWord ++ tailWord_4155500).sum := by decide
  have hdescent : baseEnd_4155500 < baseStart_4155500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155511 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 2, 5]
def baseStart_4155511 : Nat := 118140960795 + 4155511 * 2 ^ 59
def prefixEnd_4155511 : Nat := 4983230072969 + 3 ^ 40 * 4155511 * 2
def baseEnd_4155511 : Nat := 1422516338697197518534439

theorem tailTrace_4155511 : CollatzResearch.WordTrace tailWord_4155511 prefixEnd_4155511 1422516338697197518534439 := by
  unfold tailWord_4155511
  simp only [CollatzResearch.WordTrace]
  refine ⟨151563937648300826621426387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101042625098867217747617591 151563937648300826621426387)
  ·
    refine ⟨227345906472451239932139581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151563937648300826621426387 227345906472451239932139581)
    ·
      refine ⟨85254714927169214974552343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227345906472451239932139581 85254714927169214974552343)
      ·
        refine ⟨127882072390753822461828515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85254714927169214974552343 127882072390753822461828515)
        ·
          refine ⟨191823108586130733692742773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127882072390753822461828515 191823108586130733692742773)
          ·
            refine ⟨17983416429949756283694635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191823108586130733692742773 17983416429949756283694635)
            ·
              refine ⟨26975124644924634425541953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17983416429949756283694635 26975124644924634425541953)
              ·
                refine ⟨20231343483693475819156465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26975124644924634425541953 20231343483693475819156465)
                ·
                  refine ⟨15173507612770106864367349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20231343483693475819156465 15173507612770106864367349)
                  ·
                    refine ⟨1422516338697197518534439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15173507612770106864367349 1422516338697197518534439)
                    ·
                      rfl

theorem cell22_4155511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_4155511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155511 prefixEnd_4155511 := by exact prefixLift 4155511
  have htrace : WordTrace (prefixWord ++ tailWord_4155511) baseStart_4155511 baseEnd_4155511 := by
    simpa [prefixWord, tailWord_4155511, baseEnd_4155511] using wordTrace_append hprefix tailTrace_4155511
  have hstable : (prefixWord ++ tailWord_4155511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155511).length < 2 ^ (prefixWord ++ tailWord_4155511).sum := by decide
  have hdescent : baseEnd_4155511 < baseStart_4155511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155513 : List Nat := [1, 2, 1, 3, 4, 1, 3, 2, 5]
def baseStart_4155513 : Nat := 118140960795 + 4155513 * 2 ^ 59
def prefixEnd_4155513 : Nat := 4983230072969 + 3 ^ 40 * 4155513 * 2
def baseEnd_4155513 : Nat := 474172341112690059994811

theorem tailTrace_4155513 : CollatzResearch.WordTrace tailWord_4155513 prefixEnd_4155513 474172341112690059994811 := by
  unfold tailWord_4155513
  simp only [CollatzResearch.WordTrace]
  refine ⟨151564010594293580962999193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101042673729529053975332795 151564010594293580962999193)
  ·
    refine ⟨113673007945720185722249395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151564010594293580962999193 113673007945720185722249395)
    ·
      refine ⟨170509511918580278583374093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113673007945720185722249395 170509511918580278583374093)
      ·
        refine ⟨63941066969467604468765285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170509511918580278583374093 63941066969467604468765285)
        ·
          refine ⟨11988950056775175837893491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63941066969467604468765285 11988950056775175837893491)
          ·
            refine ⟨17983425085162763756840237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11988950056775175837893491 17983425085162763756840237)
            ·
              refine ⟨6743784406936036408815089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17983425085162763756840237 6743784406936036408815089)
              ·
                refine ⟨5057838305202027306611317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6743784406936036408815089 5057838305202027306611317)
                ·
                  refine ⟨474172341112690059994811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5057838305202027306611317 474172341112690059994811)
                  ·
                    rfl

theorem cell22_4155513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 5].length) (baseStart_4155513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155513 prefixEnd_4155513 := by exact prefixLift 4155513
  have htrace : WordTrace (prefixWord ++ tailWord_4155513) baseStart_4155513 baseEnd_4155513 := by
    simpa [prefixWord, tailWord_4155513, baseEnd_4155513] using wordTrace_append hprefix tailTrace_4155513
  have hstable : (prefixWord ++ tailWord_4155513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155513).length < 2 ^ (prefixWord ++ tailWord_4155513).sum := by decide
  have hdescent : baseEnd_4155513 < baseStart_4155513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155528 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 2, 5]
def baseStart_4155528 : Nat := 118140960795 + 4155528 * 2 ^ 59
def prefixEnd_4155528 : Nat := 4983230072969 + 3 ^ 40 * 4155528 * 2
def baseEnd_4155528 : Nat := 1422522158144615140859387

theorem tailTrace_4155528 : CollatzResearch.WordTrace tailWord_4155528 prefixEnd_4155528 1422522158144615140859387 := by
  unfold tailWord_4155528
  simp only [CollatzResearch.WordTrace]
  refine ⟨75782278844619619262397619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101043038459492825683196825 75782278844619619262397619)
  ·
    refine ⟨113673418266929428893596429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75782278844619619262397619 113673418266929428893596429)
    ·
      refine ⟨42627531850098535835098661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113673418266929428893596429 42627531850098535835098661)
      ·
        refine ⟨7992662221893475469080999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42627531850098535835098661 7992662221893475469080999)
        ·
          refine ⟨11988993332840213203621499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7992662221893475469080999 11988993332840213203621499)
          ·
            refine ⟨17983489999260319805432249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11988993332840213203621499 17983489999260319805432249)
            ·
              refine ⟨13487617499445239854074187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17983489999260319805432249 13487617499445239854074187)
              ·
                refine ⟨20231426249167859781111281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13487617499445239854074187 20231426249167859781111281)
                ·
                  refine ⟨15173569686875894835833461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20231426249167859781111281 15173569686875894835833461)
                  ·
                    refine ⟨1422522158144615140859387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15173569686875894835833461 1422522158144615140859387)
                    ·
                      rfl

theorem cell22_4155528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_4155528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155528 prefixEnd_4155528 := by exact prefixLift 4155528
  have htrace : WordTrace (prefixWord ++ tailWord_4155528) baseStart_4155528 baseEnd_4155528 := by
    simpa [prefixWord, tailWord_4155528, baseEnd_4155528] using wordTrace_append hprefix tailTrace_4155528
  have hstable : (prefixWord ++ tailWord_4155528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155528).length < 2 ^ (prefixWord ++ tailWord_4155528).sum := by decide
  have hdescent : baseEnd_4155528 < baseStart_4155528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155530 : List Nat := [3, 1, 2, 3, 1, 3, 3, 1, 5]
def baseStart_4155530 : Nat := 118140960795 + 4155530 * 2 ^ 59
def prefixEnd_4155530 : Nat := 4983230072969 + 3 ^ 40 * 4155530 * 2
def baseEnd_4155530 : Nat := 474174280928495934103127

theorem tailTrace_4155530 : CollatzResearch.WordTrace tailWord_4155530 prefixEnd_4155530 474174280928495934103127 := by
  unfold tailWord_4155530
  simp only [CollatzResearch.WordTrace]
  refine ⟨37891157658807998216592011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101043087090154661910912029 37891157658807998216592011)
  ·
    refine ⟨56836736488211997324888017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37891157658807998216592011 56836736488211997324888017)
    ·
      refine ⟨42627552366158997993666013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56836736488211997324888017 42627552366158997993666013)
      ·
        refine ⟨15985332137309624247624755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42627552366158997993666013 15985332137309624247624755)
        ·
          refine ⟨23977998205964436371437133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15985332137309624247624755 23977998205964436371437133)
          ·
            refine ⟨8991749327236663639288925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23977998205964436371437133 8991749327236663639288925)
            ·
              refine ⟨3371905997713748864733347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8991749327236663639288925 3371905997713748864733347)
              ·
                refine ⟨5057858996570623297100021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3371905997713748864733347 5057858996570623297100021)
                ·
                  refine ⟨474174280928495934103127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5057858996570623297100021 474174280928495934103127)
                  ·
                    rfl

theorem cell22_4155530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_4155530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155530 prefixEnd_4155530 := by exact prefixLift 4155530
  have htrace : WordTrace (prefixWord ++ tailWord_4155530) baseStart_4155530 baseEnd_4155530 := by
    simpa [prefixWord, tailWord_4155530, baseEnd_4155530] using wordTrace_append hprefix tailTrace_4155530
  have hstable : (prefixWord ++ tailWord_4155530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155530).length < 2 ^ (prefixWord ++ tailWord_4155530).sum := by decide
  have hdescent : baseEnd_4155530 < baseStart_4155530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155541 : List Nat := [1, 3, 2, 1, 1, 1, 3, 4, 6]
def baseStart_4155541 : Nat := 118140960795 + 4155541 * 2 ^ 59
def prefixEnd_4155541 : Nat := 4983230072969 + 3 ^ 40 * 4155541 * 2
def baseEnd_4155541 : Nat := 474175536103429146761449

theorem tailTrace_4155541 : CollatzResearch.WordTrace tailWord_4155541 prefixEnd_4155541 474175536103429146761449 := by
  unfold tailWord_4155541
  simp only [CollatzResearch.WordTrace]
  refine ⟨151565031838192141745018477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101043354558794761163345651 151565031838192141745018477)
  ·
    refine ⟨56836886939322053154381929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151565031838192141745018477 56836886939322053154381929)
    ·
      refine ⟨42627665204491539865786447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56836886939322053154381929 42627665204491539865786447)
      ·
        refine ⟨63941497806737309798679671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42627665204491539865786447 63941497806737309798679671)
        ·
          refine ⟨95912246710105964698019507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63941497806737309798679671 95912246710105964698019507)
          ·
            refine ⟨143868370065158947047029261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95912246710105964698019507 143868370065158947047029261)
            ·
              refine ⟨53950638774434605142635973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143868370065158947047029261 53950638774434605142635973)
              ·
                refine ⟨10115744770206488464244245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53950638774434605142635973 10115744770206488464244245)
                ·
                  refine ⟨474175536103429146761449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10115744770206488464244245 474175536103429146761449)
                  ·
                    rfl

theorem cell22_4155541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_4155541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155541 prefixEnd_4155541 := by exact prefixLift 4155541
  have htrace : WordTrace (prefixWord ++ tailWord_4155541) baseStart_4155541 baseEnd_4155541 := by
    simpa [prefixWord, tailWord_4155541, baseEnd_4155541] using wordTrace_append hprefix tailTrace_4155541
  have hstable : (prefixWord ++ tailWord_4155541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155541).length < 2 ^ (prefixWord ++ tailWord_4155541).sum := by decide
  have hdescent : baseEnd_4155541 < baseStart_4155541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155601 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 2, 7]
def baseStart_4155601 : Nat := 118140960795 + 4155601 * 2 ^ 59
def prefixEnd_4155601 : Nat := 4983230072969 + 3 ^ 40 * 4155601 * 2
def baseEnd_4155601 : Nat := 1422547147536467283784163

theorem tailTrace_4155601 : CollatzResearch.WordTrace tailWord_4155601 prefixEnd_4155601 1422547147536467283784163 := by
  unfold tailWord_4155601
  simp only [CollatzResearch.WordTrace]
  refine ⟨151567220217974771992202657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101044813478649847994801771 151567220217974771992202657)
  ·
    refine ⟨113675415163481078994151993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151567220217974771992202657 113675415163481078994151993)
    ·
      refine ⟨85256561372610809245613995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113675415163481078994151993 85256561372610809245613995)
      ·
        refine ⟨127884842058916213868420993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85256561372610809245613995 127884842058916213868420993)
        ·
          refine ⟨95913631544187160401315745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127884842058916213868420993 95913631544187160401315745)
          ·
            refine ⟨71935223658140370300986809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95913631544187160401315745 71935223658140370300986809)
            ·
              refine ⟨53951417743605277725740107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71935223658140370300986809 53951417743605277725740107)
              ·
                refine ⟨80927126615407916588610161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53951417743605277725740107 80927126615407916588610161)
                ·
                  refine ⟨60695344961555937441457621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80927126615407916588610161 60695344961555937441457621)
                  ·
                    refine ⟨1422547147536467283784163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60695344961555937441457621 1422547147536467283784163)
                    ·
                      rfl

theorem cell22_4155601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_4155601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155601 prefixEnd_4155601 := by exact prefixLift 4155601
  have htrace : WordTrace (prefixWord ++ tailWord_4155601) baseStart_4155601 baseEnd_4155601 := by
    simpa [prefixWord, tailWord_4155601, baseEnd_4155601] using wordTrace_append hprefix tailTrace_4155601
  have hstable : (prefixWord ++ tailWord_4155601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155601).length < 2 ^ (prefixWord ++ tailWord_4155601).sum := by decide
  have hdescent : baseEnd_4155601 < baseStart_4155601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155648 : List Nat := [2, 1, 1, 2, 1, 1, 6, 3, 5]
def baseStart_4155648 : Nat := 118140960795 + 4155648 * 2 ^ 59
def prefixEnd_4155648 : Nat := 4983230072969 + 3 ^ 40 * 4155648 * 2
def baseEnd_4155648 : Nat := 474187745532324942619673

theorem tailTrace_4155648 : CollatzResearch.WordTrace tailWord_4155648 prefixEnd_4155648 474187745532324942619673 := by
  unfold tailWord_4155648
  simp only [CollatzResearch.WordTrace]
  refine ⟨75784467224402249509581799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101045956299202999346109065 75784467224402249509581799)
  ·
    refine ⟨113676700836603374264372699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75784467224402249509581799 113676700836603374264372699)
    ·
      refine ⟨170515051254905061396559049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113676700836603374264372699 170515051254905061396559049)
      ·
        refine ⟨127886288441178796047419287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170515051254905061396559049 127886288441178796047419287)
        ·
          refine ⟨191829432661768194071128931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127886288441178796047419287 191829432661768194071128931)
          ·
            refine ⟨287744148992652291106693397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191829432661768194071128931 287744148992652291106693397)
            ·
              refine ⟨13488006984030576145626253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 287744148992652291106693397 13488006984030576145626253)
              ·
                refine ⟨5058002619011466054609845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13488006984030576145626253 5058002619011466054609845)
                ·
                  refine ⟨474187745532324942619673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5058002619011466054609845 474187745532324942619673)
                  ·
                    rfl

theorem cell22_4155648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 5].length) (baseStart_4155648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155648 prefixEnd_4155648 := by exact prefixLift 4155648
  have htrace : WordTrace (prefixWord ++ tailWord_4155648) baseStart_4155648 baseEnd_4155648 := by
    simpa [prefixWord, tailWord_4155648, baseEnd_4155648] using wordTrace_append hprefix tailTrace_4155648
  have hstable : (prefixWord ++ tailWord_4155648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155648).length < 2 ^ (prefixWord ++ tailWord_4155648).sum := by decide
  have hdescent : baseEnd_4155648 < baseStart_4155648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155652 : List Nat := [2, 3, 2, 2, 3, 1, 1, 2, 3, 3]
def baseStart_4155652 : Nat := 118140960795 + 4155652 * 2 ^ 59
def prefixEnd_4155652 : Nat := 4983230072969 + 3 ^ 40 * 4155652 * 2
def baseEnd_4155652 : Nat := 1422564605878720150759007

theorem tailTrace_4155652 : CollatzResearch.WordTrace tailWord_4155652 prefixEnd_4155652 1422564605878720150759007 := by
  unfold tailWord_4155652
  simp only [CollatzResearch.WordTrace]
  refine ⟨75784540170395003851154605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101046053560526671801539473 75784540170395003851154605)
  ·
    refine ⟨28419202563898126444182977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75784540170395003851154605 28419202563898126444182977)
    ·
      refine ⟨21314401922923594833137233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28419202563898126444182977 21314401922923594833137233)
      ·
        refine ⟨15985801442192696124852925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21314401922923594833137233 15985801442192696124852925)
        ·
          refine ⟨5994675540822261046819847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15985801442192696124852925 5994675540822261046819847)
          ·
            refine ⟨8992013311233391570229771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5994675540822261046819847 8992013311233391570229771)
            ·
              refine ⟨13488019966850087355344657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8992013311233391570229771 13488019966850087355344657)
              ·
                refine ⟨10116014975137565516508493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13488019966850087355344657 10116014975137565516508493)
                ·
                  refine ⟨3793505615676587068690685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10116014975137565516508493 3793505615676587068690685)
                  ·
                    refine ⟨1422564605878720150759007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3793505615676587068690685 1422564605878720150759007)
                    ·
                      rfl

theorem cell22_4155652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_4155652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155652 prefixEnd_4155652 := by exact prefixLift 4155652
  have htrace : WordTrace (prefixWord ++ tailWord_4155652) baseStart_4155652 baseEnd_4155652 := by
    simpa [prefixWord, tailWord_4155652, baseEnd_4155652] using wordTrace_append hprefix tailTrace_4155652
  have hstable : (prefixWord ++ tailWord_4155652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155652).length < 2 ^ (prefixWord ++ tailWord_4155652).sum := by decide
  have hdescent : baseEnd_4155652 < baseStart_4155652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155682 : List Nat := [3, 3, 1, 1, 3, 3, 1, 2, 5]
def baseStart_4155682 : Nat := 118140960795 + 4155682 * 2 ^ 59
def prefixEnd_4155682 : Nat := 4983230072969 + 3 ^ 40 * 4155682 * 2
def baseEnd_4155682 : Nat := 474191625163936690836305

theorem tailTrace_4155682 : CollatzResearch.WordTrace tailWord_4155682 prefixEnd_4155682 474191625163936690836305 := by
  unfold tailWord_4155682
  simp only [CollatzResearch.WordTrace]
  refine ⟨37892543632670330706475325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101046783020454215217267533 37892543632670330706475325)
  ·
    refine ⟨14209703862251374014928247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37892543632670330706475325 14209703862251374014928247)
    ·
      refine ⟨21314555793377061022392371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14209703862251374014928247 21314555793377061022392371)
      ·
        refine ⟨31971833690065591533588557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21314555793377061022392371 31971833690065591533588557)
        ·
          refine ⟨11989437633774596825095709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31971833690065591533588557 11989437633774596825095709)
          ·
            refine ⟨4496039112665473809410891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11989437633774596825095709 4496039112665473809410891)
            ·
              refine ⟨6744058668998210714116337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4496039112665473809410891 6744058668998210714116337)
              ·
                refine ⟨5058044001748658035587253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6744058668998210714116337 5058044001748658035587253)
                ·
                  refine ⟨474191625163936690836305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5058044001748658035587253 474191625163936690836305)
                  ·
                    rfl

theorem cell22_4155682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_4155682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155682 prefixEnd_4155682 := by exact prefixLift 4155682
  have htrace : WordTrace (prefixWord ++ tailWord_4155682) baseStart_4155682 baseEnd_4155682 := by
    simpa [prefixWord, tailWord_4155682, baseEnd_4155682] using wordTrace_append hprefix tailTrace_4155682
  have hstable : (prefixWord ++ tailWord_4155682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155682).length < 2 ^ (prefixWord ++ tailWord_4155682).sum := by decide
  have hdescent : baseEnd_4155682 < baseStart_4155682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155710 : List Nat := [4, 2, 1, 2, 1, 2, 2, 2, 6]
def baseStart_4155710 : Nat := 118140960795 + 4155710 * 2 ^ 59
def prefixEnd_4155710 : Nat := 4983230072969 + 3 ^ 40 * 4155710 * 2
def baseEnd_4155710 : Nat := 474194820154675777602943

theorem tailTrace_4155710 : CollatzResearch.WordTrace tailWord_4155710 prefixEnd_4155710 474194820154675777602943 := by
  unfold tailWord_4155710
  simp only [CollatzResearch.WordTrace]
  refine ⟨18946399471822485450990073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101047463849719922405280389 18946399471822485450990073)
  ·
    refine ⟨14209799603866864088242555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18946399471822485450990073 14209799603866864088242555)
    ·
      refine ⟨21314699405800296132363833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14209799603866864088242555 21314699405800296132363833)
      ·
        refine ⟨15986024554350222099272875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21314699405800296132363833 15986024554350222099272875)
        ·
          refine ⟨23979036831525333148909313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15986024554350222099272875 23979036831525333148909313)
          ·
            refine ⟨17984277623643999861681985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23979036831525333148909313 17984277623643999861681985)
            ·
              refine ⟨13488208217732999896261489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17984277623643999861681985 13488208217732999896261489)
              ·
                refine ⟨10116156163299749922196117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13488208217732999896261489 10116156163299749922196117)
                ·
                  refine ⟨474194820154675777602943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10116156163299749922196117 474194820154675777602943)
                  ·
                    rfl

theorem cell22_4155710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_4155710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155710 prefixEnd_4155710 := by exact prefixLift 4155710
  have htrace : WordTrace (prefixWord ++ tailWord_4155710) baseStart_4155710 baseEnd_4155710 := by
    simpa [prefixWord, tailWord_4155710, baseEnd_4155710] using wordTrace_append hprefix tailTrace_4155710
  have hstable : (prefixWord ++ tailWord_4155710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155710).length < 2 ^ (prefixWord ++ tailWord_4155710).sum := by decide
  have hdescent : baseEnd_4155710 < baseStart_4155710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155744 : List Nat := [2, 1, 1, 3, 5, 1, 3, 2, 4]
def baseStart_4155744 : Nat := 118140960795 + 4155744 * 2 ^ 59
def prefixEnd_4155744 : Nat := 4983230072969 + 3 ^ 40 * 4155744 * 2
def baseEnd_4155744 : Nat := 474198699786287525819575

theorem tailTrace_4155744 : CollatzResearch.WordTrace tailWord_4155744 prefixEnd_4155744 474198699786287525819575 := by
  unfold tailWord_4155744
  simp only [CollatzResearch.WordTrace]
  refine ⟨75786217928228353707329143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101048290570971138276438857 75786217928228353707329143)
  ·
    refine ⟨113679326892342530560993715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75786217928228353707329143 113679326892342530560993715)
    ·
      refine ⟨170518990338513795841490573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113679326892342530560993715 170518990338513795841490573)
      ·
        refine ⟨63944621376942673440558965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170518990338513795841490573 63944621376942673440558965)
        ·
          refine ⟨5994808254088375635052403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63944621376942673440558965 5994808254088375635052403)
          ·
            refine ⟨8992212381132563452578605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5994808254088375635052403 8992212381132563452578605)
            ·
              refine ⟨3372079642924711294716977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8992212381132563452578605 3372079642924711294716977)
              ·
                refine ⟨2529059732193533471037733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3372079642924711294716977 2529059732193533471037733)
                ·
                  refine ⟨474198699786287525819575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2529059732193533471037733 474198699786287525819575)
                  ·
                    rfl

theorem cell22_4155744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 4].length) (baseStart_4155744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155744 prefixEnd_4155744 := by exact prefixLift 4155744
  have htrace : WordTrace (prefixWord ++ tailWord_4155744) baseStart_4155744 baseEnd_4155744 := by
    simpa [prefixWord, tailWord_4155744, baseEnd_4155744] using wordTrace_append hprefix tailTrace_4155744
  have hstable : (prefixWord ++ tailWord_4155744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155744).length < 2 ^ (prefixWord ++ tailWord_4155744).sum := by decide
  have hdescent : baseEnd_4155744 < baseStart_4155744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155815 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 1, 7]
def baseStart_4155815 : Nat := 118140960795 + 4155815 * 2 ^ 59
def prefixEnd_4155815 : Nat := 4983230072969 + 3 ^ 40 * 4155815 * 2
def baseEnd_4155815 : Nat := 1422620404109842058933507

theorem tailTrace_4155815 : CollatzResearch.WordTrace tailWord_4155815 prefixEnd_4155815 1422620404109842058933507 := by
  unfold tailWord_4155815
  simp only [CollatzResearch.WordTrace]
  refine ⟨151575025439199486540492899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101050016959466324360328599 151575025439199486540492899)
  ·
    refine ⟨227362538158799229810739349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151575025439199486540492899 227362538158799229810739349)
    ·
      refine ⟨10657618976193713897378407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 227362538158799229810739349 10657618976193713897378407)
      ·
        refine ⟨15986428464290570846067611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10657618976193713897378407 15986428464290570846067611)
        ·
          refine ⟨23979642696435856269101417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15986428464290570846067611 23979642696435856269101417)
          ·
            refine ⟨17984732022326892201826063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23979642696435856269101417 17984732022326892201826063)
            ·
              refine ⟨26977098033490338302739095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17984732022326892201826063 26977098033490338302739095)
              ·
                refine ⟨40465647050235507454108643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26977098033490338302739095 40465647050235507454108643)
                ·
                  refine ⟨60698470575353261181162965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40465647050235507454108643 60698470575353261181162965)
                  ·
                    refine ⟨1422620404109842058933507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60698470575353261181162965 1422620404109842058933507)
                    ·
                      rfl

theorem cell22_4155815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_4155815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155815 prefixEnd_4155815 := by exact prefixLift 4155815
  have htrace : WordTrace (prefixWord ++ tailWord_4155815) baseStart_4155815 baseEnd_4155815 := by
    simpa [prefixWord, tailWord_4155815, baseEnd_4155815] using wordTrace_append hprefix tailTrace_4155815
  have hstable : (prefixWord ++ tailWord_4155815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155815).length < 2 ^ (prefixWord ++ tailWord_4155815).sum := by decide
  have hdescent : baseEnd_4155815 < baseStart_4155815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155847 : List Nat := [1, 1, 4, 1, 1, 5, 1, 3, 1, 4]
def baseStart_4155847 : Nat := 118140960795 + 4155847 * 2 ^ 59
def prefixEnd_4155847 : Nat := 4983230072969 + 3 ^ 40 * 4155847 * 2
def baseEnd_4155847 : Nat := 1422631358363804642133409

theorem tailTrace_4155847 : CollatzResearch.WordTrace tailWord_4155847 prefixEnd_4155847 1422631358363804642133409 := by
  unfold tailWord_4155847
  simp only [CollatzResearch.WordTrace]
  refine ⟨151576192575083556005657795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101050795050055704003771863 151576192575083556005657795)
  ·
    refine ⟨227364288862625334008486693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151576192575083556005657795 227364288862625334008486693)
    ·
      refine ⟨42630804161742250126591255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227364288862625334008486693 42630804161742250126591255)
      ·
        refine ⟨63946206242613375189886883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42630804161742250126591255 63946206242613375189886883)
        ·
          refine ⟨95919309363920062784830325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63946206242613375189886883 95919309363920062784830325)
          ·
            refine ⟨8992435252867505886077843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95919309363920062784830325 8992435252867505886077843)
            ·
              refine ⟨13488652879301258829116765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8992435252867505886077843 13488652879301258829116765)
              ·
                refine ⟨5058244829737972060918787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13488652879301258829116765 5058244829737972060918787)
                ·
                  refine ⟨7587367244606958091378181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5058244829737972060918787 7587367244606958091378181)
                  ·
                    refine ⟨1422631358363804642133409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7587367244606958091378181 1422631358363804642133409)
                    ·
                      rfl

theorem cell22_4155847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_4155847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155847 prefixEnd_4155847 := by exact prefixLift 4155847
  have htrace : WordTrace (prefixWord ++ tailWord_4155847) baseStart_4155847 baseEnd_4155847 := by
    simpa [prefixWord, tailWord_4155847, baseEnd_4155847] using wordTrace_append hprefix tailTrace_4155847
  have hstable : (prefixWord ++ tailWord_4155847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155847).length < 2 ^ (prefixWord ++ tailWord_4155847).sum := by decide
  have hdescent : baseEnd_4155847 < baseStart_4155847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155924 : List Nat := [2, 4, 3, 1, 1, 2, 2, 7]
def baseStart_4155924 : Nat := 118140960795 + 4155924 * 2 ^ 59
def prefixEnd_4155924 : Nat := 4983230072969 + 3 ^ 40 * 4155924 * 2
def baseEnd_4155924 : Nat := 158073079670822456439797

theorem tailTrace_4155924 : CollatzResearch.WordTrace tailWord_4155924 prefixEnd_4155924 158073079670822456439797 := by
  unfold tailWord_4155924
  simp only [CollatzResearch.WordTrace]
  refine ⟨75789500497902299078105413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101052667330536398770807217 75789500497902299078105413)
  ·
    refine ⟨14210531343356681077144765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75789500497902299078105413 14210531343356681077144765)
    ·
      refine ⟨5328949253758755403929287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14210531343356681077144765 5328949253758755403929287)
      ·
        refine ⟨7993423880638133105893931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5328949253758755403929287 7993423880638133105893931)
        ·
          refine ⟨11990135820957199658840897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7993423880638133105893931 11990135820957199658840897)
          ·
            refine ⟨8992601865717899744130673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11990135820957199658840897 8992601865717899744130673)
            ·
              refine ⟨6744451399288424808098005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8992601865717899744130673 6744451399288424808098005)
              ·
                refine ⟨158073079670822456439797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6744451399288424808098005 158073079670822456439797)
                ·
                  rfl

theorem cell22_4155924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 7].length) (baseStart_4155924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155924 prefixEnd_4155924 := by exact prefixLift 4155924
  have htrace : WordTrace (prefixWord ++ tailWord_4155924) baseStart_4155924 baseEnd_4155924 := by
    simpa [prefixWord, tailWord_4155924, baseEnd_4155924] using wordTrace_append hprefix tailTrace_4155924
  have hstable : (prefixWord ++ tailWord_4155924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155924).length < 2 ^ (prefixWord ++ tailWord_4155924).sum := by decide
  have hdescent : baseEnd_4155924 < baseStart_4155924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155969 : List Nat := [1, 2, 5, 1, 1, 3, 2, 2, 5]
def baseStart_4155969 : Nat := 118140960795 + 4155969 * 2 ^ 59
def prefixEnd_4155969 : Nat := 4983230072969 + 3 ^ 40 * 4155969 * 2
def baseEnd_4155969 : Nat := 474224373819012330194345

theorem tailTrace_4155969 : CollatzResearch.WordTrace tailWord_4155969 prefixEnd_4155969 474224373819012330194345 := by
  unfold tailWord_4155969
  simp only [CollatzResearch.WordTrace]
  refine ⟨151580642280641570841598961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101053761520427713894399307 151580642280641570841598961)
  ·
    refine ⟨113685481710481178131199221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151580642280641570841598961 113685481710481178131199221)
    ·
      refine ⟨10658013910357610449799927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113685481710481178131199221 10658013910357610449799927)
      ·
        refine ⟨15987020865536415674699891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10658013910357610449799927 15987020865536415674699891)
        ·
          refine ⟨23980531298304623512049837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15987020865536415674699891 23980531298304623512049837)
          ·
            refine ⟨8992699236864233817018689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23980531298304623512049837 8992699236864233817018689)
            ·
              refine ⟨6744524427648175362764017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8992699236864233817018689 6744524427648175362764017)
              ·
                refine ⟨5058393320736131522073013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6744524427648175362764017 5058393320736131522073013)
                ·
                  refine ⟨474224373819012330194345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5058393320736131522073013 474224373819012330194345)
                  ·
                    rfl

theorem cell22_4155969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 5].length) (baseStart_4155969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155969 prefixEnd_4155969 := by exact prefixLift 4155969
  have htrace : WordTrace (prefixWord ++ tailWord_4155969) baseStart_4155969 baseEnd_4155969 := by
    simpa [prefixWord, tailWord_4155969, baseEnd_4155969] using wordTrace_append hprefix tailTrace_4155969
  have hstable : (prefixWord ++ tailWord_4155969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155969).length < 2 ^ (prefixWord ++ tailWord_4155969).sum := by decide
  have hdescent : baseEnd_4155969 < baseStart_4155969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155973 : List Nat := [1, 3, 1, 1, 1, 7, 2, 2, 1, 3]
def baseStart_4155973 : Nat := 118140960795 + 4155973 * 2 ^ 59
def prefixEnd_4155973 : Nat := 4983230072969 + 3 ^ 40 * 4155973 * 2
def baseEnd_4155973 : Nat := 1422674490738782313483023

theorem tailTrace_4155973 : CollatzResearch.WordTrace tailWord_4155973 prefixEnd_4155973 1422674490738782313483023 := by
  unfold tailWord_4155973
  simp only [CollatzResearch.WordTrace]
  refine ⟨151580788172627079524744573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101053858781751386349829715 151580788172627079524744573)
  ·
    refine ⟨56842795564735154821779215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151580788172627079524744573 56842795564735154821779215)
    ·
      refine ⟨85264193347102732232668823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56842795564735154821779215 85264193347102732232668823)
      ·
        refine ⟨127896290020654098349003235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85264193347102732232668823 127896290020654098349003235)
        ·
          refine ⟨191844435030981147523504853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127896290020654098349003235 191844435030981147523504853)
          ·
            refine ⟨4496353946038620645082145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 191844435030981147523504853 4496353946038620645082145)
            ·
              refine ⟨3372265459528965483811609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4496353946038620645082145 3372265459528965483811609)
              ·
                refine ⟨2529199094646724112858707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3372265459528965483811609 2529199094646724112858707)
                ·
                  refine ⟨3793798641970086169288061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529199094646724112858707 3793798641970086169288061)
                  ·
                    refine ⟨1422674490738782313483023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3793798641970086169288061 1422674490738782313483023)
                    ·
                      rfl

theorem cell22_4155973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 1, 3].length) (baseStart_4155973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155973 prefixEnd_4155973 := by exact prefixLift 4155973
  have htrace : WordTrace (prefixWord ++ tailWord_4155973) baseStart_4155973 baseEnd_4155973 := by
    simpa [prefixWord, tailWord_4155973, baseEnd_4155973] using wordTrace_append hprefix tailTrace_4155973
  have hstable : (prefixWord ++ tailWord_4155973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155973).length < 2 ^ (prefixWord ++ tailWord_4155973).sum := by decide
  have hdescent : baseEnd_4155973 < baseStart_4155973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4155982 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_4155982 : Nat := 118140960795 + 4155982 * 2 ^ 59
def prefixEnd_4155982 : Nat := 4983230072969 + 3 ^ 40 * 4155982 * 2
def baseEnd_4155982 : Nat := 1422677571622709290007995

theorem tailTrace_4155982 : CollatzResearch.WordTrace tailWord_4155982 prefixEnd_4155982 1422677571622709290007995 := by
  unfold tailWord_4155982
  simp only [CollatzResearch.WordTrace]
  refine ⟨18947639553699309257727775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101054077619729649374548133 18947639553699309257727775)
  ·
    refine ⟨28421459330548963886591663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18947639553699309257727775 28421459330548963886591663)
    ·
      refine ⟨42632188995823445829887495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28421459330548963886591663 42632188995823445829887495)
      ·
        refine ⟨63948283493735168744831243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42632188995823445829887495 63948283493735168744831243)
        ·
          refine ⟨95922425240602753117246865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63948283493735168744831243 95922425240602753117246865)
          ·
            refine ⟨71941818930452064837935149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95922425240602753117246865 71941818930452064837935149)
            ·
              refine ⟨26978182098919524314225681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71941818930452064837935149 26978182098919524314225681)
              ·
                refine ⟨20233636574189643235669261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26978182098919524314225681 20233636574189643235669261)
                ·
                  refine ⟨7587613715321116213375973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20233636574189643235669261 7587613715321116213375973)
                  ·
                    refine ⟨1422677571622709290007995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7587613715321116213375973 1422677571622709290007995)
                    ·
                      rfl

theorem cell22_4155982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_4155982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4155982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4155982 prefixEnd_4155982 := by exact prefixLift 4155982
  have htrace : WordTrace (prefixWord ++ tailWord_4155982) baseStart_4155982 baseEnd_4155982 := by
    simpa [prefixWord, tailWord_4155982, baseEnd_4155982] using wordTrace_append hprefix tailTrace_4155982
  have hstable : (prefixWord ++ tailWord_4155982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4155982).length < 2 ^ (prefixWord ++ tailWord_4155982).sum := by decide
  have hdescent : baseEnd_4155982 < baseStart_4155982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4155982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156012 : List Nat := [2, 2, 1, 1, 3, 1, 4, 2, 1, 5]
def baseStart_4156012 : Nat := 118140960795 + 4156012 * 2 ^ 59
def prefixEnd_4156012 : Nat := 4983230072969 + 3 ^ 40 * 4156012 * 2
def baseEnd_4156012 : Nat := 1422687841235799211757903

theorem tailTrace_4156012 : CollatzResearch.WordTrace tailWord_4156012 prefixEnd_4156012 1422687841235799211757903 := by
  unfold tailWord_4156012
  simp only [CollatzResearch.WordTrace]
  refine ⟨75791105309742894592707145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101054807079657192790276193 75791105309742894592707145)
  ·
    refine ⟨56843328982307170944530359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75791105309742894592707145 56843328982307170944530359)
    ·
      refine ⟨85264993473460756416795539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56843328982307170944530359 85264993473460756416795539)
      ·
        refine ⟨127897490210191134625193309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85264993473460756416795539 127897490210191134625193309)
        ·
          refine ⟨47961558828821675484447491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127897490210191134625193309 47961558828821675484447491)
          ·
            refine ⟨71942338243232513226671237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47961558828821675484447491 71942338243232513226671237)
            ·
              refine ⟨13489188420606096230000857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71942338243232513226671237 13489188420606096230000857)
              ·
                refine ⟨10116891315454572172500643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13489188420606096230000857 10116891315454572172500643)
                ·
                  refine ⟨15175336973181858258750965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10116891315454572172500643 15175336973181858258750965)
                  ·
                    refine ⟨1422687841235799211757903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15175336973181858258750965 1422687841235799211757903)
                    ·
                      rfl

theorem cell22_4156012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_4156012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156012 prefixEnd_4156012 := by exact prefixLift 4156012
  have htrace : WordTrace (prefixWord ++ tailWord_4156012) baseStart_4156012 baseEnd_4156012 := by
    simpa [prefixWord, tailWord_4156012, baseEnd_4156012] using wordTrace_append hprefix tailTrace_4156012
  have hstable : (prefixWord ++ tailWord_4156012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156012).length < 2 ^ (prefixWord ++ tailWord_4156012).sum := by decide
  have hdescent : baseEnd_4156012 < baseStart_4156012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156097 : List Nat := [1, 2, 6, 2, 1, 2, 2, 1, 2, 3]
def baseStart_4156097 : Nat := 118140960795 + 4156097 * 2 ^ 59
def prefixEnd_4156097 : Nat := 4983230072969 + 3 ^ 40 * 4156097 * 2
def baseEnd_4156097 : Nat := 1422716938472887323382643

theorem tailTrace_4156097 : CollatzResearch.WordTrace tailWord_4156097 prefixEnd_4156097 1422716938472887323382643 := by
  unfold tailWord_4156097
  simp only [CollatzResearch.WordTrace]
  refine ⟨151585310824177848702258545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101056873882785232468172363 151585310824177848702258545)
  ·
    refine ⟨113688983118133386526693909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151585310824177848702258545 113688983118133386526693909)
    ·
      refine ⟨5329171083662502493438777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113688983118133386526693909 5329171083662502493438777)
      ·
        refine ⟨3996878312746876870079083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5329171083662502493438777 3996878312746876870079083)
        ·
          refine ⟨5995317469120315305118625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3996878312746876870079083 5995317469120315305118625)
          ·
            refine ⟨4496488101840236478838969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5995317469120315305118625 4496488101840236478838969)
            ·
              refine ⟨3372366076380177359129227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4496488101840236478838969 3372366076380177359129227)
              ·
                refine ⟨5058549114570266038693841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3372366076380177359129227 5058549114570266038693841)
                ·
                  refine ⟨3793911835927699529020381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5058549114570266038693841 3793911835927699529020381)
                  ·
                    refine ⟨1422716938472887323382643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3793911835927699529020381 1422716938472887323382643)
                    ·
                      rfl

theorem cell22_4156097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_4156097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156097 prefixEnd_4156097 := by exact prefixLift 4156097
  have htrace : WordTrace (prefixWord ++ tailWord_4156097) baseStart_4156097 baseEnd_4156097 := by
    simpa [prefixWord, tailWord_4156097, baseEnd_4156097] using wordTrace_append hprefix tailTrace_4156097
  have hstable : (prefixWord ++ tailWord_4156097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156097).length < 2 ^ (prefixWord ++ tailWord_4156097).sum := by decide
  have hdescent : baseEnd_4156097 < baseStart_4156097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156104 : List Nat := [2, 1, 3, 1, 2, 4, 1, 3, 5]
def baseStart_4156104 : Nat := 118140960795 + 4156104 * 2 ^ 59
def prefixEnd_4156104 : Nat := 4983230072969 + 3 ^ 40 * 4156104 * 2
def baseEnd_4156104 : Nat := 474239778238647212819207

theorem tailTrace_4156104 : CollatzResearch.WordTrace tailWord_4156104 prefixEnd_4156104 474239778238647212819207 := by
  unfold tailWord_4156104
  simp only [CollatzResearch.WordTrace]
  refine ⟨75792783067576244448881683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101057044090101659265175577 75792783067576244448881683)
  ·
    refine ⟨113689174601364366673322525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75792783067576244448881683 113689174601364366673322525)
    ·
      refine ⟨42633440475511637502495947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113689174601364366673322525 42633440475511637502495947)
      ·
        refine ⟨63950160713267456253743921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42633440475511637502495947 63950160713267456253743921)
        ·
          refine ⟨47962620534950592190307941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63950160713267456253743921 47962620534950592190307941)
          ·
            refine ⟨8992991350303236035682739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47962620534950592190307941 8992991350303236035682739)
            ·
              refine ⟨13489487025454854053524109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8992991350303236035682739 13489487025454854053524109)
              ·
                refine ⟨5058557634545570270071541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13489487025454854053524109 5058557634545570270071541)
                ·
                  refine ⟨474239778238647212819207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5058557634545570270071541 474239778238647212819207)
                  ·
                    rfl

theorem cell22_4156104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 5].length) (baseStart_4156104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156104 prefixEnd_4156104 := by exact prefixLift 4156104
  have htrace : WordTrace (prefixWord ++ tailWord_4156104) baseStart_4156104 baseEnd_4156104 := by
    simpa [prefixWord, tailWord_4156104, baseEnd_4156104] using wordTrace_append hprefix tailTrace_4156104
  have hstable : (prefixWord ++ tailWord_4156104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156104).length < 2 ^ (prefixWord ++ tailWord_4156104).sum := by decide
  have hdescent : baseEnd_4156104 < baseStart_4156104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156147 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 5, 5]
def baseStart_4156147 : Nat := 118140960795 + 4156147 * 2 ^ 59
def prefixEnd_4156147 : Nat := 4983230072969 + 3 ^ 40 * 4156147 * 2
def baseEnd_4156147 : Nat := 1422734054494703859632489

theorem tailTrace_4156147 : CollatzResearch.WordTrace tailWord_4156147 prefixEnd_4156147 1422734054494703859632489 := by
  unfold tailWord_4156147
  simp only [CollatzResearch.WordTrace]
  refine ⟨151587134473996707241578695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101058089649331138161052463 151587134473996707241578695)
  ·
    refine ⟨227380701710995060862368043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151587134473996707241578695 227380701710995060862368043)
    ·
      refine ⟨341071052566492591293552065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227380701710995060862368043 341071052566492591293552065)
      ·
        refine ⟨255803289424869443470164049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341071052566492591293552065 255803289424869443470164049)
        ·
          refine ⟨191852467068652082602623037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255803289424869443470164049 191852467068652082602623037)
          ·
            refine ⟨71944675150744530975983639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191852467068652082602623037 71944675150744530975983639)
            ·
              refine ⟨107917012726116796463975459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71944675150744530975983639 107917012726116796463975459)
              ·
                refine ⟨161875519089175194695963189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107917012726116796463975459 161875519089175194695963189)
                ·
                  refine ⟨15175829914610174502746549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161875519089175194695963189 15175829914610174502746549)
                  ·
                    refine ⟨1422734054494703859632489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15175829914610174502746549 1422734054494703859632489)
                    ·
                      rfl

theorem cell22_4156147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 5].length) (baseStart_4156147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156147 prefixEnd_4156147 := by exact prefixLift 4156147
  have htrace : WordTrace (prefixWord ++ tailWord_4156147) baseStart_4156147 baseEnd_4156147 := by
    simpa [prefixWord, tailWord_4156147, baseEnd_4156147] using wordTrace_append hprefix tailTrace_4156147
  have hstable : (prefixWord ++ tailWord_4156147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156147).length < 2 ^ (prefixWord ++ tailWord_4156147).sum := by decide
  have hdescent : baseEnd_4156147 < baseStart_4156147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156177 : List Nat := [1, 2, 2, 1, 1, 3, 2, 10]
def baseStart_4156177 : Nat := 118140960795 + 4156177 * 2 ^ 59
def prefixEnd_4156177 : Nat := 4983230072969 + 3 ^ 40 * 4156177 * 2
def baseEnd_4156177 : Nat := 158082702678643753486933

theorem tailTrace_4156177 : CollatzResearch.WordTrace tailWord_4156177 prefixEnd_4156177 158082702678643753486933 := by
  unfold tailWord_4156177
  simp only [CollatzResearch.WordTrace]
  refine ⟨151588228663888022365170785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101058819109258681576780523 151588228663888022365170785)
  ·
    refine ⟨113691171497916016773878089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151588228663888022365170785 113691171497916016773878089)
    ·
      refine ⟨85268378623437012580408567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113691171497916016773878089 85268378623437012580408567)
      ·
        refine ⟨127902567935155518870612851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85268378623437012580408567 127902567935155518870612851)
        ·
          refine ⟨191853851902733278305919277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127902567935155518870612851 191853851902733278305919277)
          ·
            refine ⟨71945194463524979364719729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191853851902733278305919277 71945194463524979364719729)
            ·
              refine ⟨53958895847643734523539797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71945194463524979364719729 53958895847643734523539797)
              ·
                refine ⟨158082702678643753486933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53958895847643734523539797 158082702678643753486933)
                ·
                  rfl

theorem cell22_4156177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 10].length) (baseStart_4156177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156177 prefixEnd_4156177 := by exact prefixLift 4156177
  have htrace : WordTrace (prefixWord ++ tailWord_4156177) baseStart_4156177 baseEnd_4156177 := by
    simpa [prefixWord, tailWord_4156177, baseEnd_4156177] using wordTrace_append hprefix tailTrace_4156177
  have hstable : (prefixWord ++ tailWord_4156177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156177).length < 2 ^ (prefixWord ++ tailWord_4156177).sum := by decide
  have hdescent : baseEnd_4156177 < baseStart_4156177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156183 : List Nat := [1, 1, 3, 4, 3, 1, 2, 3, 4]
def baseStart_4156183 : Nat := 118140960795 + 4156183 * 2 ^ 59
def prefixEnd_4156183 : Nat := 4983230072969 + 3 ^ 40 * 4156183 * 2
def baseEnd_4156183 : Nat := 474248792676803921910793

theorem tailTrace_4156183 : CollatzResearch.WordTrace tailWord_4156183 prefixEnd_4156183 474248792676803921910793 := by
  unfold tailWord_4156183
  simp only [CollatzResearch.WordTrace]
  refine ⟨151588447501866285389889203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101058965001244190259926135 151588447501866285389889203)
  ·
    refine ⟨227382671252799428084833805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151588447501866285389889203 227382671252799428084833805)
    ·
      refine ⟨85268501719799785531812677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227382671252799428084833805 85268501719799785531812677)
      ·
        refine ⟨15987844072462459787214877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85268501719799785531812677 15987844072462459787214877)
        ·
          refine ⟨5995441527173422420205579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15987844072462459787214877 5995441527173422420205579)
          ·
            refine ⟨8993162290760133630308369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5995441527173422420205579 8993162290760133630308369)
            ·
              refine ⟨6744871718070100222731277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8993162290760133630308369 6744871718070100222731277)
              ·
                refine ⟨2529326894276287583524229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6744871718070100222731277 2529326894276287583524229)
                ·
                  refine ⟨474248792676803921910793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2529326894276287583524229 474248792676803921910793)
                  ·
                    rfl

theorem cell22_4156183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 4].length) (baseStart_4156183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156183 prefixEnd_4156183 := by exact prefixLift 4156183
  have htrace : WordTrace (prefixWord ++ tailWord_4156183) baseStart_4156183 baseEnd_4156183 := by
    simpa [prefixWord, tailWord_4156183, baseEnd_4156183] using wordTrace_append hprefix tailTrace_4156183
  have hstable : (prefixWord ++ tailWord_4156183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156183).length < 2 ^ (prefixWord ++ tailWord_4156183).sum := by decide
  have hdescent : baseEnd_4156183 < baseStart_4156183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156194 : List Nat := [3, 3, 1, 1, 2, 3, 9]
def baseStart_4156194 : Nat := 118140960795 + 4156194 * 2 ^ 59
def prefixEnd_4156194 : Nat := 4983230072969 + 3 ^ 40 * 4156194 * 2
def baseEnd_4156194 : Nat := 52694449761304126063235

theorem tailTrace_4156194 : CollatzResearch.WordTrace tailWord_4156194 prefixEnd_4156194 52694449761304126063235 := by
  unfold tailWord_4156194
  simp only [CollatzResearch.WordTrace]
  refine ⟨37897212176206608567134909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101059232469884289512359757 37897212176206608567134909)
  ·
    refine ⟨14211454566077478212675591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37897212176206608567134909 14211454566077478212675591)
    ·
      refine ⟨21317181849116217319013387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14211454566077478212675591 21317181849116217319013387)
      ·
        refine ⟨31975772773674325978520081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21317181849116217319013387 31975772773674325978520081)
        ·
          refine ⟨23981829580255744483890061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31975772773674325978520081 23981829580255744483890061)
          ·
            refine ⟨8993186092595904181458773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23981829580255744483890061 8993186092595904181458773)
            ·
              refine ⟨52694449761304126063235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8993186092595904181458773 52694449761304126063235)
              ·
                rfl

theorem cell22_4156194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 9].length) (baseStart_4156194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156194 prefixEnd_4156194 := by exact prefixLift 4156194
  have htrace : WordTrace (prefixWord ++ tailWord_4156194) baseStart_4156194 baseEnd_4156194 := by
    simpa [prefixWord, tailWord_4156194, baseEnd_4156194] using wordTrace_append hprefix tailTrace_4156194
  have hstable : (prefixWord ++ tailWord_4156194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156194).length < 2 ^ (prefixWord ++ tailWord_4156194).sum := by decide
  have hdescent : baseEnd_4156194 < baseStart_4156194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156228 : List Nat := [2, 3, 4, 2, 1, 1, 1, 8]
def baseStart_4156228 : Nat := 118140960795 + 4156228 * 2 ^ 59
def prefixEnd_4156228 : Nat := 4983230072969 + 3 ^ 40 * 4156228 * 2
def baseEnd_4156228 : Nat := 158084642494449627595249

theorem tailTrace_4156228 : CollatzResearch.WordTrace tailWord_4156228 prefixEnd_4156228 158084642494449627595249 := by
  unfold tailWord_4156228
  simp only [CollatzResearch.WordTrace]
  refine ⟨75795044393351629037638669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101060059191135505383518225 75795044393351629037638669)
  ·
    refine ⟨28423141647506860889114501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75795044393351629037638669 28423141647506860889114501)
    ·
      refine ⟨5329339058907536416708969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28423141647506860889114501 5329339058907536416708969)
      ·
        refine ⟨3997004294180652312531727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5329339058907536416708969 3997004294180652312531727)
        ·
          refine ⟨5995506441270978468797591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3997004294180652312531727 5995506441270978468797591)
          ·
            refine ⟨8993259661906467703196387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5995506441270978468797591 8993259661906467703196387)
            ·
              refine ⟨13489889492859701554794581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8993259661906467703196387 13489889492859701554794581)
              ·
                refine ⟨158084642494449627595249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13489889492859701554794581 158084642494449627595249)
                ·
                  rfl

theorem cell22_4156228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 8].length) (baseStart_4156228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156228 prefixEnd_4156228 := by exact prefixLift 4156228
  have htrace : WordTrace (prefixWord ++ tailWord_4156228) baseStart_4156228 baseEnd_4156228 := by
    simpa [prefixWord, tailWord_4156228, baseEnd_4156228] using wordTrace_append hprefix tailTrace_4156228
  have hstable : (prefixWord ++ tailWord_4156228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156228).length < 2 ^ (prefixWord ++ tailWord_4156228).sum := by decide
  have hdescent : baseEnd_4156228 < baseStart_4156228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156269 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_4156269 : Nat := 118140960795 + 4156269 * 2 ^ 59
def prefixEnd_4156269 : Nat := 4983230072969 + 3 ^ 40 * 4156269 * 2
def baseEnd_4156269 : Nat := 1422775817587936208082115

theorem tailTrace_4156269 : CollatzResearch.WordTrace tailWord_4156269 prefixEnd_4156269 1422775817587936208082115 := by
  unfold tailWord_4156269
  simp only [CollatzResearch.WordTrace]
  refine ⟨151591584179554722077519861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101061056119703148051679907 151591584179554722077519861)
  ·
    refine ⟨14211711016833255194767487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151591584179554722077519861 14211711016833255194767487)
    ·
      refine ⟨21317566525249882792151231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14211711016833255194767487 21317566525249882792151231)
      ·
        refine ⟨31976349787874824188226847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21317566525249882792151231 31976349787874824188226847)
        ·
          refine ⟨47964524681812236282340271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31976349787874824188226847 47964524681812236282340271)
          ·
            refine ⟨71946787022718354423510407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47964524681812236282340271 71946787022718354423510407)
            ·
              refine ⟨107920180534077531635265611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71946787022718354423510407 107920180534077531635265611)
              ·
                refine ⟨161880270801116297452898417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107920180534077531635265611 161880270801116297452898417)
                ·
                  refine ⟨121410203100837223089673813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161880270801116297452898417 121410203100837223089673813)
                  ·
                    refine ⟨1422775817587936208082115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121410203100837223089673813 1422775817587936208082115)
                    ·
                      rfl

theorem cell22_4156269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_4156269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156269 prefixEnd_4156269 := by exact prefixLift 4156269
  have htrace : WordTrace (prefixWord ++ tailWord_4156269) baseStart_4156269 baseEnd_4156269 := by
    simpa [prefixWord, tailWord_4156269, baseEnd_4156269] using wordTrace_append hprefix tailTrace_4156269
  have hstable : (prefixWord ++ tailWord_4156269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156269).length < 2 ^ (prefixWord ++ tailWord_4156269).sum := by decide
  have hdescent : baseEnd_4156269 < baseStart_4156269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156273 : List Nat := [1, 2, 2, 2, 1, 6, 2, 1, 5]
def baseStart_4156273 : Nat := 118140960795 + 4156273 * 2 ^ 59
def prefixEnd_4156273 : Nat := 4983230072969 + 3 ^ 40 * 4156273 * 2
def baseEnd_4156273 : Nat := 474259062289893843660701

theorem tailTrace_4156273 : CollatzResearch.WordTrace tailWord_4156273 prefixEnd_4156273 474259062289893843660701 := by
  unfold tailWord_4156273
  simp only [CollatzResearch.WordTrace]
  refine ⟨151591730071540230760665473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101061153381026820507110315 151591730071540230760665473)
  ·
    refine ⟨113693797553655173070499105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151591730071540230760665473 113693797553655173070499105)
    ·
      refine ⟨85270348165241379802874329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113693797553655173070499105 85270348165241379802874329)
      ·
        refine ⟨63952761123931034852155747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85270348165241379802874329 63952761123931034852155747)
        ·
          refine ⟨95929141685896552278233621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63952761123931034852155747 95929141685896552278233621)
          ·
            refine ⟨4496678516526400888042201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95929141685896552278233621 4496678516526400888042201)
            ·
              refine ⟨3372508887394800666031651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4496678516526400888042201 3372508887394800666031651)
              ·
                refine ⟨5058763331092200999047477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3372508887394800666031651 5058763331092200999047477)
                ·
                  refine ⟨474259062289893843660701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5058763331092200999047477 474259062289893843660701)
                  ·
                    rfl

theorem cell22_4156273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 5].length) (baseStart_4156273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156273 prefixEnd_4156273 := by exact prefixLift 4156273
  have htrace : WordTrace (prefixWord ++ tailWord_4156273) baseStart_4156273 baseEnd_4156273 := by
    simpa [prefixWord, tailWord_4156273, baseEnd_4156273] using wordTrace_append hprefix tailTrace_4156273
  have hstable : (prefixWord ++ tailWord_4156273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156273).length < 2 ^ (prefixWord ++ tailWord_4156273).sum := by decide
  have hdescent : baseEnd_4156273 < baseStart_4156273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156284 : List Nat := [2, 2, 2, 1, 1, 1, 1, 6, 6]
def baseStart_4156284 : Nat := 118140960795 + 4156284 * 2 ^ 59
def prefixEnd_4156284 : Nat := 4983230072969 + 3 ^ 40 * 4156284 * 2
def baseEnd_4156284 : Nat := 474260317464827056319023

theorem tailTrace_4156284 : CollatzResearch.WordTrace tailWord_4156284 prefixEnd_4156284 474260317464827056319023 := by
  unfold tailWord_4156284
  simp only [CollatzResearch.WordTrace]
  refine ⟨75796065637250189819657953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101061420849666919759543937 75796065637250189819657953)
  ·
    refine ⟨56847049227937642364743465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75796065637250189819657953 56847049227937642364743465)
    ·
      refine ⟨42635286920953231773557599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56847049227937642364743465 42635286920953231773557599)
      ·
        refine ⟨63952930381429847660336399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42635286920953231773557599 63952930381429847660336399)
        ·
          refine ⟨95929395572144771490504599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63952930381429847660336399 95929395572144771490504599)
          ·
            refine ⟨143894093358217157235756899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95929395572144771490504599 143894093358217157235756899)
            ·
              refine ⟨215841140037325735853635349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143894093358217157235756899 215841140037325735853635349)
              ·
                refine ⟨10117553439249643868139157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 215841140037325735853635349 10117553439249643868139157)
                ·
                  refine ⟨474260317464827056319023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10117553439249643868139157 474260317464827056319023)
                  ·
                    rfl

theorem cell22_4156284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_4156284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156284 prefixEnd_4156284 := by exact prefixLift 4156284
  have htrace : WordTrace (prefixWord ++ tailWord_4156284) baseStart_4156284 baseEnd_4156284 := by
    simpa [prefixWord, tailWord_4156284, baseEnd_4156284] using wordTrace_append hprefix tailTrace_4156284
  have hstable : (prefixWord ++ tailWord_4156284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156284).length < 2 ^ (prefixWord ++ tailWord_4156284).sum := by decide
  have hdescent : baseEnd_4156284 < baseStart_4156284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156299 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 3, 5]
def baseStart_4156299 : Nat := 118140960795 + 4156299 * 2 ^ 59
def prefixEnd_4156299 : Nat := 4983230072969 + 3 ^ 40 * 4156299 * 2
def baseEnd_4156299 : Nat := 1422786087201026129832023

theorem tailTrace_4156299 : CollatzResearch.WordTrace tailWord_4156299 prefixEnd_4156299 1422786087201026129832023 := by
  unfold tailWord_4156299
  simp only [CollatzResearch.WordTrace]
  refine ⟨151592678369446037201111951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101061785579630691467407967 151592678369446037201111951)
  ·
    refine ⟨227389017554169055801667927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151592678369446037201111951 227389017554169055801667927)
    ·
      refine ⟨341083526331253583702501891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227389017554169055801667927 341083526331253583702501891)
      ·
        refine ⟨511625289496880375553752837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341083526331253583702501891 511625289496880375553752837)
        ·
          refine ⟨95929741780665070416328657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 511625289496880375553752837 95929741780665070416328657)
          ·
            refine ⟨71947306335498802812246493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95929741780665070416328657 71947306335498802812246493)
            ·
              refine ⟨26980239875812051054592435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71947306335498802812246493 26980239875812051054592435)
              ·
                refine ⟨40470359813718076581888653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26980239875812051054592435 40470359813718076581888653)
                ·
                  refine ⟨15176384930144278718208245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40470359813718076581888653 15176384930144278718208245)
                  ·
                    refine ⟨1422786087201026129832023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15176384930144278718208245 1422786087201026129832023)
                    ·
                      rfl

theorem cell22_4156299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 5].length) (baseStart_4156299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156299 prefixEnd_4156299 := by exact prefixLift 4156299
  have htrace : WordTrace (prefixWord ++ tailWord_4156299) baseStart_4156299 baseEnd_4156299 := by
    simpa [prefixWord, tailWord_4156299, baseEnd_4156299] using wordTrace_append hprefix tailTrace_4156299
  have hstable : (prefixWord ++ tailWord_4156299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156299).length < 2 ^ (prefixWord ++ tailWord_4156299).sum := by decide
  have hdescent : baseEnd_4156299 < baseStart_4156299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156346 : List Nat := [3, 1, 1, 1, 2, 1, 7, 6]
def baseStart_4156346 : Nat := 118140960795 + 4156346 * 2 ^ 59
def prefixEnd_4156346 : Nat := 4983230072969 + 3 ^ 40 * 4156346 * 2
def baseEnd_4156346 : Nat := 158089130695725963767431

theorem tailTrace_4156346 : CollatzResearch.WordTrace tailWord_4156346 prefixEnd_4156346 158089130695725963767431 := by
  unfold tailWord_4156346
  simp only [CollatzResearch.WordTrace]
  refine ⟨37898598150068941057018223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101062928400183842818715261 37898598150068941057018223)
  ·
    refine ⟨56847897225103411585527335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37898598150068941057018223 56847897225103411585527335)
    ·
      refine ⟨85271845837655117378291003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56847897225103411585527335 85271845837655117378291003)
      ·
        refine ⟨127907768756482676067436505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85271845837655117378291003 127907768756482676067436505)
        ·
          refine ⟨95930826567362007050577379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127907768756482676067436505 95930826567362007050577379)
          ·
            refine ⟨143896239851043010575866069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95930826567362007050577379 143896239851043010575866069)
            ·
              refine ⟨3372568121508820560371861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 143896239851043010575866069 3372568121508820560371861)
              ·
                refine ⟨158089130695725963767431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3372568121508820560371861 158089130695725963767431)
                ·
                  rfl

theorem cell22_4156346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 6].length) (baseStart_4156346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156346 prefixEnd_4156346 := by exact prefixLift 4156346
  have htrace : WordTrace (prefixWord ++ tailWord_4156346) baseStart_4156346 baseEnd_4156346 := by
    simpa [prefixWord, tailWord_4156346, baseEnd_4156346] using wordTrace_append hprefix tailTrace_4156346
  have hstable : (prefixWord ++ tailWord_4156346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156346).length < 2 ^ (prefixWord ++ tailWord_4156346).sum := by decide
  have hdescent : baseEnd_4156346 < baseStart_4156346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156378 : List Nat := [3, 1, 1, 2, 4, 1, 1, 3, 3, 3]
def baseStart_4156378 : Nat := 118140960795 + 4156378 * 2 ^ 59
def prefixEnd_4156378 : Nat := 4983230072969 + 3 ^ 40 * 4156378 * 2
def baseEnd_4156378 : Nat := 1422813130515496257106781

theorem tailTrace_4156378 : CollatzResearch.WordTrace tailWord_4156378 prefixEnd_4156378 1422813130515496257106781 := by
  unfold tailWord_4156378
  simp only [CollatzResearch.WordTrace]
  refine ⟨37898889934039958423309447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101063706490773222462158525 37898889934039958423309447)
  ·
    refine ⟨56848334901059937634964171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37898889934039958423309447 56848334901059937634964171)
    ·
      refine ⟨85272502351589906452446257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56848334901059937634964171 85272502351589906452446257)
      ·
        refine ⟨63954376763692429839334693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85272502351589906452446257 63954376763692429839334693)
        ·
          refine ⟨11991445643192330594875255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63954376763692429839334693 11991445643192330594875255)
          ·
            refine ⟨17987168464788495892312883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11991445643192330594875255 17987168464788495892312883)
            ·
              refine ⟨26980752697182743838469325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17987168464788495892312883 26980752697182743838469325)
              ·
                refine ⟨10117782261443528939425997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26980752697182743838469325 10117782261443528939425997)
                ·
                  refine ⟨3794168348041323352284749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10117782261443528939425997 3794168348041323352284749)
                  ·
                    refine ⟨1422813130515496257106781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3794168348041323352284749 1422813130515496257106781)
                    ·
                      rfl

theorem cell22_4156378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_4156378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156378 prefixEnd_4156378 := by exact prefixLift 4156378
  have htrace : WordTrace (prefixWord ++ tailWord_4156378) baseStart_4156378 baseEnd_4156378 := by
    simpa [prefixWord, tailWord_4156378, baseEnd_4156378] using wordTrace_append hprefix tailTrace_4156378
  have hstable : (prefixWord ++ tailWord_4156378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156378).length < 2 ^ (prefixWord ++ tailWord_4156378).sum := by decide
  have hdescent : baseEnd_4156378 < baseStart_4156378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156412 : List Nat := [2, 2, 2, 1, 2, 5, 1, 3, 1, 3]
def baseStart_4156412 : Nat := 118140960795 + 4156412 * 2 ^ 59
def prefixEnd_4156412 : Nat := 4983230072969 + 3 ^ 40 * 4156412 * 2
def baseEnd_4156412 : Nat := 1422824769410331501756677

theorem tailTrace_4156412 : CollatzResearch.WordTrace tailWord_4156412 prefixEnd_4156412 1422824769410331501756677 := by
  unfold tailWord_4156412
  simp only [CollatzResearch.WordTrace]
  refine ⟨75798399909018328749987745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101064533212024438333316993 75798399909018328749987745)
  ·
    refine ⟨56848799931763746562490809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75798399909018328749987745 56848799931763746562490809)
    ·
      refine ⟨42636599948822809921868107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56848799931763746562490809 42636599948822809921868107)
      ·
        refine ⟨63954899923234214882802161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42636599948822809921868107 63954899923234214882802161)
        ·
          refine ⟨47966174942425661162101621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63954899923234214882802161 47966174942425661162101621)
          ·
            refine ⟨4496828900852405733947027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47966174942425661162101621 4496828900852405733947027)
            ·
              refine ⟨6745243351278608600920541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4496828900852405733947027 6745243351278608600920541)
              ·
                refine ⟨2529466256729478225345203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6745243351278608600920541 2529466256729478225345203)
                ·
                  refine ⟨3794199385094217338017805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529466256729478225345203 3794199385094217338017805)
                  ·
                    refine ⟨1422824769410331501756677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3794199385094217338017805 1422824769410331501756677)
                    ·
                      rfl

theorem cell22_4156412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_4156412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156412 prefixEnd_4156412 := by exact prefixLift 4156412
  have htrace : WordTrace (prefixWord ++ tailWord_4156412) baseStart_4156412 baseEnd_4156412 := by
    simpa [prefixWord, tailWord_4156412, baseEnd_4156412] using wordTrace_append hprefix tailTrace_4156412
  have hstable : (prefixWord ++ tailWord_4156412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156412).length < 2 ^ (prefixWord ++ tailWord_4156412).sum := by decide
  have hdescent : baseEnd_4156412 < baseStart_4156412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156455 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 3, 4]
def baseStart_4156455 : Nat := 118140960795 + 4156455 * 2 ^ 59
def prefixEnd_4156455 : Nat := 4983230072969 + 3 ^ 40 * 4156455 * 2
def baseEnd_4156455 : Nat := 1422839489189093722931545

theorem tailTrace_4156455 : CollatzResearch.WordTrace tailWord_4156455 prefixEnd_4156455 1422839489189093722931545 := by
  unfold tailWord_4156455
  simp only [CollatzResearch.WordTrace]
  refine ⟨151598368156880875843790819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101065578771253917229193879 151598368156880875843790819)
  ·
    refine ⟨227397552235321313765686229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151598368156880875843790819 227397552235321313765686229)
    ·
      refine ⟨5329630130515343291383271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 227397552235321313765686229 5329630130515343291383271)
      ·
        refine ⟨7994445195773014937074907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5329630130515343291383271 7994445195773014937074907)
        ·
          refine ⟨11991667793659522405612361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7994445195773014937074907 11991667793659522405612361)
          ·
            refine ⟨8993750845244641804209271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11991667793659522405612361 8993750845244641804209271)
            ·
              refine ⟨13490626267866962706313907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8993750845244641804209271 13490626267866962706313907)
              ·
                refine ⟨20235939401800444059470861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13490626267866962706313907 20235939401800444059470861)
                ·
                  refine ⟨7588477275675166522301573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20235939401800444059470861 7588477275675166522301573)
                  ·
                    refine ⟨1422839489189093722931545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7588477275675166522301573 1422839489189093722931545)
                    ·
                      rfl

theorem cell22_4156455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_4156455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156455 prefixEnd_4156455 := by exact prefixLift 4156455
  have htrace : WordTrace (prefixWord ++ tailWord_4156455) baseStart_4156455 baseEnd_4156455 := by
    simpa [prefixWord, tailWord_4156455, baseEnd_4156455] using wordTrace_append hprefix tailTrace_4156455
  have hstable : (prefixWord ++ tailWord_4156455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156455).length < 2 ^ (prefixWord ++ tailWord_4156455).sum := by decide
  have hdescent : baseEnd_4156455 < baseStart_4156455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156481 : List Nat := [1, 2, 5, 1, 13]
def baseStart_4156481 : Nat := 118140960795 + 4156481 * 2 ^ 59
def prefixEnd_4156481 : Nat := 4983230072969 + 3 ^ 40 * 4156481 * 2
def baseEnd_4156481 : Nat := 5855343166750774986755

theorem tailTrace_4156481 : CollatzResearch.WordTrace tailWord_4156481 prefixEnd_4156481 5855343166750774986755 := by
  unfold tailWord_4156481
  simp only [CollatzResearch.WordTrace]
  refine ⟨151599316454786682284237297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101066210969857788189491531 151599316454786682284237297)
  ·
    refine ⟨113699487341090011713177973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151599316454786682284237297 113699487341090011713177973)
    ·
      refine ⟨10659326938227188598110435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113699487341090011713177973 10659326938227188598110435)
      ·
        refine ⟨15988990407340782897165653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10659326938227188598110435 15988990407340782897165653)
        ·
          refine ⟨5855343166750774986755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 15988990407340782897165653 5855343166750774986755)
          ·
            rfl

theorem cell22_4156481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 13].length) (baseStart_4156481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156481 prefixEnd_4156481 := by exact prefixLift 4156481
  have htrace : WordTrace (prefixWord ++ tailWord_4156481) baseStart_4156481 baseEnd_4156481 := by
    simpa [prefixWord, tailWord_4156481, baseEnd_4156481] using wordTrace_append hprefix tailTrace_4156481
  have hstable : (prefixWord ++ tailWord_4156481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156481).length < 2 ^ (prefixWord ++ tailWord_4156481).sum := by decide
  have hdescent : baseEnd_4156481 < baseStart_4156481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156487 : List Nat := [1, 1, 4, 1, 3, 4, 2, 2, 4]
def baseStart_4156487 : Nat := 118140960795 + 4156487 * 2 ^ 59
def prefixEnd_4156487 : Nat := 4983230072969 + 3 ^ 40 * 4156487 * 2
def baseEnd_4156487 : Nat := 474283481147685435377149

theorem tailTrace_4156487 : CollatzResearch.WordTrace tailWord_4156487 prefixEnd_4156487 474283481147685435377149 := by
  unfold tailWord_4156487
  simp only [CollatzResearch.WordTrace]
  refine ⟨151599535292764945308955715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101066356861843296872637143 151599535292764945308955715)
  ·
    refine ⟨227399302939147417963433573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151599535292764945308955715 227399302939147417963433573)
    ·
      refine ⟨42637369301090140868143795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227399302939147417963433573 42637369301090140868143795)
      ·
        refine ⟨63956053951635211302215693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42637369301090140868143795 63956053951635211302215693)
        ·
          refine ⟨23983520231863204238330885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63956053951635211302215693 23983520231863204238330885)
          ·
            refine ⟨4496910043474350794687041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23983520231863204238330885 4496910043474350794687041)
            ·
              refine ⟨3372682532605763096015281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4496910043474350794687041 3372682532605763096015281)
              ·
                refine ⟨2529511899454322322011461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3372682532605763096015281 2529511899454322322011461)
                ·
                  refine ⟨474283481147685435377149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2529511899454322322011461 474283481147685435377149)
                  ·
                    rfl

theorem cell22_4156487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 4].length) (baseStart_4156487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156487 prefixEnd_4156487 := by exact prefixLift 4156487
  have htrace : WordTrace (prefixWord ++ tailWord_4156487) baseStart_4156487 baseEnd_4156487 := by
    simpa [prefixWord, tailWord_4156487, baseEnd_4156487] using wordTrace_append hprefix tailTrace_4156487
  have hstable : (prefixWord ++ tailWord_4156487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156487).length < 2 ^ (prefixWord ++ tailWord_4156487).sum := by decide
  have hdescent : baseEnd_4156487 < baseStart_4156487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156498 : List Nat := [3, 2, 2, 1, 3, 1, 3, 7]
def baseStart_4156498 : Nat := 118140960795 + 4156498 * 2 ^ 59
def prefixEnd_4156498 : Nat := 4983230072969 + 3 ^ 40 * 4156498 * 2
def baseEnd_4156498 : Nat := 158094912107539549345157

theorem tailTrace_4156498 : CollatzResearch.WordTrace tailWord_4156498 prefixEnd_4156498 158094912107539549345157 := by
  unfold tailWord_4156498
  simp only [CollatzResearch.WordTrace]
  refine ⟨37899984123931273546901537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101066624330483396125070765 37899984123931273546901537)
  ·
    refine ⟨28424988092948455160176153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37899984123931273546901537 28424988092948455160176153)
    ·
      refine ⟨21318741069711341370132115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28424988092948455160176153 21318741069711341370132115)
      ·
        refine ⟨31978111604567012055198173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21318741069711341370132115 31978111604567012055198173)
        ·
          refine ⟨11991791851712629520699315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31978111604567012055198173 11991791851712629520699315)
          ·
            refine ⟨17987687777568944281048973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11991791851712629520699315 17987687777568944281048973)
            ·
              refine ⟨6745382916588354105393365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17987687777568944281048973 6745382916588354105393365)
              ·
                refine ⟨158094912107539549345157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6745382916588354105393365 158094912107539549345157)
                ·
                  rfl

theorem cell22_4156498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 7].length) (baseStart_4156498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156498 prefixEnd_4156498 := by exact prefixLift 4156498
  have htrace : WordTrace (prefixWord ++ tailWord_4156498) baseStart_4156498 baseEnd_4156498 := by
    simpa [prefixWord, tailWord_4156498, baseEnd_4156498] using wordTrace_append hprefix tailTrace_4156498
  have hstable : (prefixWord ++ tailWord_4156498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156498).length < 2 ^ (prefixWord ++ tailWord_4156498).sum := by decide
  have hdescent : baseEnd_4156498 < baseStart_4156498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156511 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 2, 6]
def baseStart_4156511 : Nat := 118140960795 + 4156511 * 2 ^ 59
def prefixEnd_4156511 : Nat := 4983230072969 + 3 ^ 40 * 4156511 * 2
def baseEnd_4156511 : Nat := 1422858659133528243531373

theorem tailTrace_4156511 : CollatzResearch.WordTrace tailWord_4156511 prefixEnd_4156511 1422858659133528243531373 := by
  unfold tailWord_4156511
  simp only [CollatzResearch.WordTrace]
  refine ⟨151600410644677997407829387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101066940429785331605219591 151600410644677997407829387)
  ·
    refine ⟨227400615967016996111744081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151600410644677997407829387 227400615967016996111744081)
    ·
      refine ⟨170550461975262747083808061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227400615967016996111744081 170550461975262747083808061)
      ·
        refine ⟨63956423240723530156428023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170550461975262747083808061 63956423240723530156428023)
        ·
          refine ⟨95934634861085295234642035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63956423240723530156428023 95934634861085295234642035)
          ·
            refine ⟨143901952291627942851963053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95934634861085295234642035 143901952291627942851963053)
            ·
              refine ⟨53963232109360478569486145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143901952291627942851963053 53963232109360478569486145)
              ·
                refine ⟨40472424082020358927114609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53963232109360478569486145 40472424082020358927114609)
                ·
                  refine ⟨30354318061515269195335957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40472424082020358927114609 30354318061515269195335957)
                  ·
                    refine ⟨1422858659133528243531373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30354318061515269195335957 1422858659133528243531373)
                    ·
                      rfl

theorem cell22_4156511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_4156511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156511 prefixEnd_4156511 := by exact prefixLift 4156511
  have htrace : WordTrace (prefixWord ++ tailWord_4156511) baseStart_4156511 baseEnd_4156511 := by
    simpa [prefixWord, tailWord_4156511, baseEnd_4156511] using wordTrace_append hprefix tailTrace_4156511
  have hstable : (prefixWord ++ tailWord_4156511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156511).length < 2 ^ (prefixWord ++ tailWord_4156511).sum := by decide
  have hdescent : baseEnd_4156511 < baseStart_4156511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156513 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 5, 3]
def baseStart_4156513 : Nat := 118140960795 + 4156513 * 2 ^ 59
def prefixEnd_4156513 : Nat := 4983230072969 + 3 ^ 40 * 4156513 * 2
def baseEnd_4156513 : Nat := 1422859343774400904981367

theorem tailTrace_4156513 : CollatzResearch.WordTrace tailWord_4156513 prefixEnd_4156513 1422859343774400904981367 := by
  unfold tailWord_4156513
  simp only [CollatzResearch.WordTrace]
  refine ⟨151600483590670751749402193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101066989060447167832934795 151600483590670751749402193)
  ·
    refine ⟨113700362693003063812051645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151600483590670751749402193 113700362693003063812051645)
    ·
      refine ⟨42637636009876148929519367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113700362693003063812051645 42637636009876148929519367)
      ·
        refine ⟨63956454014814223394279051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42637636009876148929519367 63956454014814223394279051)
        ·
          refine ⟨95934681022221335091418577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63956454014814223394279051 95934681022221335091418577)
          ·
            refine ⟨71951010766666001318563933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95934681022221335091418577 71951010766666001318563933)
            ·
              refine ⟨26981629037499750494461475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71951010766666001318563933 26981629037499750494461475)
              ·
                refine ⟨40472443556249625741692213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26981629037499750494461475 40472443556249625741692213)
                ·
                  refine ⟨3794291583398402413283645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40472443556249625741692213 3794291583398402413283645)
                  ·
                    refine ⟨1422859343774400904981367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3794291583398402413283645 1422859343774400904981367)
                    ·
                      rfl

theorem cell22_4156513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_4156513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156513 prefixEnd_4156513 := by exact prefixLift 4156513
  have htrace : WordTrace (prefixWord ++ tailWord_4156513) baseStart_4156513 baseEnd_4156513 := by
    simpa [prefixWord, tailWord_4156513, baseEnd_4156513] using wordTrace_append hprefix tailTrace_4156513
  have hstable : (prefixWord ++ tailWord_4156513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156513).length < 2 ^ (prefixWord ++ tailWord_4156513).sum := by decide
  have hdescent : baseEnd_4156513 < baseStart_4156513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156598 : List Nat := [5, 1, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_4156598 : Nat := 118140960795 + 4156598 * 2 ^ 59
def prefixEnd_4156598 : Nat := 4983230072969 + 3 ^ 40 * 4156598 * 2
def baseEnd_4156598 : Nat := 1422888441011489016606107

theorem tailTrace_4156598 : CollatzResearch.WordTrace tailWord_4156598 prefixEnd_4156598 1422888441011489016606107 := by
  unfold tailWord_4156598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9475223987210175704140403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101069055863575207510830965 9475223987210175704140403)
  ·
    refine ⟨14212835980815263556210605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9475223987210175704140403 14212835980815263556210605)
    ·
      refine ⟨5329813492805723833578977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14212835980815263556210605 5329813492805723833578977)
      ·
        refine ⟨3997360119604292875184233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5329813492805723833578977 3997360119604292875184233)
        ·
          refine ⟨2998020089703219656388175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3997360119604292875184233 2998020089703219656388175)
          ·
            refine ⟨4497030134554829484582263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2998020089703219656388175 4497030134554829484582263)
            ·
              refine ⟨6745545201832244226873395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4497030134554829484582263 6745545201832244226873395)
              ·
                refine ⟨10118317802748366340310093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6745545201832244226873395 10118317802748366340310093)
                ·
                  refine ⟨3794369176030637377616285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10118317802748366340310093 3794369176030637377616285)
                  ·
                    refine ⟨1422888441011489016606107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3794369176030637377616285 1422888441011489016606107)
                    ·
                      rfl

theorem cell22_4156598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_4156598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156598 prefixEnd_4156598 := by exact prefixLift 4156598
  have htrace : WordTrace (prefixWord ++ tailWord_4156598) baseStart_4156598 baseEnd_4156598 := by
    simpa [prefixWord, tailWord_4156598, baseEnd_4156598] using wordTrace_append hprefix tailTrace_4156598
  have hstable : (prefixWord ++ tailWord_4156598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156598).length < 2 ^ (prefixWord ++ tailWord_4156598).sum := by decide
  have hdescent : baseEnd_4156598 < baseStart_4156598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156605 : List Nat := [1, 4, 1, 2, 1, 1, 2, 6, 4]
def baseStart_4156605 : Nat := 118140960795 + 4156605 * 2 ^ 59
def prefixEnd_4156605 : Nat := 4983230072969 + 3 ^ 40 * 4156605 * 2
def baseEnd_4156605 : Nat := 474296945751514443893695

theorem tailTrace_4156605 : CollatzResearch.WordTrace tailWord_4156605 prefixEnd_4156605 474296945751514443893695 := by
  unfold tailWord_4156605
  simp only [CollatzResearch.WordTrace]
  refine ⟨151603839106337451461751269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101069226070891634307834179 151603839106337451461751269)
  ·
    refine ⟨28425719832438272149078363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151603839106337451461751269 28425719832438272149078363)
    ·
      refine ⟨42638579748657408223617545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28425719832438272149078363 42638579748657408223617545)
      ·
        refine ⟨31978934811493056167713159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42638579748657408223617545 31978934811493056167713159)
        ·
          refine ⟨47968402217239584251569739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31978934811493056167713159 47968402217239584251569739)
          ·
            refine ⟨71952603325859376377354609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47968402217239584251569739 71952603325859376377354609)
            ·
              refine ⟨53964452494394532283015957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71952603325859376377354609 53964452494394532283015957)
              ·
                refine ⟨2529583710674743700766373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53964452494394532283015957 2529583710674743700766373)
                ·
                  refine ⟨474296945751514443893695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2529583710674743700766373 474296945751514443893695)
                  ·
                    rfl

theorem cell22_4156605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_4156605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156605 prefixEnd_4156605 := by exact prefixLift 4156605
  have htrace : WordTrace (prefixWord ++ tailWord_4156605) baseStart_4156605 baseEnd_4156605 := by
    simpa [prefixWord, tailWord_4156605, baseEnd_4156605] using wordTrace_append hprefix tailTrace_4156605
  have hstable : (prefixWord ++ tailWord_4156605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156605).length < 2 ^ (prefixWord ++ tailWord_4156605).sum := by decide
  have hdescent : baseEnd_4156605 < baseStart_4156605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156637 : List Nat := [1, 4, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_4156637 : Nat := 118140960795 + 4156637 * 2 ^ 59
def prefixEnd_4156637 : Nat := 4983230072969 + 3 ^ 40 * 4156637 * 2
def baseEnd_4156637 : Nat := 1422901791508505914880987

theorem tailTrace_4156637 : CollatzResearch.WordTrace tailWord_4156637 prefixEnd_4156637 1422901791508505914880987 := by
  unfold tailWord_4156637
  simp only [CollatzResearch.WordTrace]
  refine ⟨151605006242221520926916165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101070004161481013951277443 151605006242221520926916165)
  ·
    refine ⟨28425938670416535173796781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151605006242221520926916165 28425938670416535173796781)
    ·
      refine ⟨10659727001406200690173793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28425938670416535173796781 10659727001406200690173793)
      ·
        refine ⟨7994795251054650517630345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10659727001406200690173793 7994795251054650517630345)
        ·
          refine ⟨5996096438290987888222759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7994795251054650517630345 5996096438290987888222759)
          ·
            refine ⟨8994144657436481832334139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5996096438290987888222759 8994144657436481832334139)
            ·
              refine ⟨13491216986154722748501209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8994144657436481832334139 13491216986154722748501209)
              ·
                refine ⟨10118412739616042061375907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13491216986154722748501209 10118412739616042061375907)
                ·
                  refine ⟨15177619109424063092063861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10118412739616042061375907 15177619109424063092063861)
                  ·
                    refine ⟨1422901791508505914880987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15177619109424063092063861 1422901791508505914880987)
                    ·
                      rfl

theorem cell22_4156637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_4156637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156637 prefixEnd_4156637 := by exact prefixLift 4156637
  have htrace : WordTrace (prefixWord ++ tailWord_4156637) baseStart_4156637 baseEnd_4156637 := by
    simpa [prefixWord, tailWord_4156637, baseEnd_4156637] using wordTrace_append hprefix tailTrace_4156637
  have hstable : (prefixWord ++ tailWord_4156637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156637).length < 2 ^ (prefixWord ++ tailWord_4156637).sum := by decide
  have hdescent : baseEnd_4156637 < baseStart_4156637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156665 : List Nat := [1, 2, 1, 3, 1, 1, 4, 3, 3, 3]
def baseStart_4156665 : Nat := 118140960795 + 4156665 * 2 ^ 59
def prefixEnd_4156665 : Nat := 4983230072969 + 3 ^ 40 * 4156665 * 2
def baseEnd_4156665 : Nat := 1422911376480723175180901

theorem tailTrace_4156665 : CollatzResearch.WordTrace tailWord_4156665 prefixEnd_4156665 1422911376480723175180901 := by
  unfold tailWord_4156665
  simp only [CollatzResearch.WordTrace]
  refine ⟨151606027486120081708935449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101070684990746721139290299 151606027486120081708935449)
  ·
    refine ⟨113704520614590061281701587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151606027486120081708935449 113704520614590061281701587)
    ·
      refine ⟨170556780921885091922552381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113704520614590061281701587 170556780921885091922552381)
      ·
        refine ⟨63958792845706909470957143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170556780921885091922552381 63958792845706909470957143)
        ·
          refine ⟨95938189268560364206435715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63958792845706909470957143 95938189268560364206435715)
          ·
            refine ⟨143907283902840546309653573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95938189268560364206435715 143907283902840546309653573)
            ·
              refine ⟨26982615731782602433060045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143907283902840546309653573 26982615731782602433060045)
              ·
                refine ⟨10118480899418475912397517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26982615731782602433060045 10118480899418475912397517)
                ·
                  refine ⟨3794430337281928467149069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10118480899418475912397517 3794430337281928467149069)
                  ·
                    refine ⟨1422911376480723175180901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3794430337281928467149069 1422911376480723175180901)
                    ·
                      rfl

theorem cell22_4156665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 3].length) (baseStart_4156665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156665 prefixEnd_4156665 := by exact prefixLift 4156665
  have htrace : WordTrace (prefixWord ++ tailWord_4156665) baseStart_4156665 baseEnd_4156665 := by
    simpa [prefixWord, tailWord_4156665, baseEnd_4156665] using wordTrace_append hprefix tailTrace_4156665
  have hstable : (prefixWord ++ tailWord_4156665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156665).length < 2 ^ (prefixWord ++ tailWord_4156665).sum := by decide
  have hdescent : baseEnd_4156665 < baseStart_4156665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156693 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 3, 7]
def baseStart_4156693 : Nat := 118140960795 + 4156693 * 2 ^ 59
def prefixEnd_4156693 : Nat := 4983230072969 + 3 ^ 40 * 4156693 * 2
def baseEnd_4156693 : Nat := 1422920961452940435480815

theorem tailTrace_4156693 : CollatzResearch.WordTrace tailWord_4156693 prefixEnd_4156693 1422920961452940435480815 := by
  unfold tailWord_4156693
  simp only [CollatzResearch.WordTrace]
  refine ⟨151607048730018642490954733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101071365820012428327303155 151607048730018642490954733)
  ·
    refine ⟨56852643273756990934108025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151607048730018642490954733 56852643273756990934108025)
    ·
      refine ⟨42639482455317743200581019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56852643273756990934108025 42639482455317743200581019)
      ·
        refine ⟨63959223682976614800871529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42639482455317743200581019 63959223682976614800871529)
        ·
          refine ⟨47969417762232461100653647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63959223682976614800871529 47969417762232461100653647)
          ·
            refine ⟨71954126643348691650980471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47969417762232461100653647 71954126643348691650980471)
            ·
              refine ⟨107931189965023037476470707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71954126643348691650980471 107931189965023037476470707)
              ·
                refine ⟨161896784947534556214706061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107931189965023037476470707 161896784947534556214706061)
                ·
                  refine ⟨60711294355325458580514773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161896784947534556214706061 60711294355325458580514773)
                  ·
                    refine ⟨1422920961452940435480815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60711294355325458580514773 1422920961452940435480815)
                    ·
                      rfl

theorem cell22_4156693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_4156693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156693 prefixEnd_4156693 := by exact prefixLift 4156693
  have htrace : WordTrace (prefixWord ++ tailWord_4156693) baseStart_4156693 baseEnd_4156693 := by
    simpa [prefixWord, tailWord_4156693, baseEnd_4156693] using wordTrace_append hprefix tailTrace_4156693
  have hstable : (prefixWord ++ tailWord_4156693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156693).length < 2 ^ (prefixWord ++ tailWord_4156693).sum := by decide
  have hdescent : baseEnd_4156693 < baseStart_4156693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156712 : List Nat := [2, 1, 5, 1, 2, 1, 3, 2, 5]
def baseStart_4156712 : Nat := 118140960795 + 4156712 * 2 ^ 59
def prefixEnd_4156712 : Nat := 4983230072969 + 3 ^ 40 * 4156712 * 2
def baseEnd_4156712 : Nat := 474309155180410239751919

theorem tailTrace_4156712 : CollatzResearch.WordTrace tailWord_4156712 prefixEnd_4156712 474309155180410239751919 := by
  unfold tailWord_4156712
  simp only [CollatzResearch.WordTrace]
  refine ⟨75803870858474904367948195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101071827811299872490597593 75803870858474904367948195)
  ·
    refine ⟨113705806287712356551922293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75803870858474904367948195 113705806287712356551922293)
    ·
      refine ⟨10659919339473033426742715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113705806287712356551922293 10659919339473033426742715)
      ·
        refine ⟨15989879009209550140114073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10659919339473033426742715 15989879009209550140114073)
        ·
          refine ⟨11992409256907162605085555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15989879009209550140114073 11992409256907162605085555)
          ·
            refine ⟨17988613885360743907628333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11992409256907162605085555 17988613885360743907628333)
            ·
              refine ⟨6745730207010278965360625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17988613885360743907628333 6745730207010278965360625)
              ·
                refine ⟨5059297655257709224020469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6745730207010278965360625 5059297655257709224020469)
                ·
                  refine ⟨474309155180410239751919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5059297655257709224020469 474309155180410239751919)
                  ·
                    rfl

theorem cell22_4156712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 5].length) (baseStart_4156712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156712 prefixEnd_4156712 := by exact prefixLift 4156712
  have htrace : WordTrace (prefixWord ++ tailWord_4156712) baseStart_4156712 baseEnd_4156712 := by
    simpa [prefixWord, tailWord_4156712, baseEnd_4156712] using wordTrace_append hprefix tailTrace_4156712
  have hstable : (prefixWord ++ tailWord_4156712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156712).length < 2 ^ (prefixWord ++ tailWord_4156712).sum := by decide
  have hdescent : baseEnd_4156712 < baseStart_4156712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156729 : List Nat := [1, 2, 1, 6, 2, 1, 3, 1, 5]
def baseStart_4156729 : Nat := 118140960795 + 4156729 * 2 ^ 59
def prefixEnd_4156729 : Nat := 4983230072969 + 3 ^ 40 * 4156729 * 2
def baseEnd_4156729 : Nat := 474311094996216113860235

theorem tailTrace_4156729 : CollatzResearch.WordTrace tailWord_4156729 prefixEnd_4156729 474311094996216113860235 := by
  unfold tailWord_4156729
  simp only [CollatzResearch.WordTrace]
  refine ⟨151608361757888220639265241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101072241171925480426176827 151608361757888220639265241)
  ·
    refine ⟨113706271318416165479448931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151608361757888220639265241 113706271318416165479448931)
    ·
      refine ⟨170559406977624248219173397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113706271318416165479448931 170559406977624248219173397)
      ·
        refine ⟨7994972202076136635273753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 170559406977624248219173397 7994972202076136635273753)
        ·
          refine ⟨5996229151557102476455315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7994972202076136635273753 5996229151557102476455315)
          ·
            refine ⟨8994343727335653714682973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5996229151557102476455315 8994343727335653714682973)
            ·
              refine ⟨3372878897750870143006115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8994343727335653714682973 3372878897750870143006115)
              ·
                refine ⟨5059318346626305214509173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3372878897750870143006115 5059318346626305214509173)
                ·
                  refine ⟨474311094996216113860235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5059318346626305214509173 474311094996216113860235)
                  ·
                    rfl

theorem cell22_4156729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 5].length) (baseStart_4156729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156729 prefixEnd_4156729 := by exact prefixLift 4156729
  have htrace : WordTrace (prefixWord ++ tailWord_4156729) baseStart_4156729 baseEnd_4156729 := by
    simpa [prefixWord, tailWord_4156729, baseEnd_4156729] using wordTrace_append hprefix tailTrace_4156729
  have hstable : (prefixWord ++ tailWord_4156729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156729).length < 2 ^ (prefixWord ++ tailWord_4156729).sum := by decide
  have hdescent : baseEnd_4156729 < baseStart_4156729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156755 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 6, 3]
def baseStart_4156755 : Nat := 118140960795 + 4156755 * 2 ^ 59
def prefixEnd_4156755 : Nat := 4983230072969 + 3 ^ 40 * 4156755 * 2
def baseEnd_4156755 : Nat := 1422942185319992940430625

theorem tailTrace_4156755 : CollatzResearch.WordTrace tailWord_4156755 prefixEnd_4156755 1422942185319992940430625 := by
  unfold tailWord_4156755
  simp only [CollatzResearch.WordTrace]
  refine ⟨151609310055794027079711719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101072873370529351386474479 151609310055794027079711719)
  ·
    refine ⟨227413965083691040619567579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151609310055794027079711719 227413965083691040619567579)
    ·
      refine ⟨341120947625536560929351369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227413965083691040619567579 341120947625536560929351369)
      ·
        refine ⟨255840710719152420697013527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341120947625536560929351369 255840710719152420697013527)
        ·
          refine ⟨383761066078728631045520291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255840710719152420697013527 383761066078728631045520291)
          ·
            refine ⟨575641599118092946568280437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383761066078728631045520291 575641599118092946568280437)
            ·
              refine ⟨53966399917321213740776291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 575641599118092946568280437 53966399917321213740776291)
              ·
                refine ⟨80949599875981820611164437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53966399917321213740776291 80949599875981820611164437)
                ·
                  refine ⟨3794512494186647841148333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80949599875981820611164437 3794512494186647841148333)
                  ·
                    refine ⟨1422942185319992940430625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3794512494186647841148333 1422942185319992940430625)
                    ·
                      rfl

theorem cell22_4156755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 3].length) (baseStart_4156755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156755 prefixEnd_4156755 := by exact prefixLift 4156755
  have htrace : WordTrace (prefixWord ++ tailWord_4156755) baseStart_4156755 baseEnd_4156755 := by
    simpa [prefixWord, tailWord_4156755, baseEnd_4156755] using wordTrace_append hprefix tailTrace_4156755
  have hstable : (prefixWord ++ tailWord_4156755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156755).length < 2 ^ (prefixWord ++ tailWord_4156755).sum := by decide
  have hdescent : baseEnd_4156755 < baseStart_4156755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156772 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 4, 3]
def baseStart_4156772 : Nat := 118140960795 + 4156772 * 2 ^ 59
def prefixEnd_4156772 : Nat := 4983230072969 + 3 ^ 40 * 4156772 * 2
def baseEnd_4156772 : Nat := 1422948004767410562755573

theorem tailTrace_4156772 : CollatzResearch.WordTrace tailWord_4156772 prefixEnd_4156772 1422948004767410562755573 := by
  unfold tailWord_4156772
  simp only [CollatzResearch.WordTrace]
  refine ⟨75804965048366219491540285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101073286731154959322053713 75804965048366219491540285)
  ·
    refine ⟨28426861893137332309327607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75804965048366219491540285 28426861893137332309327607)
    ·
      refine ⟨42640292839705998463991411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28426861893137332309327607 42640292839705998463991411)
      ·
        refine ⟨63960439259558997695987117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42640292839705998463991411 63960439259558997695987117)
        ·
          refine ⟨23985164722334624135995169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63960439259558997695987117 23985164722334624135995169)
          ·
            refine ⟨17988873541750968101996377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23985164722334624135995169 17988873541750968101996377)
            ·
              refine ⟨13491655156313226076497283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17988873541750968101996377 13491655156313226076497283)
              ·
                refine ⟨20237482734469839114745925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13491655156313226076497283 20237482734469839114745925)
                ·
                  refine ⟨3794528012713094834014861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20237482734469839114745925 3794528012713094834014861)
                  ·
                    refine ⟨1422948004767410562755573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3794528012713094834014861 1422948004767410562755573)
                    ·
                      rfl

theorem cell22_4156772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_4156772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156772 prefixEnd_4156772 := by exact prefixLift 4156772
  have htrace : WordTrace (prefixWord ++ tailWord_4156772) baseStart_4156772 baseEnd_4156772 := by
    simpa [prefixWord, tailWord_4156772, baseEnd_4156772] using wordTrace_append hprefix tailTrace_4156772
  have hstable : (prefixWord ++ tailWord_4156772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156772).length < 2 ^ (prefixWord ++ tailWord_4156772).sum := by decide
  have hdescent : baseEnd_4156772 < baseStart_4156772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156868 : List Nat := [2, 3, 3, 2, 1, 2, 2, 3, 1, 3]
def baseStart_4156868 : Nat := 118140960795 + 4156868 * 2 ^ 59
def prefixEnd_4156868 : Nat := 4983230072969 + 3 ^ 40 * 4156868 * 2
def baseEnd_4156868 : Nat := 1422980867529298312355279

theorem tailTrace_4156868 : CollatzResearch.WordTrace tailWord_4156868 prefixEnd_4156868 1422980867529298312355279 := by
  unfold tailWord_4156868
  simp only [CollatzResearch.WordTrace]
  refine ⟨75806715752192323689287629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101075621002923098252383505 75806715752192323689287629)
  ·
    refine ⟨28427518407072121383482861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75806715752192323689287629 28427518407072121383482861)
    ·
      refine ⟨10660319402652045518806073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28427518407072121383482861 10660319402652045518806073)
      ·
        refine ⟨7995239551989034139104555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10660319402652045518806073 7995239551989034139104555)
        ·
          refine ⟨11992859327983551208656833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7995239551989034139104555 11992859327983551208656833)
          ·
            refine ⟨8994644495987663406492625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11992859327983551208656833 8994644495987663406492625)
            ·
              refine ⟨6745983371990747554869469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8994644495987663406492625 6745983371990747554869469)
              ·
                refine ⟨2529743764496530333076051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6745983371990747554869469 2529743764496530333076051)
                ·
                  refine ⟨3794615646744795499614077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529743764496530333076051 3794615646744795499614077)
                  ·
                    refine ⟨1422980867529298312355279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3794615646744795499614077 1422980867529298312355279)
                    ·
                      rfl

theorem cell22_4156868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_4156868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156868 prefixEnd_4156868 := by exact prefixLift 4156868
  have htrace : WordTrace (prefixWord ++ tailWord_4156868) baseStart_4156868 baseEnd_4156868 := by
    simpa [prefixWord, tailWord_4156868, baseEnd_4156868] using wordTrace_append hprefix tailTrace_4156868
  have hstable : (prefixWord ++ tailWord_4156868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156868).length < 2 ^ (prefixWord ++ tailWord_4156868).sum := by decide
  have hdescent : baseEnd_4156868 < baseStart_4156868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156922 : List Nat := [3, 1, 1, 1, 1, 2, 4, 3, 2, 4]
def baseStart_4156922 : Nat := 118140960795 + 4156922 * 2 ^ 59
def prefixEnd_4156922 : Nat := 4983230072969 + 3 ^ 40 * 4156922 * 2
def baseEnd_4156922 : Nat := 1422999352832860171505113

theorem tailTrace_4156922 : CollatzResearch.WordTrace tailWord_4156922 prefixEnd_4156922 1422999352832860171505113 := by
  unfold tailWord_4156922
  simp only [CollatzResearch.WordTrace]
  refine ⟨37903850261547253650260255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101076934030792676400694013 37903850261547253650260255)
  ·
    refine ⟨56855775392320880475390383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37903850261547253650260255 56855775392320880475390383)
    ·
      refine ⟨85283663088481320713085575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56855775392320880475390383 85283663088481320713085575)
      ·
        refine ⟨127925494632721981069628363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85283663088481320713085575 127925494632721981069628363)
        ·
          refine ⟨191888241949082971604442545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127925494632721981069628363 191888241949082971604442545)
          ·
            refine ⟨143916181461812228703331909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191888241949082971604442545 143916181461812228703331909)
            ·
              refine ⟨26984284024089792881874733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143916181461812228703331909 26984284024089792881874733)
              ·
                refine ⟨10119106509033672330703025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26984284024089792881874733 10119106509033672330703025)
                ·
                  refine ⟨7589329881775254248027269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10119106509033672330703025 7589329881775254248027269)
                  ·
                    refine ⟨1422999352832860171505113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7589329881775254248027269 1422999352832860171505113)
                    ·
                      rfl

theorem cell22_4156922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_4156922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156922 prefixEnd_4156922 := by exact prefixLift 4156922
  have htrace : WordTrace (prefixWord ++ tailWord_4156922) baseStart_4156922 baseEnd_4156922 := by
    simpa [prefixWord, tailWord_4156922, baseEnd_4156922] using wordTrace_append hprefix tailTrace_4156922
  have hstable : (prefixWord ++ tailWord_4156922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156922).length < 2 ^ (prefixWord ++ tailWord_4156922).sum := by decide
  have hdescent : baseEnd_4156922 < baseStart_4156922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156939 : List Nat := [1, 1, 1, 1, 8, 1, 1, 2, 2, 4]
def baseStart_4156939 : Nat := 118140960795 + 4156939 * 2 ^ 59
def prefixEnd_4156939 : Nat := 4983230072969 + 3 ^ 40 * 4156939 * 2
def baseEnd_4156939 : Nat := 1423005172280277793830061

theorem tailTrace_4156939 : CollatzResearch.WordTrace tailWord_4156939 prefixEnd_4156939 1423005172280277793830061 := by
  unfold tailWord_4156939
  simp only [CollatzResearch.WordTrace]
  refine ⟨151616021087127426504409871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101077347391418284336273247 151616021087127426504409871)
  ·
    refine ⟨227424031630691139756614807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151616021087127426504409871 227424031630691139756614807)
    ·
      refine ⟨341136047446036709634922211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227424031630691139756614807 341136047446036709634922211)
      ·
        refine ⟨511704071169055064452383317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341136047446036709634922211 511704071169055064452383317)
        ·
          refine ⟨5996532084012364036551367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 511704071169055064452383317 5996532084012364036551367)
          ·
            refine ⟨8994798126018546054827051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5996532084012364036551367 8994798126018546054827051)
            ·
              refine ⟨13492197189027819082240577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8994798126018546054827051 13492197189027819082240577)
              ·
                refine ⟨10119147891770864311680433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13492197189027819082240577 10119147891770864311680433)
                ·
                  refine ⟨7589360918828148233760325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10119147891770864311680433 7589360918828148233760325)
                  ·
                    refine ⟨1423005172280277793830061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7589360918828148233760325 1423005172280277793830061)
                    ·
                      rfl

theorem cell22_4156939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 4].length) (baseStart_4156939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156939 prefixEnd_4156939 := by exact prefixLift 4156939
  have htrace : WordTrace (prefixWord ++ tailWord_4156939) baseStart_4156939 baseEnd_4156939 := by
    simpa [prefixWord, tailWord_4156939, baseEnd_4156939] using wordTrace_append hprefix tailTrace_4156939
  have hstable : (prefixWord ++ tailWord_4156939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156939).length < 2 ^ (prefixWord ++ tailWord_4156939).sum := by decide
  have hdescent : baseEnd_4156939 < baseStart_4156939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156986 : List Nat := [3, 1, 1, 1, 3, 2, 2, 5, 1, 3]
def baseStart_4156986 : Nat := 118140960795 + 4156986 * 2 ^ 59
def prefixEnd_4156986 : Nat := 4983230072969 + 3 ^ 40 * 4156986 * 2
def baseEnd_4156986 : Nat := 1423021261340785337904917

theorem tailTrace_4156986 : CollatzResearch.WordTrace tailWord_4156986 prefixEnd_4156986 1423021261340785337904917 := by
  unfold tailWord_4156986
  simp only [CollatzResearch.WordTrace]
  refine ⟨37904433829489288382842703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101078490211971435687580541 37904433829489288382842703)
  ·
    refine ⟨56856650744233932574264055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37904433829489288382842703 56856650744233932574264055)
    ·
      refine ⟨85284976116350898861396083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56856650744233932574264055 85284976116350898861396083)
      ·
        refine ⟨127927464174526348292094125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85284976116350898861396083 127927464174526348292094125)
        ·
          refine ⟨47972799065447380609535297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127927464174526348292094125 47972799065447380609535297)
          ·
            refine ⟨35979599299085535457151473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47972799065447380609535297 35979599299085535457151473)
            ·
              refine ⟨26984699474314151592863605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35979599299085535457151473 26984699474314151592863605)
              ·
                refine ⟨2529815575716951711830963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26984699474314151592863605 2529815575716951711830963)
                ·
                  refine ⟨3794723363575427567746445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529815575716951711830963 3794723363575427567746445)
                  ·
                    refine ⟨1423021261340785337904917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3794723363575427567746445 1423021261340785337904917)
                    ·
                      rfl

theorem cell22_4156986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 1, 3].length) (baseStart_4156986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156986 prefixEnd_4156986 := by exact prefixLift 4156986
  have htrace : WordTrace (prefixWord ++ tailWord_4156986) baseStart_4156986 baseEnd_4156986 := by
    simpa [prefixWord, tailWord_4156986, baseEnd_4156986] using wordTrace_append hprefix tailTrace_4156986
  have hstable : (prefixWord ++ tailWord_4156986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156986).length < 2 ^ (prefixWord ++ tailWord_4156986).sum := by decide
  have hdescent : baseEnd_4156986 < baseStart_4156986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156997 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 2, 5]
def baseStart_4156997 : Nat := 118140960795 + 4156997 * 2 ^ 59
def prefixEnd_4156997 : Nat := 4983230072969 + 3 ^ 40 * 4156997 * 2
def baseEnd_4156997 : Nat := 1423025026865584975879883

theorem tailTrace_4156997 : CollatzResearch.WordTrace tailWord_4156997 prefixEnd_4156997 1423025026865584975879883 := by
  unfold tailWord_4156997
  simp only [CollatzResearch.WordTrace]
  refine ⟨151618136520917302410021245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101078757680611534940014163 151618136520917302410021245)
  ·
    refine ⟨56856801195343988403757967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151618136520917302410021245 56856801195343988403757967)
    ·
      refine ⟨85285201793015982605636951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56856801195343988403757967 85285201793015982605636951)
      ·
        refine ⟨127927802689523973908455427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85285201793015982605636951 127927802689523973908455427)
        ·
          refine ⟨191891704034285960862683141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127927802689523973908455427 191891704034285960862683141)
          ·
            refine ⟨35979694506428617661753089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191891704034285960862683141 35979694506428617661753089)
            ·
              refine ⟨26984770879821463246314817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35979694506428617661753089 26984770879821463246314817)
              ·
                refine ⟨20238578159866097434736113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26984770879821463246314817 20238578159866097434736113)
                ·
                  refine ⟨15178933619899573076052085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20238578159866097434736113 15178933619899573076052085)
                  ·
                    refine ⟨1423025026865584975879883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15178933619899573076052085 1423025026865584975879883)
                    ·
                      rfl

theorem cell22_4156997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_4156997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4156997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4156997 prefixEnd_4156997 := by exact prefixLift 4156997
  have htrace : WordTrace (prefixWord ++ tailWord_4156997) baseStart_4156997 baseEnd_4156997 := by
    simpa [prefixWord, tailWord_4156997, baseEnd_4156997] using wordTrace_append hprefix tailTrace_4156997
  have hstable : (prefixWord ++ tailWord_4156997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156997).length < 2 ^ (prefixWord ++ tailWord_4156997).sum := by decide
  have hdescent : baseEnd_4156997 < baseStart_4156997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157027 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 8]
def baseStart_4157027 : Nat := 118140960795 + 4157027 * 2 ^ 59
def prefixEnd_4157027 : Nat := 4983230072969 + 3 ^ 40 * 4157027 * 2
def baseEnd_4157027 : Nat := 474345098826224965876597

theorem tailTrace_4157027 : CollatzResearch.WordTrace tailWord_4157027 prefixEnd_4157027 474345098826224965876597 := by
  unfold tailWord_4157027
  simp only [CollatzResearch.WordTrace]
  refine ⟨151619230710808617533613335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101079487140539078355742223 151619230710808617533613335)
  ·
    refine ⟨227428846066212926300420003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151619230710808617533613335 227428846066212926300420003)
    ·
      refine ⟨341143269099319389450630005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227428846066212926300420003 341143269099319389450630005)
      ·
        refine ⟨31982181478061192760996563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 341143269099319389450630005 31982181478061192760996563)
        ·
          refine ⟨47973272217091789141494845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31982181478061192760996563 47973272217091789141494845)
          ·
            refine ⟨17989977081409420928060567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47973272217091789141494845 17989977081409420928060567)
            ·
              refine ⟨26984965622114131392090851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17989977081409420928060567 26984965622114131392090851)
              ·
                refine ⟨40477448433171197088136277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26984965622114131392090851 40477448433171197088136277)
                ·
                  refine ⟨474345098826224965876597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40477448433171197088136277 474345098826224965876597)
                  ·
                    rfl

theorem cell22_4157027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 8].length) (baseStart_4157027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157027 prefixEnd_4157027 := by exact prefixLift 4157027
  have htrace : WordTrace (prefixWord ++ tailWord_4157027) baseStart_4157027 baseEnd_4157027 := by
    simpa [prefixWord, tailWord_4157027, baseEnd_4157027] using wordTrace_append hprefix tailTrace_4157027
  have hstable : (prefixWord ++ tailWord_4157027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157027).length < 2 ^ (prefixWord ++ tailWord_4157027).sum := by decide
  have hdescent : baseEnd_4157027 < baseStart_4157027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157029 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 3, 4]
def baseStart_4157029 : Nat := 118140960795 + 4157029 * 2 ^ 59
def prefixEnd_4157029 : Nat := 4983230072969 + 3 ^ 40 * 4157029 * 2
def baseEnd_4157029 : Nat := 1423035981119547559079785

theorem tailTrace_4157029 : CollatzResearch.WordTrace tailWord_4157029 prefixEnd_4157029 1423035981119547559079785 := by
  unfold tailWord_4157029
  simp only [CollatzResearch.WordTrace]
  refine ⟨151619303656801371875186141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101079535771200914583457427 151619303656801371875186141)
  ·
    refine ⟨56857238871300514453194803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151619303656801371875186141 56857238871300514453194803)
    ·
      refine ⟨85285858306950771679792205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56857238871300514453194803 85285858306950771679792205)
      ·
        refine ⟨31982196865106539379922077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85285858306950771679792205 31982196865106539379922077)
        ·
          refine ⟨11993323824414952267470779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31982196865106539379922077 11993323824414952267470779)
          ·
            refine ⟨17989985736622428401206169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11993323824414952267470779 17989985736622428401206169)
            ·
              refine ⟨13492489302466821300904627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17989985736622428401206169 13492489302466821300904627)
              ·
                refine ⟨20238733953700231951356941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13492489302466821300904627 20238733953700231951356941)
                ·
                  refine ⟨7589525232637586981758853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20238733953700231951356941 7589525232637586981758853)
                  ·
                    refine ⟨1423035981119547559079785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7589525232637586981758853 1423035981119547559079785)
                    ·
                      rfl

theorem cell22_4157029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_4157029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157029 prefixEnd_4157029 := by exact prefixLift 4157029
  have htrace : WordTrace (prefixWord ++ tailWord_4157029) baseStart_4157029 baseEnd_4157029 := by
    simpa [prefixWord, tailWord_4157029, baseEnd_4157029] using wordTrace_append hprefix tailTrace_4157029
  have hstable : (prefixWord ++ tailWord_4157029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157029).length < 2 ^ (prefixWord ++ tailWord_4157029).sum := by decide
  have hdescent : baseEnd_4157029 < baseStart_4157029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157089 : List Nat := [1, 2, 3, 3, 2, 2, 1, 8]
def baseStart_4157089 : Nat := 118140960795 + 4157089 * 2 ^ 59
def prefixEnd_4157089 : Nat := 4983230072969 + 3 ^ 40 * 4157089 * 2
def baseEnd_4157089 : Nat := 158117391149525266953289

theorem tailTrace_4157089 : CollatzResearch.WordTrace tailWord_4157089 prefixEnd_4157089 158117391149525266953289 := by
  unfold tailWord_4157089
  simp only [CollatzResearch.WordTrace]
  refine ⟨151621492036584002122370321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101080994691056001414913547 151621492036584002122370321)
  ·
    refine ⟨113716119027438001591777741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151621492036584002122370321 113716119027438001591777741)
    ·
      refine ⟨42643544635289250596916653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113716119027438001591777741 42643544635289250596916653)
      ·
        refine ⟨15991329238233468973843745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42643544635289250596916653 15991329238233468973843745)
        ·
          refine ⟨11993496928675101730382809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15991329238233468973843745 11993496928675101730382809)
          ·
            refine ⟨8995122696506326297787107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11993496928675101730382809 8995122696506326297787107)
            ·
              refine ⟨13492684044759489446680661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8995122696506326297787107 13492684044759489446680661)
              ·
                refine ⟨158117391149525266953289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13492684044759489446680661 158117391149525266953289)
                ·
                  rfl

theorem cell22_4157089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 8].length) (baseStart_4157089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157089 prefixEnd_4157089 := by exact prefixLift 4157089
  have htrace : WordTrace (prefixWord ++ tailWord_4157089) baseStart_4157089 baseEnd_4157089 := by
    simpa [prefixWord, tailWord_4157089, baseEnd_4157089] using wordTrace_append hprefix tailTrace_4157089
  have hstable : (prefixWord ++ tailWord_4157089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157089).length < 2 ^ (prefixWord ++ tailWord_4157089).sum := by decide
  have hdescent : baseEnd_4157089 < baseStart_4157089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157104 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 5, 3]
def baseStart_4157104 : Nat := 118140960795 + 4157104 * 2 ^ 59
def prefixEnd_4157104 : Nat := 4983230072969 + 3 ^ 40 * 4157104 * 2
def baseEnd_4157104 : Nat := 1423061655152272363454555

theorem tailTrace_4157104 : CollatzResearch.WordTrace tailWord_4157104 prefixEnd_4157104 1423061655152272363454555 := by
  unfold tailWord_4157104
  simp only [CollatzResearch.WordTrace]
  refine ⟨75811019565764829842083183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101081359421019773122777577 75811019565764829842083183)
  ·
    refine ⟨113716529348647244763124775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75811019565764829842083183 113716529348647244763124775)
    ·
      refine ⟨170574794022970867144687163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113716529348647244763124775 170574794022970867144687163)
      ·
        refine ⟨255862191034456300717030745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170574794022970867144687163 255862191034456300717030745)
        ·
          refine ⟨191896643275842225537773059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255862191034456300717030745 191896643275842225537773059)
          ·
            refine ⟨287844964913763338306659589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191896643275842225537773059 287844964913763338306659589)
            ·
              refine ⟨53970930921330625932498673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287844964913763338306659589 53970930921330625932498673)
              ·
                refine ⟨40478198190997969449374005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53970930921330625932498673 40478198190997969449374005)
                ·
                  refine ⟨3794831080406059635878813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40478198190997969449374005 3794831080406059635878813)
                  ·
                    refine ⟨1423061655152272363454555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3794831080406059635878813 1423061655152272363454555)
                    ·
                      rfl

theorem cell22_4157104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 5, 3].length) (baseStart_4157104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157104 prefixEnd_4157104 := by exact prefixLift 4157104
  have htrace : WordTrace (prefixWord ++ tailWord_4157104) baseStart_4157104 baseEnd_4157104 := by
    simpa [prefixWord, tailWord_4157104, baseEnd_4157104] using wordTrace_append hprefix tailTrace_4157104
  have hstable : (prefixWord ++ tailWord_4157104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157104).length < 2 ^ (prefixWord ++ tailWord_4157104).sum := by decide
  have hdescent : baseEnd_4157104 < baseStart_4157104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157228 : List Nat := [2, 2, 1, 1, 1, 5, 3, 2, 2, 3]
def baseStart_4157228 : Nat := 118140960795 + 4157228 * 2 ^ 59
def prefixEnd_4157228 : Nat := 4983230072969 + 3 ^ 40 * 4157228 * 2
def baseEnd_4157228 : Nat := 1423104102886377373354175

theorem tailTrace_4157228 : CollatzResearch.WordTrace tailWord_4157228 prefixEnd_4157228 1423104102886377373354175 := by
  unfold tailWord_4157228
  simp only [CollatzResearch.WordTrace]
  refine ⟨75813280891540214430840169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101084374522053619241120225 75813280891540214430840169)
  ·
    refine ⟨56859960668655160823130127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75813280891540214430840169 56859960668655160823130127)
    ·
      refine ⟨85289941002982741234695191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56859960668655160823130127 85289941002982741234695191)
      ·
        refine ⟨127934911504474111852042787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85289941002982741234695191 127934911504474111852042787)
        ·
          refine ⟨191902367256711167778064181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127934911504474111852042787 191902367256711167778064181)
          ·
            refine ⟨17990846930316671979193517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191902367256711167778064181 17990846930316671979193517)
            ·
              refine ⟨6746567598868751992197569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17990846930316671979193517 6746567598868751992197569)
              ·
                refine ⟨5059925699151563994148177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6746567598868751992197569 5059925699151563994148177)
                ·
                  refine ⟨3794944274363672995611133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5059925699151563994148177 3794944274363672995611133)
                  ·
                    refine ⟨1423104102886377373354175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3794944274363672995611133 1423104102886377373354175)
                    ·
                      rfl

theorem cell22_4157228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_4157228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157228 prefixEnd_4157228 := by exact prefixLift 4157228
  have htrace : WordTrace (prefixWord ++ tailWord_4157228) baseStart_4157228 baseEnd_4157228 := by
    simpa [prefixWord, tailWord_4157228, baseEnd_4157228] using wordTrace_append hprefix tailTrace_4157228
  have hstable : (prefixWord ++ tailWord_4157228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157228).length < 2 ^ (prefixWord ++ tailWord_4157228).sum := by decide
  have hdescent : baseEnd_4157228 < baseStart_4157228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157299 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 2, 8]
def baseStart_4157299 : Nat := 118140960795 + 4157299 * 2 ^ 59
def prefixEnd_4157299 : Nat := 4983230072969 + 3 ^ 40 * 4157299 * 2
def baseEnd_4157299 : Nat := 1423128407637356854828957

theorem tailTrace_4157299 : CollatzResearch.WordTrace tailWord_4157299 prefixEnd_4157299 1423128407637356854828957 := by
  unfold tailWord_4157299
  simp only [CollatzResearch.WordTrace]
  refine ⟨151629151365823207987514951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101086100910548805325009967 151629151365823207987514951)
  ·
    refine ⟨227443727048734811981272427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151629151365823207987514951 227443727048734811981272427)
    ·
      refine ⟨341165590573102217971908641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227443727048734811981272427 341165590573102217971908641)
      ·
        refine ⟨255874192929826663478931481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341165590573102217971908641 255874192929826663478931481)
        ·
          refine ⟨191905644697369997609198611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255874192929826663478931481 191905644697369997609198611)
          ·
            refine ⟨287858467046054996413797917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191905644697369997609198611 287858467046054996413797917)
            ·
              refine ⟨107946925142270623655174219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287858467046054996413797917 107946925142270623655174219)
              ·
                refine ⟨161920387713405935482761329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107946925142270623655174219 161920387713405935482761329)
                ·
                  refine ⟨121440290785054451612070997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161920387713405935482761329 121440290785054451612070997)
                  ·
                    refine ⟨1423128407637356854828957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121440290785054451612070997 1423128407637356854828957)
                    ·
                      rfl

theorem cell22_4157299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 8].length) (baseStart_4157299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157299 prefixEnd_4157299 := by exact prefixLift 4157299
  have htrace : WordTrace (prefixWord ++ tailWord_4157299) baseStart_4157299 baseEnd_4157299 := by
    simpa [prefixWord, tailWord_4157299, baseEnd_4157299] using wordTrace_append hprefix tailTrace_4157299
  have hstable : (prefixWord ++ tailWord_4157299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157299).length < 2 ^ (prefixWord ++ tailWord_4157299).sum := by decide
  have hdescent : baseEnd_4157299 < baseStart_4157299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157301 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 1, 7]
def baseStart_4157301 : Nat := 118140960795 + 4157301 * 2 ^ 59
def prefixEnd_4157301 : Nat := 4983230072969 + 3 ^ 40 * 4157301 * 2
def baseEnd_4157301 : Nat := 1423129092278229516278951

theorem tailTrace_4157301 : CollatzResearch.WordTrace tailWord_4157301 prefixEnd_4157301 1423129092278229516278951 := by
  unfold tailWord_4157301
  simp only [CollatzResearch.WordTrace]
  refine ⟨151629224311815962329087757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101086149541210641552725171 151629224311815962329087757)
  ·
    refine ⟨56860959116930985873407909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151629224311815962329087757 56860959116930985873407909)
    ·
      refine ⟨10661429834424559851263983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56860959116930985873407909 10661429834424559851263983)
      ·
        refine ⟨15992144751636839776895975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10661429834424559851263983 15992144751636839776895975)
        ·
          refine ⟨23988217127455259665343963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15992144751636839776895975 23988217127455259665343963)
          ·
            refine ⟨35982325691182889498015945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23988217127455259665343963 35982325691182889498015945)
            ·
              refine ⟨26986744268387167123511959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35982325691182889498015945 26986744268387167123511959)
              ·
                refine ⟨40480116402580750685267939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26986744268387167123511959 40480116402580750685267939)
                ·
                  refine ⟨60720174603871126027901909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40480116402580750685267939 60720174603871126027901909)
                  ·
                    refine ⟨1423129092278229516278951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60720174603871126027901909 1423129092278229516278951)
                    ·
                      rfl

theorem cell22_4157301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_4157301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157301 prefixEnd_4157301 := by exact prefixLift 4157301
  have htrace : WordTrace (prefixWord ++ tailWord_4157301) baseStart_4157301 baseEnd_4157301 := by
    simpa [prefixWord, tailWord_4157301, baseEnd_4157301] using wordTrace_append hprefix tailTrace_4157301
  have hstable : (prefixWord ++ tailWord_4157301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157301).length < 2 ^ (prefixWord ++ tailWord_4157301).sum := by decide
  have hdescent : baseEnd_4157301 < baseStart_4157301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157363 : List Nat := [1, 1, 1, 2, 3, 1, 3, 5, 2, 3]
def baseStart_4157363 : Nat := 118140960795 + 4157363 * 2 ^ 59
def prefixEnd_4157363 : Nat := 4983230072969 + 3 ^ 40 * 4157363 * 2
def baseEnd_4157363 : Nat := 1423150316145282021228761

theorem tailTrace_4157363 : CollatzResearch.WordTrace tailWord_4157363 prefixEnd_4157363 1423150316145282021228761 := by
  unfold tailWord_4157363
  simp only [CollatzResearch.WordTrace]
  refine ⟨151631485637591346917844743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101087657091727564611896495 151631485637591346917844743)
  ·
    refine ⟨227447228456387020376767115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151631485637591346917844743 227447228456387020376767115)
    ·
      refine ⟨341170842684580530565150673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227447228456387020376767115 341170842684580530565150673)
      ·
        refine ⟨255878132013435397923863005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341170842684580530565150673 255878132013435397923863005)
        ·
          refine ⟨95954299505038274221448627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255878132013435397923863005 95954299505038274221448627)
          ·
            refine ⟨143931449257557411332172941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95954299505038274221448627 143931449257557411332172941)
            ·
              refine ⟨53974293471584029249564853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143931449257557411332172941 53974293471584029249564853)
              ·
                refine ⟨5060090012961002742146705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53974293471584029249564853 5060090012961002742146705)
                ·
                  refine ⟨3795067509720752056610029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5060090012961002742146705 3795067509720752056610029)
                  ·
                    refine ⟨1423150316145282021228761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3795067509720752056610029 1423150316145282021228761)
                    ·
                      rfl

theorem cell22_4157363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 3].length) (baseStart_4157363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157363 prefixEnd_4157363 := by exact prefixLift 4157363
  have htrace : WordTrace (prefixWord ++ tailWord_4157363) baseStart_4157363 baseEnd_4157363 := by
    simpa [prefixWord, tailWord_4157363, baseEnd_4157363] using wordTrace_append hprefix tailTrace_4157363
  have hstable : (prefixWord ++ tailWord_4157363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157363).length < 2 ^ (prefixWord ++ tailWord_4157363).sum := by decide
  have hdescent : baseEnd_4157363 < baseStart_4157363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157397 : List Nat := [1, 3, 2, 3, 2, 3, 1, 2, 2, 3]
def baseStart_4157397 : Nat := 118140960795 + 4157397 * 2 ^ 59
def prefixEnd_4157397 : Nat := 4983230072969 + 3 ^ 40 * 4157397 * 2
def baseEnd_4157397 : Nat := 1423161955040117265878657

theorem tailTrace_4157397 : CollatzResearch.WordTrace tailWord_4157397 prefixEnd_4157397 1423161955040117265878657 := by
  unfold tailWord_4157397
  simp only [CollatzResearch.WordTrace]
  refine ⟨151632725719468170724582445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101088483812978780483054963 151632725719468170724582445)
  ·
    refine ⟨56862272144800564021718417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151632725719468170724582445 56862272144800564021718417)
    ·
      refine ⟨42646704108600423016288813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56862272144800564021718417 42646704108600423016288813)
      ·
        refine ⟨15992514040725158631108305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42646704108600423016288813 15992514040725158631108305)
        ·
          refine ⟨11994385530543868973331229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15992514040725158631108305 11994385530543868973331229)
          ·
            refine ⟨4497894573953950864999211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11994385530543868973331229 4497894573953950864999211)
            ·
              refine ⟨6746841860930926297498817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4497894573953950864999211 6746841860930926297498817)
              ·
                refine ⟨5060131395698194723124113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6746841860930926297498817 5060131395698194723124113)
                ·
                  refine ⟨3795098546773646042343085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5060131395698194723124113 3795098546773646042343085)
                  ·
                    refine ⟨1423161955040117265878657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3795098546773646042343085 1423161955040117265878657)
                    ·
                      rfl

theorem cell22_4157397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_4157397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157397 prefixEnd_4157397 := by exact prefixLift 4157397
  have htrace : WordTrace (prefixWord ++ tailWord_4157397) baseStart_4157397 baseEnd_4157397 := by
    simpa [prefixWord, tailWord_4157397, baseEnd_4157397] using wordTrace_append hprefix tailTrace_4157397
  have hstable : (prefixWord ++ tailWord_4157397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157397).length < 2 ^ (prefixWord ++ tailWord_4157397).sum := by decide
  have hdescent : baseEnd_4157397 < baseStart_4157397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157446 : List Nat := [6, 2, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_4157446 : Nat := 118140960795 + 4157446 * 2 ^ 59
def prefixEnd_4157446 : Nat := 4983230072969 + 3 ^ 40 * 4157446 * 2
def baseEnd_4157446 : Nat := 1423178728741497471403507

theorem tailTrace_4157446 : CollatzResearch.WordTrace tailWord_4157446 prefixEnd_4157446 1423178728741497471403507 := by
  unfold tailWord_4157446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4738578528009082877909881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101089675264193768062077461 4738578528009082877909881)
  ·
    refine ⟨3553933896006812158432411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4738578528009082877909881 3553933896006812158432411)
    ·
      refine ⟨5330900844010218237648617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3553933896006812158432411 5330900844010218237648617)
      ·
        refine ⟨3998175633007663678236463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5330900844010218237648617 3998175633007663678236463)
        ·
          refine ⟨5997263449511495517354695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3998175633007663678236463 5997263449511495517354695)
          ·
            refine ⟨8995895174267243276032043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5997263449511495517354695 8995895174267243276032043)
            ·
              refine ⟨13493842761400864914048065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8995895174267243276032043 13493842761400864914048065)
              ·
                refine ⟨10120382071050648685536049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13493842761400864914048065 10120382071050648685536049)
                ·
                  refine ⟨7590286553287986514152037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10120382071050648685536049 7590286553287986514152037)
                  ·
                    refine ⟨1423178728741497471403507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7590286553287986514152037 1423178728741497471403507)
                    ·
                      rfl

theorem cell22_4157446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_4157446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157446 prefixEnd_4157446 := by exact prefixLift 4157446
  have htrace : WordTrace (prefixWord ++ tailWord_4157446) baseStart_4157446 baseEnd_4157446 := by
    simpa [prefixWord, tailWord_4157446, baseEnd_4157446] using wordTrace_append hprefix tailTrace_4157446
  have hstable : (prefixWord ++ tailWord_4157446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157446).length < 2 ^ (prefixWord ++ tailWord_4157446).sum := by decide
  have hdescent : baseEnd_4157446 < baseStart_4157446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157500 : List Nat := [2, 2, 2, 2, 2, 1, 2, 5, 4]
def baseStart_4157500 : Nat := 118140960795 + 4157500 * 2 ^ 59
def prefixEnd_4157500 : Nat := 4983230072969 + 3 ^ 40 * 4157500 * 2
def baseEnd_4157500 : Nat := 474399071348353110184447

theorem tailTrace_4157500 : CollatzResearch.WordTrace tailWord_4157500 prefixEnd_4157500 474399071348353110184447 := by
  unfold tailWord_4157500
  simp only [CollatzResearch.WordTrace]
  refine ⟨75818241219047509657790977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101090988292063346210387969 75818241219047509657790977)
  ·
    refine ⟨56863680914285632243343233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75818241219047509657790977 56863680914285632243343233)
    ·
      refine ⟨42647760685714224182507425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56863680914285632243343233 42647760685714224182507425)
      ·
        refine ⟨31985820514285668136880569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42647760685714224182507425 31985820514285668136880569)
        ·
          refine ⟨23989365385714251102660427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31985820514285668136880569 23989365385714251102660427)
          ·
            refine ⟨35984048078571376653990641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23989365385714251102660427 35984048078571376653990641)
            ·
              refine ⟨26988036058928532490492981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35984048078571376653990641 26988036058928532490492981)
              ·
                refine ⟨2530128380524549920983717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26988036058928532490492981 2530128380524549920983717)
                ·
                  refine ⟨474399071348353110184447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2530128380524549920983717 474399071348353110184447)
                  ·
                    rfl

theorem cell22_4157500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_4157500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157500 prefixEnd_4157500 := by exact prefixLift 4157500
  have htrace : WordTrace (prefixWord ++ tailWord_4157500) baseStart_4157500 baseEnd_4157500 := by
    simpa [prefixWord, tailWord_4157500, baseEnd_4157500] using wordTrace_append hprefix tailTrace_4157500
  have hstable : (prefixWord ++ tailWord_4157500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157500).length < 2 ^ (prefixWord ++ tailWord_4157500).sum := by decide
  have hdescent : baseEnd_4157500 < baseStart_4157500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157513 : List Nat := [1, 2, 1, 1, 2, 2, 3, 4, 2, 4]
def baseStart_4157513 : Nat := 118140960795 + 4157513 * 2 ^ 59
def prefixEnd_4157513 : Nat := 4983230072969 + 3 ^ 40 * 4157513 * 2
def baseEnd_4157513 : Nat := 1423201664210731629978301

theorem tailTrace_4157513 : CollatzResearch.WordTrace tailWord_4157513 prefixEnd_4157513 1423201664210731629978301 := by
  unfold tailWord_4157513
  simp only [CollatzResearch.WordTrace]
  refine ⟨151636956587047922535805193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101091304391365281690536795 151636956587047922535805193)
  ·
    refine ⟨113727717440285941901853895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151636956587047922535805193 113727717440285941901853895)
    ·
      refine ⟨170591576160428912852780843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113727717440285941901853895 170591576160428912852780843)
      ·
        refine ⟨255887364240643369279171265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170591576160428912852780843 255887364240643369279171265)
        ·
          refine ⟨191915523180482526959378449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255887364240643369279171265 191915523180482526959378449)
          ·
            refine ⟨143936642385361895219533837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191915523180482526959378449 143936642385361895219533837)
            ·
              refine ⟨53976240894510710707325189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143936642385361895219533837 53976240894510710707325189)
              ·
                refine ⟨10120545167720758257623473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53976240894510710707325189 10120545167720758257623473)
                ·
                  refine ⟨7590408875790568693217605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10120545167720758257623473 7590408875790568693217605)
                  ·
                    refine ⟨1423201664210731629978301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7590408875790568693217605 1423201664210731629978301)
                    ·
                      rfl

theorem cell22_4157513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_4157513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157513 prefixEnd_4157513 := by exact prefixLift 4157513
  have htrace : WordTrace (prefixWord ++ tailWord_4157513) baseStart_4157513 baseEnd_4157513 := by
    simpa [prefixWord, tailWord_4157513, baseEnd_4157513] using wordTrace_append hprefix tailTrace_4157513
  have hstable : (prefixWord ++ tailWord_4157513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157513).length < 2 ^ (prefixWord ++ tailWord_4157513).sum := by decide
  have hdescent : baseEnd_4157513 < baseStart_4157513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157517 : List Nat := [1, 6, 1, 1, 1, 1, 3, 4, 4]
def baseStart_4157517 : Nat := 118140960795 + 4157517 * 2 ^ 59
def prefixEnd_4157517 : Nat := 4983230072969 + 3 ^ 40 * 4157517 * 2
def baseEnd_4157517 : Nat := 474401011164158984292763

theorem tailTrace_4157517 : CollatzResearch.WordTrace tailWord_4157517 prefixEnd_4157517 474401011164158984292763 := by
  unfold tailWord_4157517
  simp only [CollatzResearch.WordTrace]
  refine ⟨151637102479033431218950805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101091401652688954145967203 151637102479033431218950805)
  ·
    refine ⟨7107989178704692088388319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151637102479033431218950805 7107989178704692088388319)
    ·
      refine ⟨10661983768057038132582479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7107989178704692088388319 10661983768057038132582479)
      ·
        refine ⟨15992975652085557198873719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10661983768057038132582479 15992975652085557198873719)
        ·
          refine ⟨23989463478128335798310579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15992975652085557198873719 23989463478128335798310579)
          ·
            refine ⟨35984195217192503697465869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23989463478128335798310579 35984195217192503697465869)
            ·
              refine ⟨13494073206447188886549701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35984195217192503697465869 13494073206447188886549701)
              ·
                refine ⟨2530138726208847916228069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13494073206447188886549701 2530138726208847916228069)
                ·
                  refine ⟨474401011164158984292763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2530138726208847916228069 474401011164158984292763)
                  ·
                    rfl

theorem cell22_4157517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_4157517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157517 prefixEnd_4157517 := by exact prefixLift 4157517
  have htrace : WordTrace (prefixWord ++ tailWord_4157517) baseStart_4157517 baseEnd_4157517 := by
    simpa [prefixWord, tailWord_4157517, baseEnd_4157517] using wordTrace_append hprefix tailTrace_4157517
  have hstable : (prefixWord ++ tailWord_4157517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157517).length < 2 ^ (prefixWord ++ tailWord_4157517).sum := by decide
  have hdescent : baseEnd_4157517 < baseStart_4157517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157528 : List Nat := [2, 1, 2, 2, 1, 4, 3, 7]
def baseStart_4157528 : Nat := 118140960795 + 4157528 * 2 ^ 59
def prefixEnd_4157528 : Nat := 4983230072969 + 3 ^ 40 * 4157528 * 2
def baseEnd_4157528 : Nat := 158134088779697398983695

theorem tailTrace_4157528 : CollatzResearch.WordTrace tailWord_4157528 prefixEnd_4157528 158134088779697398983695 := by
  unfold tailWord_4157528
  simp only [CollatzResearch.WordTrace]
  refine ⟨75818751840996790048800619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101091669121329053398400825 75818751840996790048800619)
  ·
    refine ⟨113728127761495185073200929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75818751840996790048800619 113728127761495185073200929)
    ·
      refine ⟨85296095821121388804900697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113728127761495185073200929 85296095821121388804900697)
      ·
        refine ⟨63972071865841041603675523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85296095821121388804900697 63972071865841041603675523)
        ·
          refine ⟨95958107798761562405513285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63972071865841041603675523 95958107798761562405513285)
          ·
            refine ⟨17992145212267792951033741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95958107798761562405513285 17992145212267792951033741)
            ·
              refine ⟨6747054454600422356637653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17992145212267792951033741 6747054454600422356637653)
              ·
                refine ⟨158134088779697398983695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6747054454600422356637653 158134088779697398983695)
                ·
                  rfl

theorem cell22_4157528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 7].length) (baseStart_4157528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157528 prefixEnd_4157528 := by exact prefixLift 4157528
  have htrace : WordTrace (prefixWord ++ tailWord_4157528) baseStart_4157528 baseEnd_4157528 := by
    simpa [prefixWord, tailWord_4157528, baseEnd_4157528] using wordTrace_append hprefix tailTrace_4157528
  have hstable : (prefixWord ++ tailWord_4157528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157528).length < 2 ^ (prefixWord ++ tailWord_4157528).sum := by decide
  have hdescent : baseEnd_4157528 < baseStart_4157528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157532 : List Nat := [2, 2, 4, 1, 1, 2, 2, 3, 2, 3]
def baseStart_4157532 : Nat := 118140960795 + 4157532 * 2 ^ 59
def prefixEnd_4157532 : Nat := 4983230072969 + 3 ^ 40 * 4157532 * 2
def baseEnd_4157532 : Nat := 1423208168299021913753243

theorem tailTrace_4157532 : CollatzResearch.WordTrace tailWord_4157532 prefixEnd_4157532 1423208168299021913753243 := by
  unfold tailWord_4157532
  simp only [CollatzResearch.WordTrace]
  refine ⟨75818824786989544390373425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101091766382652725853831233 75818824786989544390373425)
  ·
    refine ⟨56864118590242158292780069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75818824786989544390373425 56864118590242158292780069)
    ·
      refine ⟨10662022235670404679896263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56864118590242158292780069 10662022235670404679896263)
      ·
        refine ⟨15993033353505607019844395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10662022235670404679896263 15993033353505607019844395)
        ·
          refine ⟨23989550030258410529766593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15993033353505607019844395 23989550030258410529766593)
          ·
            refine ⟨17992162522693807897324945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23989550030258410529766593 17992162522693807897324945)
            ·
              refine ⟨13494121892020355922993709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17992162522693807897324945 13494121892020355922993709)
              ·
                refine ⟨5060295709507633471122641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13494121892020355922993709 5060295709507633471122641)
                ·
                  refine ⟨3795221782130725103341981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5060295709507633471122641 3795221782130725103341981)
                  ·
                    refine ⟨1423208168299021913753243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3795221782130725103341981 1423208168299021913753243)
                    ·
                      rfl

theorem cell22_4157532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_4157532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157532 prefixEnd_4157532 := by exact prefixLift 4157532
  have htrace : WordTrace (prefixWord ++ tailWord_4157532) baseStart_4157532 baseEnd_4157532 := by
    simpa [prefixWord, tailWord_4157532, baseEnd_4157532] using wordTrace_append hprefix tailTrace_4157532
  have hstable : (prefixWord ++ tailWord_4157532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157532).length < 2 ^ (prefixWord ++ tailWord_4157532).sum := by decide
  have hdescent : baseEnd_4157532 < baseStart_4157532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157534 : List Nat := [4, 4, 1, 1, 2, 1, 1, 2, 6]
def baseStart_4157534 : Nat := 118140960795 + 4157534 * 2 ^ 59
def prefixEnd_4157534 : Nat := 4983230072969 + 3 ^ 40 * 4157534 * 2
def baseEnd_4157534 : Nat := 474402950979964858401079

theorem tailTrace_4157534 : CollatzResearch.WordTrace tailWord_4157534 prefixEnd_4157534 474402950979964858401079 := by
  unfold tailWord_4157534
  simp only [CollatzResearch.WordTrace]
  refine ⟨18954715314996480390289957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101091815013314562081546437 18954715314996480390289957)
  ·
    refine ⟨3554009121561840073179367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18954715314996480390289957 3554009121561840073179367)
    ·
      refine ⟨5331013682342760109769051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3554009121561840073179367 5331013682342760109769051)
      ·
        refine ⟨7996520523514140164653577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5331013682342760109769051 7996520523514140164653577)
        ·
          refine ⟨5997390392635605123490183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7996520523514140164653577 5997390392635605123490183)
          ·
            refine ⟨8996085588953407685235275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5997390392635605123490183 8996085588953407685235275)
            ·
              refine ⟨13494128383430111527852913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8996085588953407685235275 13494128383430111527852913)
              ·
                refine ⟨10120596287572583645889685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13494128383430111527852913 10120596287572583645889685)
                ·
                  refine ⟨474402950979964858401079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10120596287572583645889685 474402950979964858401079)
                  ·
                    rfl

theorem cell22_4157534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_4157534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157534 prefixEnd_4157534 := by exact prefixLift 4157534
  have htrace : WordTrace (prefixWord ++ tailWord_4157534) baseStart_4157534 baseEnd_4157534 := by
    simpa [prefixWord, tailWord_4157534, baseEnd_4157534] using wordTrace_append hprefix tailTrace_4157534
  have hstable : (prefixWord ++ tailWord_4157534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157534).length < 2 ^ (prefixWord ++ tailWord_4157534).sum := by decide
  have hdescent : baseEnd_4157534 < baseStart_4157534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157577 : List Nat := [1, 2, 1, 1, 4, 2, 1, 6, 1, 3]
def baseStart_4157577 : Nat := 118140960795 + 4157577 * 2 ^ 59
def prefixEnd_4157577 : Nat := 4983230072969 + 3 ^ 40 * 4157577 * 2
def baseEnd_4157577 : Nat := 1423223572718656796378105

theorem tailTrace_4157577 : CollatzResearch.WordTrace tailWord_4157577 prefixEnd_4157577 1423223572718656796378105 := by
  unfold tailWord_4157577
  simp only [CollatzResearch.WordTrace]
  refine ⟨151639290858816061466134985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101092860572544040977423323 151639290858816061466134985)
  ·
    refine ⟨113729468144112046099601239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151639290858816061466134985 113729468144112046099601239)
    ·
      refine ⟨170594202216168069149401859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113729468144112046099601239 170594202216168069149401859)
      ·
        refine ⟨255891303324252103724102789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170594202216168069149401859 255891303324252103724102789)
        ·
          refine ⟨47979619373297269448269273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255891303324252103724102789 47979619373297269448269273)
          ·
            refine ⟨35984714529972952086201955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47979619373297269448269273 35984714529972952086201955)
            ·
              refine ⟨53977071794959428129302933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35984714529972952086201955 53977071794959428129302933)
              ·
                refine ⟨2530175240388723193561075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53977071794959428129302933 2530175240388723193561075)
                ·
                  refine ⟨3795262860583084790341613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2530175240388723193561075 3795262860583084790341613)
                  ·
                    refine ⟨1423223572718656796378105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3795262860583084790341613 1423223572718656796378105)
                    ·
                      rfl

theorem cell22_4157577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 1, 3].length) (baseStart_4157577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157577 prefixEnd_4157577 := by exact prefixLift 4157577
  have htrace : WordTrace (prefixWord ++ tailWord_4157577) baseStart_4157577 baseEnd_4157577 := by
    simpa [prefixWord, tailWord_4157577, baseEnd_4157577] using wordTrace_append hprefix tailTrace_4157577
  have hstable : (prefixWord ++ tailWord_4157577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157577).length < 2 ^ (prefixWord ++ tailWord_4157577).sum := by decide
  have hdescent : baseEnd_4157577 < baseStart_4157577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157654 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_4157654 : Nat := 118140960795 + 4157654 * 2 ^ 59
def prefixEnd_4157654 : Nat := 4983230072969 + 3 ^ 40 * 4157654 * 2
def baseEnd_4157654 : Nat := 1423249931392254262202869

theorem tailTrace_4157654 : CollatzResearch.WordTrace tailWord_4157654 prefixEnd_4157654 1423249931392254262202869 := by
  unfold tailWord_4157654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9477631204971068976043001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101094732853024735744458677 9477631204971068976043001)
  ·
    refine ⟨7108223403728301732032251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9477631204971068976043001 7108223403728301732032251)
    ·
      refine ⟨10662335105592452598048377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7108223403728301732032251 10662335105592452598048377)
      ·
        refine ⟨7996751329194339448536283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10662335105592452598048377 7996751329194339448536283)
        ·
          refine ⟨11995126993791509172804425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7996751329194339448536283 11995126993791509172804425)
          ·
            refine ⟨8996345245343631879603319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11995126993791509172804425 8996345245343631879603319)
            ·
              refine ⟨13494517868015447819404979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8996345245343631879603319 13494517868015447819404979)
              ·
                refine ⟨20241776802023171729107469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13494517868015447819404979 20241776802023171729107469)
                ·
                  refine ⟨7590666300758689398415301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20241776802023171729107469 7590666300758689398415301)
                  ·
                    refine ⟨1423249931392254262202869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7590666300758689398415301 1423249931392254262202869)
                    ·
                      rfl

theorem cell22_4157654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_4157654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157654 prefixEnd_4157654 := by exact prefixLift 4157654
  have htrace : WordTrace (prefixWord ++ tailWord_4157654) baseStart_4157654 baseEnd_4157654 := by
    simpa [prefixWord, tailWord_4157654, baseEnd_4157654] using wordTrace_append hprefix tailTrace_4157654
  have hstable : (prefixWord ++ tailWord_4157654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157654).length < 2 ^ (prefixWord ++ tailWord_4157654).sum := by decide
  have hdescent : baseEnd_4157654 < baseStart_4157654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157682 : List Nat := [3, 2, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_4157682 : Nat := 118140960795 + 4157682 * 2 ^ 59
def prefixEnd_4157682 : Nat := 4983230072969 + 3 ^ 40 * 4157682 * 2
def baseEnd_4157682 : Nat := 1423259516364471522502783

theorem tailTrace_4157682 : CollatzResearch.WordTrace tailWord_4157682 prefixEnd_4157682 1423259516364471522502783 := by
  unfold tailWord_4157682
  simp only [CollatzResearch.WordTrace]
  refine ⟨37910780130858916099676825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101095413682290442932471533 37910780130858916099676825)
  ·
    refine ⟨28433085098144187074757619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37910780130858916099676825 28433085098144187074757619)
    ·
      refine ⟨42649627647216280612136429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28433085098144187074757619 42649627647216280612136429)
      ·
        refine ⟨15993610367706105229551161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42649627647216280612136429 15993610367706105229551161)
        ·
          refine ⟨11995207775779578922163371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15993610367706105229551161 11995207775779578922163371)
          ·
            refine ⟨17992811663669368383245057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11995207775779578922163371 17992811663669368383245057)
            ·
              refine ⟨13494608747752026287433793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17992811663669368383245057 13494608747752026287433793)
              ·
                refine ⟨10120956560814019715575345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13494608747752026287433793 10120956560814019715575345)
                ·
                  refine ⟨7590717420610514786681509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10120956560814019715575345 7590717420610514786681509)
                  ·
                    refine ⟨1423259516364471522502783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7590717420610514786681509 1423259516364471522502783)
                    ·
                      rfl

theorem cell22_4157682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_4157682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157682 prefixEnd_4157682 := by exact prefixLift 4157682
  have htrace : WordTrace (prefixWord ++ tailWord_4157682) baseStart_4157682 baseEnd_4157682 := by
    simpa [prefixWord, tailWord_4157682, baseEnd_4157682] using wordTrace_append hprefix tailTrace_4157682
  have hstable : (prefixWord ++ tailWord_4157682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157682).length < 2 ^ (prefixWord ++ tailWord_4157682).sum := by decide
  have hdescent : baseEnd_4157682 < baseStart_4157682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157710 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_4157710 : Nat := 118140960795 + 4157710 * 2 ^ 59
def prefixEnd_4157710 : Nat := 4983230072969 + 3 ^ 40 * 4157710 * 2
def baseEnd_4157710 : Nat := 1423269101336688782802697

theorem tailTrace_4157710 : CollatzResearch.WordTrace tailWord_4157710 prefixEnd_4157710 1423269101336688782802697 := by
  unfold tailWord_4157710
  simp only [CollatzResearch.WordTrace]
  refine ⟨18955517720916778147590823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101096094511556150120484389 18955517720916778147590823)
  ·
    refine ⟨28433276581375167221386235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18955517720916778147590823 28433276581375167221386235)
    ·
      refine ⟨42649914872062750832079353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28433276581375167221386235 42649914872062750832079353)
      ·
        refine ⟨31987436154047063124059515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42649914872062750832079353 31987436154047063124059515)
        ·
          refine ⟨47981154231070594686089273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31987436154047063124059515 47981154231070594686089273)
          ·
            refine ⟨35985865673302946014566955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47981154231070594686089273 35985865673302946014566955)
            ·
              refine ⟨53978798509954419021850433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35985865673302946014566955 53978798509954419021850433)
              ·
                refine ⟨40484098882465814266387825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53978798509954419021850433 40484098882465814266387825)
                ·
                  refine ⟨30363074161849360699790869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40484098882465814266387825 30363074161849360699790869)
                  ·
                    refine ⟨1423269101336688782802697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30363074161849360699790869 1423269101336688782802697)
                    ·
                      rfl

theorem cell22_4157710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_4157710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157710 prefixEnd_4157710 := by exact prefixLift 4157710
  have htrace : WordTrace (prefixWord ++ tailWord_4157710) baseStart_4157710 baseEnd_4157710 := by
    simpa [prefixWord, tailWord_4157710, baseEnd_4157710] using wordTrace_append hprefix tailTrace_4157710
  have hstable : (prefixWord ++ tailWord_4157710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157710).length < 2 ^ (prefixWord ++ tailWord_4157710).sum := by decide
  have hdescent : baseEnd_4157710 < baseStart_4157710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157729 : List Nat := [1, 2, 3, 2, 1, 1, 3, 5, 1, 3]
def baseStart_4157729 : Nat := 118140960795 + 4157729 * 2 ^ 59
def prefixEnd_4157729 : Nat := 4983230072969 + 3 ^ 40 * 4157729 * 2
def baseEnd_4157729 : Nat := 1423275605424979066577639

theorem tailTrace_4157729 : CollatzResearch.WordTrace tailWord_4157729 prefixEnd_4157729 1423275605424979066577639 := by
  unfold tailWord_4157729
  simp only [CollatzResearch.WordTrace]
  refine ⟨151644834754265391425668241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101096556502843594283778827 151644834754265391425668241)
  ·
    refine ⟨113733626065699043569251181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151644834754265391425668241 113733626065699043569251181)
    ·
      refine ⟨42650109774637141338469193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113733626065699043569251181 42650109774637141338469193)
      ·
        refine ⟨31987582330977856003851895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42650109774637141338469193 31987582330977856003851895)
        ·
          refine ⟨47981373496466784005777843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31987582330977856003851895 47981373496466784005777843)
          ·
            refine ⟨71972060244700176008666765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47981373496466784005777843 71972060244700176008666765)
            ·
              refine ⟨26989522591762566003250037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71972060244700176008666765 26989522591762566003250037)
              ·
                refine ⟨2530267742977740562804691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26989522591762566003250037 2530267742977740562804691)
                ·
                  refine ⟨3795401614466610844207037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2530267742977740562804691 3795401614466610844207037)
                  ·
                    refine ⟨1423275605424979066577639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3795401614466610844207037 1423275605424979066577639)
                    ·
                      rfl

theorem cell22_4157729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_4157729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157729 prefixEnd_4157729 := by exact prefixLift 4157729
  have htrace : WordTrace (prefixWord ++ tailWord_4157729) baseStart_4157729 baseEnd_4157729 := by
    simpa [prefixWord, tailWord_4157729, baseEnd_4157729] using wordTrace_append hprefix tailTrace_4157729
  have hstable : (prefixWord ++ tailWord_4157729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157729).length < 2 ^ (prefixWord ++ tailWord_4157729).sum := by decide
  have hdescent : baseEnd_4157729 < baseStart_4157729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157735 : List Nat := [1, 1, 8, 1, 1, 2, 1, 2, 2, 3]
def baseStart_4157735 : Nat := 118140960795 + 4157735 * 2 ^ 59
def prefixEnd_4157735 : Nat := 4983230072969 + 3 ^ 40 * 4157735 * 2
def baseEnd_4157735 : Nat := 1423277659347597050927621

theorem tailTrace_4157735 : CollatzResearch.WordTrace tailWord_4157735 prefixEnd_4157735 1423277659347597050927621 := by
  unfold tailWord_4157735
  simp only [CollatzResearch.WordTrace]
  refine ⟨151645053592243654450386659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101096702394829102966924439 151645053592243654450386659)
  ·
    refine ⟨227467580388365481675579989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151645053592243654450386659 227467580388365481675579989)
    ·
      refine ⟨2665635707676157988385703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 227467580388365481675579989 2665635707676157988385703)
      ·
        refine ⟨3998453561514236982578555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2665635707676157988385703 3998453561514236982578555)
        ·
          refine ⟨5997680342271355473867833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3998453561514236982578555 5997680342271355473867833)
          ·
            refine ⟨4498260256703516605400875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5997680342271355473867833 4498260256703516605400875)
            ·
              refine ⟨6747390385055274908101313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4498260256703516605400875 6747390385055274908101313)
              ·
                refine ⟨5060542788791456181075985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6747390385055274908101313 5060542788791456181075985)
                ·
                  refine ⟨3795407091593592135806989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5060542788791456181075985 3795407091593592135806989)
                  ·
                    refine ⟨1423277659347597050927621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3795407091593592135806989 1423277659347597050927621)
                    ·
                      rfl

theorem cell22_4157735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_4157735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157735 prefixEnd_4157735 := by exact prefixLift 4157735
  have htrace : WordTrace (prefixWord ++ tailWord_4157735) baseStart_4157735 baseEnd_4157735 := by
    simpa [prefixWord, tailWord_4157735, baseEnd_4157735] using wordTrace_append hprefix tailTrace_4157735
  have hstable : (prefixWord ++ tailWord_4157735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157735).length < 2 ^ (prefixWord ++ tailWord_4157735).sum := by decide
  have hdescent : baseEnd_4157735 < baseStart_4157735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157740 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 2, 5]
def baseStart_4157740 : Nat := 118140960795 + 4157740 * 2 ^ 59
def prefixEnd_4157740 : Nat := 4983230072969 + 3 ^ 40 * 4157740 * 2
def baseEnd_4157740 : Nat := 1423279370949778704552605

theorem tailTrace_4157740 : CollatzResearch.WordTrace tailWord_4157740 prefixEnd_4157740 1423279370949778704552605 := by
  unfold tailWord_4157740
  simp only [CollatzResearch.WordTrace]
  refine ⟨75822617978612770152159337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101096823971483693536212449 75822617978612770152159337)
  ·
    refine ⟨56866963483959577614119503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75822617978612770152159337 56866963483959577614119503)
    ·
      refine ⟨85300445225939366421179255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56866963483959577614119503 85300445225939366421179255)
      ·
        refine ⟨127950667838909049631768883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85300445225939366421179255 127950667838909049631768883)
        ·
          refine ⟨191926001758363574447653325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127950667838909049631768883 191926001758363574447653325)
          ·
            refine ⟨71972250659386340417869997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191926001758363574447653325 71972250659386340417869997)
            ·
              refine ⟨26989593997269877656701249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71972250659386340417869997 26989593997269877656701249)
              ·
                refine ⟨20242195497952408242525937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26989593997269877656701249 20242195497952408242525937)
                ·
                  refine ⟨15181646623464306181894453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20242195497952408242525937 15181646623464306181894453)
                  ·
                    refine ⟨1423279370949778704552605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15181646623464306181894453 1423279370949778704552605)
                    ·
                      rfl

theorem cell22_4157740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_4157740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157740 prefixEnd_4157740 := by exact prefixLift 4157740
  have htrace : WordTrace (prefixWord ++ tailWord_4157740) baseStart_4157740 baseEnd_4157740 := by
    simpa [prefixWord, tailWord_4157740, baseEnd_4157740] using wordTrace_append hprefix tailTrace_4157740
  have hstable : (prefixWord ++ tailWord_4157740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157740).length < 2 ^ (prefixWord ++ tailWord_4157740).sum := by decide
  have hdescent : baseEnd_4157740 < baseStart_4157740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157785 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 3, 5]
def baseStart_4157785 : Nat := 118140960795 + 4157785 * 2 ^ 59
def prefixEnd_4157785 : Nat := 4983230072969 + 3 ^ 40 * 4157785 * 2
def baseEnd_4157785 : Nat := 1423294775369413587177467

theorem tailTrace_4157785 : CollatzResearch.WordTrace tailWord_4157785 prefixEnd_4157785 1423294775369413587177467 := by
  unfold tailWord_4157785
  simp only [CollatzResearch.WordTrace]
  refine ⟨151646877242062512989706809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101097918161375008659804539 151646877242062512989706809)
  ·
    refine ⟨113735157931546884742280107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151646877242062512989706809 113735157931546884742280107)
    ·
      refine ⟨170602736897320327113420161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113735157931546884742280107 170602736897320327113420161)
      ·
        refine ⟨127952052672990245335065121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170602736897320327113420161 127952052672990245335065121)
        ·
          refine ⟨95964039504742684001298841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127952052672990245335065121 95964039504742684001298841)
          ·
            refine ⟨71973029628557013000974131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95964039504742684001298841 71973029628557013000974131)
            ·
              refine ⟨107959544442835519501461197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71973029628557013000974131 107959544442835519501461197)
              ·
                refine ⟨40484829166063319813047949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107959544442835519501461197 40484829166063319813047949)
                ·
                  refine ⟨15181810937273744929892981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40484829166063319813047949 15181810937273744929892981)
                  ·
                    refine ⟨1423294775369413587177467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15181810937273744929892981 1423294775369413587177467)
                    ·
                      rfl

theorem cell22_4157785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_4157785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157785 prefixEnd_4157785 := by exact prefixLift 4157785
  have htrace : WordTrace (prefixWord ++ tailWord_4157785) baseStart_4157785 baseEnd_4157785 := by
    simpa [prefixWord, tailWord_4157785, baseEnd_4157785] using wordTrace_append hprefix tailTrace_4157785
  have hstable : (prefixWord ++ tailWord_4157785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157785).length < 2 ^ (prefixWord ++ tailWord_4157785).sum := by decide
  have hdescent : baseEnd_4157785 < baseStart_4157785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157804 : List Nat := [2, 2, 1, 1, 6, 2, 1, 1, 6]
def baseStart_4157804 : Nat := 118140960795 + 4157804 * 2 ^ 59
def prefixEnd_4157804 : Nat := 4983230072969 + 3 ^ 40 * 4157804 * 2
def baseEnd_4157804 : Nat := 474433759819234623650803

theorem tailTrace_4157804 : CollatzResearch.WordTrace tailWord_4157804 prefixEnd_4157804 474433759819234623650803 := by
  unfold tailWord_4157804
  simp only [CollatzResearch.WordTrace]
  refine ⟨75823785114496839617324233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101098380152662452823098977 75823785114496839617324233)
  ·
    refine ⟨56867838835872629712993175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75823785114496839617324233 56867838835872629712993175)
    ·
      refine ⟨85301758253808944569489763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56867838835872629712993175 85301758253808944569489763)
      ·
        refine ⟨127952637380713416854234645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85301758253808944569489763 127952637380713416854234645)
        ·
          refine ⟨5997779877220941415042249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 127952637380713416854234645 5997779877220941415042249)
          ·
            refine ⟨4498334907915706061281687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5997779877220941415042249 4498334907915706061281687)
            ·
              refine ⟨6747502361873559091922531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4498334907915706061281687 6747502361873559091922531)
              ·
                refine ⟨10121253542810338637883797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6747502361873559091922531 10121253542810338637883797)
                ·
                  refine ⟨474433759819234623650803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10121253542810338637883797 474433759819234623650803)
                  ·
                    rfl

theorem cell22_4157804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_4157804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157804 prefixEnd_4157804 := by exact prefixLift 4157804
  have htrace : WordTrace (prefixWord ++ tailWord_4157804) baseStart_4157804 baseEnd_4157804 := by
    simpa [prefixWord, tailWord_4157804, baseEnd_4157804] using wordTrace_append hprefix tailTrace_4157804
  have hstable : (prefixWord ++ tailWord_4157804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157804).length < 2 ^ (prefixWord ++ tailWord_4157804).sum := by decide
  have hdescent : baseEnd_4157804 < baseStart_4157804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157819 : List Nat := [1, 1, 1, 1, 1, 8, 1, 3, 2, 3]
def baseStart_4157819 : Nat := 118140960795 + 4157819 * 2 ^ 59
def prefixEnd_4157819 : Nat := 4983230072969 + 3 ^ 40 * 4157819 * 2
def baseEnd_4157819 : Nat := 1423306414264248831827363

theorem tailTrace_4157819 : CollatzResearch.WordTrace tailWord_4157819 prefixEnd_4157819 1423306414264248831827363 := by
  unfold tailWord_4157819
  simp only [CollatzResearch.WordTrace]
  refine ⟨151648117323939336796444511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101098744882626224530963007 151648117323939336796444511)
  ·
    refine ⟨227472175985909005194666767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151648117323939336796444511 227472175985909005194666767)
    ·
      refine ⟨341208263978863507792000151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227472175985909005194666767 341208263978863507792000151)
      ·
        refine ⟨511812395968295261688000227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341208263978863507792000151 511812395968295261688000227)
        ·
          refine ⟨767718593952442892532000341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511812395968295261688000227 767718593952442892532000341)
          ·
            refine ⟨8996702272880190146859379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 767718593952442892532000341 8996702272880190146859379)
            ·
              refine ⟨13495053409320285220289069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8996702272880190146859379 13495053409320285220289069)
              ·
                refine ⟨5060645028495106957608401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13495053409320285220289069 5060645028495106957608401)
                ·
                  refine ⟨3795483771371330218206301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5060645028495106957608401 3795483771371330218206301)
                  ·
                    refine ⟨1423306414264248831827363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3795483771371330218206301 1423306414264248831827363)
                    ·
                      rfl

theorem cell22_4157819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 3].length) (baseStart_4157819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157819 prefixEnd_4157819 := by exact prefixLift 4157819
  have htrace : WordTrace (prefixWord ++ tailWord_4157819) baseStart_4157819 baseEnd_4157819 := by
    simpa [prefixWord, tailWord_4157819, baseEnd_4157819] using wordTrace_append hprefix tailTrace_4157819
  have hstable : (prefixWord ++ tailWord_4157819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157819).length < 2 ^ (prefixWord ++ tailWord_4157819).sum := by decide
  have hdescent : baseEnd_4157819 < baseStart_4157819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157952 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 8, 4]
def baseStart_4157952 : Nat := 118140960795 + 4157952 * 2 ^ 59
def prefixEnd_4157952 : Nat := 4983230072969 + 3 ^ 40 * 4157952 * 2
def baseEnd_4157952 : Nat := 1423351942882280818251955

theorem tailTrace_4157952 : CollatzResearch.WordTrace tailWord_4157952 prefixEnd_4157952 1423351942882280818251955 := by
  unfold tailWord_4157952
  simp only [CollatzResearch.WordTrace]
  refine ⟨75826484116228750255518055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101101978821638333674024073 75826484116228750255518055)
  ·
    refine ⟨113739726174343125383277083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75826484116228750255518055 113739726174343125383277083)
    ·
      refine ⟨170609589261514688074915625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113739726174343125383277083 170609589261514688074915625)
      ·
        refine ⟨127957191946136016056186719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170609589261514688074915625 127957191946136016056186719)
        ·
          refine ⟨191935787919204024084280079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127957191946136016056186719 191935787919204024084280079)
          ·
            refine ⟨287903681878806036126420119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191935787919204024084280079 287903681878806036126420119)
            ·
              refine ⟨431855522818209054189630179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287903681878806036126420119 431855522818209054189630179)
              ·
                refine ⟨647783284227313581284445269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431855522818209054189630179 647783284227313581284445269)
                ·
                  refine ⟨7591210362038831030677093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 647783284227313581284445269 7591210362038831030677093)
                  ·
                    refine ⟨1423351942882280818251955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7591210362038831030677093 1423351942882280818251955)
                    ·
                      rfl

theorem cell22_4157952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_4157952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4157952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4157952 prefixEnd_4157952 := by exact prefixLift 4157952
  have htrace : WordTrace (prefixWord ++ tailWord_4157952) baseStart_4157952 baseEnd_4157952 := by
    simpa [prefixWord, tailWord_4157952, baseEnd_4157952] using wordTrace_append hprefix tailTrace_4157952
  have hstable : (prefixWord ++ tailWord_4157952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157952).length < 2 ^ (prefixWord ++ tailWord_4157952).sum := by decide
  have hdescent : baseEnd_4157952 < baseStart_4157952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158033 : List Nat := [1, 2, 2, 1, 3, 4, 1, 4, 1, 3]
def baseStart_4158033 : Nat := 118140960795 + 4158033 * 2 ^ 59
def prefixEnd_4158033 : Nat := 4983230072969 + 3 ^ 40 * 4158033 * 2
def baseEnd_4158033 : Nat := 1423379670837623606976707

theorem tailTrace_4158033 : CollatzResearch.WordTrace tailWord_4158033 prefixEnd_4158033 1423379670837623606976707 := by
  unfold tailWord_4158033
  simp only [CollatzResearch.WordTrace]
  refine ⟨151655922545164051344734753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101103948363442700896489835 151655922545164051344734753)
  ·
    refine ⟨113741941908873038508551065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151655922545164051344734753 113741941908873038508551065)
    ·
      refine ⟨85306456431654778881413299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113741941908873038508551065 85306456431654778881413299)
      ·
        refine ⟨127959684647482168322119949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85306456431654778881413299 127959684647482168322119949)
        ·
          refine ⟨47984881742805813120794981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127959684647482168322119949 47984881742805813120794981)
          ·
            refine ⟨8997165326776089960149059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47984881742805813120794981 8997165326776089960149059)
            ·
              refine ⟨13495747990164134940223589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8997165326776089960149059 13495747990164134940223589)
              ·
                refine ⟨2530452748155775301291923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13495747990164134940223589 2530452748155775301291923)
                ·
                  refine ⟨3795679122233662951937885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2530452748155775301291923 3795679122233662951937885)
                  ·
                    refine ⟨1423379670837623606976707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3795679122233662951937885 1423379670837623606976707)
                    ·
                      rfl

theorem cell22_4158033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 1, 3].length) (baseStart_4158033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158033 prefixEnd_4158033 := by exact prefixLift 4158033
  have htrace : WordTrace (prefixWord ++ tailWord_4158033) baseStart_4158033 baseEnd_4158033 := by
    simpa [prefixWord, tailWord_4158033, baseEnd_4158033] using wordTrace_append hprefix tailTrace_4158033
  have hstable : (prefixWord ++ tailWord_4158033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158033).length < 2 ^ (prefixWord ++ tailWord_4158033).sum := by decide
  have hdescent : baseEnd_4158033 < baseStart_4158033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158050 : List Nat := [3, 3, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_4158050 : Nat := 118140960795 + 4158050 * 2 ^ 59
def prefixEnd_4158050 : Nat := 4983230072969 + 3 ^ 40 * 4158050 * 2
def baseEnd_4158050 : Nat := 1423385490285041229301655

theorem tailTrace_4158050 : CollatzResearch.WordTrace tailWord_4158050 prefixEnd_4158050 1423385490285041229301655 := by
  unfold tailWord_4158050
  simp only [CollatzResearch.WordTrace]
  refine ⟨37914135646525615812025901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101104361724068308832069069 37914135646525615812025901)
  ·
    refine ⟨14217800867447105929509713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37914135646525615812025901 14217800867447105929509713)
    ·
      refine ⟨10663350650585329447132285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14217800867447105929509713 10663350650585329447132285)
      ·
        refine ⟨3998756493969498542674607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10663350650585329447132285 3998756493969498542674607)
        ·
          refine ⟨5998134740954247814011911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3998756493969498542674607 5998134740954247814011911)
          ·
            refine ⟨8997202111431371721017867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5998134740954247814011911 8997202111431371721017867)
            ·
              refine ⟨13495803167147057581526801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8997202111431371721017867 13495803167147057581526801)
              ·
                refine ⟨10121852375360293186145101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13495803167147057581526801 10121852375360293186145101)
                ·
                  refine ⟨3795694640760109944804413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10121852375360293186145101 3795694640760109944804413)
                  ·
                    refine ⟨1423385490285041229301655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3795694640760109944804413 1423385490285041229301655)
                    ·
                      rfl

theorem cell22_4158050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_4158050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158050 prefixEnd_4158050 := by exact prefixLift 4158050
  have htrace : WordTrace (prefixWord ++ tailWord_4158050) baseStart_4158050 baseEnd_4158050 := by
    simpa [prefixWord, tailWord_4158050, baseEnd_4158050] using wordTrace_append hprefix tailTrace_4158050
  have hstable : (prefixWord ++ tailWord_4158050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158050).length < 2 ^ (prefixWord ++ tailWord_4158050).sum := by decide
  have hdescent : baseEnd_4158050 < baseStart_4158050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158104 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 3, 6]
def baseStart_4158104 : Nat := 118140960795 + 4158104 * 2 ^ 59
def prefixEnd_4158104 : Nat := 4983230072969 + 3 ^ 40 * 4158104 * 2
def baseEnd_4158104 : Nat := 1423403975588603088451489

theorem tailTrace_4158104 : CollatzResearch.WordTrace tailWord_4158104 prefixEnd_4158104 1423403975588603088451489 := by
  unfold tailWord_4158104
  simp only [CollatzResearch.WordTrace]
  refine ⟨75829256063953415235284683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101105674751937886980379577 75829256063953415235284683)
  ·
    refine ⟨113743884095930122852927025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75829256063953415235284683 113743884095930122852927025)
    ·
      refine ⟨85307913071947592139695269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113743884095930122852927025 85307913071947592139695269)
      ·
        refine ⟨15995233700990173526192863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85307913071947592139695269 15995233700990173526192863)
        ·
          refine ⟨23992850551485260289289295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15995233700990173526192863 23992850551485260289289295)
          ·
            refine ⟨35989275827227890433933943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23992850551485260289289295 35989275827227890433933943)
            ·
              refine ⟨53983913740841835650900915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35989275827227890433933943 53983913740841835650900915)
              ·
                refine ⟨80975870611262753476351373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53983913740841835650900915 80975870611262753476351373)
                ·
                  refine ⟨30365951479223532553631765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80975870611262753476351373 30365951479223532553631765)
                  ·
                    refine ⟨1423403975588603088451489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30365951479223532553631765 1423403975588603088451489)
                    ·
                      rfl

theorem cell22_4158104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_4158104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158104 prefixEnd_4158104 := by exact prefixLift 4158104
  have htrace : WordTrace (prefixWord ++ tailWord_4158104) baseStart_4158104 baseEnd_4158104 := by
    simpa [prefixWord, tailWord_4158104, baseEnd_4158104] using wordTrace_append hprefix tailTrace_4158104
  have hstable : (prefixWord ++ tailWord_4158104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158104).length < 2 ^ (prefixWord ++ tailWord_4158104).sum := by decide
  have hdescent : baseEnd_4158104 < baseStart_4158104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158125 : List Nat := [1, 5, 2, 1, 1, 4, 1, 3, 4]
def baseStart_4158125 : Nat := 118140960795 + 4158125 * 2 ^ 59
def prefixEnd_4158125 : Nat := 4983230072969 + 3 ^ 40 * 4158125 * 2
def baseEnd_4158125 : Nat := 474470388105922011225475

theorem tailTrace_4158125 : CollatzResearch.WordTrace tailWord_4158125 prefixEnd_4158125 474470388105922011225475 := by
  unfold tailWord_4158125
  simp only [CollatzResearch.WordTrace]
  refine ⟨151659278060830751057083829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101106185373887167371389219 151659278060830751057083829)
  ·
    refine ⟨14218057318202882911601609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151659278060830751057083829 14218057318202882911601609)
    ·
      refine ⟨10663542988652162183701207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14218057318202882911601609 10663542988652162183701207)
      ·
        refine ⟨15995314482978243275551811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10663542988652162183701207 15995314482978243275551811)
        ·
          refine ⟨23992971724467364913327717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15995314482978243275551811 23992971724467364913327717)
          ·
            refine ⟨4498682198337630921248947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23992971724467364913327717 4498682198337630921248947)
            ·
              refine ⟨6748023297506446381873421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4498682198337630921248947 6748023297506446381873421)
              ·
                refine ⟨2530508736564917393202533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6748023297506446381873421 2530508736564917393202533)
                ·
                  refine ⟨474470388105922011225475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2530508736564917393202533 474470388105922011225475)
                  ·
                    rfl

theorem cell22_4158125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_4158125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158125 prefixEnd_4158125 := by exact prefixLift 4158125
  have htrace : WordTrace (prefixWord ++ tailWord_4158125) baseStart_4158125 baseEnd_4158125 := by
    simpa [prefixWord, tailWord_4158125, baseEnd_4158125] using wordTrace_append hprefix tailTrace_4158125
  have hstable : (prefixWord ++ tailWord_4158125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158125).length < 2 ^ (prefixWord ++ tailWord_4158125).sum := by decide
  have hdescent : baseEnd_4158125 < baseStart_4158125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158151 : List Nat := [1, 1, 4, 1, 1, 1, 2, 5, 3, 3]
def baseStart_4158151 : Nat := 118140960795 + 4158151 * 2 ^ 59
def prefixEnd_4158151 : Nat := 4983230072969 + 3 ^ 40 * 4158151 * 2
def baseEnd_4158151 : Nat := 1423420064649110632526345

theorem tailTrace_4158151 : CollatzResearch.WordTrace tailWord_4158151 prefixEnd_4158151 1423420064649110632526345 := by
  unfold tailWord_4158151
  simp only [CollatzResearch.WordTrace]
  refine ⟨151660226358736557497530307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101106817572491038331686871 151660226358736557497530307)
  ·
    refine ⟨227490339538104836246295461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151660226358736557497530307 227490339538104836246295461)
    ·
      refine ⟨42654438663394656796180399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227490339538104836246295461 42654438663394656796180399)
      ·
        refine ⟨63981657995091985194270599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42654438663394656796180399 63981657995091985194270599)
        ·
          refine ⟨95972486992637977791405899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63981657995091985194270599 95972486992637977791405899)
          ·
            refine ⟨143958730488956966687108849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95972486992637977791405899 143958730488956966687108849)
            ·
              refine ⟨107969047866717725015331637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143958730488956966687108849 107969047866717725015331637)
              ·
                refine ⟨10122098237504786720187341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107969047866717725015331637 10122098237504786720187341)
                ·
                  refine ⟨3795786839064295020070253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10122098237504786720187341 3795786839064295020070253)
                  ·
                    refine ⟨1423420064649110632526345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3795786839064295020070253 1423420064649110632526345)
                    ·
                      rfl

theorem cell22_4158151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_4158151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158151 prefixEnd_4158151 := by exact prefixLift 4158151
  have htrace : WordTrace (prefixWord ++ tailWord_4158151) baseStart_4158151 baseEnd_4158151 := by
    simpa [prefixWord, tailWord_4158151, baseEnd_4158151] using wordTrace_append hprefix tailTrace_4158151
  have hstable : (prefixWord ++ tailWord_4158151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158151).length < 2 ^ (prefixWord ++ tailWord_4158151).sum := by decide
  have hdescent : baseEnd_4158151 < baseStart_4158151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158157 : List Nat := [1, 6, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_4158157 : Nat := 118140960795 + 4158157 * 2 ^ 59
def prefixEnd_4158157 : Nat := 4983230072969 + 3 ^ 40 * 4158157 * 2
def baseEnd_4158157 : Nat := 1423422118571728616876327

theorem tailTrace_4158157 : CollatzResearch.WordTrace tailWord_4158157 prefixEnd_4158157 1423422118571728616876327 := by
  unfold tailWord_4158157
  simp only [CollatzResearch.WordTrace]
  refine ⟨151660445196714820522248725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101106963464476547014832483 151660445196714820522248725)
  ·
    refine ⟨7109083368596007211980409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151660445196714820522248725 7109083368596007211980409)
    ·
      refine ⟨5331812526447005408985307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7109083368596007211980409 5331812526447005408985307)
      ·
        refine ⟨7997718789670508113477961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5331812526447005408985307 7997718789670508113477961)
        ·
          refine ⟨5998289092252881085108471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7997718789670508113477961 5998289092252881085108471)
          ·
            refine ⟨8997433638379321627662707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5998289092252881085108471 8997433638379321627662707)
            ·
              refine ⟨13496150457568982441494061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8997433638379321627662707 13496150457568982441494061)
              ·
                refine ⟨5061056421588368415560273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13496150457568982441494061 5061056421588368415560273)
                ·
                  refine ⟨3795792316191276311670205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5061056421588368415560273 3795792316191276311670205)
                  ·
                    refine ⟨1423422118571728616876327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3795792316191276311670205 1423422118571728616876327)
                    ·
                      rfl

theorem cell22_4158157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_4158157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158157 prefixEnd_4158157 := by exact prefixLift 4158157
  have htrace : WordTrace (prefixWord ++ tailWord_4158157) baseStart_4158157 baseEnd_4158157 := by
    simpa [prefixWord, tailWord_4158157, baseEnd_4158157] using wordTrace_append hprefix tailTrace_4158157
  have hstable : (prefixWord ++ tailWord_4158157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158157).length < 2 ^ (prefixWord ++ tailWord_4158157).sum := by decide
  have hdescent : baseEnd_4158157 < baseStart_4158157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158198 : List Nat := [5, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_4158198 : Nat := 118140960795 + 4158198 * 2 ^ 59
def prefixEnd_4158198 : Nat := 4983230072969 + 3 ^ 40 * 4158198 * 2
def baseEnd_4158198 : Nat := 474478717903206058867067

theorem tailTrace_4158198 : CollatzResearch.WordTrace tailWord_4158198 prefixEnd_4158198 474478717903206058867067 := by
  unfold tailWord_4158198
  simp only [CollatzResearch.WordTrace]
  refine ⟨9478871286847892782780703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101107960393044189682994165 9478871286847892782780703)
  ·
    refine ⟨14218306930271839174171055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9478871286847892782780703 14218306930271839174171055)
    ·
      refine ⟨21327460395407758761256583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14218306930271839174171055 21327460395407758761256583)
      ·
        refine ⟨31991190593111638141884875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21327460395407758761256583 31991190593111638141884875)
        ·
          refine ⟨47986785889667457212827313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31991190593111638141884875 47986785889667457212827313)
          ·
            refine ⟨35990089417250592909620485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47986785889667457212827313 35990089417250592909620485)
            ·
              refine ⟨6748141765734486170553841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35990089417250592909620485 6748141765734486170553841)
              ·
                refine ⟨5061106324300864627915381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6748141765734486170553841 5061106324300864627915381)
                ·
                  refine ⟨474478717903206058867067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5061106324300864627915381 474478717903206058867067)
                  ·
                    rfl

theorem cell22_4158198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_4158198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158198 prefixEnd_4158198 := by exact prefixLift 4158198
  have htrace : WordTrace (prefixWord ++ tailWord_4158198) baseStart_4158198 baseEnd_4158198 := by
    simpa [prefixWord, tailWord_4158198, baseEnd_4158198] using wordTrace_append hprefix tailTrace_4158198
  have hstable : (prefixWord ++ tailWord_4158198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158198).length < 2 ^ (prefixWord ++ tailWord_4158198).sum := by decide
  have hdescent : baseEnd_4158198 < baseStart_4158198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158241 : List Nat := [1, 2, 3, 2, 1, 2, 1, 4, 1, 5]
def baseStart_4158241 : Nat := 118140960795 + 4158241 * 2 ^ 59
def prefixEnd_4158241 : Nat := 4983230072969 + 3 ^ 40 * 4158241 * 2
def baseEnd_4158241 : Nat := 1423450873488380397776069

theorem tailTrace_4158241 : CollatzResearch.WordTrace tailWord_4158241 prefixEnd_4158241 1423450873488380397776069 := by
  unfold tailWord_4158241
  simp only [CollatzResearch.WordTrace]
  refine ⟨151663508928410502868306577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101109005952273668578871051 151663508928410502868306577)
  ·
    refine ⟨113747631696307877151229933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151663508928410502868306577 113747631696307877151229933)
    ·
      refine ⟨42655361886115453931711225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113747631696307877151229933 42655361886115453931711225)
      ·
        refine ⟨31991521414586590448783419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42655361886115453931711225 31991521414586590448783419)
        ·
          refine ⟨47987282121879885673175129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31991521414586590448783419 47987282121879885673175129)
          ·
            refine ⟨35990461591409914254881347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47987282121879885673175129 35990461591409914254881347)
            ·
              refine ⟨53985692387114871382322021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35990461591409914254881347 53985692387114871382322021)
              ·
                refine ⟨10122317322584038384185379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53985692387114871382322021 10122317322584038384185379)
                ·
                  refine ⟨15183475983876057576278069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10122317322584038384185379 15183475983876057576278069)
                  ·
                    refine ⟨1423450873488380397776069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15183475983876057576278069 1423450873488380397776069)
                    ·
                      rfl

theorem cell22_4158241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_4158241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158241 prefixEnd_4158241 := by exact prefixLift 4158241
  have htrace : WordTrace (prefixWord ++ tailWord_4158241) baseStart_4158241 baseEnd_4158241 := by
    simpa [prefixWord, tailWord_4158241, baseEnd_4158241] using wordTrace_append hprefix tailTrace_4158241
  have hstable : (prefixWord ++ tailWord_4158241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158241).length < 2 ^ (prefixWord ++ tailWord_4158241).sum := by decide
  have hdescent : baseEnd_4158241 < baseStart_4158241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158256 : List Nat := [2, 1, 1, 1, 2, 2, 1, 6, 2, 4]
def baseStart_4158256 : Nat := 118140960795 + 4158256 * 2 ^ 59
def prefixEnd_4158256 : Nat := 4983230072969 + 3 ^ 40 * 4158256 * 2
def baseEnd_4158256 : Nat := 1423456008294925358651023

theorem tailTrace_4158256 : CollatzResearch.WordTrace tailWord_4158256 prefixEnd_4158256 1423456008294925358651023 := by
  unfold tailWord_4158256
  simp only [CollatzResearch.WordTrace]
  refine ⟨75832028011678080215051311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101109370682237440286735081 75832028011678080215051311)
  ·
    refine ⟨113748042017517120322576967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75832028011678080215051311 113748042017517120322576967)
    ·
      refine ⟨170622063026275680483865451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113748042017517120322576967 170622063026275680483865451)
      ·
        refine ⟨255933094539413520725798177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170622063026275680483865451 255933094539413520725798177)
        ·
          refine ⟨191949820904560140544348633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255933094539413520725798177 191949820904560140544348633)
          ·
            refine ⟨143962365678420105408261475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191949820904560140544348633 143962365678420105408261475)
            ·
              refine ⟨215943548517630158112392213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143962365678420105408261475 215943548517630158112392213)
              ·
                refine ⟨10122353836763913661518385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 215943548517630158112392213 10122353836763913661518385)
                ·
                  refine ⟨7591765377572935246138789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10122353836763913661518385 7591765377572935246138789)
                  ·
                    refine ⟨1423456008294925358651023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7591765377572935246138789 1423456008294925358651023)
                    ·
                      rfl

theorem cell22_4158256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_4158256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158256 prefixEnd_4158256 := by exact prefixLift 4158256
  have htrace : WordTrace (prefixWord ++ tailWord_4158256) baseStart_4158256 baseEnd_4158256 := by
    simpa [prefixWord, tailWord_4158256, baseEnd_4158256] using wordTrace_append hprefix tailTrace_4158256
  have hstable : (prefixWord ++ tailWord_4158256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158256).length < 2 ^ (prefixWord ++ tailWord_4158256).sum := by decide
  have hdescent : baseEnd_4158256 < baseStart_4158256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158258 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 4, 3]
def baseStart_4158258 : Nat := 118140960795 + 4158258 * 2 ^ 59
def prefixEnd_4158258 : Nat := 4983230072969 + 3 ^ 40 * 4158258 * 2
def baseEnd_4158258 : Nat := 1423456692935798020101017

theorem tailTrace_4158258 : CollatzResearch.WordTrace tailWord_4158258 prefixEnd_4158258 1423456692935798020101017 := by
  unfold tailWord_4158258
  simp only [CollatzResearch.WordTrace]
  refine ⟨37916032242337228692918857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101109419312899276514450285 37916032242337228692918857)
  ·
    refine ⟨28437024181752921519689143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37916032242337228692918857 28437024181752921519689143)
    ·
      refine ⟨42655536272629382279533715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28437024181752921519689143 42655536272629382279533715)
      ·
        refine ⟨63983304408944073419300573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42655536272629382279533715 63983304408944073419300573)
        ·
          refine ⟨23993739153354027532237715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63983304408944073419300573 23993739153354027532237715)
          ·
            refine ⟨35990608730031041298356573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23993739153354027532237715 35990608730031041298356573)
            ·
              refine ⟨13496478273761640486883715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35990608730031041298356573 13496478273761640486883715)
              ·
                refine ⟨20244717410642460730325573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13496478273761640486883715 20244717410642460730325573)
                ·
                  refine ⟨3795884514495461386936045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20244717410642460730325573 3795884514495461386936045)
                  ·
                    refine ⟨1423456692935798020101017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3795884514495461386936045 1423456692935798020101017)
                    ·
                      rfl

theorem cell22_4158258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_4158258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158258 prefixEnd_4158258 := by exact prefixLift 4158258
  have htrace : WordTrace (prefixWord ++ tailWord_4158258) baseStart_4158258 baseEnd_4158258 := by
    simpa [prefixWord, tailWord_4158258, baseEnd_4158258] using wordTrace_append hprefix tailTrace_4158258
  have hstable : (prefixWord ++ tailWord_4158258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158258).length < 2 ^ (prefixWord ++ tailWord_4158258).sum := by decide
  have hdescent : baseEnd_4158258 < baseStart_4158258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158260 : List Nat := [2, 5, 1, 1, 3, 1, 2, 1, 6]
def baseStart_4158260 : Nat := 118140960795 + 4158260 * 2 ^ 59
def prefixEnd_4158260 : Nat := 4983230072969 + 3 ^ 40 * 4158260 * 2
def baseEnd_4158260 : Nat := 474485792525556893850337

theorem tailTrace_4158260 : CollatzResearch.WordTrace tailWord_4158260 prefixEnd_4158260 474485792525556893850337 := by
  unfold tailWord_4158260
  simp only [CollatzResearch.WordTrace]
  refine ⟨75832100957670834556624117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101109467943561112742165489 75832100957670834556624117)
  ·
    refine ⟨7109259464781640739683511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75832100957670834556624117 7109259464781640739683511)
    ·
      refine ⟨10663889197172461109525267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7109259464781640739683511 10663889197172461109525267)
      ·
        refine ⟨15995833795758691664287901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10663889197172461109525267 15995833795758691664287901)
        ·
          refine ⟨5998437673409509374107963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15995833795758691664287901 5998437673409509374107963)
          ·
            refine ⟨8997656510114264061161945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5998437673409509374107963 8997656510114264061161945)
            ·
              refine ⟨6748242382585698045871459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8997656510114264061161945 6748242382585698045871459)
              ·
                refine ⟨10122363573878547068807189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6748242382585698045871459 10122363573878547068807189)
                ·
                  refine ⟨474485792525556893850337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10122363573878547068807189 474485792525556893850337)
                  ·
                    rfl

theorem cell22_4158260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_4158260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158260 prefixEnd_4158260 := by exact prefixLift 4158260
  have htrace : WordTrace (prefixWord ++ tailWord_4158260) baseStart_4158260 baseEnd_4158260 := by
    simpa [prefixWord, tailWord_4158260, baseEnd_4158260] using wordTrace_append hprefix tailTrace_4158260
  have hstable : (prefixWord ++ tailWord_4158260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158260).length < 2 ^ (prefixWord ++ tailWord_4158260).sum := by decide
  have hdescent : baseEnd_4158260 < baseStart_4158260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158275 : List Nat := [1, 1, 1, 3, 1, 4, 5, 1, 2, 3]
def baseStart_4158275 : Nat := 118140960795 + 4158275 * 2 ^ 59
def prefixEnd_4158275 : Nat := 4983230072969 + 3 ^ 40 * 4158275 * 2
def baseEnd_4158275 : Nat := 1423462512383215642425965

theorem tailTrace_4158275 : CollatzResearch.WordTrace tailWord_4158275 prefixEnd_4158275 1423462512383215642425965 := by
  unfold tailWord_4158275
  simp only [CollatzResearch.WordTrace]
  refine ⟨151664749010287326675044279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101109832673524884450029519 151664749010287326675044279)
  ·
    refine ⟨227497123515430990012566419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151664749010287326675044279 227497123515430990012566419)
    ·
      refine ⟨341245685273146485018849629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227497123515430990012566419 341245685273146485018849629)
      ·
        refine ⟨127967131977429931882068611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341245685273146485018849629 127967131977429931882068611)
        ·
          refine ⟨191950697966144897823102917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127967131977429931882068611 191950697966144897823102917)
          ·
            refine ⟨35990755868652168341831797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191950697966144897823102917 35990755868652168341831797)
            ·
              refine ⟨3374133362686140782046731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35990755868652168341831797 3374133362686140782046731)
              ·
                refine ⟨5061200044029211173070097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3374133362686140782046731 5061200044029211173070097)
                ·
                  refine ⟨3795900033021908379802573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5061200044029211173070097 3795900033021908379802573)
                  ·
                    refine ⟨1423462512383215642425965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3795900033021908379802573 1423462512383215642425965)
                    ·
                      rfl

theorem cell22_4158275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 2, 3].length) (baseStart_4158275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158275 prefixEnd_4158275 := by exact prefixLift 4158275
  have htrace : WordTrace (prefixWord ++ tailWord_4158275) baseStart_4158275 baseEnd_4158275 := by
    simpa [prefixWord, tailWord_4158275, baseEnd_4158275] using wordTrace_append hprefix tailTrace_4158275
  have hstable : (prefixWord ++ tailWord_4158275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158275).length < 2 ^ (prefixWord ++ tailWord_4158275).sum := by decide
  have hdescent : baseEnd_4158275 < baseStart_4158275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158316 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 7]
def baseStart_4158316 : Nat := 118140960795 + 4158316 * 2 ^ 59
def prefixEnd_4158316 : Nat := 4983230072969 + 3 ^ 40 * 4158316 * 2
def baseEnd_4158316 : Nat := 474492182507035067383613

theorem tailTrace_4158316 : CollatzResearch.WordTrace tailWord_4158316 prefixEnd_4158316 474492182507035067383613 := by
  unfold tailWord_4158316
  simp only [CollatzResearch.WordTrace]
  refine ⟨75833122201569395338643401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101110829602092527118191201 75833122201569395338643401)
  ·
    refine ⟨56874841651177046503982551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75833122201569395338643401 56874841651177046503982551)
    ·
      refine ⟨85312262476765569755973827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56874841651177046503982551 85312262476765569755973827)
      ·
        refine ⟨127968393715148354633960741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85312262476765569755973827 127968393715148354633960741)
        ·
          refine ⟨23994073821590316493867639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127968393715148354633960741 23994073821590316493867639)
          ·
            refine ⟨35991110732385474740801459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23994073821590316493867639 35991110732385474740801459)
            ·
              refine ⟨53986666098578212111202189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35991110732385474740801459 53986666098578212111202189)
              ·
                refine ⟨20244999786966829541700821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53986666098578212111202189 20244999786966829541700821)
                ·
                  refine ⟨474492182507035067383613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20244999786966829541700821 474492182507035067383613)
                  ·
                    rfl

theorem cell22_4158316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_4158316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158316 prefixEnd_4158316 := by exact prefixLift 4158316
  have htrace : WordTrace (prefixWord ++ tailWord_4158316) baseStart_4158316 baseEnd_4158316 := by
    simpa [prefixWord, tailWord_4158316, baseEnd_4158316] using wordTrace_append hprefix tailTrace_4158316
  have hstable : (prefixWord ++ tailWord_4158316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158316).length < 2 ^ (prefixWord ++ tailWord_4158316).sum := by decide
  have hdescent : baseEnd_4158316 < baseStart_4158316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158320 : List Nat := [2, 1, 1, 1, 4, 1, 2, 6, 1, 3]
def baseStart_4158320 : Nat := 118140960795 + 4158320 * 2 ^ 59
def prefixEnd_4158320 : Nat := 4983230072969 + 3 ^ 40 * 4158320 * 2
def baseEnd_4158320 : Nat := 1423477916802850525050827

theorem tailTrace_4158320 : CollatzResearch.WordTrace tailWord_4158320 prefixEnd_4158320 1423477916802850525050827 := by
  unfold tailWord_4158320
  simp only [CollatzResearch.WordTrace]
  refine ⟨75833195147562149680216207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101110926863416199573621609 75833195147562149680216207)
  ·
    refine ⟨113749792721343224520324311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75833195147562149680216207 113749792721343224520324311)
    ·
      refine ⟨170624689082014836780486467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113749792721343224520324311 170624689082014836780486467)
      ·
        refine ⟨255937033623022255170729701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170624689082014836780486467 255937033623022255170729701)
        ·
          refine ⟨47988193804316672844511819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255937033623022255170729701 47988193804316672844511819)
          ·
            refine ⟨71982290706475009266767729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47988193804316672844511819 71982290706475009266767729)
            ·
              refine ⟨53986718029856256950075797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71982290706475009266767729 53986718029856256950075797)
              ·
                refine ⟨2530627407649512044534803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53986718029856256950075797 2530627407649512044534803)
                ·
                  refine ⟨3795941111474268066802205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2530627407649512044534803 3795941111474268066802205)
                  ·
                    refine ⟨1423477916802850525050827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3795941111474268066802205 1423477916802850525050827)
                    ·
                      rfl

theorem cell22_4158320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 1, 3].length) (baseStart_4158320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158320 prefixEnd_4158320 := by exact prefixLift 4158320
  have htrace : WordTrace (prefixWord ++ tailWord_4158320) baseStart_4158320 baseEnd_4158320 := by
    simpa [prefixWord, tailWord_4158320, baseEnd_4158320] using wordTrace_append hprefix tailTrace_4158320
  have hstable : (prefixWord ++ tailWord_4158320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158320).length < 2 ^ (prefixWord ++ tailWord_4158320).sum := by decide
  have hdescent : baseEnd_4158320 < baseStart_4158320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158331 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 2, 5]
def baseStart_4158331 : Nat := 118140960795 + 4158331 * 2 ^ 59
def prefixEnd_4158331 : Nat := 4983230072969 + 3 ^ 40 * 4158331 * 2
def baseEnd_4158331 : Nat := 1423481682327650163025793

theorem tailTrace_4158331 : CollatzResearch.WordTrace tailWord_4158331 prefixEnd_4158331 1423481682327650163025793 := by
  unfold tailWord_4158331
  simp only [CollatzResearch.WordTrace]
  refine ⟨151666791498084448239082847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101111194332056298826055231 151666791498084448239082847)
  ·
    refine ⟨227500187247126672358624271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151666791498084448239082847 227500187247126672358624271)
    ·
      refine ⟨341250280870690008537936407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227500187247126672358624271 341250280870690008537936407)
      ·
        refine ⟨511875421306035012806904611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341250280870690008537936407 511875421306035012806904611)
        ·
          refine ⟨767813131959052519210356917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511875421306035012806904611 767813131959052519210356917)
          ·
            refine ⟨71982481121161173675970961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 767813131959052519210356917 71982481121161173675970961)
            ·
              refine ⟨53986860840870880256978221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71982481121161173675970961 53986860840870880256978221)
              ·
                refine ⟨20245072815326580096366833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53986860840870880256978221 20245072815326580096366833)
                ·
                  refine ⟨15183804611494935072275125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20245072815326580096366833 15183804611494935072275125)
                  ·
                    refine ⟨1423481682327650163025793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15183804611494935072275125 1423481682327650163025793)
                    ·
                      rfl

theorem cell22_4158331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 5].length) (baseStart_4158331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158331 prefixEnd_4158331 := by exact prefixLift 4158331
  have htrace : WordTrace (prefixWord ++ tailWord_4158331) baseStart_4158331 baseEnd_4158331 := by
    simpa [prefixWord, tailWord_4158331, baseEnd_4158331] using wordTrace_append hprefix tailTrace_4158331
  have hstable : (prefixWord ++ tailWord_4158331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158331).length < 2 ^ (prefixWord ++ tailWord_4158331).sum := by decide
  have hdescent : baseEnd_4158331 < baseStart_4158331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158393 : List Nat := [1, 2, 1, 4, 2, 2, 1, 3, 1, 5]
def baseStart_4158393 : Nat := 118140960795 + 4158393 * 2 ^ 59
def prefixEnd_4158393 : Nat := 4983230072969 + 3 ^ 40 * 4158393 * 2
def baseEnd_4158393 : Nat := 1423502906194702667975603

theorem tailTrace_4158393 : CollatzResearch.WordTrace tailWord_4158393 prefixEnd_4158393 1423502906194702667975603 := by
  unfold tailWord_4158393
  simp only [CollatzResearch.WordTrace]
  refine ⟨151669052823859832827839833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101112701882573221885226555 151669052823859832827839833)
  ·
    refine ⟨113751789617894874620879875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151669052823859832827839833 113751789617894874620879875)
    ·
      refine ⟨170627684426842311931319813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113751789617894874620879875 170627684426842311931319813)
      ·
        refine ⟨31992690830032933487122465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170627684426842311931319813 31992690830032933487122465)
        ·
          refine ⟨23994518122524700115341849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31992690830032933487122465 23994518122524700115341849)
          ·
            refine ⟨17995888591893525086506387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23994518122524700115341849 17995888591893525086506387)
            ·
              refine ⟨26993832887840287629759581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17995888591893525086506387 26993832887840287629759581)
              ·
                refine ⟨10122687332940107861159843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26993832887840287629759581 10122687332940107861159843)
                ·
                  refine ⟨15184030999410161791739765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10122687332940107861159843 15184030999410161791739765)
                  ·
                    refine ⟨1423502906194702667975603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15184030999410161791739765 1423502906194702667975603)
                    ·
                      rfl

theorem cell22_4158393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_4158393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158393 prefixEnd_4158393 := by exact prefixLift 4158393
  have htrace : WordTrace (prefixWord ++ tailWord_4158393) baseStart_4158393 baseEnd_4158393 := by
    simpa [prefixWord, tailWord_4158393, baseEnd_4158393] using wordTrace_append hprefix tailTrace_4158393
  have hstable : (prefixWord ++ tailWord_4158393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158393).length < 2 ^ (prefixWord ++ tailWord_4158393).sum := by decide
  have hdescent : baseEnd_4158393 < baseStart_4158393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158513 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 8]
def baseStart_4158513 : Nat := 118140960795 + 4158513 * 2 ^ 59
def prefixEnd_4158513 : Nat := 4983230072969 + 3 ^ 40 * 4158513 * 2
def baseEnd_4158513 : Nat := 474514661549020784991745

theorem tailTrace_4158513 : CollatzResearch.WordTrace tailWord_4158513 prefixEnd_4158513 474514661549020784991745 := by
  unfold tailWord_4158513
  simp only [CollatzResearch.WordTrace]
  refine ⟨151673429583425093322208193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101115619722283395548138795 151673429583425093322208193)
  ·
    refine ⟨113755072187568819991656145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151673429583425093322208193 113755072187568819991656145)
    ·
      refine ⟨85316304140676614993742109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113755072187568819991656145 85316304140676614993742109)
      ·
        refine ⟨31993614052753730622653291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85316304140676614993742109 31993614052753730622653291)
        ·
          refine ⟨47990421079130595933979937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31993614052753730622653291 47990421079130595933979937)
          ·
            refine ⟨35992815809347946950484953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47990421079130595933979937 35992815809347946950484953)
            ·
              refine ⟨26994611857010960212863715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35992815809347946950484953 26994611857010960212863715)
              ·
                refine ⟨40491917785516440319295573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26994611857010960212863715 40491917785516440319295573)
                ·
                  refine ⟨474514661549020784991745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40491917785516440319295573 474514661549020784991745)
                  ·
                    rfl

theorem cell22_4158513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 8].length) (baseStart_4158513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158513 prefixEnd_4158513 := by exact prefixLift 4158513
  have htrace : WordTrace (prefixWord ++ tailWord_4158513) baseStart_4158513 baseEnd_4158513 := by
    simpa [prefixWord, tailWord_4158513, baseEnd_4158513] using wordTrace_append hprefix tailTrace_4158513
  have hstable : (prefixWord ++ tailWord_4158513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158513).length < 2 ^ (prefixWord ++ tailWord_4158513).sum := by decide
  have hdescent : baseEnd_4158513 < baseStart_4158513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158545 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 4, 3]
def baseStart_4158545 : Nat := 118140960795 + 4158545 * 2 ^ 59
def prefixEnd_4158545 : Nat := 4983230072969 + 3 ^ 40 * 4158545 * 2
def baseEnd_4158545 : Nat := 1423554938901024938175137

theorem tailTrace_4158545 : CollatzResearch.WordTrace tailWord_4158545 prefixEnd_4158545 1423554938901024938175137 := by
  unfold tailWord_4158545
  simp only [CollatzResearch.WordTrace]
  refine ⟨151674596719309162787373089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101116397812872775191582059 151674596719309162787373089)
  ·
    refine ⟨113755947539481872090529817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151674596719309162787373089 113755947539481872090529817)
    ·
      refine ⟨85316960654611404067897363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113755947539481872090529817 85316960654611404067897363)
      ·
        refine ⟨127975440981917106101846045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85316960654611404067897363 127975440981917106101846045)
        ·
          refine ⟨47990790368218914788192267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127975440981917106101846045 47990790368218914788192267)
          ·
            refine ⟨71986185552328372182288401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47990790368218914788192267 71986185552328372182288401)
            ·
              refine ⟨53989639164246279136716301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71986185552328372182288401 53989639164246279136716301)
              ·
                refine ⟨20246114686592354676268613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53989639164246279136716301 20246114686592354676268613)
                ·
                  refine ⟨3796146503736066501800365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20246114686592354676268613 3796146503736066501800365)
                  ·
                    refine ⟨1423554938901024938175137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3796146503736066501800365 1423554938901024938175137)
                    ·
                      rfl

theorem cell22_4158545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_4158545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158545 prefixEnd_4158545 := by exact prefixLift 4158545
  have htrace : WordTrace (prefixWord ++ tailWord_4158545) baseStart_4158545 baseEnd_4158545 := by
    simpa [prefixWord, tailWord_4158545, baseEnd_4158545] using wordTrace_append hprefix tailTrace_4158545
  have hstable : (prefixWord ++ tailWord_4158545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158545).length < 2 ^ (prefixWord ++ tailWord_4158545).sum := by decide
  have hdescent : baseEnd_4158545 < baseStart_4158545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158562 : List Nat := [3, 3, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_4158562 : Nat := 118140960795 + 4158562 * 2 ^ 59
def prefixEnd_4158562 : Nat := 4983230072969 + 3 ^ 40 * 4158562 * 2
def baseEnd_4158562 : Nat := 1423560758348442560500085

theorem tailTrace_4158562 : CollatzResearch.WordTrace tailWord_4158562 prefixEnd_4158562 1423560758348442560500085 := by
  unfold tailWord_4158562
  simp only [CollatzResearch.WordTrace]
  refine ⟨37918804190061893672685485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101116811173498383127161293 37918804190061893672685485)
  ·
    refine ⟨14219551571273210127257057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37918804190061893672685485 14219551571273210127257057)
    ·
      refine ⟨10664663678454907595442793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14219551571273210127257057 10664663678454907595442793)
      ·
        refine ⟨7998497758841180696582095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10664663678454907595442793 7998497758841180696582095)
        ·
          refine ⟨11997746638261771044873143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7998497758841180696582095 11997746638261771044873143)
          ·
            refine ⟨17996619957392656567309715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11997746638261771044873143 17996619957392656567309715)
            ·
              refine ⟨26994929936088984850964573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17996619957392656567309715 26994929936088984850964573)
              ·
                refine ⟨10123098726033369319111715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26994929936088984850964573 10123098726033369319111715)
                ·
                  refine ⟨15184648089050053978667573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10123098726033369319111715 15184648089050053978667573)
                  ·
                    refine ⟨1423560758348442560500085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15184648089050053978667573 1423560758348442560500085)
                    ·
                      rfl

theorem cell22_4158562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_4158562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158562 prefixEnd_4158562 := by exact prefixLift 4158562
  have htrace : WordTrace (prefixWord ++ tailWord_4158562) baseStart_4158562 baseEnd_4158562 := by
    simpa [prefixWord, tailWord_4158562, baseEnd_4158562] using wordTrace_append hprefix tailTrace_4158562
  have hstable : (prefixWord ++ tailWord_4158562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158562).length < 2 ^ (prefixWord ++ tailWord_4158562).sum := by decide
  have hdescent : baseEnd_4158562 < baseStart_4158562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158575 : List Nat := [1, 1, 2, 1, 3, 3, 5, 6]
def baseStart_4158575 : Nat := 118140960795 + 4158575 * 2 ^ 59
def prefixEnd_4158575 : Nat := 4983230072969 + 3 ^ 40 * 4158575 * 2
def baseEnd_4158575 : Nat := 158173912057123873325005

theorem tailTrace_4158575 : CollatzResearch.WordTrace tailWord_4158575 prefixEnd_4158575 158173912057123873325005 := by
  unfold tailWord_4158575
  simp only [CollatzResearch.WordTrace]
  refine ⟨151675690909200477910965179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101117127272800318607310119 151675690909200477910965179)
  ·
    refine ⟨227513536363800716866447769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151675690909200477910965179 227513536363800716866447769)
    ·
      refine ⟨170635152272850537649835827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227513536363800716866447769 170635152272850537649835827)
      ·
        refine ⟨255952728409275806474753741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170635152272850537649835827 255952728409275806474753741)
        ·
          refine ⟨95982273153478427428032653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255952728409275806474753741 95982273153478427428032653)
          ·
            refine ⟨35993352432554410285512245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95982273153478427428032653 35993352432554410285512245)
            ·
              refine ⟨3374376790551975964266773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35993352432554410285512245 3374376790551975964266773)
              ·
                refine ⟨158173912057123873325005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3374376790551975964266773 158173912057123873325005)
                ·
                  rfl

theorem cell22_4158575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 6].length) (baseStart_4158575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158575 prefixEnd_4158575 := by exact prefixLift 4158575
  have htrace : WordTrace (prefixWord ++ tailWord_4158575) baseStart_4158575 baseEnd_4158575 := by
    simpa [prefixWord, tailWord_4158575, baseEnd_4158575] using wordTrace_append hprefix tailTrace_4158575
  have hstable : (prefixWord ++ tailWord_4158575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158575).length < 2 ^ (prefixWord ++ tailWord_4158575).sum := by decide
  have hdescent : baseEnd_4158575 < baseStart_4158575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158581 : List Nat := [1, 3, 4, 3, 1, 1, 2, 3, 4]
def baseStart_4158581 : Nat := 118140960795 + 4158581 * 2 ^ 59
def prefixEnd_4158581 : Nat := 4983230072969 + 3 ^ 40 * 4158581 * 2
def baseEnd_4158581 : Nat := 474522420812244281425009

theorem tailTrace_4158581 : CollatzResearch.WordTrace tailWord_4158581 prefixEnd_4158581 474522420812244281425009 := by
  unfold tailWord_4158581
  simp only [CollatzResearch.WordTrace]
  refine ⟨151675909747178740935683597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101117273164785827290455731 151675909747178740935683597)
  ·
    refine ⟨56878466155192027850881349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151675909747178740935683597 56878466155192027850881349)
    ·
      refine ⟨10664712404098505222040253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56878466155192027850881349 10664712404098505222040253)
      ·
        refine ⟨3999267151536939458265095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10664712404098505222040253 3999267151536939458265095)
        ·
          refine ⟨5998900727305409187397643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3999267151536939458265095 5998900727305409187397643)
          ·
            refine ⟨8998351090958113781096465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5998900727305409187397643 8998351090958113781096465)
            ·
              refine ⟨6748763318218585335822349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8998351090958113781096465 6748763318218585335822349)
              ·
                refine ⟨2530786244331969500933381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6748763318218585335822349 2530786244331969500933381)
                ·
                  refine ⟨474522420812244281425009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2530786244331969500933381 474522420812244281425009)
                  ·
                    rfl

theorem cell22_4158581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_4158581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158581 prefixEnd_4158581 := by exact prefixLift 4158581
  have htrace : WordTrace (prefixWord ++ tailWord_4158581) baseStart_4158581 baseEnd_4158581 := by
    simpa [prefixWord, tailWord_4158581, baseEnd_4158581] using wordTrace_append hprefix tailTrace_4158581
  have hstable : (prefixWord ++ tailWord_4158581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158581).length < 2 ^ (prefixWord ++ tailWord_4158581).sum := by decide
  have hdescent : baseEnd_4158581 < baseStart_4158581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158626 : List Nat := [3, 3, 1, 3, 3, 1, 2, 6]
def baseStart_4158626 : Nat := 118140960795 + 4158626 * 2 ^ 59
def prefixEnd_4158626 : Nat := 4983230072969 + 3 ^ 40 * 4158626 * 2
def baseEnd_4158626 : Nat := 158175851872929747433321

theorem tailTrace_4158626 : CollatzResearch.WordTrace tailWord_4158626 prefixEnd_4158626 158175851872929747433321 := by
  unfold tailWord_4158626
  simp only [CollatzResearch.WordTrace]
  refine ⟨37919387758003928405267933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101118367354677142414047821 37919387758003928405267933)
  ·
    refine ⟨14219770409251473151975475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37919387758003928405267933 14219770409251473151975475)
    ·
      refine ⟨21329655613877209727963213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14219770409251473151975475 21329655613877209727963213)
      ·
        refine ⟨7998620855203953647986205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21329655613877209727963213 7998620855203953647986205)
        ·
          refine ⟨2999482820701482617994827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7998620855203953647986205 2999482820701482617994827)
          ·
            refine ⟨4499224231052223926992241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2999482820701482617994827 4499224231052223926992241)
            ·
              refine ⟨3374418173289167945244181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4499224231052223926992241 3374418173289167945244181)
              ·
                refine ⟨158175851872929747433321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3374418173289167945244181 158175851872929747433321)
                ·
                  rfl

theorem cell22_4158626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 6].length) (baseStart_4158626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158626 prefixEnd_4158626 := by exact prefixLift 4158626
  have htrace : WordTrace (prefixWord ++ tailWord_4158626) baseStart_4158626 baseEnd_4158626 := by
    simpa [prefixWord, tailWord_4158626, baseEnd_4158626] using wordTrace_append hprefix tailTrace_4158626
  have hstable : (prefixWord ++ tailWord_4158626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158626).length < 2 ^ (prefixWord ++ tailWord_4158626).sum := by decide
  have hdescent : baseEnd_4158626 < baseStart_4158626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158641 : List Nat := [1, 2, 2, 5, 1, 1, 3, 3, 1, 3]
def baseStart_4158641 : Nat := 118140960795 + 4158641 * 2 ^ 59
def prefixEnd_4158641 : Nat := 4983230072969 + 3 ^ 40 * 4158641 * 2
def baseEnd_4158641 : Nat := 1423587801662912687774843

theorem tailTrace_4158641 : CollatzResearch.WordTrace tailWord_4158641 prefixEnd_4158641 1423587801662912687774843 := by
  unfold tailWord_4158641
  simp only [CollatzResearch.WordTrace]
  refine ⟨151678098126961371182867777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101118732084640914121911851 151678098126961371182867777)
  ·
    refine ⟨113758573595221028387150833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151678098126961371182867777 113758573595221028387150833)
    ·
      refine ⟨85318930196415771290363125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113758573595221028387150833 85318930196415771290363125)
      ·
        refine ⟨7998649705913978558471543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85318930196415771290363125 7998649705913978558471543)
        ·
          refine ⟨11997974558870967837707315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7998649705913978558471543 11997974558870967837707315)
          ·
            refine ⟨17996961838306451756560973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11997974558870967837707315 17996961838306451756560973)
            ·
              refine ⟨6748860689364919408710365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17996961838306451756560973 6748860689364919408710365)
              ·
                refine ⟨2530822758511844778266387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6748860689364919408710365 2530822758511844778266387)
                ·
                  refine ⟨3796234137767767167399581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2530822758511844778266387 3796234137767767167399581)
                  ·
                    refine ⟨1423587801662912687774843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3796234137767767167399581 1423587801662912687774843)
                    ·
                      rfl

theorem cell22_4158641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 1, 3].length) (baseStart_4158641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158641 prefixEnd_4158641 := by exact prefixLift 4158641
  have htrace : WordTrace (prefixWord ++ tailWord_4158641) baseStart_4158641 baseEnd_4158641 := by
    simpa [prefixWord, tailWord_4158641, baseEnd_4158641] using wordTrace_append hprefix tailTrace_4158641
  have hstable : (prefixWord ++ tailWord_4158641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158641).length < 2 ^ (prefixWord ++ tailWord_4158641).sum := by decide
  have hdescent : baseEnd_4158641 < baseStart_4158641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158650 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 5, 4]
def baseStart_4158650 : Nat := 118140960795 + 4158650 * 2 ^ 59
def prefixEnd_4158650 : Nat := 4983230072969 + 3 ^ 40 * 4158650 * 2
def baseEnd_4158650 : Nat := 1423590882546839664299815

theorem tailTrace_4158650 : CollatzResearch.WordTrace tailWord_4158650 prefixEnd_4158650 1423590882546839664299815 := by
  unfold tailWord_4158650
  simp only [CollatzResearch.WordTrace]
  refine ⟨37919606595982191429986351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101118950922619177146630269 37919606595982191429986351)
  ·
    refine ⟨56879409893973287144979527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37919606595982191429986351 56879409893973287144979527)
    ·
      refine ⟨85319114840959930717469291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56879409893973287144979527 85319114840959930717469291)
      ·
        refine ⟨127978672261439896076203937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85319114840959930717469291 127978672261439896076203937)
        ·
          refine ⟨95984004196079922057152953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127978672261439896076203937 95984004196079922057152953)
          ·
            refine ⟨71988003147059941542864715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95984004196079922057152953 71988003147059941542864715)
            ·
              refine ⟨107982004720589912314297073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71988003147059941542864715 107982004720589912314297073)
              ·
                refine ⟨80986503540442434235722805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107982004720589912314297073 80986503540442434235722805)
                ·
                  refine ⟨7592484706916478209599013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80986503540442434235722805 7592484706916478209599013)
                  ·
                    refine ⟨1423590882546839664299815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7592484706916478209599013 1423590882546839664299815)
                    ·
                      rfl

theorem cell22_4158650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_4158650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158650 prefixEnd_4158650 := by exact prefixLift 4158650
  have htrace : WordTrace (prefixWord ++ tailWord_4158650) baseStart_4158650 baseEnd_4158650 := by
    simpa [prefixWord, tailWord_4158650, baseEnd_4158650] using wordTrace_append hprefix tailTrace_4158650
  have hstable : (prefixWord ++ tailWord_4158650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158650).length < 2 ^ (prefixWord ++ tailWord_4158650).sum := by decide
  have hdescent : baseEnd_4158650 < baseStart_4158650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158701 : List Nat := [1, 5, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_4158701 : Nat := 118140960795 + 4158701 * 2 ^ 59
def prefixEnd_4158701 : Nat := 4983230072969 + 3 ^ 40 * 4158701 * 2
def baseEnd_4158701 : Nat := 1423608340889092531274659

theorem tailTrace_4158701 : CollatzResearch.WordTrace tailWord_4158701 prefixEnd_4158701 1423608340889092531274659 := by
  unfold tailWord_4158701
  simp only [CollatzResearch.WordTrace]
  refine ⟨151680286506744001430051957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101120191004496000953367971 151680286506744001430051957)
  ·
    refine ⟨14220026860007250134067371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151680286506744001430051957 14220026860007250134067371)
    ·
      refine ⟨21330040290010875201101057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14220026860007250134067371 21330040290010875201101057)
      ·
        refine ⟨15997530217508156400825793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21330040290010875201101057 15997530217508156400825793)
        ·
          refine ⟨11998147663131117300619345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15997530217508156400825793 11998147663131117300619345)
          ·
            refine ⟨8998610747348337975464509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11998147663131117300619345 8998610747348337975464509)
            ·
              refine ⟨3374479030255626740799191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8998610747348337975464509 3374479030255626740799191)
              ·
                refine ⟨5061718545383440111198787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3374479030255626740799191 5061718545383440111198787)
                ·
                  refine ⟨7592577818075160166798181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5061718545383440111198787 7592577818075160166798181)
                  ·
                    refine ⟨1423608340889092531274659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7592577818075160166798181 1423608340889092531274659)
                    ·
                      rfl

theorem cell22_4158701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_4158701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158701 prefixEnd_4158701 := by exact prefixLift 4158701
  have htrace : WordTrace (prefixWord ++ tailWord_4158701) baseStart_4158701 baseEnd_4158701 := by
    simpa [prefixWord, tailWord_4158701, baseEnd_4158701] using wordTrace_append hprefix tailTrace_4158701
  have hstable : (prefixWord ++ tailWord_4158701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158701).length < 2 ^ (prefixWord ++ tailWord_4158701).sum := by decide
  have hdescent : baseEnd_4158701 < baseStart_4158701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158714 : List Nat := [3, 1, 1, 1, 1, 4, 4, 2, 2, 3]
def baseStart_4158714 : Nat := 118140960795 + 4158714 * 2 ^ 59
def prefixEnd_4158714 : Nat := 4983230072969 + 3 ^ 40 * 4158714 * 2
def baseEnd_4158714 : Nat := 1423612791054764830699619

theorem tailTrace_4158714 : CollatzResearch.WordTrace tailWord_4158714 prefixEnd_4158714 1423612791054764830699619 := by
  unfold tailWord_4158714
  simp only [CollatzResearch.WordTrace]
  refine ⟨37920190163924226162568799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101120507103797936433516797 37920190163924226162568799)
  ·
    refine ⟨56880285245886339243853199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37920190163924226162568799 56880285245886339243853199)
    ·
      refine ⟨85320427868829508865779799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56880285245886339243853199 85320427868829508865779799)
      ·
        refine ⟨127980641803244263298669699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85320427868829508865779799 127980641803244263298669699)
        ·
          refine ⟨191970962704866394948004549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127980641803244263298669699 191970962704866394948004549)
          ·
            refine ⟨35994555507162449052750853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191970962704866394948004549 35994555507162449052750853)
            ·
              refine ⟨6748979157592959197390785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35994555507162449052750853 6748979157592959197390785)
              ·
                refine ⟨5061734368194719398043089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6748979157592959197390785 5061734368194719398043089)
                ·
                  refine ⟨3796300776146039548532317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5061734368194719398043089 3796300776146039548532317)
                  ·
                    refine ⟨1423612791054764830699619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3796300776146039548532317 1423612791054764830699619)
                    ·
                      rfl

theorem cell22_4158714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_4158714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158714 prefixEnd_4158714 := by exact prefixLift 4158714
  have htrace : WordTrace (prefixWord ++ tailWord_4158714) baseStart_4158714 baseEnd_4158714 := by
    simpa [prefixWord, tailWord_4158714, baseEnd_4158714] using wordTrace_append hprefix tailTrace_4158714
  have hstable : (prefixWord ++ tailWord_4158714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158714).length < 2 ^ (prefixWord ++ tailWord_4158714).sum := by decide
  have hdescent : baseEnd_4158714 < baseStart_4158714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158819 : List Nat := [1, 1, 1, 5, 2, 2, 2, 3, 1, 4]
def baseStart_4158819 : Nat := 118140960795 + 4158819 * 2 ^ 59
def prefixEnd_4158819 : Nat := 4983230072969 + 3 ^ 40 * 4158819 * 2
def baseEnd_4158819 : Nat := 1423648734700579556824297

theorem tailTrace_4158819 : CollatzResearch.WordTrace tailWord_4158819 prefixEnd_4158819 1423648734700579556824297 := by
  unfold tailWord_4158819
  simp only [CollatzResearch.WordTrace]
  refine ⟨151684590320316507582847511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101123060213544338388565007 151684590320316507582847511)
  ·
    refine ⟨227526885480474761374271267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151684590320316507582847511 227526885480474761374271267)
    ·
      refine ⟨341290328220712142061406901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227526885480474761374271267 341290328220712142061406901)
      ·
        refine ⟨31995968270691763318256897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 341290328220712142061406901 31995968270691763318256897)
        ·
          refine ⟨23996976203018822488692673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31995968270691763318256897 23996976203018822488692673)
          ·
            refine ⟨17997732152264116866519505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23996976203018822488692673 17997732152264116866519505)
            ·
              refine ⟨13498299114198087649889629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17997732152264116866519505 13498299114198087649889629)
              ·
                refine ⟨5061862167824282868708611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13498299114198087649889629 5061862167824282868708611)
                ·
                  refine ⟨7592793251736424303062917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5061862167824282868708611 7592793251736424303062917)
                  ·
                    refine ⟨1423648734700579556824297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7592793251736424303062917 1423648734700579556824297)
                    ·
                      rfl

theorem cell22_4158819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 4].length) (baseStart_4158819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158819 prefixEnd_4158819 := by exact prefixLift 4158819
  have htrace : WordTrace (prefixWord ++ tailWord_4158819) baseStart_4158819 baseEnd_4158819 := by
    simpa [prefixWord, tailWord_4158819, baseEnd_4158819] using wordTrace_append hprefix tailTrace_4158819
  have hstable : (prefixWord ++ tailWord_4158819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158819).length < 2 ^ (prefixWord ++ tailWord_4158819).sum := by decide
  have hdescent : baseEnd_4158819 < baseStart_4158819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158892 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 2, 6]
def baseStart_4158892 : Nat := 118140960795 + 4158892 * 2 ^ 59
def prefixEnd_4158892 : Nat := 4983230072969 + 3 ^ 40 * 4158892 * 2
def baseEnd_4158892 : Nat := 1423673724092431699749073

theorem tailTrace_4158892 : CollatzResearch.WordTrace tailWord_4158892 prefixEnd_4158892 1423673724092431699749073 := by
  unfold tailWord_4158892
  simp only [CollatzResearch.WordTrace]
  refine ⟨75843626424526020525127465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101124835232701360700169953 75843626424526020525127465)
  ·
    refine ⟨56882719818394515393845599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75843626424526020525127465 56882719818394515393845599)
    ·
      refine ⟨85324079727591773090768399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56882719818394515393845599 85324079727591773090768399)
      ·
        refine ⟨127986119591387659636152599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85324079727591773090768399 127986119591387659636152599)
        ·
          refine ⟨191979179387081489454228899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127986119591387659636152599 191979179387081489454228899)
          ·
            refine ⟨287968769080622234181343349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191979179387081489454228899 287968769080622234181343349)
            ·
              refine ⟨26997072101308334454500939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287968769080622234181343349 26997072101308334454500939)
              ·
                refine ⟨40495608151962501681751409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26997072101308334454500939 40495608151962501681751409)
                ·
                  refine ⟨30371706113971876261313557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40495608151962501681751409 30371706113971876261313557)
                  ·
                    refine ⟨1423673724092431699749073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30371706113971876261313557 1423673724092431699749073)
                    ·
                      rfl

theorem cell22_4158892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_4158892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158892 prefixEnd_4158892 := by exact prefixLift 4158892
  have htrace : WordTrace (prefixWord ++ tailWord_4158892) baseStart_4158892 baseEnd_4158892 := by
    simpa [prefixWord, tailWord_4158892, baseEnd_4158892] using wordTrace_append hprefix tailTrace_4158892
  have hstable : (prefixWord ++ tailWord_4158892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158892).length < 2 ^ (prefixWord ++ tailWord_4158892).sum := by decide
  have hdescent : baseEnd_4158892 < baseStart_4158892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158941 : List Nat := [1, 4, 3, 1, 1, 2, 3, 2, 5]
def baseStart_4158941 : Nat := 118140960795 + 4158941 * 2 ^ 59
def prefixEnd_4158941 : Nat := 4983230072969 + 3 ^ 40 * 4158941 * 2
def baseEnd_4158941 : Nat := 474563499264603968424641

theorem tailTrace_4158941 : CollatzResearch.WordTrace tailWord_4158941 prefixEnd_4158941 474563499264603968424641 := by
  unfold tailWord_4158941
  simp only [CollatzResearch.WordTrace]
  refine ⟨151689040025874522418788677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101126026683916348279192451 151689040025874522418788677)
  ·
    refine ⟨28441695004851472953522877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151689040025874522418788677 28441695004851472953522877)
    ·
      refine ⟨10665635626819302357571079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28441695004851472953522877 10665635626819302357571079)
      ·
        refine ⟨15998453440228953536356619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10665635626819302357571079 15998453440228953536356619)
        ·
          refine ⟨23997680160343430304534929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15998453440228953536356619 23997680160343430304534929)
          ·
            refine ⟨17998260120257572728401197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23997680160343430304534929 17998260120257572728401197)
            ·
              refine ⟨6749347545096589773150449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17998260120257572728401197 6749347545096589773150449)
              ·
                refine ⟨5062010658822442329862837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6749347545096589773150449 5062010658822442329862837)
                ·
                  refine ⟨474563499264603968424641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5062010658822442329862837 474563499264603968424641)
                  ·
                    rfl

theorem cell22_4158941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_4158941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158941 prefixEnd_4158941 := by exact prefixLift 4158941
  have htrace : WordTrace (prefixWord ++ tailWord_4158941) baseStart_4158941 baseEnd_4158941 := by
    simpa [prefixWord, tailWord_4158941, baseEnd_4158941] using wordTrace_append hprefix tailTrace_4158941
  have hstable : (prefixWord ++ tailWord_4158941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158941).length < 2 ^ (prefixWord ++ tailWord_4158941).sum := by decide
  have hdescent : baseEnd_4158941 < baseStart_4158941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158984 : List Nat := [2, 1, 3, 2, 1, 1, 2, 4, 1, 5]
def baseStart_4158984 : Nat := 118140960795 + 4158984 * 2 ^ 59
def prefixEnd_4158984 : Nat := 4983230072969 + 3 ^ 40 * 4158984 * 2
def baseEnd_4158984 : Nat := 1423705217572574126448791

theorem tailTrace_4158984 : CollatzResearch.WordTrace tailWord_4158984 prefixEnd_4158984 1423705217572574126448791 := by
  unfold tailWord_4158984
  simp only [CollatzResearch.WordTrace]
  refine ⟨75845304182359370381302003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101127072243145827175069337 75845304182359370381302003)
  ·
    refine ⟨113767956273539055571953005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75845304182359370381302003 113767956273539055571953005)
    ·
      refine ⟨42662983602577145839482377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113767956273539055571953005 42662983602577145839482377)
      ·
        refine ⟨31997237701932859379611783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42662983602577145839482377 31997237701932859379611783)
        ·
          refine ⟨47995856552899289069417675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31997237701932859379611783 47995856552899289069417675)
          ·
            refine ⟨71993784829348933604126513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47995856552899289069417675 71993784829348933604126513)
            ·
              refine ⟨53995338622011700203094885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71993784829348933604126513 53995338622011700203094885)
              ·
                refine ⟨10124125991627193788080291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53995338622011700203094885 10124125991627193788080291)
                ·
                  refine ⟨15186188987440790682120437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10124125991627193788080291 15186188987440790682120437)
                  ·
                    refine ⟨1423705217572574126448791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15186188987440790682120437 1423705217572574126448791)
                    ·
                      rfl

theorem cell22_4158984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_4158984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4158984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4158984 prefixEnd_4158984 := by exact prefixLift 4158984
  have htrace : WordTrace (prefixWord ++ tailWord_4158984) baseStart_4158984 baseEnd_4158984 := by
    simpa [prefixWord, tailWord_4158984, baseEnd_4158984] using wordTrace_append hprefix tailTrace_4158984
  have hstable : (prefixWord ++ tailWord_4158984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158984).length < 2 ^ (prefixWord ++ tailWord_4158984).sum := by decide
  have hdescent : baseEnd_4158984 < baseStart_4158984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159018 : List Nat := [3, 1, 4, 1, 1, 1, 3, 3, 2, 3]
def baseStart_4159018 : Nat := 118140960795 + 4159018 * 2 ^ 59
def prefixEnd_4159018 : Nat := 4983230072969 + 3 ^ 40 * 4159018 * 2
def baseEnd_4159018 : Nat := 1423716856467409371098687

theorem tailTrace_4159018 : CollatzResearch.WordTrace tailWord_4159018 prefixEnd_4159018 1423716856467409371098687 := by
  unfold tailWord_4159018
  simp only [CollatzResearch.WordTrace]
  refine ⟨37922962111648891142335427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101127898964397043046227805 37922962111648891142335427)
  ·
    refine ⟨56884443167473336713503141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37922962111648891142335427 56884443167473336713503141)
    ·
      refine ⟨10665833093901250633781839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56884443167473336713503141 10665833093901250633781839)
      ·
        refine ⟨15998749640851875950672759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10665833093901250633781839 15998749640851875950672759)
        ·
          refine ⟨23998124461277813926009139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15998749640851875950672759 23998124461277813926009139)
          ·
            refine ⟨35997186691916720889013709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23998124461277813926009139 35997186691916720889013709)
            ·
              refine ⟨13498945009468770333380141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35997186691916720889013709 13498945009468770333380141)
              ·
                refine ⟨5062104378550788875017553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13498945009468770333380141 5062104378550788875017553)
                ·
                  refine ⟨3796578283913091656263165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5062104378550788875017553 3796578283913091656263165)
                  ·
                    refine ⟨1423716856467409371098687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3796578283913091656263165 1423716856467409371098687)
                    ·
                      rfl

theorem cell22_4159018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_4159018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159018 prefixEnd_4159018 := by exact prefixLift 4159018
  have htrace : WordTrace (prefixWord ++ tailWord_4159018) baseStart_4159018 baseEnd_4159018 := by
    simpa [prefixWord, tailWord_4159018, baseEnd_4159018] using wordTrace_append hprefix tailTrace_4159018
  have hstable : (prefixWord ++ tailWord_4159018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159018).length < 2 ^ (prefixWord ++ tailWord_4159018).sum := by decide
  have hdescent : baseEnd_4159018 < baseStart_4159018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159076 : List Nat := [2, 3, 1, 1, 2, 3, 2, 3, 5]
def baseStart_4159076 : Nat := 118140960795 + 4159076 * 2 ^ 59
def prefixEnd_4159076 : Nat := 4983230072969 + 3 ^ 40 * 4159076 * 2
def baseEnd_4159076 : Nat := 474578903684238851049503

theorem tailTrace_4159076 : CollatzResearch.WordTrace tailWord_4159076 prefixEnd_4159076 474578903684238851049503 := by
  unfold tailWord_4159076
  simp only [CollatzResearch.WordTrace]
  refine ⟨75846981940192720237476541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101129309253590293649968721 75846981940192720237476541)
  ·
    refine ⟨28442618227572270089053703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75846981940192720237476541 28442618227572270089053703)
    ·
      refine ⟨42663927341358405133580555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28442618227572270089053703 42663927341358405133580555)
      ·
        refine ⟨63995891012037607700370833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42663927341358405133580555 63995891012037607700370833)
        ·
          refine ⟨47996918259028205775278125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63995891012037607700370833 47996918259028205775278125)
          ·
            refine ⟨17998844347135577165729297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47996918259028205775278125 17998844347135577165729297)
            ·
              refine ⟨13499133260351682874296973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17998844347135577165729297 13499133260351682874296973)
              ·
                refine ⟨5062174972631881077861365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13499133260351682874296973 5062174972631881077861365)
                ·
                  refine ⟨474578903684238851049503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5062174972631881077861365 474578903684238851049503)
                  ·
                    rfl

theorem cell22_4159076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_4159076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159076 prefixEnd_4159076 := by exact prefixLift 4159076
  have htrace : WordTrace (prefixWord ++ tailWord_4159076) baseStart_4159076 baseEnd_4159076 := by
    simpa [prefixWord, tailWord_4159076, baseEnd_4159076] using wordTrace_append hprefix tailTrace_4159076
  have hstable : (prefixWord ++ tailWord_4159076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159076).length < 2 ^ (prefixWord ++ tailWord_4159076).sum := by decide
  have hdescent : baseEnd_4159076 < baseStart_4159076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159104 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 8]
def baseStart_4159104 : Nat := 118140960795 + 4159104 * 2 ^ 59
def prefixEnd_4159104 : Nat := 4983230072969 + 3 ^ 40 * 4159104 * 2
def baseEnd_4159104 : Nat := 474582098674977937816141

theorem tailTrace_4159104 : CollatzResearch.WordTrace tailWord_4159104 prefixEnd_4159104 474582098674977937816141 := by
  unfold tailWord_4159104
  simp only [CollatzResearch.WordTrace]
  refine ⟨75847492562142000628486183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101129990082856000837981577 75847492562142000628486183)
  ·
    refine ⟨113771238843213000942729275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75847492562142000628486183 113771238843213000942729275)
    ·
      refine ⟨170656858264819501414093913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113771238843213000942729275 170656858264819501414093913)
      ·
        refine ⟨127992643698614626060570435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170656858264819501414093913 127992643698614626060570435)
        ·
          refine ⟨191988965547921939090855653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127992643698614626060570435 191988965547921939090855653)
          ·
            refine ⟨35997931040235363579535435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191988965547921939090855653 35997931040235363579535435)
            ·
              refine ⟨53996896560353045369303153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35997931040235363579535435 53996896560353045369303153)
              ·
                refine ⟨40497672420264784026977365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53996896560353045369303153 40497672420264784026977365)
                ·
                  refine ⟨474582098674977937816141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40497672420264784026977365 474582098674977937816141)
                  ·
                    rfl

theorem cell22_4159104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 8].length) (baseStart_4159104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159104 prefixEnd_4159104 := by exact prefixLift 4159104
  have htrace : WordTrace (prefixWord ++ tailWord_4159104) baseStart_4159104 baseEnd_4159104 := by
    simpa [prefixWord, tailWord_4159104, baseEnd_4159104] using wordTrace_append hprefix tailTrace_4159104
  have hstable : (prefixWord ++ tailWord_4159104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159104).length < 2 ^ (prefixWord ++ tailWord_4159104).sum := by decide
  have hdescent : baseEnd_4159104 < baseStart_4159104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159151 : List Nat := [1, 1, 2, 1, 2, 4, 2, 3, 2, 4]
def baseStart_4159151 : Nat := 118140960795 + 4159151 * 2 ^ 59
def prefixEnd_4159151 : Nat := 4983230072969 + 3 ^ 40 * 4159151 * 2
def baseEnd_4159151 : Nat := 1423762385085441357523279

theorem tailTrace_4159151 : CollatzResearch.WordTrace tailWord_4159151 prefixEnd_4159151 1423762385085441357523279 := by
  unfold tailWord_4159151
  simp only [CollatzResearch.WordTrace]
  refine ⟨151696699355113728283933307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101131132903409152189288871 151696699355113728283933307)
  ·
    refine ⟨227545049032670592425899961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151696699355113728283933307 227545049032670592425899961)
    ·
      refine ⟨170658786774502944319424971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227545049032670592425899961 170658786774502944319424971)
      ·
        refine ⟨255988180161754416479137457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170658786774502944319424971 255988180161754416479137457)
        ·
          refine ⟨191991135121315812359353093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255988180161754416479137457 191991135121315812359353093)
          ·
            refine ⟨35998337835246714817378705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191991135121315812359353093 35998337835246714817378705)
            ·
              refine ⟨26998753376435036113034029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35998337835246714817378705 26998753376435036113034029)
              ·
                refine ⟨10124532516163138542387761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26998753376435036113034029 10124532516163138542387761)
                ·
                  refine ⟨7593399387122353906790821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10124532516163138542387761 7593399387122353906790821)
                  ·
                    refine ⟨1423762385085441357523279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7593399387122353906790821 1423762385085441357523279)
                    ·
                      rfl

theorem cell22_4159151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_4159151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159151 prefixEnd_4159151 := by exact prefixLift 4159151
  have htrace : WordTrace (prefixWord ++ tailWord_4159151) baseStart_4159151 baseEnd_4159151 := by
    simpa [prefixWord, tailWord_4159151, baseEnd_4159151] using wordTrace_append hprefix tailTrace_4159151
  have hstable : (prefixWord ++ tailWord_4159151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159151).length < 2 ^ (prefixWord ++ tailWord_4159151).sum := by decide
  have hdescent : baseEnd_4159151 < baseStart_4159151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159166 : List Nat := [4, 2, 1, 1, 2, 2, 10]
def baseStart_4159166 : Nat := 118140960795 + 4159166 * 2 ^ 59
def prefixEnd_4159166 : Nat := 4983230072969 + 3 ^ 40 * 4159166 * 2
def baseEnd_4159166 : Nat := 52732130366369863644379

theorem tailTrace_4159166 : CollatzResearch.WordTrace tailWord_4159166 prefixEnd_4159166 52732130366369863644379 := by
  unfold tailWord_4159166
  simp only [CollatzResearch.WordTrace]
  refine ⟨18962155806257423230716169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101131497633372923897152901 18962155806257423230716169)
  ·
    refine ⟨14221616854693067423037127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18962155806257423230716169 14221616854693067423037127)
    ·
      refine ⟨21332425282039601134555691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14221616854693067423037127 21332425282039601134555691)
      ·
        refine ⟨31998637923059401701833537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21332425282039601134555691 31998637923059401701833537)
        ·
          refine ⟨23998978442294551276375153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31998637923059401701833537 23998978442294551276375153)
          ·
            refine ⟨17999233831720913457281365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23998978442294551276375153 17999233831720913457281365)
            ·
              refine ⟨52732130366369863644379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17999233831720913457281365 52732130366369863644379)
              ·
                rfl

theorem cell22_4159166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 10].length) (baseStart_4159166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159166 prefixEnd_4159166 := by exact prefixLift 4159166
  have htrace : WordTrace (prefixWord ++ tailWord_4159166) baseStart_4159166 baseEnd_4159166 := by
    simpa [prefixWord, tailWord_4159166, baseEnd_4159166] using wordTrace_append hprefix tailTrace_4159166
  have hstable : (prefixWord ++ tailWord_4159166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159166).length < 2 ^ (prefixWord ++ tailWord_4159166).sum := by decide
  have hdescent : baseEnd_4159166 < baseStart_4159166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159215 : List Nat := [1, 1, 2, 1, 5, 1, 2, 5, 1, 3]
def baseStart_4159215 : Nat := 118140960795 + 4159215 * 2 ^ 59
def prefixEnd_4159215 : Nat := 4983230072969 + 3 ^ 40 * 4159215 * 2
def baseEnd_4159215 : Nat := 1423784293593366523923083

theorem tailTrace_4159215 : CollatzResearch.WordTrace tailWord_4159215 prefixEnd_4159215 1423784293593366523923083 := by
  unfold tailWord_4159215
  simp only [CollatzResearch.WordTrace]
  refine ⟨151699033626881867214263099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101132689084587911476175399 151699033626881867214263099)
  ·
    refine ⟨227548550440322800821394649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151699033626881867214263099 227548550440322800821394649)
    ·
      refine ⟨170661412830242100616045987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227548550440322800821394649 170661412830242100616045987)
      ·
        refine ⟨255992119245363150924068981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170661412830242100616045987 255992119245363150924068981)
        ·
          refine ⟨23999261179252795399131467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 255992119245363150924068981 23999261179252795399131467)
          ·
            refine ⟨35998891768879193098697201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23999261179252795399131467 35998891768879193098697201)
            ·
              refine ⟨26999168826659394824022901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35998891768879193098697201 26999168826659394824022901)
              ·
                refine ⟨2531172077499318264752147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26999168826659394824022901 2531172077499318264752147)
                ·
                  refine ⟨3796758116248977397128221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2531172077499318264752147 3796758116248977397128221)
                  ·
                    refine ⟨1423784293593366523923083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3796758116248977397128221 1423784293593366523923083)
                    ·
                      rfl

theorem cell22_4159215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 1, 3].length) (baseStart_4159215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159215 prefixEnd_4159215 := by exact prefixLift 4159215
  have htrace : WordTrace (prefixWord ++ tailWord_4159215) baseStart_4159215 baseEnd_4159215 := by
    simpa [prefixWord, tailWord_4159215, baseEnd_4159215] using wordTrace_append hprefix tailTrace_4159215
  have hstable : (prefixWord ++ tailWord_4159215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159215).length < 2 ^ (prefixWord ++ tailWord_4159215).sum := by decide
  have hdescent : baseEnd_4159215 < baseStart_4159215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159226 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 2, 5]
def baseStart_4159226 : Nat := 118140960795 + 4159226 * 2 ^ 59
def prefixEnd_4159226 : Nat := 4983230072969 + 3 ^ 40 * 4159226 * 2
def baseEnd_4159226 : Nat := 1423788059118166161898049

theorem tailTrace_4159226 : CollatzResearch.WordTrace tailWord_4159226 prefixEnd_4159226 1423788059118166161898049 := by
  unfold tailWord_4159226
  simp only [CollatzResearch.WordTrace]
  refine ⟨37924858707460504023228383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101132956553228010728609021 37924858707460504023228383)
  ·
    refine ⟨56887288061190756034842575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37924858707460504023228383 56887288061190756034842575)
    ·
      refine ⟨85330932091786134052263863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56887288061190756034842575 85330932091786134052263863)
      ·
        refine ⟨127996398137679201078395795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85330932091786134052263863 127996398137679201078395795)
        ·
          refine ⟨191994597206518801617593693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127996398137679201078395795 191994597206518801617593693)
          ·
            refine ⟨71997973952444550606597635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191994597206518801617593693 71997973952444550606597635)
            ·
              refine ⟨107996960928666825909896453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71997973952444550606597635 107996960928666825909896453)
              ·
                refine ⟨20249430174125029858105585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107996960928666825909896453 20249430174125029858105585)
                ·
                  refine ⟨15187072630593772393579189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20249430174125029858105585 15187072630593772393579189)
                  ·
                    refine ⟨1423788059118166161898049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15187072630593772393579189 1423788059118166161898049)
                    ·
                      rfl

theorem cell22_4159226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_4159226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159226 prefixEnd_4159226 := by exact prefixLift 4159226
  have htrace : WordTrace (prefixWord ++ tailWord_4159226) baseStart_4159226 baseEnd_4159226 := by
    simpa [prefixWord, tailWord_4159226, baseEnd_4159226] using wordTrace_append hprefix tailTrace_4159226
  have hstable : (prefixWord ++ tailWord_4159226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159226).length < 2 ^ (prefixWord ++ tailWord_4159226).sum := by decide
  have hdescent : baseEnd_4159226 < baseStart_4159226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159228 : List Nat := [2, 2, 2, 1, 3, 1, 4, 2, 5]
def baseStart_4159228 : Nat := 118140960795 + 4159228 * 2 ^ 59
def prefixEnd_4159228 : Nat := 4983230072969 + 3 ^ 40 * 4159228 * 2
def baseEnd_4159228 : Nat := 474596247919679607782681

theorem tailTrace_4159228 : CollatzResearch.WordTrace tailWord_4159228 prefixEnd_4159228 474596247919679607782681 := by
  unfold tailWord_4159228
  simp only [CollatzResearch.WordTrace]
  refine ⟨75849753887917385217243169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101133005183889846956324225 75849753887917385217243169)
  ·
    refine ⟨56887315415938038912932377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75849753887917385217243169 56887315415938038912932377)
    ·
      refine ⟨42665486561953529184699283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56887315415938038912932377 42665486561953529184699283)
      ·
        refine ⟨63998229842930293777048925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42665486561953529184699283 63998229842930293777048925)
        ·
          refine ⟨23999336191098860166393347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63998229842930293777048925 23999336191098860166393347)
          ·
            refine ⟨35999004286648290249590021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23999336191098860166393347 35999004286648290249590021)
            ·
              refine ⟨6749813303746554421798129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35999004286648290249590021 6749813303746554421798129)
              ·
                refine ⟨5062359977809915816348597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6749813303746554421798129 5062359977809915816348597)
                ·
                  refine ⟨474596247919679607782681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5062359977809915816348597 474596247919679607782681)
                  ·
                    rfl

theorem cell22_4159228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_4159228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159228 prefixEnd_4159228 := by exact prefixLift 4159228
  have htrace : WordTrace (prefixWord ++ tailWord_4159228) baseStart_4159228 baseEnd_4159228 := by
    simpa [prefixWord, tailWord_4159228, baseEnd_4159228] using wordTrace_append hprefix tailTrace_4159228
  have hstable : (prefixWord ++ tailWord_4159228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159228).length < 2 ^ (prefixWord ++ tailWord_4159228).sum := by decide
  have hdescent : baseEnd_4159228 < baseStart_4159228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159256 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 8]
def baseStart_4159256 : Nat := 118140960795 + 4159256 * 2 ^ 59
def prefixEnd_4159256 : Nat := 4983230072969 + 3 ^ 40 * 4159256 * 2
def baseEnd_4159256 : Nat := 474599442910418694549319

theorem tailTrace_4159256 : CollatzResearch.WordTrace tailWord_4159256 prefixEnd_4159256 474599442910418694549319 := by
  unfold tailWord_4159256
  simp only [CollatzResearch.WordTrace]
  refine ⟨75850264509866665608252811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101133686013155554144337081 75850264509866665608252811)
  ·
    refine ⟨113775396764799998412379217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75850264509866665608252811 113775396764799998412379217)
    ·
      refine ⟨85331547573599998809284413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113775396764799998412379217 85331547573599998809284413)
      ·
        refine ⟨31999330340099999553481655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85331547573599998809284413 31999330340099999553481655)
        ·
          refine ⟨47998995510149999330222483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31999330340099999553481655 47998995510149999330222483)
          ·
            refine ⟨71998493265224998995333725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47998995510149999330222483 71998493265224998995333725)
            ·
              refine ⟨26999434974459374623250147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71998493265224998995333725 26999434974459374623250147)
              ·
                refine ⟨40499152461689061934875221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26999434974459374623250147 40499152461689061934875221)
                ·
                  refine ⟨474599442910418694549319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40499152461689061934875221 474599442910418694549319)
                  ·
                    rfl

theorem cell22_4159256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 8].length) (baseStart_4159256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159256 prefixEnd_4159256 := by exact prefixLift 4159256
  have htrace : WordTrace (prefixWord ++ tailWord_4159256) baseStart_4159256 baseEnd_4159256 := by
    simpa [prefixWord, tailWord_4159256, baseEnd_4159256] using wordTrace_append hprefix tailTrace_4159256
  have hstable : (prefixWord ++ tailWord_4159256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159256).length < 2 ^ (prefixWord ++ tailWord_4159256).sum := by decide
  have hdescent : baseEnd_4159256 < baseStart_4159256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159258 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 3, 4]
def baseStart_4159258 : Nat := 118140960795 + 4159258 * 2 ^ 59
def prefixEnd_4159258 : Nat := 4983230072969 + 3 ^ 40 * 4159258 * 2
def baseEnd_4159258 : Nat := 1423799013372128745097951

theorem tailTrace_4159258 : CollatzResearch.WordTrace tailWord_4159258 prefixEnd_4159258 1423799013372128745097951 := by
  unfold tailWord_4159258
  simp only [CollatzResearch.WordTrace]
  refine ⟨37925150491431521389519607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101133734643817390372052285 37925150491431521389519607)
  ·
    refine ⟨56887725737147282084279411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37925150491431521389519607 56887725737147282084279411)
    ·
      refine ⟨85331588605720923126419117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56887725737147282084279411 85331588605720923126419117)
      ·
        refine ⟨31999345727145346172407169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85331588605720923126419117 31999345727145346172407169)
        ·
          refine ⟨23999509295359009629305377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31999345727145346172407169 23999509295359009629305377)
          ·
            refine ⟨17999631971519257221979033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23999509295359009629305377 17999631971519257221979033)
            ·
              refine ⟨13499723978639442916484275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17999631971519257221979033 13499723978639442916484275)
              ·
                refine ⟨20249585967959164374726413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13499723978639442916484275 20249585967959164374726413)
                ·
                  refine ⟨7593594737984686640522405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20249585967959164374726413 7593594737984686640522405)
                  ·
                    refine ⟨1423799013372128745097951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7593594737984686640522405 1423799013372128745097951)
                    ·
                      rfl

theorem cell22_4159258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_4159258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159258 prefixEnd_4159258 := by exact prefixLift 4159258
  have htrace : WordTrace (prefixWord ++ tailWord_4159258) baseStart_4159258 baseEnd_4159258 := by
    simpa [prefixWord, tailWord_4159258, baseEnd_4159258] using wordTrace_append hprefix tailTrace_4159258
  have hstable : (prefixWord ++ tailWord_4159258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159258).length < 2 ^ (prefixWord ++ tailWord_4159258).sum := by decide
  have hdescent : baseEnd_4159258 < baseStart_4159258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159290 : List Nat := [3, 1, 1, 1, 5, 1, 2, 4, 4]
def baseStart_4159290 : Nat := 118140960795 + 4159290 * 2 ^ 59
def prefixEnd_4159290 : Nat := 4983230072969 + 3 ^ 40 * 4159290 * 2
def baseEnd_4159290 : Nat := 474603322542030442765951

theorem tailTrace_4159290 : CollatzResearch.WordTrace tailWord_4159290 prefixEnd_4159290 474603322542030442765951 := by
  unfold tailWord_4159290
  simp only [CollatzResearch.WordTrace]
  refine ⟨37925442275402538755810831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101134512734406770015495549 37925442275402538755810831)
  ·
    refine ⟨56888163413103808133716247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37925442275402538755810831 56888163413103808133716247)
    ·
      refine ⟨85332245119655712200574371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56888163413103808133716247 85332245119655712200574371)
      ·
        refine ⟨127998367679483568300861557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85332245119655712200574371 127998367679483568300861557)
        ·
          refine ⟨11999846969951584528205771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127998367679483568300861557 11999846969951584528205771)
          ·
            refine ⟨17999770454927376792308657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11999846969951584528205771 17999770454927376792308657)
            ·
              refine ⟨13499827841195532594231493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17999770454927376792308657 13499827841195532594231493)
              ·
                refine ⟨2531217720224162361418405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13499827841195532594231493 2531217720224162361418405)
                ·
                  refine ⟨474603322542030442765951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2531217720224162361418405 474603322542030442765951)
                  ·
                    rfl

theorem cell22_4159290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_4159290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159290 prefixEnd_4159290 := by exact prefixLift 4159290
  have htrace : WordTrace (prefixWord ++ tailWord_4159290) baseStart_4159290 baseEnd_4159290 := by
    simpa [prefixWord, tailWord_4159290, baseEnd_4159290] using wordTrace_append hprefix tailTrace_4159290
  have hstable : (prefixWord ++ tailWord_4159290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159290).length < 2 ^ (prefixWord ++ tailWord_4159290).sum := by decide
  have hdescent : baseEnd_4159290 < baseStart_4159290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159301 : List Nat := [1, 3, 1, 1, 1, 2, 4, 9]
def baseStart_4159301 : Nat := 118140960795 + 4159301 * 2 ^ 59
def prefixEnd_4159301 : Nat := 4983230072969 + 3 ^ 40 * 4159301 * 2
def baseEnd_4159301 : Nat := 158201525905654551808091

theorem tailTrace_4159301 : CollatzResearch.WordTrace tailWord_4159301 prefixEnd_4159301 158201525905654551808091 := by
  unfold tailWord_4159301
  simp only [CollatzResearch.WordTrace]
  refine ⟨151702170304570303901893757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101134780203046869267929171 151702170304570303901893757)
  ·
    refine ⟨56888313864213863963210159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151702170304570303901893757 56888313864213863963210159)
    ·
      refine ⟨85332470796320795944815239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56888313864213863963210159 85332470796320795944815239)
      ·
        refine ⟨127998706194481193917222859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85332470796320795944815239 127998706194481193917222859)
        ·
          refine ⟨191998059291721790875834289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127998706194481193917222859 191998059291721790875834289)
          ·
            refine ⟨143998544468791343156875717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191998059291721790875834289 143998544468791343156875717)
            ·
              refine ⟨26999727087898376841914197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143998544468791343156875717 26999727087898376841914197)
              ·
                refine ⟨158201525905654551808091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26999727087898376841914197 158201525905654551808091)
                ·
                  rfl

theorem cell22_4159301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 9].length) (baseStart_4159301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159301 prefixEnd_4159301 := by exact prefixLift 4159301
  have htrace : WordTrace (prefixWord ++ tailWord_4159301) baseStart_4159301 baseEnd_4159301 := by
    simpa [prefixWord, tailWord_4159301, baseEnd_4159301] using wordTrace_append hprefix tailTrace_4159301
  have hstable : (prefixWord ++ tailWord_4159301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159301).length < 2 ^ (prefixWord ++ tailWord_4159301).sum := by decide
  have hdescent : baseEnd_4159301 < baseStart_4159301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159324 : List Nat := [2, 2, 4, 2, 2, 2, 1, 3, 4]
def baseStart_4159324 : Nat := 118140960795 + 4159324 * 2 ^ 59
def prefixEnd_4159324 : Nat := 4983230072969 + 3 ^ 40 * 4159324 * 2
def baseEnd_4159324 : Nat := 474607202173642190982583

theorem tailTrace_4159324 : CollatzResearch.WordTrace tailWord_4159324 prefixEnd_4159324 474607202173642190982583 := by
  unfold tailWord_4159324
  simp only [CollatzResearch.WordTrace]
  refine ⟨75851504591743489414990513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101135339455657985886654017 75851504591743489414990513)
  ·
    refine ⟨56888628443807617061242885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75851504591743489414990513 56888628443807617061242885)
    ·
      refine ⟨10666617833213928198983041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56888628443807617061242885 10666617833213928198983041)
      ·
        refine ⟨7999963374910446149237281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10666617833213928198983041 7999963374910446149237281)
        ·
          refine ⟨5999972531182834611927961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7999963374910446149237281 5999972531182834611927961)
          ·
            refine ⟨4499979398387125958945971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5999972531182834611927961 4499979398387125958945971)
            ·
              refine ⟨6749969097580688938418957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4499979398387125958945971 6749969097580688938418957)
              ·
                refine ⟨2531238411592758351907109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6749969097580688938418957 2531238411592758351907109)
                ·
                  refine ⟨474607202173642190982583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2531238411592758351907109 474607202173642190982583)
                  ·
                    rfl

theorem cell22_4159324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_4159324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159324 prefixEnd_4159324 := by exact prefixLift 4159324
  have htrace : WordTrace (prefixWord ++ tailWord_4159324) baseStart_4159324 baseEnd_4159324 := by
    simpa [prefixWord, tailWord_4159324, baseEnd_4159324] using wordTrace_append hprefix tailTrace_4159324
  have hstable : (prefixWord ++ tailWord_4159324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159324).length < 2 ^ (prefixWord ++ tailWord_4159324).sum := by decide
  have hdescent : baseEnd_4159324 < baseStart_4159324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159457 : List Nat := [1, 2, 3, 1, 2, 1, 5, 2, 2, 3]
def baseStart_4159457 : Nat := 118140960795 + 4159457 * 2 ^ 59
def prefixEnd_4159457 : Nat := 4983230072969 + 3 ^ 40 * 4159457 * 2
def baseEnd_4159457 : Nat := 1423867135138958559372341

theorem tailTrace_4159457 : CollatzResearch.WordTrace tailWord_4159457 prefixEnd_4159457 1423867135138958559372341 := by
  unfold tailWord_4159457
  simp only [CollatzResearch.WordTrace]
  refine ⟨151707860092005142544572625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101138573394670095029715083 151707860092005142544572625)
  ·
    refine ⟨113780895069003856908429469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151707860092005142544572625 113780895069003856908429469)
    ·
      refine ⟨42667835650876446340661051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113780895069003856908429469 42667835650876446340661051)
      ·
        refine ⟨64001753476314669510991577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42667835650876446340661051 64001753476314669510991577)
        ·
          refine ⟨48001315107236002133243683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64001753476314669510991577 48001315107236002133243683)
          ·
            refine ⟨72001972660854003199865525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48001315107236002133243683 72001972660854003199865525)
            ·
              refine ⟨6750184936955062799987393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72001972660854003199865525 6750184936955062799987393)
              ·
                refine ⟨5062638702716297099990545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6750184936955062799987393 5062638702716297099990545)
                ·
                  refine ⟨3796979027037222824992909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5062638702716297099990545 3796979027037222824992909)
                  ·
                    refine ⟨1423867135138958559372341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3796979027037222824992909 1423867135138958559372341)
                    ·
                      rfl

theorem cell22_4159457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_4159457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159457 prefixEnd_4159457 := by exact prefixLift 4159457
  have htrace : WordTrace (prefixWord ++ tailWord_4159457) baseStart_4159457 baseEnd_4159457 := by
    simpa [prefixWord, tailWord_4159457, baseEnd_4159457] using wordTrace_append hprefix tailTrace_4159457
  have hstable : (prefixWord ++ tailWord_4159457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159457).length < 2 ^ (prefixWord ++ tailWord_4159457).sum := by decide
  have hdescent : baseEnd_4159457 < baseStart_4159457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159483 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 2, 6]
def baseStart_4159483 : Nat := 118140960795 + 4159483 * 2 ^ 59
def prefixEnd_4159483 : Nat := 4983230072969 + 3 ^ 40 * 4159483 * 2
def baseEnd_4159483 : Nat := 1423876035470303158222261

theorem tailTrace_4159483 : CollatzResearch.WordTrace tailWord_4159483 prefixEnd_4159483 1423876035470303158222261 := by
  unfold tailWord_4159483
  simp only [CollatzResearch.WordTrace]
  refine ⟨151708808389910948985019103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101139205593273965990012735 151708808389910948985019103)
  ·
    refine ⟨227563212584866423477528655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151708808389910948985019103 227563212584866423477528655)
    ·
      refine ⟨341344818877299635216292983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227563212584866423477528655 341344818877299635216292983)
      ·
        refine ⟨512017228315949452824439475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341344818877299635216292983 512017228315949452824439475)
        ·
          refine ⟨768025842473924179236659213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512017228315949452824439475 768025842473924179236659213)
          ·
            refine ⟨288009690927721567213747205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 768025842473924179236659213 288009690927721567213747205)
            ·
              refine ⟨54001817048947793852577601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288009690927721567213747205 54001817048947793852577601)
              ·
                refine ⟨40501362786710845389433201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54001817048947793852577601 40501362786710845389433201)
                ·
                  refine ⟨30376022090033134042074901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40501362786710845389433201 30376022090033134042074901)
                  ·
                    refine ⟨1423876035470303158222261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30376022090033134042074901 1423876035470303158222261)
                    ·
                      rfl

theorem cell22_4159483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 6].length) (baseStart_4159483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159483 prefixEnd_4159483 := by exact prefixLift 4159483
  have htrace : WordTrace (prefixWord ++ tailWord_4159483) baseStart_4159483 baseEnd_4159483 := by
    simpa [prefixWord, tailWord_4159483, baseEnd_4159483] using wordTrace_append hprefix tailTrace_4159483
  have hstable : (prefixWord ++ tailWord_4159483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159483).length < 2 ^ (prefixWord ++ tailWord_4159483).sum := by decide
  have hdescent : baseEnd_4159483 < baseStart_4159483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159570 : List Nat := [3, 2, 2, 1, 5, 1, 2, 2, 1, 3]
def baseStart_4159570 : Nat := 118140960795 + 4159570 * 2 ^ 59
def prefixEnd_4159570 : Nat := 4983230072969 + 3 ^ 40 * 4159570 * 2
def baseEnd_4159570 : Nat := 1423905817348263931296995

theorem tailTrace_4159570 : CollatzResearch.WordTrace tailWord_4159570 prefixEnd_4159570 1423905817348263931296995 := by
  unfold tailWord_4159570
  simp only [CollatzResearch.WordTrace]
  refine ⟨37927995385148940710859041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101141321027063841895624109 37927995385148940710859041)
  ·
    refine ⟨28445996538861705533144281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37927995385148940710859041 28445996538861705533144281)
    ·
      refine ⟨21334497404146279149858211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28445996538861705533144281 21334497404146279149858211)
      ·
        refine ⟨32001746106219418724787317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21334497404146279149858211 32001746106219418724787317)
        ·
          refine ⟨3000163697458070505448811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32001746106219418724787317 3000163697458070505448811)
          ·
            refine ⟨4500245546187105758173217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3000163697458070505448811 4500245546187105758173217)
            ·
              refine ⟨3375184159640329318629913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4500245546187105758173217 3375184159640329318629913)
              ·
                refine ⟨2531388119730246988972435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3375184159640329318629913 2531388119730246988972435)
                ·
                  refine ⟨3797082179595370483458653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2531388119730246988972435 3797082179595370483458653)
                  ·
                    refine ⟨1423905817348263931296995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3797082179595370483458653 1423905817348263931296995)
                    ·
                      rfl

theorem cell22_4159570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_4159570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159570 prefixEnd_4159570 := by exact prefixLift 4159570
  have htrace : WordTrace (prefixWord ++ tailWord_4159570) baseStart_4159570 baseEnd_4159570 := by
    simpa [prefixWord, tailWord_4159570, baseEnd_4159570] using wordTrace_append hprefix tailTrace_4159570
  have hstable : (prefixWord ++ tailWord_4159570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159570).length < 2 ^ (prefixWord ++ tailWord_4159570).sum := by decide
  have hdescent : baseEnd_4159570 < baseStart_4159570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159577 : List Nat := [1, 2, 1, 2, 2, 1, 5, 4, 4]
def baseStart_4159577 : Nat := 118140960795 + 4159577 * 2 ^ 59
def prefixEnd_4159577 : Nat := 4983230072969 + 3 ^ 40 * 4159577 * 2
def baseEnd_4159577 : Nat := 474636071197106082123991

theorem tailTrace_4159577 : CollatzResearch.WordTrace tailWord_4159577 prefixEnd_4159577 474636071197106082123991 := by
  unfold tailWord_4159577
  simp only [CollatzResearch.WordTrace]
  refine ⟨151712236851570403038940985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101141491234380268692627323 151712236851570403038940985)
  ·
    refine ⟨113784177638677802279205739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151712236851570403038940985 113784177638677802279205739)
    ·
      refine ⟨170676266458016703418808609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113784177638677802279205739 170676266458016703418808609)
      ·
        refine ⟨128007199843512527564106457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170676266458016703418808609 128007199843512527564106457)
        ·
          refine ⟨96005399882634395673079843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128007199843512527564106457 96005399882634395673079843)
          ·
            refine ⟨144008099823951593509619765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96005399882634395673079843 144008099823951593509619765)
            ·
              refine ⟨13500759358495461891526853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144008099823951593509619765 13500759358495461891526853)
              ·
                refine ⟨2531392379717899104661285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13500759358495461891526853 2531392379717899104661285)
                ·
                  refine ⟨474636071197106082123991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2531392379717899104661285 474636071197106082123991)
                  ·
                    rfl

theorem cell22_4159577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 4].length) (baseStart_4159577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159577 prefixEnd_4159577 := by exact prefixLift 4159577
  have htrace : WordTrace (prefixWord ++ tailWord_4159577) baseStart_4159577 baseEnd_4159577 := by
    simpa [prefixWord, tailWord_4159577, baseEnd_4159577] using wordTrace_append hprefix tailTrace_4159577
  have hstable : (prefixWord ++ tailWord_4159577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159577).length < 2 ^ (prefixWord ++ tailWord_4159577).sum := by decide
  have hdescent : baseEnd_4159577 < baseStart_4159577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159607 : List Nat := [1, 1, 3, 1, 1, 5, 3, 1, 2, 4]
def baseStart_4159607 : Nat := 118140960795 + 4159607 * 2 ^ 59
def prefixEnd_4159607 : Nat := 4983230072969 + 3 ^ 40 * 4159607 * 2
def baseEnd_4159607 : Nat := 1423918483204408168121881

theorem tailTrace_4159607 : CollatzResearch.WordTrace tailWord_4159607 prefixEnd_4159607 1423918483204408168121881 := by
  unfold tailWord_4159607
  simp only [CollatzResearch.WordTrace]
  refine ⟨151713331041461718162533075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101142220694307812108355383 151713331041461718162533075)
  ·
    refine ⟨227569996562192577243799613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151713331041461718162533075 227569996562192577243799613)
    ·
      refine ⟨85338748710822216466424855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227569996562192577243799613 85338748710822216466424855)
      ·
        refine ⟨128008123066233324699637283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85338748710822216466424855 128008123066233324699637283)
        ·
          refine ⟨192012184599349987049455925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128008123066233324699637283 192012184599349987049455925)
          ·
            refine ⟨18001142306189061285886493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192012184599349987049455925 18001142306189061285886493)
            ·
              refine ⟨6750428364820897982207435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18001142306189061285886493 6750428364820897982207435)
              ·
                refine ⟨10125642547231346973311153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6750428364820897982207435 10125642547231346973311153)
                ·
                  refine ⟨7594231910423510229983365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10125642547231346973311153 7594231910423510229983365)
                  ·
                    refine ⟨1423918483204408168121881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7594231910423510229983365 1423918483204408168121881)
                    ·
                      rfl

theorem cell22_4159607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_4159607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159607 prefixEnd_4159607 := by exact prefixLift 4159607
  have htrace : WordTrace (prefixWord ++ tailWord_4159607) baseStart_4159607 baseEnd_4159607 := by
    simpa [prefixWord, tailWord_4159607, baseEnd_4159607] using wordTrace_append hprefix tailTrace_4159607
  have hstable : (prefixWord ++ tailWord_4159607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159607).length < 2 ^ (prefixWord ++ tailWord_4159607).sum := by decide
  have hdescent : baseEnd_4159607 < baseStart_4159607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159626 : List Nat := [3, 1, 2, 3, 1, 4, 1, 2, 2, 3]
def baseStart_4159626 : Nat := 118140960795 + 4159626 * 2 ^ 59
def prefixEnd_4159626 : Nat := 4983230072969 + 3 ^ 40 * 4159626 * 2
def baseEnd_4159626 : Nat := 1423924987292698451896823

theorem tailTrace_4159626 : CollatzResearch.WordTrace tailWord_4159626 prefixEnd_4159626 1423924987292698451896823 := by
  unfold tailWord_4159626
  simp only [CollatzResearch.WordTrace]
  refine ⟨37928506007098221101868683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101142682685595256271649821 37928506007098221101868683)
  ·
    refine ⟨56892759010647331652803025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37928506007098221101868683 56892759010647331652803025)
    ·
      refine ⟨42669569257985498739602269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56892759010647331652803025 42669569257985498739602269)
      ·
        refine ⟨16001088471744562027350851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42669569257985498739602269 16001088471744562027350851)
        ·
          refine ⟨24001632707616843041026277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16001088471744562027350851 24001632707616843041026277)
          ·
            refine ⟨4500306132678158070192427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24001632707616843041026277 4500306132678158070192427)
            ·
              refine ⟨6750459199017237105288641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4500306132678158070192427 6750459199017237105288641)
              ·
                refine ⟨5062844399262927828966481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6750459199017237105288641 5062844399262927828966481)
                ·
                  refine ⟨3797133299447195871724861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5062844399262927828966481 3797133299447195871724861)
                  ·
                    refine ⟨1423924987292698451896823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3797133299447195871724861 1423924987292698451896823)
                    ·
                      rfl

theorem cell22_4159626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_4159626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159626 prefixEnd_4159626 := by exact prefixLift 4159626
  have htrace : WordTrace (prefixWord ++ tailWord_4159626) baseStart_4159626 baseEnd_4159626 := by
    simpa [prefixWord, tailWord_4159626, baseEnd_4159626] using wordTrace_append hprefix tailTrace_4159626
  have hstable : (prefixWord ++ tailWord_4159626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159626).length < 2 ^ (prefixWord ++ tailWord_4159626).sum := by decide
  have hdescent : baseEnd_4159626 < baseStart_4159626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159671 : List Nat := [1, 1, 3, 1, 4, 2, 3, 3, 1, 3]
def baseStart_4159671 : Nat := 118140960795 + 4159671 * 2 ^ 59
def prefixEnd_4159671 : Nat := 4983230072969 + 3 ^ 40 * 4159671 * 2
def baseEnd_4159671 : Nat := 1423940391712333334521685

theorem tailTrace_4159671 : CollatzResearch.WordTrace tailWord_4159671 prefixEnd_4159671 1423940391712333334521685 := by
  unfold tailWord_4159671
  simp only [CollatzResearch.WordTrace]
  refine ⟨151715665313229857092862867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101143776875486571395241911 151715665313229857092862867)
  ·
    refine ⟨227573497969844785639294301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151715665313229857092862867 227573497969844785639294301)
    ·
      refine ⟨85340061738691794614735363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227573497969844785639294301 85340061738691794614735363)
      ·
        refine ⟨128010092608037691922103045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85340061738691794614735363 128010092608037691922103045)
        ·
          refine ⟨24001892364007067235394321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128010092608037691922103045 24001892364007067235394321)
          ·
            refine ⟨18001419273005300426545741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24001892364007067235394321 18001419273005300426545741)
            ·
              refine ⟨6750532227376987659954653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18001419273005300426545741 6750532227376987659954653)
              ·
                refine ⟨2531449585266370372482995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6750532227376987659954653 2531449585266370372482995)
                ·
                  refine ⟨3797174377899555558724493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2531449585266370372482995 3797174377899555558724493)
                  ·
                    refine ⟨1423940391712333334521685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3797174377899555558724493 1423940391712333334521685)
                    ·
                      rfl

theorem cell22_4159671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 1, 3].length) (baseStart_4159671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159671 prefixEnd_4159671 := by exact prefixLift 4159671
  have htrace : WordTrace (prefixWord ++ tailWord_4159671) baseStart_4159671 baseEnd_4159671 := by
    simpa [prefixWord, tailWord_4159671, baseEnd_4159671] using wordTrace_append hprefix tailTrace_4159671
  have hstable : (prefixWord ++ tailWord_4159671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159671).length < 2 ^ (prefixWord ++ tailWord_4159671).sum := by decide
  have hdescent : baseEnd_4159671 < baseStart_4159671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159727 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 3, 5]
def baseStart_4159727 : Nat := 118140960795 + 4159727 * 2 ^ 59
def prefixEnd_4159727 : Nat := 4983230072969 + 3 ^ 40 * 4159727 * 2
def baseEnd_4159727 : Nat := 1423959561656767855121513

theorem tailTrace_4159727 : CollatzResearch.WordTrace tailWord_4159727 prefixEnd_4159727 1423959561656767855121513 := by
  unfold tailWord_4159727
  simp only [CollatzResearch.WordTrace]
  refine ⟨151717707801026978656901435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101145138534017985771267623 151717707801026978656901435)
  ·
    refine ⟨227576561701540467985352153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151717707801026978656901435 227576561701540467985352153)
    ·
      refine ⟨170682421276155350989014115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227576561701540467985352153 170682421276155350989014115)
      ·
        refine ⟨256023631914233026483521173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170682421276155350989014115 256023631914233026483521173)
        ·
          refine ⟨12001107745979673116415055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 256023631914233026483521173 12001107745979673116415055)
          ·
            refine ⟨18001661618969509674622583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12001107745979673116415055 18001661618969509674622583)
            ·
              refine ⟨27002492428454264511933875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18001661618969509674622583 27002492428454264511933875)
              ·
                refine ⟨40503738642681396767900813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27002492428454264511933875 40503738642681396767900813)
                ·
                  refine ⟨15188901991005523787962805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40503738642681396767900813 15188901991005523787962805)
                  ·
                    refine ⟨1423959561656767855121513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15188901991005523787962805 1423959561656767855121513)
                    ·
                      rfl

theorem cell22_4159727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_4159727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159727 prefixEnd_4159727 := by exact prefixLift 4159727
  have htrace : WordTrace (prefixWord ++ tailWord_4159727) baseStart_4159727 baseEnd_4159727 := by
    simpa [prefixWord, tailWord_4159727, baseEnd_4159727] using wordTrace_append hprefix tailTrace_4159727
  have hstable : (prefixWord ++ tailWord_4159727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159727).length < 2 ^ (prefixWord ++ tailWord_4159727).sum := by decide
  have hdescent : baseEnd_4159727 < baseStart_4159727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159744 : List Nat := [2, 1, 1, 2, 1, 1, 5, 4, 2, 3]
def baseStart_4159744 : Nat := 118140960795 + 4159744 * 2 ^ 59
def prefixEnd_4159744 : Nat := 4983230072969 + 3 ^ 40 * 4159744 * 2
def baseEnd_4159744 : Nat := 1423965381104185477446461

theorem tailTrace_4159744 : CollatzResearch.WordTrace tailWord_4159744 prefixEnd_4159744 1423965381104185477446461 := by
  unfold tailWord_4159744
  simp only [CollatzResearch.WordTrace]
  refine ⟨75859163920982695280135143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101145551894643593706846857 75859163920982695280135143)
  ·
    refine ⟨113788745881474042920202715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75859163920982695280135143 113788745881474042920202715)
    ·
      refine ⟨170683118822211064380304073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113788745881474042920202715 170683118822211064380304073)
      ·
        refine ⟨128012339116658298285228055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170683118822211064380304073 128012339116658298285228055)
        ·
          refine ⟨192018508674987447427842083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128012339116658298285228055 192018508674987447427842083)
          ·
            refine ⟨288027763012481171141763125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192018508674987447427842083 288027763012481171141763125)
            ·
              refine ⟨27002602782420109794540293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 288027763012481171141763125 27002602782420109794540293)
              ·
                refine ⟨5062988021703770586476305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27002602782420109794540293 5062988021703770586476305)
                ·
                  refine ⟨3797241016277827939857229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5062988021703770586476305 3797241016277827939857229)
                  ·
                    refine ⟨1423965381104185477446461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3797241016277827939857229 1423965381104185477446461)
                    ·
                      rfl

theorem cell22_4159744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 2, 3].length) (baseStart_4159744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159744 prefixEnd_4159744 := by exact prefixLift 4159744
  have htrace : WordTrace (prefixWord ++ tailWord_4159744) baseStart_4159744 baseEnd_4159744 := by
    simpa [prefixWord, tailWord_4159744, baseEnd_4159744] using wordTrace_append hprefix tailTrace_4159744
  have hstable : (prefixWord ++ tailWord_4159744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159744).length < 2 ^ (prefixWord ++ tailWord_4159744).sum := by decide
  have hdescent : baseEnd_4159744 < baseStart_4159744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159776 : List Nat := [2, 1, 1, 5, 2, 3, 1, 1, 2, 4]
def baseStart_4159776 : Nat := 118140960795 + 4159776 * 2 ^ 59
def prefixEnd_4159776 : Nat := 4983230072969 + 3 ^ 40 * 4159776 * 2
def baseEnd_4159776 : Nat := 1423976335358148060646363

theorem tailTrace_4159776 : CollatzResearch.WordTrace tailWord_4159776 prefixEnd_4159776 1423976335358148060646363 := by
  unfold tailWord_4159776
  simp only [CollatzResearch.WordTrace]
  refine ⟨75859747488924730012717591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101146329985232973350290121 75859747488924730012717591)
  ·
    refine ⟨113789621233387095019076387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75859747488924730012717591 113789621233387095019076387)
    ·
      refine ⟨170684431850080642528614581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113789621233387095019076387 170684431850080642528614581)
      ·
        refine ⟨16001665485945060237057617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170684431850080642528614581 16001665485945060237057617)
        ·
          refine ⟨12001249114458795177793213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16001665485945060237057617 12001249114458795177793213)
          ·
            refine ⟨4500468417922048191672455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12001249114458795177793213 4500468417922048191672455)
            ·
              refine ⟨6750702626883072287508683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4500468417922048191672455 6750702626883072287508683)
              ·
                refine ⟨10126053940324608431263025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6750702626883072287508683 10126053940324608431263025)
                ·
                  refine ⟨7594540455243456323447269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10126053940324608431263025 7594540455243456323447269)
                  ·
                    refine ⟨1423976335358148060646363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7594540455243456323447269 1423976335358148060646363)
                    ·
                      rfl

theorem cell22_4159776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 2, 4].length) (baseStart_4159776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159776 prefixEnd_4159776 := by exact prefixLift 4159776
  have htrace : WordTrace (prefixWord ++ tailWord_4159776) baseStart_4159776 baseEnd_4159776 := by
    simpa [prefixWord, tailWord_4159776, baseEnd_4159776] using wordTrace_append hprefix tailTrace_4159776
  have hstable : (prefixWord ++ tailWord_4159776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159776).length < 2 ^ (prefixWord ++ tailWord_4159776).sum := by decide
  have hdescent : baseEnd_4159776 < baseStart_4159776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159806 : List Nat := [4, 2, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_4159806 : Nat := 118140960795 + 4159806 * 2 ^ 59
def prefixEnd_4159806 : Nat := 4983230072969 + 3 ^ 40 * 4159806 * 2
def baseEnd_4159806 : Nat := 1423986604971237982396271

theorem tailTrace_4159806 : CollatzResearch.WordTrace tailWord_4159806 prefixEnd_4159806 1423986604971237982396271 := by
  unfold tailWord_4159806
  simp only [CollatzResearch.WordTrace]
  refine ⟨18965073645967596893628409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101147059445160516766018181 18965073645967596893628409)
  ·
    refine ⟨14223805234475697670221307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18965073645967596893628409 14223805234475697670221307)
    ·
      refine ⟨21335707851713546505331961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14223805234475697670221307 21335707851713546505331961)
      ·
        refine ⟨16001780888785159878998971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21335707851713546505331961 16001780888785159878998971)
        ·
          refine ⟨24002671333177739818498457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16001780888785159878998971 24002671333177739818498457)
          ·
            refine ⟨18002003499883304863873843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24002671333177739818498457 18002003499883304863873843)
            ·
              refine ⟨27003005249824957295810765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18002003499883304863873843 27003005249824957295810765)
              ·
                refine ⟨10126126968684358985929037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27003005249824957295810765 10126126968684358985929037)
                ·
                  refine ⟨3797297613256634619723389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10126126968684358985929037 3797297613256634619723389)
                  ·
                    refine ⟨1423986604971237982396271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3797297613256634619723389 1423986604971237982396271)
                    ·
                      rfl

theorem cell22_4159806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_4159806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159806 prefixEnd_4159806 := by exact prefixLift 4159806
  have htrace : WordTrace (prefixWord ++ tailWord_4159806) baseStart_4159806 baseEnd_4159806 := by
    simpa [prefixWord, tailWord_4159806, baseEnd_4159806] using wordTrace_append hprefix tailTrace_4159806
  have hstable : (prefixWord ++ tailWord_4159806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159806).length < 2 ^ (prefixWord ++ tailWord_4159806).sum := by decide
  have hdescent : baseEnd_4159806 < baseStart_4159806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159840 : List Nat := [2, 1, 1, 3, 5, 2, 1, 3, 1, 3]
def baseStart_4159840 : Nat := 118140960795 + 4159840 * 2 ^ 59
def prefixEnd_4159840 : Nat := 4983230072969 + 3 ^ 40 * 4159840 * 2
def baseEnd_4159840 : Nat := 1423998243866073227046167

theorem tailTrace_4159840 : CollatzResearch.WordTrace tailWord_4159840 prefixEnd_4159840 1423998243866073227046167 := by
  unfold tailWord_4159840
  simp only [CollatzResearch.WordTrace]
  refine ⟨75860914624808799477882487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101147886166411732637176649 75860914624808799477882487)
  ·
    refine ⟨113791371937213199216823731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75860914624808799477882487 113791371937213199216823731)
    ·
      refine ⟨170687057905819798825235597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113791371937213199216823731 170687057905819798825235597)
      ·
        refine ⟨64007646714682424559463349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170687057905819798825235597 64007646714682424559463349)
        ·
          refine ⟨6000716879501477302449689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64007646714682424559463349 6000716879501477302449689)
          ·
            refine ⟨4500537659626107976837267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6000716879501477302449689 4500537659626107976837267)
            ·
              refine ⟨6750806489439161965255901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4500537659626107976837267 6750806489439161965255901)
              ·
                refine ⟨2531552433539685736970963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6750806489439161965255901 2531552433539685736970963)
                ·
                  refine ⟨3797328650309528605456445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2531552433539685736970963 3797328650309528605456445)
                  ·
                    refine ⟨1423998243866073227046167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3797328650309528605456445 1423998243866073227046167)
                    ·
                      rfl

theorem cell22_4159840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 1, 3].length) (baseStart_4159840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159840 prefixEnd_4159840 := by exact prefixLift 4159840
  have htrace : WordTrace (prefixWord ++ tailWord_4159840) baseStart_4159840 baseEnd_4159840 := by
    simpa [prefixWord, tailWord_4159840, baseEnd_4159840] using wordTrace_append hprefix tailTrace_4159840
  have hstable : (prefixWord ++ tailWord_4159840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159840).length < 2 ^ (prefixWord ++ tailWord_4159840).sum := by decide
  have hdescent : baseEnd_4159840 < baseStart_4159840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159849 : List Nat := [1, 2, 1, 1, 1, 3, 3, 5, 1, 4]
def baseStart_4159849 : Nat := 118140960795 + 4159849 * 2 ^ 59
def prefixEnd_4159849 : Nat := 4983230072969 + 3 ^ 40 * 4159849 * 2
def baseEnd_4159849 : Nat := 1424001324750000203571139

theorem tailTrace_4159849 : CollatzResearch.WordTrace tailWord_4159849 prefixEnd_4159849 1424001324750000203571139 := by
  unfold tailWord_4159849
  simp only [CollatzResearch.WordTrace]
  refine ⟨151722157506584993492842601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101148105004389995661895067 151722157506584993492842601)
  ·
    refine ⟨113791618129938745119631951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151722157506584993492842601 113791618129938745119631951)
    ·
      refine ⟨170687427194908117679447927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113791618129938745119631951 170687427194908117679447927)
      ·
        refine ⟨256031140792362176519171891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170687427194908117679447927 256031140792362176519171891)
        ·
          refine ⟨384046711188543264778757837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256031140792362176519171891 384046711188543264778757837)
          ·
            refine ⟨144017516695703724292034189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384046711188543264778757837 144017516695703724292034189)
            ·
              refine ⟨54006568760888896609512821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144017516695703724292034189 54006568760888896609512821)
              ·
                refine ⟨5063115821333334057141827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54006568760888896609512821 5063115821333334057141827)
                ·
                  refine ⟨7594673732000001085712741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5063115821333334057141827 7594673732000001085712741)
                  ·
                    refine ⟨1424001324750000203571139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7594673732000001085712741 1424001324750000203571139)
                    ·
                      rfl

theorem cell22_4159849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 4].length) (baseStart_4159849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159849 prefixEnd_4159849 := by exact prefixLift 4159849
  have htrace : WordTrace (prefixWord ++ tailWord_4159849) baseStart_4159849 baseEnd_4159849 := by
    simpa [prefixWord, tailWord_4159849, baseEnd_4159849] using wordTrace_append hprefix tailTrace_4159849
  have hstable : (prefixWord ++ tailWord_4159849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159849).length < 2 ^ (prefixWord ++ tailWord_4159849).sum := by decide
  have hdescent : baseEnd_4159849 < baseStart_4159849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159879 : List Nat := [1, 1, 4, 2, 2, 1, 2, 3, 1, 5]
def baseStart_4159879 : Nat := 118140960795 + 4159879 * 2 ^ 59
def prefixEnd_4159879 : Nat := 4983230072969 + 3 ^ 40 * 4159879 * 2
def baseEnd_4159879 : Nat := 1424011594363090125321047

theorem tailTrace_4159879 : CollatzResearch.WordTrace tailWord_4159879 prefixEnd_4159879 1424011594363090125321047 := by
  unfold tailWord_4159879
  simp only [CollatzResearch.WordTrace]
  refine ⟨151723251696476308616434691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101148834464317539077623127 151723251696476308616434691)
  ·
    refine ⟨227584877544714462924652037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151723251696476308616434691 227584877544714462924652037)
    ·
      refine ⟨42672164539633961798372257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227584877544714462924652037 42672164539633961798372257)
      ·
        refine ⟨32004123404725471348779193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42672164539633961798372257 32004123404725471348779193)
        ·
          refine ⟨24003092553544103511584395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32004123404725471348779193 24003092553544103511584395)
          ·
            refine ⟨36004638830316155267376593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24003092553544103511584395 36004638830316155267376593)
            ·
              refine ⟨27003479122737116450532445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36004638830316155267376593 27003479122737116450532445)
              ·
                refine ⟨10126304671026418668949667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27003479122737116450532445 10126304671026418668949667)
                ·
                  refine ⟨15189457006539628003424501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10126304671026418668949667 15189457006539628003424501)
                  ·
                    refine ⟨1424011594363090125321047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15189457006539628003424501 1424011594363090125321047)
                    ·
                      rfl

theorem cell22_4159879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_4159879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159879 prefixEnd_4159879 := by exact prefixLift 4159879
  have htrace : WordTrace (prefixWord ++ tailWord_4159879) baseStart_4159879 baseEnd_4159879 := by
    simpa [prefixWord, tailWord_4159879, baseEnd_4159879] using wordTrace_append hprefix tailTrace_4159879
  have hstable : (prefixWord ++ tailWord_4159879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159879).length < 2 ^ (prefixWord ++ tailWord_4159879).sum := by decide
  have hdescent : baseEnd_4159879 < baseStart_4159879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159896 : List Nat := [2, 1, 2, 5, 1, 2, 1, 2, 1, 5]
def baseStart_4159896 : Nat := 118140960795 + 4159896 * 2 ^ 59
def prefixEnd_4159896 : Nat := 4983230072969 + 3 ^ 40 * 4159896 * 2
def baseEnd_4159896 : Nat := 1424017413810507747645995

theorem tailTrace_4159896 : CollatzResearch.WordTrace tailWord_4159896 prefixEnd_4159896 1424017413810507747645995 := by
  unfold tailWord_4159896
  simp only [CollatzResearch.WordTrace]
  refine ⟨75861935868707360259901771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101149247824943147013202361 75861935868707360259901771)
  ·
    refine ⟨113792903803061040389852657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75861935868707360259901771 113792903803061040389852657)
    ·
      refine ⟨85344677852295780292389493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113792903803061040389852657 85344677852295780292389493)
      ·
        refine ⟨8001063548652729402411515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85344677852295780292389493 8001063548652729402411515)
        ·
          refine ⟨12001595322979094103617273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8001063548652729402411515 12001595322979094103617273)
          ·
            refine ⟨9001196492234320577712955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12001595322979094103617273 9001196492234320577712955)
            ·
              refine ⟨13501794738351480866569433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9001196492234320577712955 13501794738351480866569433)
              ·
                refine ⟨10126346053763610649927075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13501794738351480866569433 10126346053763610649927075)
                ·
                  refine ⟨15189519080645415974890613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10126346053763610649927075 15189519080645415974890613)
                  ·
                    refine ⟨1424017413810507747645995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15189519080645415974890613 1424017413810507747645995)
                    ·
                      rfl

theorem cell22_4159896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_4159896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159896 prefixEnd_4159896 := by exact prefixLift 4159896
  have htrace : WordTrace (prefixWord ++ tailWord_4159896) baseStart_4159896 baseEnd_4159896 := by
    simpa [prefixWord, tailWord_4159896, baseEnd_4159896] using wordTrace_append hprefix tailTrace_4159896
  have hstable : (prefixWord ++ tailWord_4159896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159896).length < 2 ^ (prefixWord ++ tailWord_4159896).sum := by decide
  have hdescent : baseEnd_4159896 < baseStart_4159896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159911 : List Nat := [1, 1, 6, 1, 1, 2, 2, 2, 2, 4]
def baseStart_4159911 : Nat := 118140960795 + 4159911 * 2 ^ 59
def prefixEnd_4159911 : Nat := 4983230072969 + 3 ^ 40 * 4159911 * 2
def baseEnd_4159911 : Nat := 1424022548617052708520949

theorem tailTrace_4159911 : CollatzResearch.WordTrace tailWord_4159911 prefixEnd_4159911 1424022548617052708520949 := by
  unfold tailWord_4159911
  simp only [CollatzResearch.WordTrace]
  refine ⟨151724418832360378081599587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101149612554906918721066391 151724418832360378081599587)
  ·
    refine ⟨227586628248540567122399381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151724418832360378081599587 227586628248540567122399381)
    ·
      refine ⟨10668123199150339083862471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 227586628248540567122399381 10668123199150339083862471)
      ·
        refine ⟨16002184798725508625793707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10668123199150339083862471 16002184798725508625793707)
        ·
          refine ⟨24003277198088262938690561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16002184798725508625793707 24003277198088262938690561)
          ·
            refine ⟨18002457898566197204017921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24003277198088262938690561 18002457898566197204017921)
            ·
              refine ⟨13501843423924647903013441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18002457898566197204017921 13501843423924647903013441)
              ·
                refine ⟨10126382567943485927260081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13501843423924647903013441 10126382567943485927260081)
                ·
                  refine ⟨7594786925957614445445061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10126382567943485927260081 7594786925957614445445061)
                  ·
                    refine ⟨1424022548617052708520949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7594786925957614445445061 1424022548617052708520949)
                    ·
                      rfl

theorem cell22_4159911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_4159911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159911 prefixEnd_4159911 := by exact prefixLift 4159911
  have htrace : WordTrace (prefixWord ++ tailWord_4159911) baseStart_4159911 baseEnd_4159911 := by
    simpa [prefixWord, tailWord_4159911, baseEnd_4159911] using wordTrace_append hprefix tailTrace_4159911
  have hstable : (prefixWord ++ tailWord_4159911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159911).length < 2 ^ (prefixWord ++ tailWord_4159911).sum := by decide
  have hdescent : baseEnd_4159911 < baseStart_4159911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159958 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_4159958 : Nat := 118140960795 + 4159958 * 2 ^ 59
def prefixEnd_4159958 : Nat := 4983230072969 + 3 ^ 40 * 4159958 * 2
def baseEnd_4159958 : Nat := 1424038637677560252595805

theorem tailTrace_4159958 : CollatzResearch.WordTrace tailWord_4159958 prefixEnd_4159958 1424038637677560252595805 := by
  unfold tailWord_4159958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9482883316449381569285033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101150755375460070072373685 9482883316449381569285033)
  ·
    refine ⟨7112162487337036176963775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9482883316449381569285033 7112162487337036176963775)
    ·
      refine ⟨10668243731005554265445663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7112162487337036176963775 10668243731005554265445663)
      ·
        refine ⟨16002365596508331398168495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10668243731005554265445663 16002365596508331398168495)
        ·
          refine ⟨24003548394762497097252743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16002365596508331398168495 24003548394762497097252743)
          ·
            refine ⟨36005322592143745645879115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24003548394762497097252743 36005322592143745645879115)
            ·
              refine ⟨54007983888215618468818673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36005322592143745645879115 54007983888215618468818673)
              ·
                refine ⟨40505987916161713851614005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54007983888215618468818673 40505987916161713851614005)
                ·
                  refine ⟨3797436367140160673588813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40505987916161713851614005 3797436367140160673588813)
                  ·
                    refine ⟨1424038637677560252595805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3797436367140160673588813 1424038637677560252595805)
                    ·
                      rfl

theorem cell22_4159958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_4159958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159958 prefixEnd_4159958 := by exact prefixLift 4159958
  have htrace : WordTrace (prefixWord ++ tailWord_4159958) baseStart_4159958 baseEnd_4159958 := by
    simpa [prefixWord, tailWord_4159958, baseEnd_4159958] using wordTrace_append hprefix tailTrace_4159958
  have hstable : (prefixWord ++ tailWord_4159958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159958).length < 2 ^ (prefixWord ++ tailWord_4159958).sum := by decide
  have hdescent : baseEnd_4159958 < baseStart_4159958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159969 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 4, 5]
def baseStart_4159969 : Nat := 118140960795 + 4159969 * 2 ^ 59
def prefixEnd_4159969 : Nat := 4983230072969 + 3 ^ 40 * 4159969 * 2
def baseEnd_4159969 : Nat := 1424042403202359890570771

theorem tailTrace_4159969 : CollatzResearch.WordTrace tailWord_4159969 prefixEnd_4159969 1424042403202359890570771 := by
  unfold tailWord_4159969
  simp only [CollatzResearch.WordTrace]
  refine ⟨151726534266150253987210961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101151022844100169324807307 151726534266150253987210961)
  ·
    refine ⟨113794900699612690490408221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151726534266150253987210961 113794900699612690490408221)
    ·
      refine ⟨42673087762354758933903083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113794900699612690490408221 42673087762354758933903083)
      ·
        refine ⟨64009631643532138400854625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42673087762354758933903083 64009631643532138400854625)
        ·
          refine ⟨48007223732649103800640969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64009631643532138400854625 48007223732649103800640969)
          ·
            refine ⟨36005417799486827850480727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48007223732649103800640969 36005417799486827850480727)
            ·
              refine ⟨54008126699230241775721091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36005417799486827850480727 54008126699230241775721091)
              ·
                refine ⟨81012190048845362663581637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54008126699230241775721091 81012190048845362663581637)
                ·
                  refine ⟨15189785634158505499421557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81012190048845362663581637 15189785634158505499421557)
                  ·
                    refine ⟨1424042403202359890570771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15189785634158505499421557 1424042403202359890570771)
                    ·
                      rfl

theorem cell22_4159969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_4159969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159969 prefixEnd_4159969 := by exact prefixLift 4159969
  have htrace : WordTrace (prefixWord ++ tailWord_4159969) baseStart_4159969 baseEnd_4159969 := by
    simpa [prefixWord, tailWord_4159969, baseEnd_4159969] using wordTrace_append hprefix tailTrace_4159969
  have hstable : (prefixWord ++ tailWord_4159969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159969).length < 2 ^ (prefixWord ++ tailWord_4159969).sum := by decide
  have hdescent : baseEnd_4159969 < baseStart_4159969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159971 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 7]
def baseStart_4159971 : Nat := 118140960795 + 4159971 * 2 ^ 59
def prefixEnd_4159971 : Nat := 4983230072969 + 3 ^ 40 * 4159971 * 2
def baseEnd_4159971 : Nat := 474681029281077517340255

theorem tailTrace_4159971 : CollatzResearch.WordTrace tailWord_4159971 prefixEnd_4159971 474681029281077517340255 := by
  unfold tailWord_4159971
  simp only [CollatzResearch.WordTrace]
  refine ⟨151726607212143008328783767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101151071474762005552522511 151726607212143008328783767)
  ·
    refine ⟨227589910818214512493175651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151726607212143008328783767 227589910818214512493175651)
    ·
      refine ⟨341384866227321768739763477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227589910818214512493175651 341384866227321768739763477)
      ·
        refine ⟨16002415604405707909676413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 341384866227321768739763477 16002415604405707909676413)
        ·
          refine ⟨6000905851652140466128655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16002415604405707909676413 6000905851652140466128655)
          ·
            refine ⟨9001358777478210699192983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6000905851652140466128655 9001358777478210699192983)
            ·
              refine ⟨13502038166217316048789475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9001358777478210699192983 13502038166217316048789475)
              ·
                refine ⟨20253057249325974073184213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13502038166217316048789475 20253057249325974073184213)
                ·
                  refine ⟨474681029281077517340255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20253057249325974073184213 474681029281077517340255)
                  ·
                    rfl

theorem cell22_4159971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 7].length) (baseStart_4159971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159971 prefixEnd_4159971 := by exact prefixLift 4159971
  have htrace : WordTrace (prefixWord ++ tailWord_4159971) baseStart_4159971 baseEnd_4159971 := by
    simpa [prefixWord, tailWord_4159971, baseEnd_4159971] using wordTrace_append hprefix tailTrace_4159971
  have hstable : (prefixWord ++ tailWord_4159971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159971).length < 2 ^ (prefixWord ++ tailWord_4159971).sum := by decide
  have hdescent : baseEnd_4159971 < baseStart_4159971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159999 : List Nat := [1, 1, 2, 2, 1, 2, 3, 4, 6]
def baseStart_4159999 : Nat := 118140960795 + 4159999 * 2 ^ 59
def prefixEnd_4159999 : Nat := 4983230072969 + 3 ^ 40 * 4159999 * 2
def baseEnd_4159999 : Nat := 474684224271816604106893

theorem tailTrace_4159999 : CollatzResearch.WordTrace tailWord_4159999 prefixEnd_4159999 474684224271816604106893 := by
  unfold tailWord_4159999
  simp only [CollatzResearch.WordTrace]
  refine ⟨151727628456041569110803051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101151752304027712740535367 151727628456041569110803051)
  ·
    refine ⟨227591442684062353666204577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151727628456041569110803051 227591442684062353666204577)
    ·
      refine ⟨170693582013046765249653433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227591442684062353666204577 170693582013046765249653433)
      ·
        refine ⟨128020186509785073937240075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170693582013046765249653433 128020186509785073937240075)
        ·
          refine ⟨192030279764677610905860113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128020186509785073937240075 192030279764677610905860113)
          ·
            refine ⟨144022709823508208179395085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192030279764677610905860113 144022709823508208179395085)
            ·
              refine ⟨54008516183815578067273157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144022709823508208179395085 54008516183815578067273157)
              ·
                refine ⟨10126596784465420887613717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54008516183815578067273157 10126596784465420887613717)
                ·
                  refine ⟨474684224271816604106893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10126596784465420887613717 474684224271816604106893)
                  ·
                    rfl

theorem cell22_4159999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 6].length) (baseStart_4159999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4159999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4159999 prefixEnd_4159999 := by exact prefixLift 4159999
  have htrace : WordTrace (prefixWord ++ tailWord_4159999) baseStart_4159999 baseEnd_4159999 := by
    simpa [prefixWord, tailWord_4159999, baseEnd_4159999] using wordTrace_append hprefix tailTrace_4159999
  have hstable : (prefixWord ++ tailWord_4159999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159999).length < 2 ^ (prefixWord ++ tailWord_4159999).sum := by decide
  have hdescent : baseEnd_4159999 < baseStart_4159999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160039 : List Nat := [1, 1, 7, 2, 2, 1, 2, 1, 5]
def baseStart_4160039 : Nat := 118140960795 + 4160039 * 2 ^ 59
def prefixEnd_4160039 : Nat := 4983230072969 + 3 ^ 40 * 4160039 * 2
def baseEnd_4160039 : Nat := 474688788544301013773519

theorem tailTrace_4160039 : CollatzResearch.WordTrace tailWord_4160039 prefixEnd_4160039 474688788544301013773519 := by
  unfold tailWord_4160039
  simp only [CollatzResearch.WordTrace]
  refine ⟨151729087375896655942259171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101152724917264437294839447 151729087375896655942259171)
  ·
    refine ⟨227593631063844983913388757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151729087375896655942259171 227593631063844983913388757)
    ·
      refine ⟨5334225728058866810470049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 227593631063844983913388757 5334225728058866810470049)
      ·
        refine ⟨4000669296044150107852537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5334225728058866810470049 4000669296044150107852537)
        ·
          refine ⟨3000501972033112580889403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4000669296044150107852537 3000501972033112580889403)
          ·
            refine ⟨4500752958049668871334105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3000501972033112580889403 4500752958049668871334105)
            ·
              refine ⟨3375564718537251653500579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4500752958049668871334105 3375564718537251653500579)
              ·
                refine ⟨5063347077805877480250869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3375564718537251653500579 5063347077805877480250869)
                ·
                  refine ⟨474688788544301013773519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5063347077805877480250869 474688788544301013773519)
                  ·
                    rfl

theorem cell22_4160039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 5].length) (baseStart_4160039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160039 prefixEnd_4160039 := by exact prefixLift 4160039
  have htrace : WordTrace (prefixWord ++ tailWord_4160039) baseStart_4160039 baseEnd_4160039 := by
    simpa [prefixWord, tailWord_4160039, baseEnd_4160039] using wordTrace_append hprefix tailTrace_4160039
  have hstable : (prefixWord ++ tailWord_4160039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160039).length < 2 ^ (prefixWord ++ tailWord_4160039).sum := by decide
  have hdescent : baseEnd_4160039 < baseStart_4160039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160061 : List Nat := [1, 4, 1, 3, 2, 1, 2, 8]
def baseStart_4160061 : Nat := 118140960795 + 4160061 * 2 ^ 59
def prefixEnd_4160061 : Nat := 4983230072969 + 3 ^ 40 * 4160061 * 2
def baseEnd_4160061 : Nat := 158230432964722479696721

theorem tailTrace_4160061 : CollatzResearch.WordTrace tailWord_4160061 prefixEnd_4160061 158230432964722479696721 := by
  unfold tailWord_4160061
  simp only [CollatzResearch.WordTrace]
  refine ⟨151729889781816953699560037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101153259854544635799706691 151729889781816953699560037)
  ·
    refine ⟨28449354334090678818667507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151729889781816953699560037 28449354334090678818667507)
    ·
      refine ⟨42674031501136018228001261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28449354334090678818667507 42674031501136018228001261)
      ·
        refine ⟨16002761812926006835500473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42674031501136018228001261 16002761812926006835500473)
        ·
          refine ⟨12002071359694505126625355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16002761812926006835500473 12002071359694505126625355)
          ·
            refine ⟨18003107039541757689938033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12002071359694505126625355 18003107039541757689938033)
            ·
              refine ⟨13502330279656318267453525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18003107039541757689938033 13502330279656318267453525)
              ·
                refine ⟨158230432964722479696721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13502330279656318267453525 158230432964722479696721)
                ·
                  rfl

theorem cell22_4160061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 8].length) (baseStart_4160061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160061 prefixEnd_4160061 := by exact prefixLift 4160061
  have htrace : WordTrace (prefixWord ++ tailWord_4160061) baseStart_4160061 baseEnd_4160061 := by
    simpa [prefixWord, tailWord_4160061, baseEnd_4160061] using wordTrace_append hprefix tailTrace_4160061
  have hstable : (prefixWord ++ tailWord_4160061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160061).length < 2 ^ (prefixWord ++ tailWord_4160061).sum := by decide
  have hdescent : baseEnd_4160061 < baseStart_4160061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160110 : List Nat := [4, 1, 2, 2, 2, 2, 1, 2, 3, 3]
def baseStart_4160110 : Nat := 118140960795 + 4160110 * 2 ^ 59
def prefixEnd_4160110 : Nat := 4983230072969 + 3 ^ 40 * 4160110 * 2
def baseEnd_4160110 : Nat := 1424090670383882522795339

theorem tailTrace_4160110 : CollatzResearch.WordTrace tailWord_4160110 prefixEnd_4160110 1424090670383882522795339 := by
  unfold tailWord_4160110
  simp only [CollatzResearch.WordTrace]
  refine ⟨18966459619829929383511723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101154451305759623378729189 18966459619829929383511723)
  ·
    refine ⟨28449689429744894075267585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18966459619829929383511723 28449689429744894075267585)
    ·
      refine ⟨21337267072308670556450689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28449689429744894075267585 21337267072308670556450689)
      ·
        refine ⟨16002950304231502917338017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21337267072308670556450689 16002950304231502917338017)
        ·
          refine ⟨12002212728173627188003513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16002950304231502917338017 12002212728173627188003513)
          ·
            refine ⟨9001659546130220391002635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12002212728173627188003513 9001659546130220391002635)
            ·
              refine ⟨13502489319195330586503953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9001659546130220391002635 13502489319195330586503953)
              ·
                refine ⟨10126866989396497939877965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13502489319195330586503953 10126866989396497939877965)
                ·
                  refine ⟨3797575121023686727454237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10126866989396497939877965 3797575121023686727454237)
                  ·
                    refine ⟨1424090670383882522795339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3797575121023686727454237 1424090670383882522795339)
                    ·
                      rfl

theorem cell22_4160110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_4160110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160110 prefixEnd_4160110 := by exact prefixLift 4160110
  have htrace : WordTrace (prefixWord ++ tailWord_4160110) baseStart_4160110 baseEnd_4160110 := by
    simpa [prefixWord, tailWord_4160110, baseEnd_4160110] using wordTrace_append hprefix tailTrace_4160110
  have hstable : (prefixWord ++ tailWord_4160110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160110).length < 2 ^ (prefixWord ++ tailWord_4160110).sum := by decide
  have hdescent : baseEnd_4160110 < baseStart_4160110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160202 : List Nat := [3, 1, 2, 1, 4, 2, 3, 2, 4]
def baseStart_4160202 : Nat := 118140960795 + 4160202 * 2 ^ 59
def prefixEnd_4160202 : Nat := 4983230072969 + 3 ^ 40 * 4160202 * 2
def baseEnd_4160202 : Nat := 474707387954674983165019

theorem tailTrace_4160202 : CollatzResearch.WordTrace tailWord_4160202 prefixEnd_4160202 474707387954674983165019 := by
  unfold tailWord_4160202
  simp only [CollatzResearch.WordTrace]
  refine ⟨37933758118576533695110715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101156688316204089853628573 37933758118576533695110715)
  ·
    refine ⟨56900637177864800542666073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37933758118576533695110715 56900637177864800542666073)
    ·
      refine ⟨42675477883398600406999555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56900637177864800542666073 42675477883398600406999555)
      ·
        refine ⟨64013216825097900610499333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42675477883398600406999555 64013216825097900610499333)
        ·
          refine ⟨12002478154705856364468625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64013216825097900610499333 12002478154705856364468625)
          ·
            refine ⟨9001858616029392273351469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12002478154705856364468625 9001858616029392273351469)
            ·
              refine ⟨3375696981011022102506801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9001858616029392273351469 3375696981011022102506801)
              ·
                refine ⟨2531772735758266576880101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3375696981011022102506801 2531772735758266576880101)
                ·
                  refine ⟨474707387954674983165019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2531772735758266576880101 474707387954674983165019)
                  ·
                    rfl

theorem cell22_4160202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_4160202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160202 prefixEnd_4160202 := by exact prefixLift 4160202
  have htrace : WordTrace (prefixWord ++ tailWord_4160202) baseStart_4160202 baseEnd_4160202 := by
    simpa [prefixWord, tailWord_4160202, baseEnd_4160202] using wordTrace_append hprefix tailTrace_4160202
  have hstable : (prefixWord ++ tailWord_4160202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160202).length < 2 ^ (prefixWord ++ tailWord_4160202).sum := by decide
  have hdescent : baseEnd_4160202 < baseStart_4160202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160305 : List Nat := [1, 2, 2, 3, 2, 1, 3, 3, 1, 4]
def baseStart_4160305 : Nat := 118140960795 + 4160305 * 2 ^ 59
def prefixEnd_4160305 : Nat := 4983230072969 + 3 ^ 40 * 4160305 * 2
def baseEnd_4160305 : Nat := 1424157422868967014169741

theorem tailTrace_4160305 : CollatzResearch.WordTrace tailWord_4160305 prefixEnd_4160305 1424157422868967014169741 := by
  unfold tailWord_4160305
  simp only [CollatzResearch.WordTrace]
  refine ⟨151738789192932983371442369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101159192795288655580961579 151738789192932983371442369)
  ·
    refine ⟨113804091894699737528581777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151738789192932983371442369 113804091894699737528581777)
    ·
      refine ⟨85353068921024803146436333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113804091894699737528581777 85353068921024803146436333)
      ·
        refine ⟨32007400845384301179913625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85353068921024803146436333 32007400845384301179913625)
        ·
          refine ⟨24005550634038225884935219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32007400845384301179913625 24005550634038225884935219)
          ·
            refine ⟨36008325951057338827402829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24005550634038225884935219 36008325951057338827402829)
            ·
              refine ⟨13503122231646502060276061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36008325951057338827402829 13503122231646502060276061)
              ·
                refine ⟨5063670836867438272603523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13503122231646502060276061 5063670836867438272603523)
                ·
                  refine ⟨7595506255301157408905285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5063670836867438272603523 7595506255301157408905285)
                  ·
                    refine ⟨1424157422868967014169741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7595506255301157408905285 1424157422868967014169741)
                    ·
                      rfl

theorem cell22_4160305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_4160305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160305 prefixEnd_4160305 := by exact prefixLift 4160305
  have htrace : WordTrace (prefixWord ++ tailWord_4160305) baseStart_4160305 baseEnd_4160305 := by
    simpa [prefixWord, tailWord_4160305, baseEnd_4160305] using wordTrace_append hprefix tailTrace_4160305
  have hstable : (prefixWord ++ tailWord_4160305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160305).length < 2 ^ (prefixWord ++ tailWord_4160305).sum := by decide
  have hdescent : baseEnd_4160305 < baseStart_4160305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160326 : List Nat := [6, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_4160326 : Nat := 118140960795 + 4160326 * 2 ^ 59
def prefixEnd_4160326 : Nat := 4983230072969 + 3 ^ 40 * 4160326 * 2
def baseEnd_4160326 : Nat := 474721537199376653131559

theorem tailTrace_4160326 : CollatzResearch.WordTrace tailWord_4160326 prefixEnd_4160326 474721537199376653131559 := by
  unfold tailWord_4160326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4741861097683028248686151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101159703417237935971971221 4741861097683028248686151)
  ·
    refine ⟨7112791646524542373029227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4741861097683028248686151 7112791646524542373029227)
    ·
      refine ⟨10669187469786813559543841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7112791646524542373029227 10669187469786813559543841)
      ·
        refine ⟨8001890602340110169657881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10669187469786813559543841 8001890602340110169657881)
        ·
          refine ⟨6001417951755082627243411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8001890602340110169657881 6001417951755082627243411)
          ·
            refine ⟨9002126927632623940865117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6001417951755082627243411 9002126927632623940865117)
            ·
              refine ⟨3375797597862233977824419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9002126927632623940865117 3375797597862233977824419)
              ·
                refine ⟨5063696396793350966736629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3375797597862233977824419 5063696396793350966736629)
                ·
                  refine ⟨474721537199376653131559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5063696396793350966736629 474721537199376653131559)
                  ·
                    rfl

theorem cell22_4160326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_4160326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160326 prefixEnd_4160326 := by exact prefixLift 4160326
  have htrace : WordTrace (prefixWord ++ tailWord_4160326) baseStart_4160326 baseEnd_4160326 := by
    simpa [prefixWord, tailWord_4160326, baseEnd_4160326] using wordTrace_append hprefix tailTrace_4160326
  have hstable : (prefixWord ++ tailWord_4160326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160326).length < 2 ^ (prefixWord ++ tailWord_4160326).sum := by decide
  have hdescent : baseEnd_4160326 < baseStart_4160326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160378 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 2, 6]
def baseStart_4160378 : Nat := 118140960795 + 4160378 * 2 ^ 59
def prefixEnd_4160378 : Nat := 4983230072969 + 3 ^ 40 * 4160378 * 2
def baseEnd_4160378 : Nat := 1424182412260819157094517

theorem tailTrace_4160378 : CollatzResearch.WordTrace tailWord_4160378 prefixEnd_4160378 1424182412260819157094517 := by
  unfold tailWord_4160378
  simp only [CollatzResearch.WordTrace]
  refine ⟨37935362930417129209712447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101160967814445677892566525 37935362930417129209712447)
  ·
    refine ⟨56903044395625693814568671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37935362930417129209712447 56903044395625693814568671)
    ·
      refine ⟨85354566593438540721853007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56903044395625693814568671 85354566593438540721853007)
      ·
        refine ⟨128031849890157811082779511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85354566593438540721853007 128031849890157811082779511)
        ·
          refine ⟨192047774835236716624169267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128031849890157811082779511 192047774835236716624169267)
          ·
            refine ⟨288071662252855074936253901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192047774835236716624169267 288071662252855074936253901)
            ·
              refine ⟨108026873344820653101095213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288071662252855074936253901 108026873344820653101095213)
              ·
                refine ⟨40510077504307744912910705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108026873344820653101095213 40510077504307744912910705)
                ·
                  refine ⟨30382558128230808684683029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40510077504307744912910705 30382558128230808684683029)
                  ·
                    refine ⟨1424182412260819157094517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30382558128230808684683029 1424182412260819157094517)
                    ·
                      rfl

theorem cell22_4160378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_4160378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160378 prefixEnd_4160378 := by exact prefixLift 4160378
  have htrace : WordTrace (prefixWord ++ tailWord_4160378) baseStart_4160378 baseEnd_4160378 := by
    simpa [prefixWord, tailWord_4160378, baseEnd_4160378] using wordTrace_append hprefix tailTrace_4160378
  have hstable : (prefixWord ++ tailWord_4160378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160378).length < 2 ^ (prefixWord ++ tailWord_4160378).sum := by decide
  have hdescent : baseEnd_4160378 < baseStart_4160378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160440 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 3, 4]
def baseStart_4160440 : Nat := 118140960795 + 4160440 * 2 ^ 59
def prefixEnd_4160440 : Nat := 4983230072969 + 3 ^ 40 * 4160440 * 2
def baseEnd_4160440 : Nat := 1424203636127871662044327

theorem tailTrace_4160440 : CollatzResearch.WordTrace tailWord_4160440 prefixEnd_4160440 1424203636127871662044327 := by
  unfold tailWord_4160440
  simp only [CollatzResearch.WordTrace]
  refine ⟨75871856523721950713803387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101162475364962600951737849 75871856523721950713803387)
  ·
    refine ⟨113807784785582926070705081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75871856523721950713803387 113807784785582926070705081)
    ·
      refine ⟨85355838589187194553028811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113807784785582926070705081 85355838589187194553028811)
      ·
        refine ⟨128033757883780791829543217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85355838589187194553028811 128033757883780791829543217)
        ·
          refine ⟨96025318412835593872157413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128033757883780791829543217 96025318412835593872157413)
          ·
            refine ⟨18004747202406673851029515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96025318412835593872157413 18004747202406673851029515)
            ·
              refine ⟨27007120803610010776544273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18004747202406673851029515 27007120803610010776544273)
              ·
                refine ⟨20255340602707508082408205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27007120803610010776544273 20255340602707508082408205)
                ·
                  refine ⟨7595752726015315530903077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20255340602707508082408205 7595752726015315530903077)
                  ·
                    refine ⟨1424203636127871662044327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7595752726015315530903077 1424203636127871662044327)
                    ·
                      rfl

theorem cell22_4160440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_4160440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160440 prefixEnd_4160440 := by exact prefixLift 4160440
  have htrace : WordTrace (prefixWord ++ tailWord_4160440) baseStart_4160440 baseEnd_4160440 := by
    simpa [prefixWord, tailWord_4160440, baseEnd_4160440] using wordTrace_append hprefix tailTrace_4160440
  have hstable : (prefixWord ++ tailWord_4160440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160440).length < 2 ^ (prefixWord ++ tailWord_4160440).sum := by decide
  have hdescent : baseEnd_4160440 < baseStart_4160440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160472 : List Nat := [2, 1, 2, 2, 2, 3, 1, 5, 4]
def baseStart_4160472 : Nat := 118140960795 + 4160472 * 2 ^ 59
def prefixEnd_4160472 : Nat := 4983230072969 + 3 ^ 40 * 4160472 * 2
def baseEnd_4160472 : Nat := 474738196793944748414743

theorem tailTrace_4160472 : CollatzResearch.WordTrace tailWord_4160472 prefixEnd_4160472 474738196793944748414743 := by
  unfold tailWord_4160472
  simp only [CollatzResearch.WordTrace]
  refine ⟨75872440091663985446385835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101163253455551980595181113 75872440091663985446385835)
  ·
    refine ⟨113808660137495978169578753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75872440091663985446385835 113808660137495978169578753)
    ·
      refine ⟨85356495103121983627184065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113808660137495978169578753 85356495103121983627184065)
      ·
        refine ⟨64017371327341487720388049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85356495103121983627184065 64017371327341487720388049)
        ·
          refine ⟨48013028495506115790291037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64017371327341487720388049 48013028495506115790291037)
          ·
            refine ⟨18004885685814793421359139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48013028495506115790291037 18004885685814793421359139)
            ·
              refine ⟨27007328528722190132038709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18004885685814793421359139 27007328528722190132038709)
              ·
                refine ⟨2531937049567705324878629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27007328528722190132038709 2531937049567705324878629)
                ·
                  refine ⟨474738196793944748414743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2531937049567705324878629 474738196793944748414743)
                  ·
                    rfl

theorem cell22_4160472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 4].length) (baseStart_4160472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160472 prefixEnd_4160472 := by exact prefixLift 4160472
  have htrace : WordTrace (prefixWord ++ tailWord_4160472) baseStart_4160472 baseEnd_4160472 := by
    simpa [prefixWord, tailWord_4160472, baseEnd_4160472] using wordTrace_append hprefix tailTrace_4160472
  have hstable : (prefixWord ++ tailWord_4160472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160472).length < 2 ^ (prefixWord ++ tailWord_4160472).sum := by decide
  have hdescent : baseEnd_4160472 < baseStart_4160472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160474 : List Nat := [3, 1, 1, 2, 4, 1, 4, 1, 1, 4]
def baseStart_4160474 : Nat := 118140960795 + 4160474 * 2 ^ 59
def prefixEnd_4160474 : Nat := 4983230072969 + 3 ^ 40 * 4160474 * 2
def baseEnd_4160474 : Nat := 1424215275022706906694223

theorem tailTrace_4160474 : CollatzResearch.WordTrace tailWord_4160474 prefixEnd_4160474 1424215275022706906694223 := by
  unfold tailWord_4160474
  simp only [CollatzResearch.WordTrace]
  refine ⟨37936238282330181308586119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101163302086213816822896317 37936238282330181308586119)
  ·
    refine ⟨56904357423495271962879179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37936238282330181308586119 56904357423495271962879179)
    ·
      refine ⟨85356536135242907944318769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56904357423495271962879179 85356536135242907944318769)
      ·
        refine ⟨64017402101432180958239077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85356536135242907944318769 64017402101432180958239077)
        ·
          refine ⟨12003262894018533929669827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64017402101432180958239077 12003262894018533929669827)
          ·
            refine ⟨18004894341027800894504741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12003262894018533929669827 18004894341027800894504741)
            ·
              refine ⟨3375917688942712667719639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18004894341027800894504741 3375917688942712667719639)
              ·
                refine ⟨5063876533414069001579459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3375917688942712667719639 5063876533414069001579459)
                ·
                  refine ⟨7595814800121103502369189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5063876533414069001579459 7595814800121103502369189)
                  ·
                    refine ⟨1424215275022706906694223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7595814800121103502369189 1424215275022706906694223)
                    ·
                      rfl

theorem cell22_4160474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 1, 4].length) (baseStart_4160474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160474 prefixEnd_4160474 := by exact prefixLift 4160474
  have htrace : WordTrace (prefixWord ++ tailWord_4160474) baseStart_4160474 baseEnd_4160474 := by
    simpa [prefixWord, tailWord_4160474, baseEnd_4160474] using wordTrace_append hprefix tailTrace_4160474
  have hstable : (prefixWord ++ tailWord_4160474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160474).length < 2 ^ (prefixWord ++ tailWord_4160474).sum := by decide
  have hdescent : baseEnd_4160474 < baseStart_4160474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160502 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_4160502 : Nat := 118140960795 + 4160502 * 2 ^ 59
def prefixEnd_4160502 : Nat := 4983230072969 + 3 ^ 40 * 4160502 * 2
def baseEnd_4160502 : Nat := 1424224859994924166994137

theorem tailTrace_4160502 : CollatzResearch.WordTrace tailWord_4160502 prefixEnd_4160502 1424224859994924166994137 := by
  unfold tailWord_4160502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9484123398326205376022735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101163982915479524010909173 9484123398326205376022735)
  ·
    refine ⟨14226185097489308064034103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9484123398326205376022735 14226185097489308064034103)
    ·
      refine ⟨21339277646233962096051155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14226185097489308064034103 21339277646233962096051155)
      ·
        refine ⟨32008916469350943144076733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21339277646233962096051155 32008916469350943144076733)
        ·
          refine ⟨12003343676006603679028775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32008916469350943144076733 12003343676006603679028775)
          ·
            refine ⟨18005015514009905518543163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12003343676006603679028775 18005015514009905518543163)
            ·
              refine ⟨27007523271014858277814745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18005015514009905518543163 27007523271014858277814745)
              ·
                refine ⟨20255642453261143708361059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27007523271014858277814745 20255642453261143708361059)
                ·
                  refine ⟨30383463679891715562541589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20255642453261143708361059 30383463679891715562541589)
                  ·
                    refine ⟨1424224859994924166994137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30383463679891715562541589 1424224859994924166994137)
                    ·
                      rfl

theorem cell22_4160502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_4160502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160502 prefixEnd_4160502 := by exact prefixLift 4160502
  have htrace : WordTrace (prefixWord ++ tailWord_4160502) baseStart_4160502 baseEnd_4160502 := by
    simpa [prefixWord, tailWord_4160502, baseEnd_4160502] using wordTrace_append hprefix tailTrace_4160502
  have hstable : (prefixWord ++ tailWord_4160502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160502).length < 2 ^ (prefixWord ++ tailWord_4160502).sum := by decide
  have hdescent : baseEnd_4160502 < baseStart_4160502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160560 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 1, 7]
def baseStart_4160560 : Nat := 118140960795 + 4160560 * 2 ^ 59
def prefixEnd_4160560 : Nat := 4983230072969 + 3 ^ 40 * 4160560 * 2
def baseEnd_4160560 : Nat := 1424244714580231349043959

theorem tailTrace_4160560 : CollatzResearch.WordTrace tailWord_4160560 prefixEnd_4160560 1424244714580231349043959 := by
  unfold tailWord_4160560
  simp only [CollatzResearch.WordTrace]
  refine ⟨75874044903504580960987567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101165393204672774614650089 75874044903504580960987567)
  ·
    refine ⟨113811067355256871441481351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75874044903504580960987567 113811067355256871441481351)
    ·
      refine ⟨170716601032885307162222027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113811067355256871441481351 170716601032885307162222027)
      ·
        refine ⟨256074901549327960743333041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170716601032885307162222027 256074901549327960743333041)
        ·
          refine ⟨192056176161995970557499781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256074901549327960743333041 192056176161995970557499781)
          ·
            refine ⟨36010533030374244479531209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192056176161995970557499781 36010533030374244479531209)
            ·
              refine ⟨27007899772780683359648407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36010533030374244479531209 27007899772780683359648407)
              ·
                refine ⟨40511849659171025039472611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27007899772780683359648407 40511849659171025039472611)
                ·
                  refine ⟨60767774488756537559208917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40511849659171025039472611 60767774488756537559208917)
                  ·
                    refine ⟨1424244714580231349043959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60767774488756537559208917 1424244714580231349043959)
                    ·
                      rfl

theorem cell22_4160560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_4160560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160560 prefixEnd_4160560 := by exact prefixLift 4160560
  have htrace : WordTrace (prefixWord ++ tailWord_4160560) baseStart_4160560 baseEnd_4160560 := by
    simpa [prefixWord, tailWord_4160560, baseEnd_4160560] using wordTrace_append hprefix tailTrace_4160560
  have hstable : (prefixWord ++ tailWord_4160560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160560).length < 2 ^ (prefixWord ++ tailWord_4160560).sum := by decide
  have hdescent : baseEnd_4160560 < baseStart_4160560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160562 : List Nat := [3, 2, 1, 1, 2, 2, 3, 3, 5]
def baseStart_4160562 : Nat := 118140960795 + 4160562 * 2 ^ 59
def prefixEnd_4160562 : Nat := 4983230072969 + 3 ^ 40 * 4160562 * 2
def baseEnd_4160562 : Nat := 474748466407034670164651

theorem tailTrace_4160562 : CollatzResearch.WordTrace tailWord_4160562 prefixEnd_4160562 474748466407034670164651 := by
  unfold tailWord_4160562
  simp only [CollatzResearch.WordTrace]
  refine ⟨37937040688250479065886985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101165441835334610842365293 37937040688250479065886985)
  ·
    refine ⟨28452780516187859299415239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37937040688250479065886985 28452780516187859299415239)
    ·
      refine ⟨42679170774281788949122859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28452780516187859299415239 42679170774281788949122859)
      ·
        refine ⟨64018756161422683423684289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42679170774281788949122859 64018756161422683423684289)
        ·
          refine ⟨48014067121067012567763217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64018756161422683423684289 48014067121067012567763217)
          ·
            refine ⟨36010550340800259425822413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48014067121067012567763217 36010550340800259425822413)
            ·
              refine ⟨13503956377800097284683405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36010550340800259425822413 13503956377800097284683405)
              ·
                refine ⟨5063983641675036481756277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13503956377800097284683405 5063983641675036481756277)
                ·
                  refine ⟨474748466407034670164651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5063983641675036481756277 474748466407034670164651)
                  ·
                    rfl

theorem cell22_4160562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_4160562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160562 prefixEnd_4160562 := by exact prefixLift 4160562
  have htrace : WordTrace (prefixWord ++ tailWord_4160562) baseStart_4160562 baseEnd_4160562 := by
    simpa [prefixWord, tailWord_4160562, baseEnd_4160562] using wordTrace_append hprefix tailTrace_4160562
  have hstable : (prefixWord ++ tailWord_4160562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160562).length < 2 ^ (prefixWord ++ tailWord_4160562).sum := by decide
  have hdescent : baseEnd_4160562 < baseStart_4160562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160592 : List Nat := [2, 1, 1, 1, 1, 3, 1, 7, 1, 4]
def baseStart_4160592 : Nat := 118140960795 + 4160592 * 2 ^ 59
def prefixEnd_4160592 : Nat := 4983230072969 + 3 ^ 40 * 4160592 * 2
def baseEnd_4160592 : Nat := 1424255668834193932243861

theorem tailTrace_4160592 : CollatzResearch.WordTrace tailWord_4160592 prefixEnd_4160592 1424255668834193932243861 := by
  unfold tailWord_4160592
  simp only [CollatzResearch.WordTrace]
  refine ⟨75874628471446615693570015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101166171295262154258093353 75874628471446615693570015)
  ·
    refine ⟨113811942707169923540355023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75874628471446615693570015 113811942707169923540355023)
    ·
      refine ⟨170717914060754885310532535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113811942707169923540355023 170717914060754885310532535)
      ·
        refine ⟨256076871091132327965798803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170717914060754885310532535 256076871091132327965798803)
        ·
          refine ⟨384115306636698491948698205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256076871091132327965798803 384115306636698491948698205)
          ·
            refine ⟨144043239988761934480761827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384115306636698491948698205 144043239988761934480761827)
            ·
              refine ⟨216064859983142901721142741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144043239988761934480761827 216064859983142901721142741)
              ·
                refine ⟨5064020155854911759089283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 216064859983142901721142741 5064020155854911759089283)
                ·
                  refine ⟨7596030233782367638633925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5064020155854911759089283 7596030233782367638633925)
                  ·
                    refine ⟨1424255668834193932243861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7596030233782367638633925 1424255668834193932243861)
                    ·
                      rfl

theorem cell22_4160592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 1, 4].length) (baseStart_4160592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160592 prefixEnd_4160592 := by exact prefixLift 4160592
  have htrace : WordTrace (prefixWord ++ tailWord_4160592) baseStart_4160592 baseEnd_4160592 := by
    simpa [prefixWord, tailWord_4160592, baseEnd_4160592] using wordTrace_append hprefix tailTrace_4160592
  have hstable : (prefixWord ++ tailWord_4160592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160592).length < 2 ^ (prefixWord ++ tailWord_4160592).sum := by decide
  have hdescent : baseEnd_4160592 < baseStart_4160592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160635 : List Nat := [1, 1, 1, 1, 1, 4, 1, 12]
def baseStart_4160635 : Nat := 118140960795 + 4160635 * 2 ^ 59
def prefixEnd_4160635 : Nat := 4983230072969 + 3 ^ 40 * 4160635 * 2
def baseEnd_4160635 : Nat := 158252265401439572602081

theorem tailTrace_4160635 : CollatzResearch.WordTrace tailWord_4160635 prefixEnd_4160635 158252265401439572602081 := by
  unfold tailWord_4160635
  simp only [CollatzResearch.WordTrace]
  refine ⟨151750825281737449730955359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101167216854491633153970239 151750825281737449730955359)
  ·
    refine ⟨227626237922606174596433039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151750825281737449730955359 227626237922606174596433039)
    ·
      refine ⟨341439356883909261894649559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227626237922606174596433039 341439356883909261894649559)
      ·
        refine ⟨512159035325863892841974339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341439356883909261894649559 512159035325863892841974339)
        ·
          refine ⟨768238552988795839262961509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512159035325863892841974339 768238552988795839262961509)
          ·
            refine ⟨144044728685399219861805283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 768238552988795839262961509 144044728685399219861805283)
            ·
              refine ⟨216067093028098829792707925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144044728685399219861805283 216067093028098829792707925)
              ·
                refine ⟨158252265401439572602081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 216067093028098829792707925 158252265401439572602081)
                ·
                  rfl

theorem cell22_4160635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 12].length) (baseStart_4160635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160635 prefixEnd_4160635 := by exact prefixLift 4160635
  have htrace : WordTrace (prefixWord ++ tailWord_4160635) baseStart_4160635 baseEnd_4160635 := by
    simpa [prefixWord, tailWord_4160635, baseEnd_4160635] using wordTrace_append hprefix tailTrace_4160635
  have hstable : (prefixWord ++ tailWord_4160635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160635).length < 2 ^ (prefixWord ++ tailWord_4160635).sum := by decide
  have hdescent : baseEnd_4160635 < baseStart_4160635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160637 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_4160637 : Nat := 118140960795 + 4160637 * 2 ^ 59
def prefixEnd_4160637 : Nat := 4983230072969 + 3 ^ 40 * 4160637 * 2
def baseEnd_4160637 : Nat := 1424271073253828814868723

theorem tailTrace_4160637 : CollatzResearch.WordTrace tailWord_4160637 prefixEnd_4160637 1424271073253828814868723 := by
  unfold tailWord_4160637
  simp only [CollatzResearch.WordTrace]
  refine ⟨151750898227730204072528165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101167265485153469381685443 151750898227730204072528165)
  ·
    refine ⟨28453293417699413263599031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151750898227730204072528165 28453293417699413263599031)
    ·
      refine ⟨42679940126549119895398547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28453293417699413263599031 42679940126549119895398547)
      ·
        refine ⟨64019910189823679843097821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42679940126549119895398547 64019910189823679843097821)
        ·
          refine ⟨24007466321183879941161683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64019910189823679843097821 24007466321183879941161683)
          ·
            refine ⟨36011199481775819911742525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24007466321183879941161683 36011199481775819911742525)
            ·
              refine ⟨13504199805665932466903447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36011199481775819911742525 13504199805665932466903447)
              ·
                refine ⟨20256299708498898700355171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13504199805665932466903447 20256299708498898700355171)
                ·
                  refine ⟨30384449562748348050532757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20256299708498898700355171 30384449562748348050532757)
                  ·
                    refine ⟨1424271073253828814868723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30384449562748348050532757 1424271073253828814868723)
                    ·
                      rfl

theorem cell22_4160637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_4160637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160637 prefixEnd_4160637 := by exact prefixLift 4160637
  have htrace : WordTrace (prefixWord ++ tailWord_4160637) baseStart_4160637 baseEnd_4160637 := by
    simpa [prefixWord, tailWord_4160637, baseEnd_4160637] using wordTrace_append hprefix tailTrace_4160637
  have hstable : (prefixWord ++ tailWord_4160637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160637).length < 2 ^ (prefixWord ++ tailWord_4160637).sum := by decide
  have hdescent : baseEnd_4160637 < baseStart_4160637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160641 : List Nat := [1, 2, 4, 2, 2, 2, 2, 3, 4]
def baseStart_4160641 : Nat := 118140960795 + 4160641 * 2 ^ 59
def prefixEnd_4160641 : Nat := 4983230072969 + 3 ^ 40 * 4160641 * 2
def baseEnd_4160641 : Nat := 474757480845191379256237

theorem tailTrace_4160641 : CollatzResearch.WordTrace tailWord_4160641 prefixEnd_4160641 474757480845191379256237 := by
  unfold tailWord_4160641
  simp only [CollatzResearch.WordTrace]
  refine ⟨151751044119715712755673777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101167362746477141837115851 151751044119715712755673777)
  ·
    refine ⟨113813283089786784566755333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151751044119715712755673777 113813283089786784566755333)
    ·
      refine ⟨21339990579335022106266625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113813283089786784566755333 21339990579335022106266625)
      ·
        refine ⟨16004992934501266579699969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21339990579335022106266625 16004992934501266579699969)
        ·
          refine ⟨12003744700875949934774977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16004992934501266579699969 12003744700875949934774977)
          ·
            refine ⟨9002808525656962451081233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12003744700875949934774977 9002808525656962451081233)
            ·
              refine ⟨6752106394242721838310925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9002808525656962451081233 6752106394242721838310925)
              ·
                refine ⟨2532039897841020689366597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6752106394242721838310925 2532039897841020689366597)
                ·
                  refine ⟨474757480845191379256237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2532039897841020689366597 474757480845191379256237)
                  ·
                    rfl

theorem cell22_4160641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 4].length) (baseStart_4160641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160641 prefixEnd_4160641 := by exact prefixLift 4160641
  have htrace : WordTrace (prefixWord ++ tailWord_4160641) baseStart_4160641 baseEnd_4160641 := by
    simpa [prefixWord, tailWord_4160641, baseEnd_4160641] using wordTrace_append hprefix tailTrace_4160641
  have hstable : (prefixWord ++ tailWord_4160641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160641).length < 2 ^ (prefixWord ++ tailWord_4160641).sum := by decide
  have hdescent : baseEnd_4160641 < baseStart_4160641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160697 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 7]
def baseStart_4160697 : Nat := 118140960795 + 4160697 * 2 ^ 59
def prefixEnd_4160697 : Nat := 4983230072969 + 3 ^ 40 * 4160697 * 2
def baseEnd_4160697 : Nat := 474763870826669552789513

theorem tailTrace_4160697 : CollatzResearch.WordTrace tailWord_4160697 prefixEnd_4160697 474763870826669552789513 := by
  unfold tailWord_4160697
  simp only [CollatzResearch.WordTrace]
  refine ⟨151753086607512834319712345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101168724405008556213141563 151753086607512834319712345)
  ·
    refine ⟨113814814955634625739784259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151753086607512834319712345 113814814955634625739784259)
    ·
      refine ⟨170722222433451938609676389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113814814955634625739784259 170722222433451938609676389)
      ·
        refine ⟨32010416706272238489314323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170722222433451938609676389 32010416706272238489314323)
        ·
          refine ⟨48015625059408357733971485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32010416706272238489314323 48015625059408357733971485)
          ·
            refine ⟨18005859397278134150239307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48015625059408357733971485 18005859397278134150239307)
            ·
              refine ⟨27008789095917201225358961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18005859397278134150239307 27008789095917201225358961)
              ·
                refine ⟨20256591821937900919019221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27008789095917201225358961 20256591821937900919019221)
                ·
                  refine ⟨474763870826669552789513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20256591821937900919019221 474763870826669552789513)
                  ·
                    rfl

theorem cell22_4160697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 7].length) (baseStart_4160697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160697 prefixEnd_4160697 := by exact prefixLift 4160697
  have htrace : WordTrace (prefixWord ++ tailWord_4160697) baseStart_4160697 baseEnd_4160697 := by
    simpa [prefixWord, tailWord_4160697, baseEnd_4160697] using wordTrace_append hprefix tailTrace_4160697
  have hstable : (prefixWord ++ tailWord_4160697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160697).length < 2 ^ (prefixWord ++ tailWord_4160697).sum := by decide
  have hdescent : baseEnd_4160697 < baseStart_4160697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160712 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 4, 5]
def baseStart_4160712 : Nat := 118140960795 + 4160712 * 2 ^ 59
def prefixEnd_4160712 : Nat := 4983230072969 + 3 ^ 40 * 4160712 * 2
def baseEnd_4160712 : Nat := 1424296747286553619243493

theorem tailTrace_4160712 : CollatzResearch.WordTrace tailWord_4160712 prefixEnd_4160712 1424296747286553619243493 := by
  unfold tailWord_4160712
  simp only [CollatzResearch.WordTrace]
  refine ⟨75876816851229245940754195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101169089134972327921005593 75876816851229245940754195)
  ·
    refine ⟨113815225276843868911131293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75876816851229245940754195 113815225276843868911131293)
    ·
      refine ⟨42680709478816450841674235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113815225276843868911131293 42680709478816450841674235)
      ·
        refine ⟨64021064218224676262511353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42680709478816450841674235 64021064218224676262511353)
        ·
          refine ⟨48015798163668507196883515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64021064218224676262511353 48015798163668507196883515)
          ·
            refine ⟨72023697245502760795325273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48015798163668507196883515 72023697245502760795325273)
            ·
              refine ⟨54017772934127070596493955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72023697245502760795325273 54017772934127070596493955)
              ·
                refine ⟨81026659401190605894740933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54017772934127070596493955 81026659401190605894740933)
                ·
                  refine ⟨15192498637723238605263925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81026659401190605894740933 15192498637723238605263925)
                  ·
                    refine ⟨1424296747286553619243493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15192498637723238605263925 1424296747286553619243493)
                    ·
                      rfl

theorem cell22_4160712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_4160712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160712 prefixEnd_4160712 := by exact prefixLift 4160712
  have htrace : WordTrace (prefixWord ++ tailWord_4160712) baseStart_4160712 baseEnd_4160712 := by
    simpa [prefixWord, tailWord_4160712, baseEnd_4160712] using wordTrace_append hprefix tailTrace_4160712
  have hstable : (prefixWord ++ tailWord_4160712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160712).length < 2 ^ (prefixWord ++ tailWord_4160712).sum := by decide
  have hdescent : baseEnd_4160712 < baseStart_4160712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160718 : List Nat := [4, 1, 1, 1, 5, 2, 1, 1, 3, 3]
def baseStart_4160718 : Nat := 118140960795 + 4160718 * 2 ^ 59
def prefixEnd_4160718 : Nat := 4983230072969 + 3 ^ 40 * 4160718 * 2
def baseEnd_4160718 : Nat := 1424298801209171603593475

theorem tailTrace_4160718 : CollatzResearch.WordTrace tailWord_4160718 prefixEnd_4160718 1424298801209171603593475 := by
  unfold tailWord_4160718
  simp only [CollatzResearch.WordTrace]
  refine ⟨18969231567554594363278351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101169235026957836604151205 18969231567554594363278351)
  ·
    refine ⟨28453847351331891544917527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18969231567554594363278351 28453847351331891544917527)
    ·
      refine ⟨42680771026997837317376291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28453847351331891544917527 42680771026997837317376291)
      ·
        refine ⟨64021156540496755976064437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42680771026997837317376291 64021156540496755976064437)
        ·
          refine ⟨6001983425671570872756041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64021156540496755976064437 6001983425671570872756041)
          ·
            refine ⟨4501487569253678154567031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6001983425671570872756041 4501487569253678154567031)
            ·
              refine ⟨6752231353880517231850547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4501487569253678154567031 6752231353880517231850547)
              ·
                refine ⟨10128347030820775847775821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6752231353880517231850547 10128347030820775847775821)
                ·
                  refine ⟨3798130136557790942915933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10128347030820775847775821 3798130136557790942915933)
                  ·
                    refine ⟨1424298801209171603593475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3798130136557790942915933 1424298801209171603593475)
                    ·
                      rfl

theorem cell22_4160718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_4160718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160718 prefixEnd_4160718 := by exact prefixLift 4160718
  have htrace : WordTrace (prefixWord ++ tailWord_4160718) baseStart_4160718 baseEnd_4160718 := by
    simpa [prefixWord, tailWord_4160718, baseEnd_4160718] using wordTrace_append hprefix tailTrace_4160718
  have hstable : (prefixWord ++ tailWord_4160718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160718).length < 2 ^ (prefixWord ++ tailWord_4160718).sum := by decide
  have hdescent : baseEnd_4160718 < baseStart_4160718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160744 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 3, 4]
def baseStart_4160744 : Nat := 118140960795 + 4160744 * 2 ^ 59
def prefixEnd_4160744 : Nat := 4983230072969 + 3 ^ 40 * 4160744 * 2
def baseEnd_4160744 : Nat := 1424307701540516202443395

theorem tailTrace_4160744 : CollatzResearch.WordTrace tailWord_4160744 prefixEnd_4160744 1424307701540516202443395 := by
  unfold tailWord_4160744
  simp only [CollatzResearch.WordTrace]
  refine ⟨75877400419171280673336643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101169867225561707564448857 75877400419171280673336643)
  ·
    refine ⟨113816100628756921010004965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75877400419171280673336643 113816100628756921010004965)
    ·
      refine ⟨21340518867891922689375931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113816100628756921010004965 21340518867891922689375931)
      ·
        refine ⟨32010778301837884034063897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21340518867891922689375931 32010778301837884034063897)
        ·
          refine ⟨24008083726378413025547923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32010778301837884034063897 24008083726378413025547923)
          ·
            refine ⟨36012125589567619538321885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24008083726378413025547923 36012125589567619538321885)
            ·
              refine ⟨13504547096087857326870707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36012125589567619538321885 13504547096087857326870707)
              ·
                refine ⟨20256820644131785990306061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13504547096087857326870707 20256820644131785990306061)
                ·
                  refine ⟨7596307741549419746364773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20256820644131785990306061 7596307741549419746364773)
                  ·
                    refine ⟨1424307701540516202443395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7596307741549419746364773 1424307701540516202443395)
                    ·
                      rfl

theorem cell22_4160744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_4160744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160744 prefixEnd_4160744 := by exact prefixLift 4160744
  have htrace : WordTrace (prefixWord ++ tailWord_4160744) baseStart_4160744 baseEnd_4160744 := by
    simpa [prefixWord, tailWord_4160744, baseEnd_4160744] using wordTrace_append hprefix tailTrace_4160744
  have hstable : (prefixWord ++ tailWord_4160744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160744).length < 2 ^ (prefixWord ++ tailWord_4160744).sum := by decide
  have hdescent : baseEnd_4160744 < baseStart_4160744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160761 : List Nat := [1, 2, 1, 3, 1, 1, 7, 1, 1, 4]
def baseStart_4160761 : Nat := 118140960795 + 4160761 * 2 ^ 59
def prefixEnd_4160761 : Nat := 4983230072969 + 3 ^ 40 * 4160761 * 2
def baseEnd_4160761 : Nat := 1424313520987933824768343

theorem tailTrace_4160761 : CollatzResearch.WordTrace tailWord_4160761 prefixEnd_4160761 1424313520987933824768343 := by
  unfold tailWord_4160761
  simp only [CollatzResearch.WordTrace]
  refine ⟨151755420879280973250042137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101170280586187315500028091 151755420879280973250042137)
  ·
    refine ⟨113816565659460729937531603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151755420879280973250042137 113816565659460729937531603)
    ·
      refine ⟨170724848489191094906297405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113816565659460729937531603 170724848489191094906297405)
      ·
        refine ⟨64021818183446660589861527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170724848489191094906297405 64021818183446660589861527)
        ·
          refine ⟨96032727275169990884792291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64021818183446660589861527 96032727275169990884792291)
          ·
            refine ⟨144049090912754986327188437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96032727275169990884792291 144049090912754986327188437)
            ·
              refine ⟨3376150568267694992043479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 144049090912754986327188437 3376150568267694992043479)
              ·
                refine ⟨5064225852401542488065219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376150568267694992043479 5064225852401542488065219)
                ·
                  refine ⟨7596338778602313732097829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5064225852401542488065219 7596338778602313732097829)
                  ·
                    refine ⟨1424313520987933824768343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7596338778602313732097829 1424313520987933824768343)
                    ·
                      rfl

theorem cell22_4160761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 1, 4].length) (baseStart_4160761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160761 prefixEnd_4160761 := by exact prefixLift 4160761
  have htrace : WordTrace (prefixWord ++ tailWord_4160761) baseStart_4160761 baseEnd_4160761 := by
    simpa [prefixWord, tailWord_4160761, baseEnd_4160761] using wordTrace_append hprefix tailTrace_4160761
  have hstable : (prefixWord ++ tailWord_4160761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160761).length < 2 ^ (prefixWord ++ tailWord_4160761).sum := by decide
  have hdescent : baseEnd_4160761 < baseStart_4160761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160791 : List Nat := [1, 1, 3, 4, 1, 1, 1, 5, 2, 3]
def baseStart_4160791 : Nat := 118140960795 + 4160791 * 2 ^ 59
def prefixEnd_4160791 : Nat := 4983230072969 + 3 ^ 40 * 4160791 * 2
def baseEnd_4160791 : Nat := 1424323790601023746518251

theorem tailTrace_4160791 : CollatzResearch.WordTrace tailWord_4160791 prefixEnd_4160791 1424323790601023746518251 := by
  unfold tailWord_4160791
  simp only [CollatzResearch.WordTrace]
  refine ⟨151756515069172288373634227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101171010046114858915756151 151756515069172288373634227)
  ·
    refine ⟨227634772603758432560451341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151756515069172288373634227 227634772603758432560451341)
    ·
      refine ⟨85363039726409412210169253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227634772603758432560451341 85363039726409412210169253)
      ·
        refine ⟨16005569948701764789406735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85363039726409412210169253 16005569948701764789406735)
        ·
          refine ⟨24008354923052647184110103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16005569948701764789406735 24008354923052647184110103)
          ·
            refine ⟨36012532384578970776165155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24008354923052647184110103 36012532384578970776165155)
            ·
              refine ⟨54018798576868456164247733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36012532384578970776165155 54018798576868456164247733)
              ·
                refine ⟨5064262366581417765398225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54018798576868456164247733 5064262366581417765398225)
                ·
                  refine ⟨3798196774936063324048669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5064262366581417765398225 3798196774936063324048669)
                  ·
                    refine ⟨1424323790601023746518251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3798196774936063324048669 1424323790601023746518251)
                    ·
                      rfl

theorem cell22_4160791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_4160791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160791 prefixEnd_4160791 := by exact prefixLift 4160791
  have htrace : WordTrace (prefixWord ++ tailWord_4160791) baseStart_4160791 baseEnd_4160791 := by
    simpa [prefixWord, tailWord_4160791, baseEnd_4160791] using wordTrace_append hprefix tailTrace_4160791
  have hstable : (prefixWord ++ tailWord_4160791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160791).length < 2 ^ (prefixWord ++ tailWord_4160791).sum := by decide
  have hdescent : baseEnd_4160791 < baseStart_4160791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160825 : List Nat := [1, 2, 1, 6, 2, 2, 1, 2, 2, 3]
def baseStart_4160825 : Nat := 118140960795 + 4160825 * 2 ^ 59
def prefixEnd_4160825 : Nat := 4983230072969 + 3 ^ 40 * 4160825 * 2
def baseEnd_4160825 : Nat := 1424335429495858991168147

theorem tailTrace_4160825 : CollatzResearch.WordTrace tailWord_4160825 prefixEnd_4160825 1424335429495858991168147 := by
  unfold tailWord_4160825
  simp only [CollatzResearch.WordTrace]
  refine ⟨151757755151049112180371929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101171836767366074786914619 151757755151049112180371929)
  ·
    refine ⟨113818316363286834135278947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151757755151049112180371929 113818316363286834135278947)
    ·
      refine ⟨170727474544930251202918421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113818316363286834135278947 170727474544930251202918421)
      ·
        refine ⟨8002850369293605525136801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 170727474544930251202918421 8002850369293605525136801)
        ·
          refine ⟨6002137776970204143852601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8002850369293605525136801 6002137776970204143852601)
          ·
            refine ⟨4501603332727653107889451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6002137776970204143852601 4501603332727653107889451)
            ·
              refine ⟨6752404999091479661834177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4501603332727653107889451 6752404999091479661834177)
              ·
                refine ⟨5064303749318609746375633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6752404999091479661834177 5064303749318609746375633)
                ·
                  refine ⟨3798227811988957309781725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5064303749318609746375633 3798227811988957309781725)
                  ·
                    refine ⟨1424335429495858991168147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3798227811988957309781725 1424335429495858991168147)
                    ·
                      rfl

theorem cell22_4160825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 3].length) (baseStart_4160825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160825 prefixEnd_4160825 := by exact prefixLift 4160825
  have htrace : WordTrace (prefixWord ++ tailWord_4160825) baseStart_4160825 baseEnd_4160825 := by
    simpa [prefixWord, tailWord_4160825, baseEnd_4160825] using wordTrace_append hprefix tailTrace_4160825
  have hstable : (prefixWord ++ tailWord_4160825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160825).length < 2 ^ (prefixWord ++ tailWord_4160825).sum := by decide
  have hdescent : baseEnd_4160825 < baseStart_4160825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160930 : List Nat := [3, 3, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_4160930 : Nat := 118140960795 + 4160930 * 2 ^ 59
def prefixEnd_4160930 : Nat := 4983230072969 + 3 ^ 40 * 4160930 * 2
def baseEnd_4160930 : Nat := 1424371373141673717292825

theorem tailTrace_4160930 : CollatzResearch.WordTrace tailWord_4160930 prefixEnd_4160930 1424371373141673717292825 := by
  unfold tailWord_4160930
  simp only [CollatzResearch.WordTrace]
  refine ⟨37940396203917178778236061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101174389877112476741962829 37940396203917178778236061)
  ·
    refine ⟨14227648576468942041838523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37940396203917178778236061 14227648576468942041838523)
    ·
      refine ⟨21341472864703413062757785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14227648576468942041838523 21341472864703413062757785)
      ·
        refine ⟨16006104648527559797068339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21341472864703413062757785 16006104648527559797068339)
        ·
          refine ⟨24009156972791339695602509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16006104648527559797068339 24009156972791339695602509)
          ·
            refine ⟨9003433864796752385850941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24009156972791339695602509 9003433864796752385850941)
            ·
              refine ⟨3376287699298782144694103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9003433864796752385850941 3376287699298782144694103)
              ·
                refine ⟨5064431548948173217041155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376287699298782144694103 5064431548948173217041155)
                ·
                  refine ⟨7596647323422259825561733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5064431548948173217041155 7596647323422259825561733)
                  ·
                    refine ⟨1424371373141673717292825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7596647323422259825561733 1424371373141673717292825)
                    ·
                      rfl

theorem cell22_4160930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_4160930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160930 prefixEnd_4160930 := by exact prefixLift 4160930
  have htrace : WordTrace (prefixWord ++ tailWord_4160930) baseStart_4160930 baseEnd_4160930 := by
    simpa [prefixWord, tailWord_4160930, baseEnd_4160930] using wordTrace_append hprefix tailTrace_4160930
  have hstable : (prefixWord ++ tailWord_4160930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160930).length < 2 ^ (prefixWord ++ tailWord_4160930).sum := by decide
  have hdescent : baseEnd_4160930 < baseStart_4160930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160954 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 4, 7]
def baseStart_4160954 : Nat := 118140960795 + 4160954 * 2 ^ 59
def prefixEnd_4160954 : Nat := 4983230072969 + 3 ^ 40 * 4160954 * 2
def baseEnd_4160954 : Nat := 1424379588832145654692751

theorem tailTrace_4160954 : CollatzResearch.WordTrace tailWord_4160954 prefixEnd_4160954 1424379588832145654692751 := by
  unfold tailWord_4160954
  simp only [CollatzResearch.WordTrace]
  refine ⟨37940615041895441802954479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101174973445054511474545277 37940615041895441802954479)
  ·
    refine ⟨56910922562843162704431719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37940615041895441802954479 56910922562843162704431719)
    ·
      refine ⟨85366383844264744056647579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56910922562843162704431719 85366383844264744056647579)
      ·
        refine ⟨128049575766397116084971369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85366383844264744056647579 128049575766397116084971369)
        ·
          refine ⟨96037181824797837063728527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128049575766397116084971369 96037181824797837063728527)
          ·
            refine ⟨144055772737196755595592791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96037181824797837063728527 144055772737196755595592791)
            ·
              refine ⟨216083659105795133393389187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144055772737196755595592791 216083659105795133393389187)
              ·
                refine ⟨324125488658692700090083781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216083659105795133393389187 324125488658692700090083781)
                ·
                  refine ⟨60773529123504881266890709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324125488658692700090083781 60773529123504881266890709)
                  ·
                    refine ⟨1424379588832145654692751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60773529123504881266890709 1424379588832145654692751)
                    ·
                      rfl

theorem cell22_4160954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_4160954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160954 prefixEnd_4160954 := by exact prefixLift 4160954
  have htrace : WordTrace (prefixWord ++ tailWord_4160954) baseStart_4160954 baseEnd_4160954 := by
    simpa [prefixWord, tailWord_4160954, baseEnd_4160954] using wordTrace_append hprefix tailTrace_4160954
  have hstable : (prefixWord ++ tailWord_4160954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160954).length < 2 ^ (prefixWord ++ tailWord_4160954).sum := by decide
  have hdescent : baseEnd_4160954 < baseStart_4160954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160969 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 4, 6]
def baseStart_4160969 : Nat := 118140960795 + 4160969 * 2 ^ 59
def prefixEnd_4160969 : Nat := 4983230072969 + 3 ^ 40 * 4160969 * 2
def baseEnd_4160969 : Nat := 1424384723638690615567705

theorem tailTrace_4160969 : CollatzResearch.WordTrace tailWord_4160969 prefixEnd_4160969 1424384723638690615567705 := by
  unfold tailWord_4160969
  simp only [CollatzResearch.WordTrace]
  refine ⟨151763007262527424773613961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101175338175018283182409307 151763007262527424773613961)
  ·
    refine ⟨113822255446895568580210471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151763007262527424773613961 113822255446895568580210471)
    ·
      refine ⟨170733383170343352870315707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113822255446895568580210471 170733383170343352870315707)
      ·
        refine ⟨256100074755515029305473561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170733383170343352870315707 256100074755515029305473561)
        ·
          refine ⟨192075056066636271979105171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256100074755515029305473561 192075056066636271979105171)
          ·
            refine ⟨288112584099954407968657757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192075056066636271979105171 288112584099954407968657757)
            ·
              refine ⟨108042219037482902988246659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288112584099954407968657757 108042219037482902988246659)
              ·
                refine ⟨162063328556224354482369989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108042219037482902988246659 162063328556224354482369989)
                ·
                  refine ⟨30386874104292066465444373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162063328556224354482369989 30386874104292066465444373)
                  ·
                    refine ⟨1424384723638690615567705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30386874104292066465444373 1424384723638690615567705)
                    ·
                      rfl

theorem cell22_4160969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_4160969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160969 prefixEnd_4160969 := by exact prefixLift 4160969
  have htrace : WordTrace (prefixWord ++ tailWord_4160969) baseStart_4160969 baseEnd_4160969 := by
    simpa [prefixWord, tailWord_4160969, baseEnd_4160969] using wordTrace_append hprefix tailTrace_4160969
  have hstable : (prefixWord ++ tailWord_4160969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160969).length < 2 ^ (prefixWord ++ tailWord_4160969).sum := by decide
  have hdescent : baseEnd_4160969 < baseStart_4160969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160971 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 5, 3]
def baseStart_4160971 : Nat := 118140960795 + 4160971 * 2 ^ 59
def prefixEnd_4160971 : Nat := 4983230072969 + 3 ^ 40 * 4160971 * 2
def baseEnd_4160971 : Nat := 1424385408279563277017699

theorem tailTrace_4160971 : CollatzResearch.WordTrace tailWord_4160971 prefixEnd_4160971 1424385408279563277017699 := by
  unfold tailWord_4160971
  simp only [CollatzResearch.WordTrace]
  refine ⟨151763080208520179115186767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101175386805680119410124511 151763080208520179115186767)
  ·
    refine ⟨227644620312780268672780151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151763080208520179115186767 227644620312780268672780151)
    ·
      refine ⟨341466930469170403009170227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227644620312780268672780151 341466930469170403009170227)
      ·
        refine ⟨512200395703755604513755341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341466930469170403009170227 512200395703755604513755341)
        ·
          refine ⟨192075148388908351692658253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512200395703755604513755341 192075148388908351692658253)
          ·
            refine ⟨72028180645840631884746845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192075148388908351692658253 72028180645840631884746845)
            ·
              refine ⟨27010567742190236956780067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72028180645840631884746845 27010567742190236956780067)
              ·
                refine ⟨40515851613285355435170101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27010567742190236956780067 40515851613285355435170101)
                ·
                  refine ⟨3798361088745502072047197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40515851613285355435170101 3798361088745502072047197)
                  ·
                    refine ⟨1424385408279563277017699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3798361088745502072047197 1424385408279563277017699)
                    ·
                      rfl

theorem cell22_4160971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 3].length) (baseStart_4160971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4160971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4160971 prefixEnd_4160971 := by exact prefixLift 4160971
  have htrace : WordTrace (prefixWord ++ tailWord_4160971) baseStart_4160971 baseEnd_4160971 := by
    simpa [prefixWord, tailWord_4160971, baseEnd_4160971] using wordTrace_append hprefix tailTrace_4160971
  have hstable : (prefixWord ++ tailWord_4160971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160971).length < 2 ^ (prefixWord ++ tailWord_4160971).sum := by decide
  have hdescent : baseEnd_4160971 < baseStart_4160971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161016 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 2, 5]
def baseStart_4161016 : Nat := 118140960795 + 4161016 * 2 ^ 59
def prefixEnd_4161016 : Nat := 4983230072969 + 3 ^ 40 * 4161016 * 2
def baseEnd_4161016 : Nat := 1424400812699198159642561

theorem tailTrace_4161016 : CollatzResearch.WordTrace tailWord_4161016 prefixEnd_4161016 1424400812699198159642561 := by
  unfold tailWord_4161016
  simp only [CollatzResearch.WordTrace]
  refine ⟨75882360746678575900287451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101176480995571434533716601 75882360746678575900287451)
  ·
    refine ⟨113823541120017863850431177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75882360746678575900287451 113823541120017863850431177)
    ·
      refine ⟨85367655840013397887823383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113823541120017863850431177 85367655840013397887823383)
      ·
        refine ⟨128051483760020096831735075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85367655840013397887823383 128051483760020096831735075)
        ·
          refine ⟨192077225640030145247602613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128051483760020096831735075 192077225640030145247602613)
          ·
            refine ⟨18007239903752826116962745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192077225640030145247602613 18007239903752826116962745)
            ·
              refine ⟨13505429927814619587722059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18007239903752826116962745 13505429927814619587722059)
              ·
                refine ⟨20258144891721929381583089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13505429927814619587722059 20258144891721929381583089)
                ·
                  refine ⟨15193608668791447036187317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20258144891721929381583089 15193608668791447036187317)
                  ·
                    refine ⟨1424400812699198159642561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15193608668791447036187317 1424400812699198159642561)
                    ·
                      rfl

theorem cell22_4161016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_4161016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161016 prefixEnd_4161016 := by exact prefixLift 4161016
  have htrace : WordTrace (prefixWord ++ tailWord_4161016) baseStart_4161016 baseEnd_4161016 := by
    simpa [prefixWord, tailWord_4161016, baseEnd_4161016] using wordTrace_append hprefix tailTrace_4161016
  have hstable : (prefixWord ++ tailWord_4161016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161016).length < 2 ^ (prefixWord ++ tailWord_4161016).sum := by decide
  have hdescent : baseEnd_4161016 < baseStart_4161016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161018 : List Nat := [3, 1, 1, 1, 1, 2, 7, 1, 5]
def baseStart_4161018 : Nat := 118140960795 + 4161018 * 2 ^ 59
def prefixEnd_4161018 : Nat := 4983230072969 + 3 ^ 40 * 4161018 * 2
def baseEnd_4161018 : Nat := 474800499113356940364185

theorem tailTrace_4161018 : CollatzResearch.WordTrace tailWord_4161018 prefixEnd_4161018 474800499113356940364185 := by
  unfold tailWord_4161018
  simp only [CollatzResearch.WordTrace]
  refine ⟨37941198609837476535536927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101176529626233270761431805 37941198609837476535536927)
  ·
    refine ⟨56911797914756214803305391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37941198609837476535536927 56911797914756214803305391)
    ·
      refine ⟨85367696872134322204958087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56911797914756214803305391 85367696872134322204958087)
      ·
        refine ⟨128051545308201483307437131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85367696872134322204958087 128051545308201483307437131)
        ·
          refine ⟨192077317962302224961155697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128051545308201483307437131 192077317962302224961155697)
          ·
            refine ⟨144057988471726668720866773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192077317962302224961155697 144057988471726668720866773)
            ·
              refine ⟨3376359104806093798145315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 144057988471726668720866773 3376359104806093798145315)
              ·
                refine ⟨5064538657209140697217973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376359104806093798145315 5064538657209140697217973)
                ·
                  refine ⟨474800499113356940364185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5064538657209140697217973 474800499113356940364185)
                  ·
                    rfl

theorem cell22_4161018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_4161018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161018 prefixEnd_4161018 := by exact prefixLift 4161018
  have htrace : WordTrace (prefixWord ++ tailWord_4161018) baseStart_4161018 baseEnd_4161018 := by
    simpa [prefixWord, tailWord_4161018, baseEnd_4161018] using wordTrace_append hprefix tailTrace_4161018
  have hstable : (prefixWord ++ tailWord_4161018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161018).length < 2 ^ (prefixWord ++ tailWord_4161018).sum := by decide
  have hdescent : baseEnd_4161018 < baseStart_4161018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161093 : List Nat := [1, 3, 1, 1, 1, 4, 4, 1, 2, 4]
def baseStart_4161093 : Nat := 118140960795 + 4161093 * 2 ^ 59
def prefixEnd_4161093 : Nat := 4983230072969 + 3 ^ 40 * 4161093 * 2
def baseEnd_4161093 : Nat := 1424427171372795625467325

theorem tailTrace_4161093 : CollatzResearch.WordTrace tailWord_4161093 prefixEnd_4161093 1424427171372795625467325 := by
  unfold tailWord_4161093
  simp only [CollatzResearch.WordTrace]
  refine ⟨151767529914078193951127933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101178353276052129300751955 151767529914078193951127933)
  ·
    refine ⟨56912823717779322731672975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151767529914078193951127933 56912823717779322731672975)
    ·
      refine ⟨85369235576668984097509463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56912823717779322731672975 85369235576668984097509463)
      ·
        refine ⟨128053853365003476146264195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85369235576668984097509463 128053853365003476146264195)
        ·
          refine ⟨192080780047505214219396293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128053853365003476146264195 192080780047505214219396293)
          ·
            refine ⟨36015146258907227666136805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192080780047505214219396293 36015146258907227666136805)
            ·
              refine ⟨6752839923545105187400651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36015146258907227666136805 6752839923545105187400651)
              ·
                refine ⟨10129259885317657781100977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6752839923545105187400651 10129259885317657781100977)
                ·
                  refine ⟨7596944913988243335825733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10129259885317657781100977 7596944913988243335825733)
                  ·
                    refine ⟨1424427171372795625467325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7596944913988243335825733 1424427171372795625467325)
                    ·
                      rfl

theorem cell22_4161093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_4161093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161093 prefixEnd_4161093 := by exact prefixLift 4161093
  have htrace : WordTrace (prefixWord ++ tailWord_4161093) baseStart_4161093 baseEnd_4161093 := by
    simpa [prefixWord, tailWord_4161093, baseEnd_4161093] using wordTrace_append hprefix tailTrace_4161093
  have hstable : (prefixWord ++ tailWord_4161093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161093).length < 2 ^ (prefixWord ++ tailWord_4161093).sum := by decide
  have hdescent : baseEnd_4161093 < baseStart_4161093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161121 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 1, 8]
def baseStart_4161121 : Nat := 118140960795 + 4161121 * 2 ^ 59
def prefixEnd_4161121 : Nat := 4983230072969 + 3 ^ 40 * 4161121 * 2
def baseEnd_4161121 : Nat := 1424436756345012885767239

theorem tailTrace_4161121 : CollatzResearch.WordTrace tailWord_4161121 prefixEnd_4161121 1424436756345012885767239 := by
  unfold tailWord_4161121
  simp only [CollatzResearch.WordTrace]
  refine ⟨151768551157976754733147217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101179034105317836488764811 151768551157976754733147217)
  ·
    refine ⟨113826413368482566049860413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151768551157976754733147217 113826413368482566049860413)
    ·
      refine ⟨42684905013180962268697655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113826413368482566049860413 42684905013180962268697655)
      ·
        refine ⟨64027357519771443403046483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42684905013180962268697655 64027357519771443403046483)
        ·
          refine ⟨96041036279657165104569725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64027357519771443403046483 96041036279657165104569725)
          ·
            refine ⟨36015388604871436914213647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96041036279657165104569725 36015388604871436914213647)
            ·
              refine ⟨54023082907307155371320471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36015388604871436914213647 54023082907307155371320471)
              ·
                refine ⟨81034624360960733056980707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54023082907307155371320471 81034624360960733056980707)
                ·
                  refine ⟨121551936541441099585471061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81034624360960733056980707 121551936541441099585471061)
                  ·
                    refine ⟨1424436756345012885767239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121551936541441099585471061 1424436756345012885767239)
                    ·
                      rfl

theorem cell22_4161121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_4161121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161121 prefixEnd_4161121 := by exact prefixLift 4161121
  have htrace : WordTrace (prefixWord ++ tailWord_4161121) baseStart_4161121 baseEnd_4161121 := by
    simpa [prefixWord, tailWord_4161121, baseEnd_4161121] using wordTrace_append hprefix tailTrace_4161121
  have hstable : (prefixWord ++ tailWord_4161121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161121).length < 2 ^ (prefixWord ++ tailWord_4161121).sum := by decide
  have hdescent : baseEnd_4161121 < baseStart_4161121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161157 : List Nat := [1, 3, 1, 1, 4, 1, 4, 3, 1, 3]
def baseStart_4161157 : Nat := 118140960795 + 4161157 * 2 ^ 59
def prefixEnd_4161157 : Nat := 4983230072969 + 3 ^ 40 * 4161157 * 2
def baseEnd_4161157 : Nat := 1424449079880720791867129

theorem tailTrace_4161157 : CollatzResearch.WordTrace tailWord_4161157 prefixEnd_4161157 1424449079880720791867129 := by
  unfold tailWord_4161157
  simp only [CollatzResearch.WordTrace]
  refine ⟨151769864185846332881457725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101179909457230888587638483 151769864185846332881457725)
  ·
    refine ⟨56913699069692374830546647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151769864185846332881457725 56913699069692374830546647)
    ·
      refine ⟨85370548604538562245819971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56913699069692374830546647 85370548604538562245819971)
      ·
        refine ⟨128055822906807843368729957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85370548604538562245819971 128055822906807843368729957)
        ·
          refine ⟨24010466795026470631636867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128055822906807843368729957 24010466795026470631636867)
          ·
            refine ⟨36015700192539705947455301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24010466795026470631636867 36015700192539705947455301)
            ·
              refine ⟨6752943786101194865147869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36015700192539705947455301 6752943786101194865147869)
              ·
                refine ⟨2532353919787948074430451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6752943786101194865147869 2532353919787948074430451)
                ·
                  refine ⟨3798530879681922111645677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2532353919787948074430451 3798530879681922111645677)
                  ·
                    refine ⟨1424449079880720791867129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3798530879681922111645677 1424449079880720791867129)
                    ·
                      rfl

theorem cell22_4161157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 1, 3].length) (baseStart_4161157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161157 prefixEnd_4161157 := by exact prefixLift 4161157
  have htrace : WordTrace (prefixWord ++ tailWord_4161157) baseStart_4161157 baseEnd_4161157 := by
    simpa [prefixWord, tailWord_4161157, baseEnd_4161157] using wordTrace_append hprefix tailTrace_4161157
  have hstable : (prefixWord ++ tailWord_4161157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161157).length < 2 ^ (prefixWord ++ tailWord_4161157).sum := by decide
  have hdescent : baseEnd_4161157 < baseStart_4161157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161170 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 7]
def baseStart_4161170 : Nat := 118140960795 + 4161170 * 2 ^ 59
def prefixEnd_4161170 : Nat := 4983230072969 + 3 ^ 40 * 4161170 * 2
def baseEnd_4161170 : Nat := 474817843348797697097363

theorem tailTrace_4161170 : CollatzResearch.WordTrace tailWord_4161170 prefixEnd_4161170 474817843348797697097363 := by
  unfold tailWord_4161170
  simp only [CollatzResearch.WordTrace]
  refine ⟨37942584583699809025420241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101180225556532824067787309 37942584583699809025420241)
  ·
    refine ⟨28456938437774856769065181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37942584583699809025420241 28456938437774856769065181)
    ·
      refine ⟨10671351914165571288399443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28456938437774856769065181 10671351914165571288399443)
      ·
        refine ⟨16007027871248356932599165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10671351914165571288399443 16007027871248356932599165)
        ·
          refine ⟨6002635451718133849724687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16007027871248356932599165 6002635451718133849724687)
          ·
            refine ⟨9003953177577200774587031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6002635451718133849724687 9003953177577200774587031)
            ·
              refine ⟨13505929766365801161880547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9003953177577200774587031 13505929766365801161880547)
              ·
                refine ⟨20258894649548701742820821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13505929766365801161880547 20258894649548701742820821)
                ·
                  refine ⟨474817843348797697097363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20258894649548701742820821 474817843348797697097363)
                  ·
                    rfl

theorem cell22_4161170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_4161170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161170 prefixEnd_4161170 := by exact prefixLift 4161170
  have htrace : WordTrace (prefixWord ++ tailWord_4161170) baseStart_4161170 baseEnd_4161170 := by
    simpa [prefixWord, tailWord_4161170, baseEnd_4161170] using wordTrace_append hprefix tailTrace_4161170
  have hstable : (prefixWord ++ tailWord_4161170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161170).length < 2 ^ (prefixWord ++ tailWord_4161170).sum := by decide
  have hdescent : baseEnd_4161170 < baseStart_4161170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161213 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_4161213 : Nat := 118140960795 + 4161213 * 2 ^ 59
def prefixEnd_4161213 : Nat := 4983230072969 + 3 ^ 40 * 4161213 * 2
def baseEnd_4161213 : Nat := 1424468249825155312466957

theorem tailTrace_4161213 : CollatzResearch.WordTrace tailWord_4161213 prefixEnd_4161213 1424468249825155312466957 := by
  unfold tailWord_4161213
  simp only [CollatzResearch.WordTrace]
  refine ⟨151771906673643454445496293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101181271115762302963664195 151771906673643454445496293)
  ·
    refine ⟨28457232501308147708530555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151771906673643454445496293 28457232501308147708530555)
    ·
      refine ⟨42685848751962221562795833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28457232501308147708530555 42685848751962221562795833)
      ·
        refine ⟨32014386563971666172096875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42685848751962221562795833 32014386563971666172096875)
        ·
          refine ⟨48021579845957499258145313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32014386563971666172096875 48021579845957499258145313)
          ·
            refine ⟨36016184884468124443608985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48021579845957499258145313 36016184884468124443608985)
            ·
              refine ⟨27012138663351093332706739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36016184884468124443608985 27012138663351093332706739)
              ·
                refine ⟨40518207995026639999060109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27012138663351093332706739 40518207995026639999060109)
                ·
                  refine ⟨15194327998134989999647541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40518207995026639999060109 15194327998134989999647541)
                  ·
                    refine ⟨1424468249825155312466957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15194327998134989999647541 1424468249825155312466957)
                    ·
                      rfl

theorem cell22_4161213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_4161213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161213 prefixEnd_4161213 := by exact prefixLift 4161213
  have htrace : WordTrace (prefixWord ++ tailWord_4161213) baseStart_4161213 baseEnd_4161213 := by
    simpa [prefixWord, tailWord_4161213, baseEnd_4161213] using wordTrace_append hprefix tailTrace_4161213
  have hstable : (prefixWord ++ tailWord_4161213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161213).length < 2 ^ (prefixWord ++ tailWord_4161213).sum := by decide
  have hdescent : baseEnd_4161213 < baseStart_4161213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161230 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 4, 3]
def baseStart_4161230 : Nat := 118140960795 + 4161230 * 2 ^ 59
def prefixEnd_4161230 : Nat := 4983230072969 + 3 ^ 40 * 4161230 * 2
def baseEnd_4161230 : Nat := 1424474069272572934791905

theorem tailTrace_4161230 : CollatzResearch.WordTrace tailWord_4161230 prefixEnd_4161230 1424474069272572934791905 := by
  unfold tailWord_4161230
  simp only [CollatzResearch.WordTrace]
  refine ⟨18971565839322733293608143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101181684476387910899243429 18971565839322733293608143)
  ·
    refine ⟨28457348758984099940412215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18971565839322733293608143 28457348758984099940412215)
    ·
      refine ⟨42686023138476149910618323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28457348758984099940412215 42686023138476149910618323)
      ·
        refine ⟨64029034707714224865927485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42686023138476149910618323 64029034707714224865927485)
        ·
          refine ⟨24010888015392834324722807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64029034707714224865927485 24010888015392834324722807)
          ·
            refine ⟨36016332023089251487084211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24010888015392834324722807 36016332023089251487084211)
            ·
              refine ⟨54024498034633877230626317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36016332023089251487084211 54024498034633877230626317)
              ·
                refine ⟨20259186762987703961484869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54024498034633877230626317 20259186762987703961484869)
                ·
                  refine ⟨3798597518060194492778413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20259186762987703961484869 3798597518060194492778413)
                  ·
                    refine ⟨1424474069272572934791905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3798597518060194492778413 1424474069272572934791905)
                    ·
                      rfl

theorem cell22_4161230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_4161230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161230 prefixEnd_4161230 := by exact prefixLift 4161230
  have htrace : WordTrace (prefixWord ++ tailWord_4161230) baseStart_4161230 baseEnd_4161230 := by
    simpa [prefixWord, tailWord_4161230, baseEnd_4161230] using wordTrace_append hprefix tailTrace_4161230
  have hstable : (prefixWord ++ tailWord_4161230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161230).length < 2 ^ (prefixWord ++ tailWord_4161230).sum := by decide
  have hdescent : baseEnd_4161230 < baseStart_4161230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161238 : List Nat := [5, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_4161238 : Nat := 118140960795 + 4161238 * 2 ^ 59
def prefixEnd_4161238 : Nat := 4983230072969 + 3 ^ 40 * 4161238 * 2
def baseEnd_4161238 : Nat := 474825602612021193530627

theorem tailTrace_4161238 : CollatzResearch.WordTrace tailWord_4161238 prefixEnd_4161238 474825602612021193530627 := by
  unfold tailWord_4161238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9485801156159555232197273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101181878999035255810104245 9485801156159555232197273)
  ·
    refine ⟨7114350867119666424147955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9485801156159555232197273 7114350867119666424147955)
    ·
      refine ⟨10671526300679499636221933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7114350867119666424147955 10671526300679499636221933)
      ·
        refine ⟨4001822362754812363583225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10671526300679499636221933 4001822362754812363583225)
        ·
          refine ⟨3001366772066109272687419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4001822362754812363583225 3001366772066109272687419)
          ·
            refine ⟨4502050158099163909031129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3001366772066109272687419 4502050158099163909031129)
            ·
              refine ⟨3376537618574372931773347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4502050158099163909031129 3376537618574372931773347)
              ·
                refine ⟨5064806427861559397660021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376537618574372931773347 5064806427861559397660021)
                ·
                  refine ⟨474825602612021193530627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5064806427861559397660021 474825602612021193530627)
                  ·
                    rfl

theorem cell22_4161238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_4161238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161238 prefixEnd_4161238 := by exact prefixLift 4161238
  have htrace : WordTrace (prefixWord ++ tailWord_4161238) baseStart_4161238 baseEnd_4161238 := by
    simpa [prefixWord, tailWord_4161238, baseEnd_4161238] using wordTrace_append hprefix tailTrace_4161238
  have hstable : (prefixWord ++ tailWord_4161238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161238).length < 2 ^ (prefixWord ++ tailWord_4161238).sum := by decide
  have hdescent : baseEnd_4161238 < baseStart_4161238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161258 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 2, 7]
def baseStart_4161258 : Nat := 118140960795 + 4161258 * 2 ^ 59
def prefixEnd_4161258 : Nat := 4983230072969 + 3 ^ 40 * 4161258 * 2
def baseEnd_4161258 : Nat := 1424483654244790195091819

theorem tailTrace_4161258 : CollatzResearch.WordTrace tailWord_4161258 prefixEnd_4161258 1424483654244790195091819 := by
  unfold tailWord_4161258
  simp only [CollatzResearch.WordTrace]
  refine ⟨37943386989620106782721107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101182365305653618087256285 37943386989620106782721107)
  ·
    refine ⟨56915080484430160174081661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37943386989620106782721107 56915080484430160174081661)
    ·
      refine ⟨21343155181661310065280623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56915080484430160174081661 21343155181661310065280623)
      ·
        refine ⟨32014732772491965097920935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21343155181661310065280623 32014732772491965097920935)
        ·
          refine ⟨48022099158737947646881403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32014732772491965097920935 48022099158737947646881403)
          ·
            refine ⟨72033148738106921470322105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48022099158737947646881403 72033148738106921470322105)
            ·
              refine ⟨54024861553580191102741579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72033148738106921470322105 54024861553580191102741579)
              ·
                refine ⟨81037292330370286654112369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54024861553580191102741579 81037292330370286654112369)
                ·
                  refine ⟨60777969247777714990584277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81037292330370286654112369 60777969247777714990584277)
                  ·
                    refine ⟨1424483654244790195091819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60777969247777714990584277 1424483654244790195091819)
                    ·
                      rfl

theorem cell22_4161258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_4161258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161258 prefixEnd_4161258 := by exact prefixLift 4161258
  have htrace : WordTrace (prefixWord ++ tailWord_4161258) baseStart_4161258 baseEnd_4161258 := by
    simpa [prefixWord, tailWord_4161258, baseEnd_4161258] using wordTrace_append hprefix tailTrace_4161258
  have hstable : (prefixWord ++ tailWord_4161258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161258).length < 2 ^ (prefixWord ++ tailWord_4161258).sum := by decide
  have hdescent : baseEnd_4161258 < baseStart_4161258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161397 : List Nat := [1, 3, 4, 1, 1, 1, 3, 2, 2, 4]
def baseStart_4161397 : Nat := 118140960795 + 4161397 * 2 ^ 59
def prefixEnd_4161397 : Nat := 4983230072969 + 3 ^ 40 * 4161397 * 2
def baseEnd_4161397 : Nat := 1424531236785440165866393

theorem tailTrace_4161397 : CollatzResearch.WordTrace tailWord_4161397 prefixEnd_4161397 1424531236785440165866393 := by
  unfold tailWord_4161397
  simp only [CollatzResearch.WordTrace]
  refine ⟨151778617704976853870194445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101185745136651235913462963 151778617704976853870194445)
  ·
    refine ⟨56916981639366320201322917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151778617704976853870194445 56916981639366320201322917)
    ·
      refine ⟨10671934057381185037748047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56916981639366320201322917 10671934057381185037748047)
      ·
        refine ⟨16007901086071777556622071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10671934057381185037748047 16007901086071777556622071)
        ·
          refine ⟨24011851629107666334933107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16007901086071777556622071 24011851629107666334933107)
          ·
            refine ⟨36017777443661499502399661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24011851629107666334933107 36017777443661499502399661)
            ·
              refine ⟨13506666541373062313399873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36017777443661499502399661 13506666541373062313399873)
              ·
                refine ⟨10129999906029796735049905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13506666541373062313399873 10129999906029796735049905)
                ·
                  refine ⟨7597499929522347551287429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10129999906029796735049905 7597499929522347551287429)
                  ·
                    refine ⟨1424531236785440165866393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7597499929522347551287429 1424531236785440165866393)
                    ·
                      rfl

theorem cell22_4161397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_4161397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161397 prefixEnd_4161397 := by exact prefixLift 4161397
  have htrace : WordTrace (prefixWord ++ tailWord_4161397) baseStart_4161397 baseEnd_4161397 := by
    simpa [prefixWord, tailWord_4161397, baseEnd_4161397] using wordTrace_append hprefix tailTrace_4161397
  have hstable : (prefixWord ++ tailWord_4161397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161397).length < 2 ^ (prefixWord ++ tailWord_4161397).sum := by decide
  have hdescent : baseEnd_4161397 < baseStart_4161397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161455 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 2, 5]
def baseStart_4161455 : Nat := 118140960795 + 4161455 * 2 ^ 59
def prefixEnd_4161455 : Nat := 4983230072969 + 3 ^ 40 * 4161455 * 2
def baseEnd_4161455 : Nat := 1424551091370747347916215

theorem tailTrace_4161455 : CollatzResearch.WordTrace tailWord_4161455 prefixEnd_4161455 1424551091370747347916215 := by
  unfold tailWord_4161455
  simp only [CollatzResearch.WordTrace]
  refine ⟨151780733138766729775805819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101187155425844486517203879 151780733138766729775805819)
  ·
    refine ⟨227671099708150094663708729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151780733138766729775805819 227671099708150094663708729)
    ·
      refine ⟨170753324781112570997781547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227671099708150094663708729 170753324781112570997781547)
      ·
        refine ⟨256129987171668856496672321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170753324781112570997781547 256129987171668856496672321)
        ·
          refine ⟨192097490378751642372504241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256129987171668856496672321 192097490378751642372504241)
          ·
            refine ⟨144073117784063731779378181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192097490378751642372504241 144073117784063731779378181)
            ·
              refine ⟨27013709584511949708633409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144073117784063731779378181 27013709584511949708633409)
              ·
                refine ⟨20260282188383962281475057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27013709584511949708633409 20260282188383962281475057)
                ·
                  refine ⟨15195211641287971711106293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20260282188383962281475057 15195211641287971711106293)
                  ·
                    refine ⟨1424551091370747347916215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15195211641287971711106293 1424551091370747347916215)
                    ·
                      rfl

theorem cell22_4161455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_4161455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161455 prefixEnd_4161455 := by exact prefixLift 4161455
  have htrace : WordTrace (prefixWord ++ tailWord_4161455) baseStart_4161455 baseEnd_4161455 := by
    simpa [prefixWord, tailWord_4161455, baseEnd_4161455] using wordTrace_append hprefix tailTrace_4161455
  have hstable : (prefixWord ++ tailWord_4161455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161455).length < 2 ^ (prefixWord ++ tailWord_4161455).sum := by decide
  have hdescent : baseEnd_4161455 < baseStart_4161455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161457 : List Nat := [1, 2, 2, 4, 2, 1, 1, 4, 5]
def baseStart_4161457 : Nat := 118140960795 + 4161457 * 2 ^ 59
def prefixEnd_4161457 : Nat := 4983230072969 + 3 ^ 40 * 4161457 * 2
def baseEnd_4161457 : Nat := 474850592003873336455403

theorem tailTrace_4161457 : CollatzResearch.WordTrace tailWord_4161457 prefixEnd_4161457 474850592003873336455403 := by
  unfold tailWord_4161457
  simp only [CollatzResearch.WordTrace]
  refine ⟨151780806084759484117378625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101187204056506322744919083 151780806084759484117378625)
  ·
    refine ⟨113835604563569613088033969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151780806084759484117378625 113835604563569613088033969)
    ·
      refine ⟨85376703422677209816025477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113835604563569613088033969 85376703422677209816025477)
      ·
        refine ⟨16008131891751976840504777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85376703422677209816025477 16008131891751976840504777)
        ·
          refine ⟨12006098918813982630378583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16008131891751976840504777 12006098918813982630378583)
          ·
            refine ⟨18009148378220973945567875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12006098918813982630378583 18009148378220973945567875)
            ·
              refine ⟨27013722567331460918351813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18009148378220973945567875 27013722567331460918351813)
              ·
                refine ⟨5065072981374648922190965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27013722567331460918351813 5065072981374648922190965)
                ·
                  refine ⟨474850592003873336455403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5065072981374648922190965 474850592003873336455403)
                  ·
                    rfl

theorem cell22_4161457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 5].length) (baseStart_4161457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161457 prefixEnd_4161457 := by exact prefixLift 4161457
  have htrace : WordTrace (prefixWord ++ tailWord_4161457) baseStart_4161457 baseEnd_4161457 := by
    simpa [prefixWord, tailWord_4161457, baseEnd_4161457] using wordTrace_append hprefix tailTrace_4161457
  have hstable : (prefixWord ++ tailWord_4161457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161457).length < 2 ^ (prefixWord ++ tailWord_4161457).sum := by decide
  have hdescent : baseEnd_4161457 < baseStart_4161457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161461 : List Nat := [1, 3, 3, 2, 1, 3, 1, 4, 1, 3]
def baseStart_4161461 : Nat := 118140960795 + 4161461 * 2 ^ 59
def prefixEnd_4161461 : Nat := 4983230072969 + 3 ^ 40 * 4161461 * 2
def baseEnd_4161461 : Nat := 1424553145293365332266197

theorem tailTrace_4161461 : CollatzResearch.WordTrace tailWord_4161461 prefixEnd_4161461 1424553145293365332266197 := by
  unfold tailWord_4161461
  simp only [CollatzResearch.WordTrace]
  refine ⟨151780951976744992800524237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101187301317829995200349491 151780951976744992800524237)
  ·
    refine ⟨56917856991279372300196589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151780951976744992800524237 56917856991279372300196589)
    ·
      refine ⟨21344196371729764612573721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56917856991279372300196589 21344196371729764612573721)
      ·
        refine ⟨16008147278797323459430291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21344196371729764612573721 16008147278797323459430291)
        ·
          refine ⟨24012220918195985189145437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16008147278797323459430291 24012220918195985189145437)
          ·
            refine ⟨9004582844323494445929539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24012220918195985189145437 9004582844323494445929539)
            ·
              refine ⟨13506874266485241668894309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9004582844323494445929539 13506874266485241668894309)
              ·
                refine ⟨2532538924965982812917683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13506874266485241668894309 2532538924965982812917683)
                ·
                  refine ⟨3798808387448974219376525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2532538924965982812917683 3798808387448974219376525)
                  ·
                    refine ⟨1424553145293365332266197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3798808387448974219376525 1424553145293365332266197)
                    ·
                      rfl

theorem cell22_4161461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_4161461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161461 prefixEnd_4161461 := by exact prefixLift 4161461
  have htrace : WordTrace (prefixWord ++ tailWord_4161461) baseStart_4161461 baseEnd_4161461 := by
    simpa [prefixWord, tailWord_4161461, baseEnd_4161461] using wordTrace_append hprefix tailTrace_4161461
  have hstable : (prefixWord ++ tailWord_4161461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161461).length < 2 ^ (prefixWord ++ tailWord_4161461).sum := by decide
  have hdescent : baseEnd_4161461 < baseStart_4161461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161487 : List Nat := [1, 1, 2, 1, 1, 5, 2, 4, 1, 4]
def baseStart_4161487 : Nat := 118140960795 + 4161487 * 2 ^ 59
def prefixEnd_4161487 : Nat := 4983230072969 + 3 ^ 40 * 4161487 * 2
def baseEnd_4161487 : Nat := 1424562045624709931116117

theorem tailTrace_4161487 : CollatzResearch.WordTrace tailWord_4161487 prefixEnd_4161487 1424562045624709931116117 := by
  unfold tailWord_4161487
  simp only [CollatzResearch.WordTrace]
  refine ⟨151781900274650799240970715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101187933516433866160647143 151781900274650799240970715)
  ·
    refine ⟨227672850411976198861456073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151781900274650799240970715 227672850411976198861456073)
    ·
      refine ⟨170754637808982149146092055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227672850411976198861456073 170754637808982149146092055)
      ·
        refine ⟨256131956713473223719138083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170754637808982149146092055 256131956713473223719138083)
        ·
          refine ⟨384197935070209835578707125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256131956713473223719138083 384197935070209835578707125)
          ·
            refine ⟨36018556412832172085503793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 384197935070209835578707125 36018556412832172085503793)
            ·
              refine ⟨27013917309624129064127845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36018556412832172085503793 27013917309624129064127845)
              ·
                refine ⟨5065109495554524199523971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27013917309624129064127845 5065109495554524199523971)
                ·
                  refine ⟨7597664243331786299285957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5065109495554524199523971 7597664243331786299285957)
                  ·
                    refine ⟨1424562045624709931116117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7597664243331786299285957 1424562045624709931116117)
                    ·
                      rfl

theorem cell22_4161487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 4].length) (baseStart_4161487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161487 prefixEnd_4161487 := by exact prefixLift 4161487
  have htrace : WordTrace (prefixWord ++ tailWord_4161487) baseStart_4161487 baseEnd_4161487 := by
    simpa [prefixWord, tailWord_4161487, baseEnd_4161487] using wordTrace_append hprefix tailTrace_4161487
  have hstable : (prefixWord ++ tailWord_4161487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161487).length < 2 ^ (prefixWord ++ tailWord_4161487).sum := by decide
  have hdescent : baseEnd_4161487 < baseStart_4161487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161613 : List Nat := [1, 6, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_4161613 : Nat := 118140960795 + 4161613 * 2 ^ 59
def prefixEnd_4161613 : Nat := 4983230072969 + 3 ^ 40 * 4161613 * 2
def baseEnd_4161613 : Nat := 1424605177999687602465731

theorem tailTrace_4161613 : CollatzResearch.WordTrace tailWord_4161613 prefixEnd_4161613 1424605177999687602465731 := by
  unfold tailWord_4161613
  simp only [CollatzResearch.WordTrace]
  refine ⟨151786495872194322760057493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101190997248129548506704995 151786495872194322760057493)
  ·
    refine ⟨7114991994009108879377695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151786495872194322760057493 7114991994009108879377695)
    ·
      refine ⟨10672487991013663319066543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7114991994009108879377695 10672487991013663319066543)
      ·
        refine ⟨16008731986520494978599815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10672487991013663319066543 16008731986520494978599815)
        ·
          refine ⟨24013097979780742467899723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16008731986520494978599815 24013097979780742467899723)
          ·
            refine ⟨36019646969671113701849585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24013097979780742467899723 36019646969671113701849585)
            ·
              refine ⟨27014735227253335276387189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36019646969671113701849585 27014735227253335276387189)
              ·
                refine ⟨2532631427555000182161299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27014735227253335276387189 2532631427555000182161299)
                ·
                  refine ⟨3798947141332500273241949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2532631427555000182161299 3798947141332500273241949)
                  ·
                    refine ⟨1424605177999687602465731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3798947141332500273241949 1424605177999687602465731)
                    ·
                      rfl

theorem cell22_4161613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_4161613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161613 prefixEnd_4161613 := by exact prefixLift 4161613
  have htrace : WordTrace (prefixWord ++ tailWord_4161613) baseStart_4161613 baseEnd_4161613 := by
    simpa [prefixWord, tailWord_4161613, baseEnd_4161613] using wordTrace_append hprefix tailTrace_4161613
  have hstable : (prefixWord ++ tailWord_4161613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161613).length < 2 ^ (prefixWord ++ tailWord_4161613).sum := by decide
  have hdescent : baseEnd_4161613 < baseStart_4161613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161654 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_4161654 : Nat := 118140960795 + 4161654 * 2 ^ 59
def prefixEnd_4161654 : Nat := 4983230072969 + 3 ^ 40 * 4161654 * 2
def baseEnd_4161654 : Nat := 474873071045859054063535

theorem tailTrace_4161654 : CollatzResearch.WordTrace tailWord_4161654 prefixEnd_4161654 474873071045859054063535 := by
  unfold tailWord_4161654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9486749454065361672643751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101191994176697191174866677 9486749454065361672643751)
  ·
    refine ⟨14230124181098042508965627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9486749454065361672643751 14230124181098042508965627)
    ·
      refine ⟨21345186271647063763448441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14230124181098042508965627 21345186271647063763448441)
      ·
        refine ⟨16008889703735297822586331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21345186271647063763448441 16008889703735297822586331)
        ·
          refine ⟨24013334555602946733879497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16008889703735297822586331 24013334555602946733879497)
          ·
            refine ⟨18010000916702210050409623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24013334555602946733879497 18010000916702210050409623)
            ·
              refine ⟨27015001375053315075614435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18010000916702210050409623 27015001375053315075614435)
              ·
                refine ⟨40522502062579972613421653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27015001375053315075614435 40522502062579972613421653)
                ·
                  refine ⟨474873071045859054063535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40522502062579972613421653 474873071045859054063535)
                  ·
                    rfl

theorem cell22_4161654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_4161654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161654 prefixEnd_4161654 := by exact prefixLift 4161654
  have htrace : WordTrace (prefixWord ++ tailWord_4161654) baseStart_4161654 baseEnd_4161654 := by
    simpa [prefixWord, tailWord_4161654, baseEnd_4161654] using wordTrace_append hprefix tailTrace_4161654
  have hstable : (prefixWord ++ tailWord_4161654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161654).length < 2 ^ (prefixWord ++ tailWord_4161654).sum := by decide
  have hdescent : baseEnd_4161654 < baseStart_4161654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161669 : List Nat := [1, 3, 1, 1, 5, 1, 2, 2, 1, 5]
def baseStart_4161669 : Nat := 118140960795 + 4161669 * 2 ^ 59
def prefixEnd_4161669 : Nat := 4983230072969 + 3 ^ 40 * 4161669 * 2
def baseEnd_4161669 : Nat := 1424624347944122123065559

theorem tailTrace_4161669 : CollatzResearch.WordTrace tailWord_4161669 prefixEnd_4161669 1424624347944122123065559 := by
  unfold tailWord_4161669
  simp only [CollatzResearch.WordTrace]
  refine ⟨151788538359991444324096061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101192358906660962882730707 151788538359991444324096061)
  ·
    refine ⟨56920701884996791621536023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151788538359991444324096061 56920701884996791621536023)
    ·
      refine ⟨85381052827495187432304035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56920701884996791621536023 85381052827495187432304035)
      ·
        refine ⟨128071579241242781148456053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85381052827495187432304035 128071579241242781148456053)
        ·
          refine ⟨12006710553866510732667755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128071579241242781148456053 12006710553866510732667755)
          ·
            refine ⟨18010065830799766099001633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12006710553866510732667755 18010065830799766099001633)
            ·
              refine ⟨13507549373099824574251225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18010065830799766099001633 13507549373099824574251225)
              ·
                refine ⟨10130662029824868430688419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13507549373099824574251225 10130662029824868430688419)
                ·
                  refine ⟨15195993044737302646032629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10130662029824868430688419 15195993044737302646032629)
                  ·
                    refine ⟨1424624347944122123065559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15195993044737302646032629 1424624347944122123065559)
                    ·
                      rfl

theorem cell22_4161669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_4161669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161669 prefixEnd_4161669 := by exact prefixLift 4161669
  have htrace : WordTrace (prefixWord ++ tailWord_4161669) baseStart_4161669 baseEnd_4161669 := by
    simpa [prefixWord, tailWord_4161669, baseEnd_4161669] using wordTrace_append hprefix tailTrace_4161669
  have hstable : (prefixWord ++ tailWord_4161669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161669).length < 2 ^ (prefixWord ++ tailWord_4161669).sum := by decide
  have hdescent : baseEnd_4161669 < baseStart_4161669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161703 : List Nat := [1, 1, 6, 2, 2, 2, 1, 1, 1, 5]
def baseStart_4161703 : Nat := 118140960795 + 4161703 * 2 ^ 59
def prefixEnd_4161703 : Nat := 4983230072969 + 3 ^ 40 * 4161703 * 2
def baseEnd_4161703 : Nat := 1424635986838957367715455

theorem tailTrace_4161703 : CollatzResearch.WordTrace tailWord_4161703 prefixEnd_4161703 1424635986838957367715455 := by
  unfold tailWord_4161703
  simp only [CollatzResearch.WordTrace]
  refine ⟨151789778441868268130833763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101193185627912178753889175 151789778441868268130833763)
  ·
    refine ⟨227684667662802402196250645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151789778441868268130833763 227684667662802402196250645)
    ·
      refine ⟨10672718796693862602949249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 227684667662802402196250645 10672718796693862602949249)
      ·
        refine ⟨8004539097520396952211937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10672718796693862602949249 8004539097520396952211937)
        ·
          refine ⟨6003404323140297714158953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8004539097520396952211937 6003404323140297714158953)
          ·
            refine ⟨4502553242355223285619215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6003404323140297714158953 4502553242355223285619215)
            ·
              refine ⟨6753829863532834928428823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4502553242355223285619215 6753829863532834928428823)
              ·
                refine ⟨10130744795299252392643235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6753829863532834928428823 10130744795299252392643235)
                ·
                  refine ⟨15196117192948878588964853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10130744795299252392643235 15196117192948878588964853)
                  ·
                    refine ⟨1424635986838957367715455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15196117192948878588964853 1424635986838957367715455)
                    ·
                      rfl

theorem cell22_4161703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_4161703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161703 prefixEnd_4161703 := by exact prefixLift 4161703
  have htrace : WordTrace (prefixWord ++ tailWord_4161703) baseStart_4161703 baseEnd_4161703 := by
    simpa [prefixWord, tailWord_4161703, baseEnd_4161703] using wordTrace_append hprefix tailTrace_4161703
  have hstable : (prefixWord ++ tailWord_4161703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161703).length < 2 ^ (prefixWord ++ tailWord_4161703).sum := by decide
  have hdescent : baseEnd_4161703 < baseStart_4161703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161799 : List Nat := [1, 1, 4, 5, 1, 2, 2, 2, 1, 3]
def baseStart_4161799 : Nat := 118140960795 + 4161799 * 2 ^ 59
def prefixEnd_4161799 : Nat := 4983230072969 + 3 ^ 40 * 4161799 * 2
def baseEnd_4161799 : Nat := 1424668849600845117315161

theorem tailTrace_4161799 : CollatzResearch.WordTrace tailWord_4161799 prefixEnd_4161799 1424668849600845117315161 := by
  unfold tailWord_4161799
  simp only [CollatzResearch.WordTrace]
  refine ⟨151793279849520476526328451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101195519899680317684218967 151793279849520476526328451)
  ·
    refine ⟨227689919774280714789492677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151793279849520476526328451 227689919774280714789492677)
    ·
      refine ⟨42691859957677634023029877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227689919774280714789492677 42691859957677634023029877)
      ·
        refine ⟨4002361871032278189659051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42691859957677634023029877 4002361871032278189659051)
        ·
          refine ⟨6003542806548417284488577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4002361871032278189659051 6003542806548417284488577)
          ·
            refine ⟨4502657104911312963366433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6003542806548417284488577 4502657104911312963366433)
            ·
              refine ⟨3376992828683484722524825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4502657104911312963366433 3376992828683484722524825)
              ·
                refine ⟨2532744621512613541893619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3376992828683484722524825 2532744621512613541893619)
                ·
                  refine ⟨3799116932268920312840429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2532744621512613541893619 3799116932268920312840429)
                  ·
                    refine ⟨1424668849600845117315161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3799116932268920312840429 1424668849600845117315161)
                    ·
                      rfl

theorem cell22_4161799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_4161799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161799 prefixEnd_4161799 := by exact prefixLift 4161799
  have htrace : WordTrace (prefixWord ++ tailWord_4161799) baseStart_4161799 baseEnd_4161799 := by
    simpa [prefixWord, tailWord_4161799, baseEnd_4161799] using wordTrace_append hprefix tailTrace_4161799
  have hstable : (prefixWord ++ tailWord_4161799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161799).length < 2 ^ (prefixWord ++ tailWord_4161799).sum := by decide
  have hdescent : baseEnd_4161799 < baseStart_4161799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161804 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 3, 5]
def baseStart_4161804 : Nat := 118140960795 + 4161804 * 2 ^ 59
def prefixEnd_4161804 : Nat := 4983230072969 + 3 ^ 40 * 4161804 * 2
def baseEnd_4161804 : Nat := 1424670561203026770940145

theorem tailTrace_4161804 : CollatzResearch.WordTrace tailWord_4161804 prefixEnd_4161804 1424670561203026770940145 := by
  unfold tailWord_4161804
  simp only [CollatzResearch.WordTrace]
  refine ⟨75896731107251181190130233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101195641476334908253506977 75896731107251181190130233)
  ·
    refine ⟨56922548330438385892597675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75896731107251181190130233 56922548330438385892597675)
    ·
      refine ⟨85383822495657578838896513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56922548330438385892597675 85383822495657578838896513)
      ·
        refine ⟨64037866871743184129172385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85383822495657578838896513 64037866871743184129172385)
        ·
          refine ⟨48028400153807388096879289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64037866871743184129172385 48028400153807388096879289)
          ·
            refine ⟨36021300115355541072659467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48028400153807388096879289 36021300115355541072659467)
            ·
              refine ⟨54031950173033311608989201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36021300115355541072659467 54031950173033311608989201)
              ·
                refine ⟨40523962629774983706741901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54031950173033311608989201 40523962629774983706741901)
                ·
                  refine ⟨15196485986165618890028213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40523962629774983706741901 15196485986165618890028213)
                  ·
                    refine ⟨1424670561203026770940145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15196485986165618890028213 1424670561203026770940145)
                    ·
                      rfl

theorem cell22_4161804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_4161804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161804 prefixEnd_4161804 := by exact prefixLift 4161804
  have htrace : WordTrace (prefixWord ++ tailWord_4161804) baseStart_4161804 baseEnd_4161804 := by
    simpa [prefixWord, tailWord_4161804, baseEnd_4161804] using wordTrace_append hprefix tailTrace_4161804
  have hstable : (prefixWord ++ tailWord_4161804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161804).length < 2 ^ (prefixWord ++ tailWord_4161804).sum := by decide
  have hdescent : baseEnd_4161804 < baseStart_4161804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161819 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 4, 4]
def baseStart_4161819 : Nat := 118140960795 + 4161819 * 2 ^ 59
def prefixEnd_4161819 : Nat := 4983230072969 + 3 ^ 40 * 4161819 * 2
def baseEnd_4161819 : Nat := 1424675696009571731815099

theorem tailTrace_4161819 : CollatzResearch.WordTrace tailWord_4161819 prefixEnd_4161819 1424675696009571731815099 := by
  unfold tailWord_4161819
  simp only [CollatzResearch.WordTrace]
  refine ⟨151794009309448019942056511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101196006206298679961371007 151794009309448019942056511)
  ·
    refine ⟨227691013964172029913084767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151794009309448019942056511 227691013964172029913084767)
    ·
      refine ⟨341536520946258044869627151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227691013964172029913084767 341536520946258044869627151)
      ·
        refine ⟨512304781419387067304440727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341536520946258044869627151 512304781419387067304440727)
        ·
          refine ⟨768457172129080600956661091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512304781419387067304440727 768457172129080600956661091)
          ·
            refine ⟨1152685758193620901434991637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768457172129080600956661091 1152685758193620901434991637)
            ·
              refine ⟨54032144915325979754765233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1152685758193620901434991637 54032144915325979754765233)
              ·
                refine ⟨40524108686494484816073925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54032144915325979754765233 40524108686494484816073925)
                ·
                  refine ⟨7598270378717715903013861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40524108686494484816073925 7598270378717715903013861)
                  ·
                    refine ⟨1424675696009571731815099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7598270378717715903013861 1424675696009571731815099)
                    ·
                      rfl

theorem cell22_4161819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 4].length) (baseStart_4161819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161819 prefixEnd_4161819 := by exact prefixLift 4161819
  have htrace : WordTrace (prefixWord ++ tailWord_4161819) baseStart_4161819 baseEnd_4161819 := by
    simpa [prefixWord, tailWord_4161819, baseEnd_4161819] using wordTrace_append hprefix tailTrace_4161819
  have hstable : (prefixWord ++ tailWord_4161819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161819).length < 2 ^ (prefixWord ++ tailWord_4161819).sum := by decide
  have hdescent : baseEnd_4161819 < baseStart_4161819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161836 : List Nat := [2, 2, 1, 1, 1, 3, 5, 1, 2, 4]
def baseStart_4161836 : Nat := 118140960795 + 4161836 * 2 ^ 59
def prefixEnd_4161836 : Nat := 4983230072969 + 3 ^ 40 * 4161836 * 2
def baseEnd_4161836 : Nat := 1424681515456989354140047

theorem tailTrace_4161836 : CollatzResearch.WordTrace tailWord_4161836 prefixEnd_4161836 1424681515456989354140047 := by
  unfold tailWord_4161836
  simp only [CollatzResearch.WordTrace]
  refine ⟨75897314675193215922712681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101196419566924287896950241 75897314675193215922712681)
  ·
    refine ⟨56922986006394911942034511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75897314675193215922712681 56922986006394911942034511)
    ·
      refine ⟨85384479009592367913051767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56922986006394911942034511 85384479009592367913051767)
      ·
        refine ⟨128076718514388551869577651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85384479009592367913051767 128076718514388551869577651)
        ·
          refine ⟨192115077771582827804366477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128076718514388551869577651 192115077771582827804366477)
          ·
            refine ⟨72043154164343560426637429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192115077771582827804366477 72043154164343560426637429)
            ·
              refine ⟨6754045702907208789997259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72043154164343560426637429 6754045702907208789997259)
              ·
                refine ⟨10131068554360813184995889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6754045702907208789997259 10131068554360813184995889)
                ·
                  refine ⟨7598301415770609888746917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10131068554360813184995889 7598301415770609888746917)
                  ·
                    refine ⟨1424681515456989354140047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7598301415770609888746917 1424681515456989354140047)
                    ·
                      rfl

theorem cell22_4161836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_4161836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161836 prefixEnd_4161836 := by exact prefixLift 4161836
  have htrace : WordTrace (prefixWord ++ tailWord_4161836) baseStart_4161836 baseEnd_4161836 := by
    simpa [prefixWord, tailWord_4161836, baseEnd_4161836] using wordTrace_append hprefix tailTrace_4161836
  have hstable : (prefixWord ++ tailWord_4161836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161836).length < 2 ^ (prefixWord ++ tailWord_4161836).sum := by decide
  have hdescent : baseEnd_4161836 < baseStart_4161836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161842 : List Nat := [3, 2, 1, 1, 6, 1, 2, 1, 1, 4]
def baseStart_4161842 : Nat := 118140960795 + 4161842 * 2 ^ 59
def prefixEnd_4161842 : Nat := 4983230072969 + 3 ^ 40 * 4161842 * 2
def baseEnd_4161842 : Nat := 1424683569379607338490029

theorem tailTrace_4161842 : CollatzResearch.WordTrace tailWord_4161842 prefixEnd_4161842 1424683569379607338490029 := by
  unfold tailWord_4161842
  simp only [CollatzResearch.WordTrace]
  refine ⟨37948712047091173717535945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101196565458909796580095853 37948712047091173717535945)
  ·
    refine ⟨28461534035318380288151959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37948712047091173717535945 28461534035318380288151959)
    ·
      refine ⟨42692301052977570432227939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28461534035318380288151959 42692301052977570432227939)
      ·
        refine ⟨64038451579466355648341909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42692301052977570432227939 64038451579466355648341909)
        ·
          refine ⟨3001802417787485421016027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64038451579466355648341909 3001802417787485421016027)
          ·
            refine ⟨4502703626681228131524041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3001802417787485421016027 4502703626681228131524041)
            ·
              refine ⟨3377027720010921098643031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4502703626681228131524041 3377027720010921098643031)
              ·
                refine ⟨5065541580016381647964547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3377027720010921098643031 5065541580016381647964547)
                ·
                  refine ⟨7598312370024572471946821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5065541580016381647964547 7598312370024572471946821)
                  ·
                    refine ⟨1424683569379607338490029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7598312370024572471946821 1424683569379607338490029)
                    ·
                      rfl

theorem cell22_4161842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_4161842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161842 prefixEnd_4161842 := by exact prefixLift 4161842
  have htrace : WordTrace (prefixWord ++ tailWord_4161842) baseStart_4161842 baseEnd_4161842 := by
    simpa [prefixWord, tailWord_4161842, baseEnd_4161842] using wordTrace_append hprefix tailTrace_4161842
  have hstable : (prefixWord ++ tailWord_4161842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161842).length < 2 ^ (prefixWord ++ tailWord_4161842).sum := by decide
  have hdescent : baseEnd_4161842 < baseStart_4161842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161864 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 1, 8]
def baseStart_4161864 : Nat := 118140960795 + 4161864 * 2 ^ 59
def prefixEnd_4161864 : Nat := 4983230072969 + 3 ^ 40 * 4161864 * 2
def baseEnd_4161864 : Nat := 1424691100429206614439961

theorem tailTrace_4161864 : CollatzResearch.WordTrace tailWord_4161864 prefixEnd_4161864 1424691100429206614439961 := by
  unfold tailWord_4161864
  simp only [CollatzResearch.WordTrace]
  refine ⟨75897825297142496313722323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101197100396189995084963097 75897825297142496313722323)
  ·
    refine ⟨113846737945713744470583485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75897825297142496313722323 113846737945713744470583485)
    ·
      refine ⟨42692526729642654176468807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113846737945713744470583485 42692526729642654176468807)
      ·
        refine ⟨64038790094463981264703211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42692526729642654176468807 64038790094463981264703211)
        ·
          refine ⟨96058185141695971897054817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64038790094463981264703211 96058185141695971897054817)
          ·
            refine ⟨72043638856271978922791113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96058185141695971897054817 72043638856271978922791113)
            ·
              refine ⟨54032729142203984192093335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72043638856271978922791113 54032729142203984192093335)
              ·
                refine ⟨81049093713305976288140003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54032729142203984192093335 81049093713305976288140003)
                ·
                  refine ⟨121573640569958964432210005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81049093713305976288140003 121573640569958964432210005)
                  ·
                    refine ⟨1424691100429206614439961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121573640569958964432210005 1424691100429206614439961)
                    ·
                      rfl

theorem cell22_4161864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_4161864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161864 prefixEnd_4161864 := by exact prefixLift 4161864
  have htrace : WordTrace (prefixWord ++ tailWord_4161864) baseStart_4161864 baseEnd_4161864 := by
    simpa [prefixWord, tailWord_4161864, baseEnd_4161864] using wordTrace_append hprefix tailTrace_4161864
  have hstable : (prefixWord ++ tailWord_4161864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161864).length < 2 ^ (prefixWord ++ tailWord_4161864).sum := by decide
  have hdescent : baseEnd_4161864 < baseStart_4161864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161896 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 7]
def baseStart_4161896 : Nat := 118140960795 + 4161896 * 2 ^ 59
def prefixEnd_4161896 : Nat := 4983230072969 + 3 ^ 40 * 4161896 * 2
def baseEnd_4161896 : Nat := 474900684894389732546621

theorem tailTrace_4161896 : CollatzResearch.WordTrace tailWord_4161896 prefixEnd_4161896 474900684894389732546621 := by
  unfold tailWord_4161896
  simp only [CollatzResearch.WordTrace]
  refine ⟨75898408865084531046304771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101197878486779374728406361 75898408865084531046304771)
  ·
    refine ⟨113847613297626796569457157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75898408865084531046304771 113847613297626796569457157)
    ·
      refine ⟨21346427493305024356773217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113847613297626796569457157 21346427493305024356773217)
      ·
        refine ⟨16009820619978768267579913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21346427493305024356773217 16009820619978768267579913)
        ·
          refine ⟨12007365464984076200684935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16009820619978768267579913 12007365464984076200684935)
          ·
            refine ⟨18011048197476114301027403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12007365464984076200684935 18011048197476114301027403)
            ·
              refine ⟨27016572296214171451541105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18011048197476114301027403 27016572296214171451541105)
              ·
                refine ⟨20262429222160628588655829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27016572296214171451541105 20262429222160628588655829)
                ·
                  refine ⟨474900684894389732546621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20262429222160628588655829 474900684894389732546621)
                  ·
                    rfl

theorem cell22_4161896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 7].length) (baseStart_4161896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161896 prefixEnd_4161896 := by exact prefixLift 4161896
  have htrace : WordTrace (prefixWord ++ tailWord_4161896) baseStart_4161896 baseEnd_4161896 := by
    simpa [prefixWord, tailWord_4161896, baseEnd_4161896] using wordTrace_append hprefix tailTrace_4161896
  have hstable : (prefixWord ++ tailWord_4161896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161896).length < 2 ^ (prefixWord ++ tailWord_4161896).sum := by decide
  have hdescent : baseEnd_4161896 < baseStart_4161896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161917 : List Nat := [1, 4, 1, 1, 2, 4, 3, 2, 1, 3]
def baseStart_4161917 : Nat := 118140960795 + 4161917 * 2 ^ 59
def prefixEnd_4161917 : Nat := 4983230072969 + 3 ^ 40 * 4161917 * 2
def baseEnd_4161917 : Nat := 1424709243412332142864799

theorem tailTrace_4161917 : CollatzResearch.WordTrace tailWord_4161917 prefixEnd_4161917 1424709243412332142864799 := by
  unfold tailWord_4161917
  simp only [CollatzResearch.WordTrace]
  refine ⟨151797583663092982679124005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101198389108728655119416003 151797583663092982679124005)
  ·
    refine ⟨28462046936829934252335751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151797583663092982679124005 28462046936829934252335751)
    ·
      refine ⟨42693070405244901378503627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28462046936829934252335751 42693070405244901378503627)
      ·
        refine ⟨64039605607867352067755441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42693070405244901378503627 64039605607867352067755441)
        ·
          refine ⟨48029704205900514050816581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64039605607867352067755441 48029704205900514050816581)
          ·
            refine ⟨9005569538606346384528109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48029704205900514050816581 9005569538606346384528109)
            ·
              refine ⟨3377088576977379894198041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9005569538606346384528109 3377088576977379894198041)
              ·
                refine ⟨2532816432733034920648531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3377088576977379894198041 2532816432733034920648531)
                ·
                  refine ⟨3799224649099552380972797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2532816432733034920648531 3799224649099552380972797)
                  ·
                    refine ⟨1424709243412332142864799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3799224649099552380972797 1424709243412332142864799)
                    ·
                      rfl

theorem cell22_4161917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_4161917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161917 prefixEnd_4161917 := by exact prefixLift 4161917
  have htrace : WordTrace (prefixWord ++ tailWord_4161917) baseStart_4161917 baseEnd_4161917 := by
    simpa [prefixWord, tailWord_4161917, baseEnd_4161917] using wordTrace_append hprefix tailTrace_4161917
  have hstable : (prefixWord ++ tailWord_4161917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161917).length < 2 ^ (prefixWord ++ tailWord_4161917).sum := by decide
  have hdescent : baseEnd_4161917 < baseStart_4161917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161930 : List Nat := [3, 1, 2, 5, 1, 1, 1, 3, 5]
def baseStart_4161930 : Nat := 118140960795 + 4161930 * 2 ^ 59
def prefixEnd_4161930 : Nat := 4983230072969 + 3 ^ 40 * 4161930 * 2
def baseEnd_4161930 : Nat := 474904564526001480763253

theorem tailTrace_4161930 : CollatzResearch.WordTrace tailWord_4161930 prefixEnd_4161930 474904564526001480763253 := by
  unfold tailWord_4161930
  simp only [CollatzResearch.WordTrace]
  refine ⟨37949514453011471474836811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101198705208030590599564829 37949514453011471474836811)
  ·
    refine ⟨56924271679517207212255217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37949514453011471474836811 56924271679517207212255217)
    ·
      refine ⟨42693203759637905409191413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56924271679517207212255217 42693203759637905409191413)
      ·
        refine ⟨4002487852466053632111695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42693203759637905409191413 4002487852466053632111695)
        ·
          refine ⟨6003731778699080448167543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4002487852466053632111695 6003731778699080448167543)
          ·
            refine ⟨9005597668048620672251315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6003731778699080448167543 9005597668048620672251315)
            ·
              refine ⟨13508396502072931008376973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9005597668048620672251315 13508396502072931008376973)
              ·
                refine ⟨5065648688277349128141365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13508396502072931008376973 5065648688277349128141365)
                ·
                  refine ⟨474904564526001480763253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5065648688277349128141365 474904564526001480763253)
                  ·
                    rfl

theorem cell22_4161930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_4161930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161930 prefixEnd_4161930 := by exact prefixLift 4161930
  have htrace : WordTrace (prefixWord ++ tailWord_4161930) baseStart_4161930 baseEnd_4161930 := by
    simpa [prefixWord, tailWord_4161930, baseEnd_4161930] using wordTrace_append hprefix tailTrace_4161930
  have hstable : (prefixWord ++ tailWord_4161930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161930).length < 2 ^ (prefixWord ++ tailWord_4161930).sum := by decide
  have hdescent : baseEnd_4161930 < baseStart_4161930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161943 : List Nat := [1, 1, 3, 3, 1, 1, 5, 2, 1, 4]
def baseStart_4161943 : Nat := 118140960795 + 4161943 * 2 ^ 59
def prefixEnd_4161943 : Nat := 4983230072969 + 3 ^ 40 * 4161943 * 2
def baseEnd_4161943 : Nat := 1424718143743676741714719

theorem tailTrace_4161943 : CollatzResearch.WordTrace tailWord_4161943 prefixEnd_4161943 1424718143743676741714719 := by
  unfold tailWord_4161943
  simp only [CollatzResearch.WordTrace]
  refine ⟨151798531960998789119570483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101199021307332526079713655 151798531960998789119570483)
  ·
    refine ⟨227697797941498183679355725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151798531960998789119570483 227697797941498183679355725)
    ·
      refine ⟨85386674228061818879758397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227697797941498183679355725 85386674228061818879758397)
      ·
        refine ⟨32020002835523182079909399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85386674228061818879758397 32020002835523182079909399)
        ·
          refine ⟨48030004253284773119864099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32020002835523182079909399 48030004253284773119864099)
          ·
            refine ⟨72045006379927159679796149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48030004253284773119864099 72045006379927159679796149)
            ·
              refine ⟨6754219348118171219980889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72045006379927159679796149 6754219348118171219980889)
              ·
                refine ⟨5065664511088628414985667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6754219348118171219980889 5065664511088628414985667)
                ·
                  refine ⟨7598496766632942622478501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5065664511088628414985667 7598496766632942622478501)
                  ·
                    refine ⟨1424718143743676741714719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7598496766632942622478501 1424718143743676741714719)
                    ·
                      rfl

theorem cell22_4161943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_4161943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161943 prefixEnd_4161943 := by exact prefixLift 4161943
  have htrace : WordTrace (prefixWord ++ tailWord_4161943) baseStart_4161943 baseEnd_4161943 := by
    simpa [prefixWord, tailWord_4161943, baseEnd_4161943] using wordTrace_append hprefix tailTrace_4161943
  have hstable : (prefixWord ++ tailWord_4161943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161943).length < 2 ^ (prefixWord ++ tailWord_4161943).sum := by decide
  have hdescent : baseEnd_4161943 < baseStart_4161943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161956 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_4161956 : Nat := 118140960795 + 4161956 * 2 ^ 59
def prefixEnd_4161956 : Nat := 4983230072969 + 3 ^ 40 * 4161956 * 2
def baseEnd_4161956 : Nat := 1424722593909349041139679

theorem tailTrace_4161956 : CollatzResearch.WordTrace tailWord_4161956 prefixEnd_4161956 1424722593909349041139679 := by
  unfold tailWord_4161956
  simp only [CollatzResearch.WordTrace]
  refine ⟨75899503054975846169896861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101199337406634461559862481 75899503054975846169896861)
  ·
    refine ⟨28462313645615942313711323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75899503054975846169896861 28462313645615942313711323)
    ·
      refine ⟨42693470468423913470566985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28462313645615942313711323 42693470468423913470566985)
      ·
        refine ⟨32020102851317935102925239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42693470468423913470566985 32020102851317935102925239)
        ·
          refine ⟨48030154276976902654387859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32020102851317935102925239 48030154276976902654387859)
          ·
            refine ⟨72045231415465353981581789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48030154276976902654387859 72045231415465353981581789)
            ·
              refine ⟨27016961780799507743093171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72045231415465353981581789 27016961780799507743093171)
              ·
                refine ⟨40525442671199261614639757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27016961780799507743093171 40525442671199261614639757)
                ·
                  refine ⟨15197041001699723105489909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40525442671199261614639757 15197041001699723105489909)
                  ·
                    refine ⟨1424722593909349041139679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15197041001699723105489909 1424722593909349041139679)
                    ·
                      rfl

theorem cell22_4161956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_4161956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161956 prefixEnd_4161956 := by exact prefixLift 4161956
  have htrace : WordTrace (prefixWord ++ tailWord_4161956) baseStart_4161956 baseEnd_4161956 := by
    simpa [prefixWord, tailWord_4161956, baseEnd_4161956] using wordTrace_append hprefix tailTrace_4161956
  have hstable : (prefixWord ++ tailWord_4161956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161956).length < 2 ^ (prefixWord ++ tailWord_4161956).sum := by decide
  have hdescent : baseEnd_4161956 < baseStart_4161956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161975 : List Nat := [1, 1, 3, 1, 3, 3, 4, 2, 4]
def baseStart_4161975 : Nat := 118140960795 + 4161975 * 2 ^ 59
def prefixEnd_4161975 : Nat := 4983230072969 + 3 ^ 40 * 4161975 * 2
def baseEnd_4161975 : Nat := 474909699332546441638207

theorem tailTrace_4161975 : CollatzResearch.WordTrace tailWord_4161975 prefixEnd_4161975 474909699332546441638207 := by
  unfold tailWord_4161975
  simp only [CollatzResearch.WordTrace]
  refine ⟨151799699096882858584735379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101199799397921905723156919 151799699096882858584735379)
  ·
    refine ⟨227699548645324287877103069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151799699096882858584735379 227699548645324287877103069)
    ·
      refine ⟨85387330741996607953913651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227699548645324287877103069 85387330741996607953913651)
      ·
        refine ⟨128080996112994911930870477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85387330741996607953913651 128080996112994911930870477)
        ·
          refine ⟨48030373542373091974076429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128080996112994911930870477 48030373542373091974076429)
          ·
            refine ⟨18011390078389909490278661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48030373542373091974076429 18011390078389909490278661)
            ·
              refine ⟨3377135639698108029427249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18011390078389909490278661 3377135639698108029427249)
              ·
                refine ⟨2532851729773581022070437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3377135639698108029427249 2532851729773581022070437)
                ·
                  refine ⟨474909699332546441638207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2532851729773581022070437 474909699332546441638207)
                  ·
                    rfl

theorem cell22_4161975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 4].length) (baseStart_4161975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4161975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4161975 prefixEnd_4161975 := by exact prefixLift 4161975
  have htrace : WordTrace (prefixWord ++ tailWord_4161975) baseStart_4161975 baseEnd_4161975 := by
    simpa [prefixWord, tailWord_4161975, baseEnd_4161975] using wordTrace_append hprefix tailTrace_4161975
  have hstable : (prefixWord ++ tailWord_4161975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161975).length < 2 ^ (prefixWord ++ tailWord_4161975).sum := by decide
  have hdescent : baseEnd_4161975 < baseStart_4161975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162005 : List Nat := [1, 3, 2, 3, 1, 4, 1, 1, 2, 4]
def baseStart_4162005 : Nat := 118140960795 + 4162005 * 2 ^ 59
def prefixEnd_4162005 : Nat := 4983230072969 + 3 ^ 40 * 4162005 * 2
def baseEnd_4162005 : Nat := 1424739367610729246664529

theorem tailTrace_4162005 : CollatzResearch.WordTrace tailWord_4162005 prefixEnd_4162005 1424739367610729246664529 := by
  unfold tailWord_4162005
  simp only [CollatzResearch.WordTrace]
  refine ⟨151800793286774173708327469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101200528857849449138884979 151800793286774173708327469)
  ·
    refine ⟨56925297482540315140622801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151800793286774173708327469 56925297482540315140622801)
    ·
      refine ⟨42693973111905236355467101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56925297482540315140622801 42693973111905236355467101)
      ·
        refine ⟨16010239916964463633300163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42693973111905236355467101 16010239916964463633300163)
        ·
          refine ⟨24015359875446695449950245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16010239916964463633300163 24015359875446695449950245)
          ·
            refine ⟨4502879976646255396865671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24015359875446695449950245 4502879976646255396865671)
            ·
              refine ⟨6754319964969383095298507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4502879976646255396865671 6754319964969383095298507)
              ·
                refine ⟨10131479947454074642947761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6754319964969383095298507 10131479947454074642947761)
                ·
                  refine ⟨7598609960590555982210821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10131479947454074642947761 7598609960590555982210821)
                  ·
                    refine ⟨1424739367610729246664529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7598609960590555982210821 1424739367610729246664529)
                    ·
                      rfl

theorem cell22_4162005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_4162005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162005 prefixEnd_4162005 := by exact prefixLift 4162005
  have htrace : WordTrace (prefixWord ++ tailWord_4162005) baseStart_4162005 baseEnd_4162005 := by
    simpa [prefixWord, tailWord_4162005, baseEnd_4162005] using wordTrace_append hprefix tailTrace_4162005
  have hstable : (prefixWord ++ tailWord_4162005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162005).length < 2 ^ (prefixWord ++ tailWord_4162005).sum := by decide
  have hdescent : baseEnd_4162005 < baseStart_4162005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162035 : List Nat := [1, 1, 1, 2, 2, 2, 3, 6, 1, 3]
def baseStart_4162035 : Nat := 118140960795 + 4162035 * 2 ^ 59
def prefixEnd_4162035 : Nat := 4983230072969 + 3 ^ 40 * 4162035 * 2
def baseEnd_4162035 : Nat := 1424749637223819168414437

theorem tailTrace_4162035 : CollatzResearch.WordTrace tailWord_4162035 prefixEnd_4162035 1424749637223819168414437 := by
  unfold tailWord_4162035
  simp only [CollatzResearch.WordTrace]
  refine ⟨151801887476665488831919559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101201258317776992554613039 151801887476665488831919559)
  ·
    refine ⟨227702831214998233247879339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151801887476665488831919559 227702831214998233247879339)
    ·
      refine ⟨341554246822497349871819009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227702831214998233247879339 341554246822497349871819009)
      ·
        refine ⟨256165685116873012403864257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341554246822497349871819009 256165685116873012403864257)
        ·
          refine ⟨192124263837654759302898193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256165685116873012403864257 192124263837654759302898193)
          ·
            refine ⟨144093197878241069477173645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192124263837654759302898193 144093197878241069477173645)
            ·
              refine ⟨54034949204340401053940117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144093197878241069477173645 54034949204340401053940117)
              ·
                refine ⟨2532888243953456299403443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54034949204340401053940117 2532888243953456299403443)
                ·
                  refine ⟨3799332365930184449105165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2532888243953456299403443 3799332365930184449105165)
                  ·
                    refine ⟨1424749637223819168414437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3799332365930184449105165 1424749637223819168414437)
                    ·
                      rfl

theorem cell22_4162035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 1, 3].length) (baseStart_4162035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162035 prefixEnd_4162035 := by exact prefixLift 4162035
  have htrace : WordTrace (prefixWord ++ tailWord_4162035) baseStart_4162035 baseEnd_4162035 := by
    simpa [prefixWord, tailWord_4162035, baseEnd_4162035] using wordTrace_append hprefix tailTrace_4162035
  have hstable : (prefixWord ++ tailWord_4162035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162035).length < 2 ^ (prefixWord ++ tailWord_4162035).sum := by decide
  have hdescent : baseEnd_4162035 < baseStart_4162035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162054 : List Nat := [6, 2, 1, 1, 1, 1, 4, 6]
def baseStart_4162054 : Nat := 118140960795 + 4162054 * 2 ^ 59
def prefixEnd_4162054 : Nat := 4983230072969 + 3 ^ 40 * 4162054 * 2
def baseEnd_4162054 : Nat := 158306237923567716909931

theorem tailTrace_4162054 : CollatzResearch.WordTrace tailWord_4162054 prefixEnd_4162054 158306237923567716909931 := by
  unfold tailWord_4162054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4743830639487395471151913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101201720309064436717907477 4743830639487395471151913)
  ·
    refine ⟨3557872979615546603363935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4743830639487395471151913 3557872979615546603363935)
    ·
      refine ⟨5336809469423319905045903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3557872979615546603363935 5336809469423319905045903)
      ·
        refine ⟨8005214204134979857568855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5336809469423319905045903 8005214204134979857568855)
        ·
          refine ⟨12007821306202469786353283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8005214204134979857568855 12007821306202469786353283)
          ·
            refine ⟨18011731959303704679529925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12007821306202469786353283 18011731959303704679529925)
            ·
              refine ⟨3377199742369444627411861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18011731959303704679529925 3377199742369444627411861)
              ·
                refine ⟨158306237923567716909931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3377199742369444627411861 158306237923567716909931)
                ·
                  rfl

theorem cell22_4162054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_4162054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162054 prefixEnd_4162054 := by exact prefixLift 4162054
  have htrace : WordTrace (prefixWord ++ tailWord_4162054) baseStart_4162054 baseEnd_4162054 := by
    simpa [prefixWord, tailWord_4162054, baseEnd_4162054] using wordTrace_append hprefix tailTrace_4162054
  have hstable : (prefixWord ++ tailWord_4162054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162054).length < 2 ^ (prefixWord ++ tailWord_4162054).sum := by decide
  have hdescent : baseEnd_4162054 < baseStart_4162054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162123 : List Nat := [1, 1, 1, 1, 3, 1, 5, 3, 2, 4]
def baseStart_4162123 : Nat := 118140960795 + 4162123 * 2 ^ 59
def prefixEnd_4162123 : Nat := 4983230072969 + 3 ^ 40 * 4162123 * 2
def baseEnd_4162123 : Nat := 1424779761422216272214167

theorem tailTrace_4162123 : CollatzResearch.WordTrace tailWord_4162123 prefixEnd_4162123 1424779761422216272214167 := by
  unfold tailWord_4162123
  simp only [CollatzResearch.WordTrace]
  refine ⟨151805097100346679861123023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101203398066897786574082015 151805097100346679861123023)
  ·
    refine ⟨227707645650520019791684535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151805097100346679861123023 227707645650520019791684535)
    ·
      refine ⟨341561468475780029687526803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227707645650520019791684535 341561468475780029687526803)
      ·
        refine ⟨512342202713670044531290205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341561468475780029687526803 512342202713670044531290205)
        ·
          refine ⟨192128326017626266699233827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512342202713670044531290205 192128326017626266699233827)
          ·
            refine ⟨288192489026439400048850741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192128326017626266699233827 288192489026439400048850741)
            ·
              refine ⟨27018045846228693754579757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 288192489026439400048850741 27018045846228693754579757)
              ·
                refine ⟨10131767192335760157967409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27018045846228693754579757 10131767192335760157967409)
                ·
                  refine ⟨7598825394251820118475557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10131767192335760157967409 7598825394251820118475557)
                  ·
                    refine ⟨1424779761422216272214167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7598825394251820118475557 1424779761422216272214167)
                    ·
                      rfl

theorem cell22_4162123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 4].length) (baseStart_4162123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162123 prefixEnd_4162123 := by exact prefixLift 4162123
  have htrace : WordTrace (prefixWord ++ tailWord_4162123) baseStart_4162123 baseEnd_4162123 := by
    simpa [prefixWord, tailWord_4162123, baseEnd_4162123] using wordTrace_append hprefix tailTrace_4162123
  have hstable : (prefixWord ++ tailWord_4162123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162123).length < 2 ^ (prefixWord ++ tailWord_4162123).sum := by decide
  have hdescent : baseEnd_4162123 < baseStart_4162123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162125 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_4162125 : Nat := 118140960795 + 4162125 * 2 ^ 59
def prefixEnd_4162125 : Nat := 4983230072969 + 3 ^ 40 * 4162125 * 2
def baseEnd_4162125 : Nat := 1424780446063088933664161

theorem tailTrace_4162125 : CollatzResearch.WordTrace tailWord_4162125 prefixEnd_4162125 1424780446063088933664161 := by
  unfold tailWord_4162125
  simp only [CollatzResearch.WordTrace]
  refine ⟨151805170046339434202695829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101203446697559622801797219 151805170046339434202695829)
  ·
    refine ⟨7115867345922160978251367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151805170046339434202695829 7115867345922160978251367)
    ·
      refine ⟨10673801018883241467377051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7115867345922160978251367 10673801018883241467377051)
      ·
        refine ⟨16010701528324862201065577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10673801018883241467377051 16010701528324862201065577)
        ·
          refine ⟨12008026146243646650799183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16010701528324862201065577 12008026146243646650799183)
          ·
            refine ⟨18012039219365469976198775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12008026146243646650799183 18012039219365469976198775)
            ·
              refine ⟨27018058829048204964298163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18012039219365469976198775 27018058829048204964298163)
              ·
                refine ⟨40527088243572307446447245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27018058829048204964298163 40527088243572307446447245)
                ·
                  refine ⟨15197658091339615292417717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40527088243572307446447245 15197658091339615292417717)
                  ·
                    refine ⟨1424780446063088933664161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15197658091339615292417717 1424780446063088933664161)
                    ·
                      rfl

theorem cell22_4162125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_4162125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162125 prefixEnd_4162125 := by exact prefixLift 4162125
  have htrace : WordTrace (prefixWord ++ tailWord_4162125) baseStart_4162125 baseEnd_4162125 := by
    simpa [prefixWord, tailWord_4162125, baseEnd_4162125] using wordTrace_append hprefix tailTrace_4162125
  have hstable : (prefixWord ++ tailWord_4162125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162125).length < 2 ^ (prefixWord ++ tailWord_4162125).sum := by decide
  have hdescent : baseEnd_4162125 < baseStart_4162125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162178 : List Nat := [3, 4, 3, 1, 1, 1, 2, 3, 4]
def baseStart_4162178 : Nat := 118140960795 + 4162178 * 2 ^ 59
def prefixEnd_4162178 : Nat := 4983230072969 + 3 ^ 40 * 4162178 * 2
def baseEnd_4162178 : Nat := 474932863015404820696333

theorem tailTrace_4162178 : CollatzResearch.WordTrace tailWord_4162178 prefixEnd_4162178 474932863015404820696333 := by
  unfold tailWord_4162178
  simp only [CollatzResearch.WordTrace]
  refine ⟨37951775778786856063593797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101204735410098282836250125 37951775778786856063593797)
  ·
    refine ⟨7115957958522535511923837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37951775778786856063593797 7115957958522535511923837)
    ·
      refine ⟨2668484234445950816971439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7115957958522535511923837 2668484234445950816971439)
      ·
        refine ⟨4002726351668926225457159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2668484234445950816971439 4002726351668926225457159)
        ·
          refine ⟨6004089527503389338185739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4002726351668926225457159 6004089527503389338185739)
          ·
            refine ⟨9006134291255084007278609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6004089527503389338185739 9006134291255084007278609)
            ·
              refine ⟨6754600718441313005458957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9006134291255084007278609 6754600718441313005458957)
              ·
                refine ⟨2532975269415492377047109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6754600718441313005458957 2532975269415492377047109)
                ·
                  refine ⟨474932863015404820696333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2532975269415492377047109 474932863015404820696333)
                  ·
                    rfl

theorem cell22_4162178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_4162178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162178 prefixEnd_4162178 := by exact prefixLift 4162178
  have htrace : WordTrace (prefixWord ++ tailWord_4162178) baseStart_4162178 baseEnd_4162178 := by
    simpa [prefixWord, tailWord_4162178, baseEnd_4162178] using wordTrace_append hprefix tailTrace_4162178
  have hstable : (prefixWord ++ tailWord_4162178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162178).length < 2 ^ (prefixWord ++ tailWord_4162178).sum := by decide
  have hdescent : baseEnd_4162178 < baseStart_4162178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162183 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 7]
def baseStart_4162183 : Nat := 118140960795 + 4162183 * 2 ^ 59
def prefixEnd_4162183 : Nat := 4983230072969 + 3 ^ 40 * 4162183 * 2
def baseEnd_4162183 : Nat := 474933433549465371904661

theorem tailTrace_4162183 : CollatzResearch.WordTrace tailWord_4162183 prefixEnd_4162183 474933433549465371904661 := by
  unfold tailWord_4162183
  simp only [CollatzResearch.WordTrace]
  refine ⟨151807285480129310108307203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101204856986752873405538135 151807285480129310108307203)
  ·
    refine ⟨227710928220193965162460805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151807285480129310108307203 227710928220193965162460805)
    ·
      refine ⟨42695799041286368467961401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227710928220193965162460805 42695799041286368467961401)
      ·
        refine ⟨32021849280964776350971051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42695799041286368467961401 32021849280964776350971051)
        ·
          refine ⟨48032773921447164526456577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32021849280964776350971051 48032773921447164526456577)
          ·
            refine ⟨36024580441085373394842433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48032773921447164526456577 36024580441085373394842433)
            ·
              refine ⟨27018435330814030046131825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36024580441085373394842433 27018435330814030046131825)
              ·
                refine ⟨20263826498110522534598869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27018435330814030046131825 20263826498110522534598869)
                ·
                  refine ⟨474933433549465371904661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20263826498110522534598869 474933433549465371904661)
                  ·
                    rfl

theorem cell22_4162183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 7].length) (baseStart_4162183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162183 prefixEnd_4162183 := by exact prefixLift 4162183
  have htrace : WordTrace (prefixWord ++ tailWord_4162183) baseStart_4162183 baseEnd_4162183 := by
    simpa [prefixWord, tailWord_4162183, baseEnd_4162183] using wordTrace_append hprefix tailTrace_4162183
  have hstable : (prefixWord ++ tailWord_4162183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162183).length < 2 ^ (prefixWord ++ tailWord_4162183).sum := by decide
  have hdescent : baseEnd_4162183 < baseStart_4162183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162204 : List Nat := [2, 2, 3, 2, 2, 1, 2, 4, 1, 3]
def baseStart_4162204 : Nat := 118140960795 + 4162204 * 2 ^ 59
def prefixEnd_4162204 : Nat := 4983230072969 + 3 ^ 40 * 4162204 * 2
def baseEnd_4162204 : Nat := 1424807489377559060938919

theorem tailTrace_4162204 : CollatzResearch.WordTrace tailWord_4162204 prefixEnd_4162204 1424807489377559060938919 := by
  unfold tailWord_4162204
  simp only [CollatzResearch.WordTrace]
  refine ⟨75904025706526615347410833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101205367608702153796547777 75904025706526615347410833)
  ·
    refine ⟨56928019279894961510558125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75904025706526615347410833 56928019279894961510558125)
    ·
      refine ⟨21348007229960610566459297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56928019279894961510558125 21348007229960610566459297)
      ·
        refine ⟨16011005422470457924844473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21348007229960610566459297 16011005422470457924844473)
        ·
          refine ⟨12008254066852843443633355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16011005422470457924844473 12008254066852843443633355)
          ·
            refine ⟨18012381100279265165450033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12008254066852843443633355 18012381100279265165450033)
            ·
              refine ⟨13509285825209448874087525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18012381100279265165450033 13509285825209448874087525)
              ·
                refine ⟨2532991092226771663891411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13509285825209448874087525 2532991092226771663891411)
                ·
                  refine ⟨3799486638340157495837117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2532991092226771663891411 3799486638340157495837117)
                  ·
                    refine ⟨1424807489377559060938919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3799486638340157495837117 1424807489377559060938919)
                    ·
                      rfl

theorem cell22_4162204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_4162204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162204 prefixEnd_4162204 := by exact prefixLift 4162204
  have htrace : WordTrace (prefixWord ++ tailWord_4162204) baseStart_4162204 baseEnd_4162204 := by
    simpa [prefixWord, tailWord_4162204, baseEnd_4162204] using wordTrace_append hprefix tailTrace_4162204
  have hstable : (prefixWord ++ tailWord_4162204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162204).length < 2 ^ (prefixWord ++ tailWord_4162204).sum := by decide
  have hdescent : baseEnd_4162204 < baseStart_4162204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162290 : List Nat := [3, 2, 1, 3, 1, 2, 2, 8]
def baseStart_4162290 : Nat := 118140960795 + 4162290 * 2 ^ 59
def prefixEnd_4162290 : Nat := 4983230072969 + 3 ^ 40 * 4162290 * 2
def baseEnd_4162290 : Nat := 158315214326120389254295

theorem tailTrace_4162290 : CollatzResearch.WordTrace tailWord_4162290 prefixEnd_4162290 158315214326120389254295 := by
  unfold tailWord_4162290
  simp only [CollatzResearch.WordTrace]
  refine ⟨37952797022685416845613081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101207458727161111588301549 37952797022685416845613081)
  ·
    refine ⟨28464597767014062634209811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37952797022685416845613081 28464597767014062634209811)
    ·
      refine ⟨42696896650521093951314717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28464597767014062634209811 42696896650521093951314717)
      ·
        refine ⟨16011336243945410231743019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42696896650521093951314717 16011336243945410231743019)
        ·
          refine ⟨24017004365918115347614529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16011336243945410231743019 24017004365918115347614529)
          ·
            refine ⟨18012753274438586510710897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24017004365918115347614529 18012753274438586510710897)
            ·
              refine ⟨13509564955828939883033173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18012753274438586510710897 13509564955828939883033173)
              ·
                refine ⟨158315214326120389254295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13509564955828939883033173 158315214326120389254295)
                ·
                  rfl

theorem cell22_4162290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 8].length) (baseStart_4162290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162290 prefixEnd_4162290 := by exact prefixLift 4162290
  have htrace : WordTrace (prefixWord ++ tailWord_4162290) baseStart_4162290 baseEnd_4162290 := by
    simpa [prefixWord, tailWord_4162290, baseEnd_4162290] using wordTrace_append hprefix tailTrace_4162290
  have hstable : (prefixWord ++ tailWord_4162290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162290).length < 2 ^ (prefixWord ++ tailWord_4162290).sum := by decide
  have hdescent : baseEnd_4162290 < baseStart_4162290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162369 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 7]
def baseStart_4162369 : Nat := 118140960795 + 4162369 * 2 ^ 59
def prefixEnd_4162369 : Nat := 4983230072969 + 3 ^ 40 * 4162369 * 2
def baseEnd_4162369 : Nat := 474954657416517876854471

theorem tailTrace_4162369 : CollatzResearch.WordTrace tailWord_4162369 prefixEnd_4162369 474954657416517876854471 := by
  unfold tailWord_4162369
  simp only [CollatzResearch.WordTrace]
  refine ⟨151814069457455463874578161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101209379638303642583052107 151814069457455463874578161)
  ·
    refine ⟨113860552093091597905933621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151814069457455463874578161 113860552093091597905933621)
    ·
      refine ⟨10674426758727337303681277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113860552093091597905933621 10674426758727337303681277)
      ·
        refine ⟨4002910034522751488880479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10674426758727337303681277 4002910034522751488880479)
        ·
          refine ⟨6004365051784127233320719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4002910034522751488880479 6004365051784127233320719)
          ·
            refine ⟨9006547577676190849981079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6004365051784127233320719 9006547577676190849981079)
            ·
              refine ⟨13509821366514286274971619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9006547577676190849981079 13509821366514286274971619)
              ·
                refine ⟨20264732049771429412457429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13509821366514286274971619 20264732049771429412457429)
                ·
                  refine ⟨474954657416517876854471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20264732049771429412457429 474954657416517876854471)
                  ·
                    rfl

theorem cell22_4162369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 7].length) (baseStart_4162369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162369 prefixEnd_4162369 := by exact prefixLift 4162369
  have htrace : WordTrace (prefixWord ++ tailWord_4162369) baseStart_4162369 baseEnd_4162369 := by
    simpa [prefixWord, tailWord_4162369, baseEnd_4162369] using wordTrace_append hprefix tailTrace_4162369
  have hstable : (prefixWord ++ tailWord_4162369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162369).length < 2 ^ (prefixWord ++ tailWord_4162369).sum := by decide
  have hdescent : baseEnd_4162369 < baseStart_4162369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162412 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 6, 3]
def baseStart_4162412 : Nat := 118140960795 + 4162412 * 2 ^ 59
def prefixEnd_4162412 : Nat := 4983230072969 + 3 ^ 40 * 4162412 * 2
def baseEnd_4162412 : Nat := 1424878692028315851738281

theorem tailTrace_4162412 : CollatzResearch.WordTrace tailWord_4162412 prefixEnd_4162412 1424878692028315851738281 := by
  unfold tailWord_4162412
  simp only [CollatzResearch.WordTrace]
  refine ⟨75907818898149841109196745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101210425197533121478928993 75907818898149841109196745)
  ·
    refine ⟨56930864173612380831897559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75907818898149841109196745 56930864173612380831897559)
    ·
      refine ⟨85396296260418571247846339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56930864173612380831897559 85396296260418571247846339)
      ·
        refine ⟨128094444390627856871769509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85396296260418571247846339 128094444390627856871769509)
        ·
          refine ⟨24017708323242723163456783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128094444390627856871769509 24017708323242723163456783)
          ·
            refine ⟨36026562484864084745185175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24017708323242723163456783 36026562484864084745185175)
            ·
              refine ⟨54039843727296127117777763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36026562484864084745185175 54039843727296127117777763)
              ·
                refine ⟨81059765590944190676666645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54039843727296127117777763 81059765590944190676666645)
                ·
                  refine ⟨3799676512075508937968749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81059765590944190676666645 3799676512075508937968749)
                  ·
                    refine ⟨1424878692028315851738281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3799676512075508937968749 1424878692028315851738281)
                    ·
                      rfl

theorem cell22_4162412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_4162412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162412 prefixEnd_4162412 := by exact prefixLift 4162412
  have htrace : WordTrace (prefixWord ++ tailWord_4162412) baseStart_4162412 baseEnd_4162412 := by
    simpa [prefixWord, tailWord_4162412, baseEnd_4162412] using wordTrace_append hprefix tailTrace_4162412
  have hstable : (prefixWord ++ tailWord_4162412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162412).length < 2 ^ (prefixWord ++ tailWord_4162412).sum := by decide
  have hdescent : baseEnd_4162412 < baseStart_4162412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162425 : List Nat := [1, 2, 1, 3, 2, 3, 10]
def baseStart_4162425 : Nat := 118140960795 + 4162425 * 2 ^ 59
def prefixEnd_4162425 : Nat := 4983230072969 + 3 ^ 40 * 4162425 * 2
def baseEnd_4162425 : Nat := 52773449710888450043083

theorem tailTrace_4162425 : CollatzResearch.WordTrace tailWord_4162425 prefixEnd_4162425 52773449710888450043083 := by
  unfold tailWord_4162425
  simp only [CollatzResearch.WordTrace]
  refine ⟨151816111945252585438616729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101210741296835056959077819 151816111945252585438616729)
  ·
    refine ⟨113862083958939439078962547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151816111945252585438616729 113862083958939439078962547)
    ·
      refine ⟨170793125938409158618443821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113862083958939439078962547 170793125938409158618443821)
      ·
        refine ⟨64047422226903434481916433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170793125938409158618443821 64047422226903434481916433)
        ·
          refine ⟨48035566670177575861437325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64047422226903434481916433 48035566670177575861437325)
          ·
            refine ⟨18013337501316590948038997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48035566670177575861437325 18013337501316590948038997)
            ·
              refine ⟨52773449710888450043083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 18013337501316590948038997 52773449710888450043083)
              ·
                rfl

theorem cell22_4162425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 10].length) (baseStart_4162425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162425 prefixEnd_4162425 := by exact prefixLift 4162425
  have htrace : WordTrace (prefixWord ++ tailWord_4162425) baseStart_4162425 baseEnd_4162425 := by
    simpa [prefixWord, tailWord_4162425, baseEnd_4162425] using wordTrace_append hprefix tailTrace_4162425
  have hstable : (prefixWord ++ tailWord_4162425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162425).length < 2 ^ (prefixWord ++ tailWord_4162425).sum := by decide
  have hdescent : baseEnd_4162425 < baseStart_4162425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162442 : List Nat := [3, 1, 2, 4, 1, 1, 1, 9]
def baseStart_4162442 : Nat := 118140960795 + 4162442 * 2 ^ 59
def prefixEnd_4162442 : Nat := 4983230072969 + 3 ^ 40 * 4162442 * 2
def baseEnd_4162442 : Nat := 158320995737933974832021

theorem tailTrace_4162442 : CollatzResearch.WordTrace tailWord_4162442 prefixEnd_4162442 158320995737933974832021 := by
  unfold tailWord_4162442
  simp only [CollatzResearch.WordTrace]
  refine ⟨37954182996547749335496395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101211154657460664894657053 37954182996547749335496395)
  ·
    refine ⟨56931274494821624003244593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37954182996547749335496395 56931274494821624003244593)
    ·
      refine ⟨42698455871116218002433445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56931274494821624003244593 42698455871116218002433445)
      ·
        refine ⟨8005960475834290875456271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42698455871116218002433445 8005960475834290875456271)
        ·
          refine ⟨12008940713751436313184407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8005960475834290875456271 12008940713751436313184407)
          ·
            refine ⟨18013411070627154469776611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12008940713751436313184407 18013411070627154469776611)
            ·
              refine ⟨27020116605940731704664917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18013411070627154469776611 27020116605940731704664917)
              ·
                refine ⟨158320995737933974832021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27020116605940731704664917 158320995737933974832021)
                ·
                  rfl

theorem cell22_4162442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 9].length) (baseStart_4162442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162442 prefixEnd_4162442 := by exact prefixLift 4162442
  have htrace : WordTrace (prefixWord ++ tailWord_4162442) baseStart_4162442 baseEnd_4162442 := by
    simpa [prefixWord, tailWord_4162442, baseEnd_4162442] using wordTrace_append hprefix tailTrace_4162442
  have hstable : (prefixWord ++ tailWord_4162442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162442).length < 2 ^ (prefixWord ++ tailWord_4162442).sum := by decide
  have hdescent : baseEnd_4162442 < baseStart_4162442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162457 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 5, 3]
def baseStart_4162457 : Nat := 118140960795 + 4162457 * 2 ^ 59
def prefixEnd_4162457 : Nat := 4983230072969 + 3 ^ 40 * 4162457 * 2
def baseEnd_4162457 : Nat := 1424894096447950734363143

theorem tailTrace_4162457 : CollatzResearch.WordTrace tailWord_4162457 prefixEnd_4162457 1424894096447950734363143 := by
  unfold tailWord_4162457
  simp only [CollatzResearch.WordTrace]
  refine ⟨151817279081136654903781625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101211519387424436602521083 151817279081136654903781625)
  ·
    refine ⟨113862959310852491177836219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151817279081136654903781625 113862959310852491177836219)
    ·
      refine ⟨170794438966278736766754329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113862959310852491177836219 170794438966278736766754329)
      ·
        refine ⟨128095829224709052575065747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170794438966278736766754329 128095829224709052575065747)
        ·
          refine ⟨192143743837063578862598621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128095829224709052575065747 192143743837063578862598621)
          ·
            refine ⟨72053903938898842073474483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192143743837063578862598621 72053903938898842073474483)
            ·
              refine ⟨108080855908348263110211725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72053903938898842073474483 108080855908348263110211725)
              ·
                refine ⟨40530320965630598666329397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108080855908348263110211725 40530320965630598666329397)
                ·
                  refine ⟨3799717590527868624968381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40530320965630598666329397 3799717590527868624968381)
                  ·
                    refine ⟨1424894096447950734363143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3799717590527868624968381 1424894096447950734363143)
                    ·
                      rfl

theorem cell22_4162457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 3].length) (baseStart_4162457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162457 prefixEnd_4162457 := by exact prefixLift 4162457
  have htrace : WordTrace (prefixWord ++ tailWord_4162457) baseStart_4162457 baseEnd_4162457 := by
    simpa [prefixWord, tailWord_4162457, baseEnd_4162457] using wordTrace_append hprefix tailTrace_4162457
  have hstable : (prefixWord ++ tailWord_4162457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162457).length < 2 ^ (prefixWord ++ tailWord_4162457).sum := by decide
  have hdescent : baseEnd_4162457 < baseStart_4162457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162487 : List Nat := [1, 1, 3, 1, 3, 1, 3, 4, 5]
def baseStart_4162487 : Nat := 118140960795 + 4162487 * 2 ^ 59
def prefixEnd_4162487 : Nat := 4983230072969 + 3 ^ 40 * 4162487 * 2
def baseEnd_4162487 : Nat := 474968122020346885371017

theorem tailTrace_4162487 : CollatzResearch.WordTrace tailWord_4162487 prefixEnd_4162487 474968122020346885371017 := by
  unfold tailWord_4162487
  simp only [CollatzResearch.WordTrace]
  refine ⟨151818373271027970027373715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101212248847351980018249143 151818373271027970027373715)
  ·
    refine ⟨227727559906541955041060573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151818373271027970027373715 227727559906541955041060573)
    ·
      refine ⟨85397834964953233140397715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227727559906541955041060573 85397834964953233140397715)
      ·
        refine ⟨128096752447429849710596573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85397834964953233140397715 128096752447429849710596573)
        ·
          refine ⟨48036282167786193641473715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128096752447429849710596573 48036282167786193641473715)
          ·
            refine ⟨72054423251679290462210573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48036282167786193641473715 72054423251679290462210573)
            ·
              refine ⟨27020408719379733923328965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72054423251679290462210573 27020408719379733923328965)
              ·
                refine ⟨5066326634883700110624181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27020408719379733923328965 5066326634883700110624181)
                ·
                  refine ⟨474968122020346885371017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5066326634883700110624181 474968122020346885371017)
                  ·
                    rfl

theorem cell22_4162487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 5].length) (baseStart_4162487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162487 prefixEnd_4162487 := by exact prefixLift 4162487
  have htrace : WordTrace (prefixWord ++ tailWord_4162487) baseStart_4162487 baseEnd_4162487 := by
    simpa [prefixWord, tailWord_4162487, baseEnd_4162487] using wordTrace_append hprefix tailTrace_4162487
  have hstable : (prefixWord ++ tailWord_4162487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162487).length < 2 ^ (prefixWord ++ tailWord_4162487).sum := by decide
  have hdescent : baseEnd_4162487 < baseStart_4162487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162583 : List Nat := [1, 1, 3, 5, 1, 3, 1, 3, 4]
def baseStart_4162583 : Nat := 118140960795 + 4162583 * 2 ^ 59
def prefixEnd_4162583 : Nat := 4983230072969 + 3 ^ 40 * 4162583 * 2
def baseEnd_4162583 : Nat := 474979076274309468570919

theorem tailTrace_4162583 : CollatzResearch.WordTrace tailWord_4162583 prefixEnd_4162583 474979076274309468570919 := by
  unfold tailWord_4162583
  simp only [CollatzResearch.WordTrace]
  refine ⟨151821874678680178422868403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101214583119120118948578935 151821874678680178422868403)
  ·
    refine ⟨227732812018020267634302605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151821874678680178422868403 227732812018020267634302605)
    ·
      refine ⟨85399804506757600362863477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227732812018020267634302605 85399804506757600362863477)
      ·
        refine ⟨8006231672508525034018451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85399804506757600362863477 8006231672508525034018451)
        ·
          refine ⟨12009347508762787551027677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8006231672508525034018451 12009347508762787551027677)
          ·
            refine ⟨4503505315786045331635379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12009347508762787551027677 4503505315786045331635379)
            ·
              refine ⟨6755257973679067997453069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4503505315786045331635379 6755257973679067997453069)
              ·
                refine ⟨2533221740129650499044901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6755257973679067997453069 2533221740129650499044901)
                ·
                  refine ⟨474979076274309468570919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2533221740129650499044901 474979076274309468570919)
                  ·
                    rfl

theorem cell22_4162583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 4].length) (baseStart_4162583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162583 prefixEnd_4162583 := by exact prefixLift 4162583
  have htrace : WordTrace (prefixWord ++ tailWord_4162583) baseStart_4162583 baseEnd_4162583 := by
    simpa [prefixWord, tailWord_4162583, baseEnd_4162583] using wordTrace_append hprefix tailTrace_4162583
  have hstable : (prefixWord ++ tailWord_4162583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162583).length < 2 ^ (prefixWord ++ tailWord_4162583).sum := by decide
  have hdescent : baseEnd_4162583 < baseStart_4162583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162594 : List Nat := [3, 3, 1, 1, 1, 5, 8]
def baseStart_4162594 : Nat := 118140960795 + 4162594 * 2 ^ 59
def prefixEnd_4162594 : Nat := 4983230072969 + 3 ^ 40 * 4162594 * 2
def baseEnd_4162594 : Nat := 52775592383249186803249

theorem tailTrace_4162594 : CollatzResearch.WordTrace tailWord_4162594 prefixEnd_4162594 52775592383249186803249 := by
  unfold tailWord_4162594
  simp only [CollatzResearch.WordTrace]
  refine ⟨37955568970410081825379709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101214850587760218201012557 37955568970410081825379709)
  ·
    refine ⟨14233338363903780684517391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37955568970410081825379709 14233338363903780684517391)
    ·
      refine ⟨21350007545855671026776087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14233338363903780684517391 21350007545855671026776087)
      ·
        refine ⟨32025011318783506540164131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21350007545855671026776087 32025011318783506540164131)
        ·
          refine ⟨48037516978175259810246197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32025011318783506540164131 48037516978175259810246197)
          ·
            refine ⟨4503517216703930607210581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48037516978175259810246197 4503517216703930607210581)
            ·
              refine ⟨52775592383249186803249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4503517216703930607210581 52775592383249186803249)
              ·
                rfl

theorem cell22_4162594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 8].length) (baseStart_4162594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162594 prefixEnd_4162594 := by exact prefixLift 4162594
  have htrace : WordTrace (prefixWord ++ tailWord_4162594) baseStart_4162594 baseEnd_4162594 := by
    simpa [prefixWord, tailWord_4162594, baseEnd_4162594] using wordTrace_append hprefix tailTrace_4162594
  have hstable : (prefixWord ++ tailWord_4162594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162594).length < 2 ^ (prefixWord ++ tailWord_4162594).sum := by decide
  have hdescent : baseEnd_4162594 < baseStart_4162594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162596 : List Nat := [2, 3, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_4162596 : Nat := 118140960795 + 4162596 * 2 ^ 59
def prefixEnd_4162596 : Nat := 4983230072969 + 3 ^ 40 * 4162596 * 2
def baseEnd_4162596 : Nat := 1424941678988600705137717

theorem tailTrace_4162596 : CollatzResearch.WordTrace tailWord_4162596 prefixEnd_4162596 1424941678988600705137717 := by
  unfold tailWord_4162596
  simp only [CollatzResearch.WordTrace]
  refine ⟨75911174413816540821545821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101214899218422054428727761 75911174413816540821545821)
  ·
    refine ⟨28466690405181202808079683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75911174413816540821545821 28466690405181202808079683)
    ·
      refine ⟨42700035607771804212119525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28466690405181202808079683 42700035607771804212119525)
      ·
        refine ⟨8006256676457213289772411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42700035607771804212119525 8006256676457213289772411)
        ·
          refine ⟨12009385014685819934658617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8006256676457213289772411 12009385014685819934658617)
          ·
            refine ⟨9007038761014364950993963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12009385014685819934658617 9007038761014364950993963)
            ·
              refine ⟨13510558141521547426490945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9007038761014364950993963 13510558141521547426490945)
              ·
                refine ⟨10132918606141160569868209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13510558141521547426490945 10132918606141160569868209)
                ·
                  refine ⟨7599688954605870427401157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10132918606141160569868209 7599688954605870427401157)
                  ·
                    refine ⟨1424941678988600705137717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7599688954605870427401157 1424941678988600705137717)
                    ·
                      rfl

theorem cell22_4162596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_4162596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4162596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4162596 prefixEnd_4162596 := by exact prefixLift 4162596
  have htrace : WordTrace (prefixWord ++ tailWord_4162596) baseStart_4162596 baseEnd_4162596 := by
    simpa [prefixWord, tailWord_4162596, baseEnd_4162596] using wordTrace_append hprefix tailTrace_4162596
  have hstable : (prefixWord ++ tailWord_4162596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162596).length < 2 ^ (prefixWord ++ tailWord_4162596).sum := by decide
  have hdescent : baseEnd_4162596 < baseStart_4162596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
