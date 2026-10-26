import V185TrunkScan23Chunk0846

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5012586 : List Nat := [3, 1, 3, 2, 2, 1, 2, 4, 1, 1, 3]
def baseStart_5012586 : Nat := 118140960795 + 5012586 * 2 ^ 59
def prefixEnd_5012586 : Nat := 4983230072969 + 3 ^ 40 * 5012586 * 2
def baseEnd_5012586 : Nat := 2573865939998030467922543

theorem tailTrace_5012586 : CollatzResearch.WordTrace tailWord_5012586 prefixEnd_5012586 2573865939998030467922543 := by
  unfold tailWord_5012586
  simp only [CollatzResearch.WordTrace]
  refine ⟨45706007754566119594444403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121882687345509652251851741 45706007754566119594444403)
  ·
    refine ⟨68559011631849179391666605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45706007754566119594444403 68559011631849179391666605)
    ·
      refine ⟨25709629361943442271874977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68559011631849179391666605 25709629361943442271874977)
      ·
        refine ⟨19282222021457581703906233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25709629361943442271874977 19282222021457581703906233)
        ·
          refine ⟨14461666516093186277929675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19282222021457581703906233 14461666516093186277929675)
          ·
            refine ⟨21692499774139779416894513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14461666516093186277929675 21692499774139779416894513)
            ·
              refine ⟨16269374830604834562670885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21692499774139779416894513 16269374830604834562670885)
              ·
                refine ⟨3050507780738406480500791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16269374830604834562670885 3050507780738406480500791)
                ·
                  refine ⟨4575761671107609720751187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3050507780738406480500791 4575761671107609720751187)
                  ·
                    refine ⟨6863642506661414581126781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4575761671107609720751187 6863642506661414581126781)
                    ·
                      refine ⟨2573865939998030467922543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6863642506661414581126781 2573865939998030467922543)
                      ·
                        rfl

theorem cell23_5012586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_5012586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012586 prefixEnd_5012586 := by exact prefixLift 5012586
  have htrace : WordTrace (prefixWord ++ tailWord_5012586) baseStart_5012586 baseEnd_5012586 := by
    simpa [prefixWord, tailWord_5012586, baseEnd_5012586] using wordTrace_append hprefix tailTrace_5012586
  have hstable : (prefixWord ++ tailWord_5012586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012586).length < 2 ^ (prefixWord ++ tailWord_5012586).sum := by decide
  have hdescent : baseEnd_5012586 < baseStart_5012586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012605 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_5012605 : Nat := 118140960795 + 5012605 * 2 ^ 59
def prefixEnd_5012605 : Nat := 4983230072969 + 3 ^ 40 * 5012605 * 2
def baseEnd_5012605 : Nat := 2573875696130465893584955

theorem tailTrace_5012605 : CollatzResearch.WordTrace tailWord_5012605 prefixEnd_5012605 2573875696130465893584955 := by
  unfold tailWord_5012605
  simp only [CollatzResearch.WordTrace]
  refine ⟨182824724005195644622719269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121883149336797096415146179 182824724005195644622719269)
  ·
    refine ⟨34279635750974183366759863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182824724005195644622719269 34279635750974183366759863)
    ·
      refine ⟨51419453626461275050139795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34279635750974183366759863 51419453626461275050139795)
      ·
        refine ⟨77129180439691912575209693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51419453626461275050139795 77129180439691912575209693)
        ·
          refine ⟨28923442664884467215703635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77129180439691912575209693 28923442664884467215703635)
          ·
            refine ⟨43385163997326700823555453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28923442664884467215703635 43385163997326700823555453)
            ·
              refine ⟨16269436498997512808833295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43385163997326700823555453 16269436498997512808833295)
              ·
                refine ⟨24404154748496269213249943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16269436498997512808833295 24404154748496269213249943)
                ·
                  refine ⟨36606232122744403819874915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24404154748496269213249943 36606232122744403819874915)
                  ·
                    refine ⟨54909348184116605729812373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36606232122744403819874915 54909348184116605729812373)
                    ·
                      refine ⟨2573875696130465893584955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54909348184116605729812373 2573875696130465893584955)
                      ·
                        rfl

theorem cell23_5012605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_5012605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012605 prefixEnd_5012605 := by exact prefixLift 5012605
  have htrace : WordTrace (prefixWord ++ tailWord_5012605) baseStart_5012605 baseEnd_5012605 := by
    simpa [prefixWord, tailWord_5012605, baseEnd_5012605] using wordTrace_append hprefix tailTrace_5012605
  have hstable : (prefixWord ++ tailWord_5012605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012605).length < 2 ^ (prefixWord ++ tailWord_5012605).sum := by decide
  have hdescent : baseEnd_5012605 < baseStart_5012605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012609 : List Nat := [1, 2, 4, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_5012609 : Nat := 118140960795 + 5012609 * 2 ^ 59
def prefixEnd_5012609 : Nat := 4983230072969 + 3 ^ 40 * 5012609 * 2
def baseEnd_5012609 : Nat := 2573877750053083877934937

theorem tailTrace_5012609 : CollatzResearch.WordTrace tailWord_5012609 prefixEnd_5012609 2573877750053083877934937 := by
  unfold tailWord_5012609
  simp only [CollatzResearch.WordTrace]
  refine ⟨182824869897181153305864881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121883246598120768870576587 182824869897181153305864881)
  ·
    refine ⟨137118652422885864979398661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182824869897181153305864881 137118652422885864979398661)
    ·
      refine ⟨25709747329291099683637249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137118652422885864979398661 25709747329291099683637249)
      ·
        refine ⟨19282310496968324762727937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25709747329291099683637249 19282310496968324762727937)
        ·
          refine ⟨14461732872726243572045953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19282310496968324762727937 14461732872726243572045953)
          ·
            refine ⟨10846299654544682679034465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14461732872726243572045953 10846299654544682679034465)
            ·
              refine ⟨8134724740908512009275849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10846299654544682679034465 8134724740908512009275849)
              ·
                refine ⟨6101043555681384006956887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8134724740908512009275849 6101043555681384006956887)
                ·
                  refine ⟨9151565333522076010435331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6101043555681384006956887 9151565333522076010435331)
                  ·
                    refine ⟨13727348000283114015652997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9151565333522076010435331 13727348000283114015652997)
                    ·
                      refine ⟨2573877750053083877934937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13727348000283114015652997 2573877750053083877934937)
                      ·
                        rfl

theorem cell23_5012609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_5012609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012609 prefixEnd_5012609 := by exact prefixLift 5012609
  have htrace : WordTrace (prefixWord ++ tailWord_5012609) baseStart_5012609 baseEnd_5012609 := by
    simpa [prefixWord, tailWord_5012609, baseEnd_5012609] using wordTrace_append hprefix tailTrace_5012609
  have hstable : (prefixWord ++ tailWord_5012609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012609).length < 2 ^ (prefixWord ++ tailWord_5012609).sum := by decide
  have hdescent : baseEnd_5012609 < baseStart_5012609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012653 : List Nat := [1, 5, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_5012653 : Nat := 118140960795 + 5012653 * 2 ^ 59
def prefixEnd_5012653 : Nat := 4983230072969 + 3 ^ 40 * 5012653 * 2
def baseEnd_5012653 : Nat := 857966781067293901928245

theorem tailTrace_5012653 : CollatzResearch.WordTrace tailWord_5012653 prefixEnd_5012653 857966781067293901928245 := by
  unfold tailWord_5012653
  simp only [CollatzResearch.WordTrace]
  refine ⟨182826474709021748820466613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121884316472681165880311075 182826474709021748820466613)
  ·
    refine ⟨17139982003970788951918745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 182826474709021748820466613 17139982003970788951918745)
    ·
      refine ⟨12854986502978091713939059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17139982003970788951918745 12854986502978091713939059)
      ·
        refine ⟨19282479754467137570908589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12854986502978091713939059 19282479754467137570908589)
        ·
          refine ⟨7230929907925176589090721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19282479754467137570908589 7230929907925176589090721)
          ·
            refine ⟨5423197430943882441818041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7230929907925176589090721 5423197430943882441818041)
            ·
              refine ⟨4067398073207911831363531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5423197430943882441818041 4067398073207911831363531)
              ·
                refine ⟨6101097109811867747045297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4067398073207911831363531 6101097109811867747045297)
                ·
                  refine ⟨4575822832358900810283973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6101097109811867747045297 4575822832358900810283973)
                  ·
                    refine ⟨857966781067293901928245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4575822832358900810283973 857966781067293901928245)
                    ·
                      rfl

theorem cell23_5012653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_5012653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012653 prefixEnd_5012653 := by exact prefixLift 5012653
  have htrace : WordTrace (prefixWord ++ tailWord_5012653) baseStart_5012653 baseEnd_5012653 := by
    simpa [prefixWord, tailWord_5012653, baseEnd_5012653] using wordTrace_append hprefix tailTrace_5012653
  have hstable : (prefixWord ++ tailWord_5012653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012653).length < 2 ^ (prefixWord ++ tailWord_5012653).sum := by decide
  have hdescent : baseEnd_5012653 < baseStart_5012653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012694 : List Nat := [5, 2, 1, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_5012694 : Nat := 118140960795 + 5012694 * 2 ^ 59
def prefixEnd_5012694 : Nat := 4983230072969 + 3 ^ 40 * 5012694 * 2
def baseEnd_5012694 : Nat := 2573921395908716045372047

theorem tailTrace_5012694 : CollatzResearch.WordTrace tailWord_5012694 prefixEnd_5012694 2573921395908716045372047 := by
  unfold tailWord_5012694
  simp only [CollatzResearch.WordTrace]
  refine ⟨11426748131367075801419321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121885313401248808548472757 11426748131367075801419321)
  ·
    refine ⟨8570061098525306851064491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11426748131367075801419321 8570061098525306851064491)
    ·
      refine ⟨12855091647787960276596737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8570061098525306851064491 12855091647787960276596737)
      ·
        refine ⟨9641318735840970207447553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12855091647787960276596737 9641318735840970207447553)
        ·
          refine ⟨7230989051880727655585665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9641318735840970207447553 7230989051880727655585665)
          ·
            refine ⟨5423241788910545741689249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7230989051880727655585665 5423241788910545741689249)
            ·
              refine ⟨4067431341682909306266937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5423241788910545741689249 4067431341682909306266937)
              ·
                refine ⟨3050573506262181979700203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4067431341682909306266937 3050573506262181979700203)
                ·
                  refine ⟨4575860259393272969550305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3050573506262181979700203 4575860259393272969550305)
                  ·
                    refine ⟨3431895194544954727162729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4575860259393272969550305 3431895194544954727162729)
                    ·
                      refine ⟨2573921395908716045372047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3431895194544954727162729 2573921395908716045372047)
                      ·
                        rfl

theorem cell23_5012694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_5012694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012694 prefixEnd_5012694 := by exact prefixLift 5012694
  have htrace : WordTrace (prefixWord ++ tailWord_5012694) baseStart_5012694 baseEnd_5012694 := by
    simpa [prefixWord, tailWord_5012694, baseEnd_5012694] using wordTrace_append hprefix tailTrace_5012694
  have hstable : (prefixWord ++ tailWord_5012694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012694).length < 2 ^ (prefixWord ++ tailWord_5012694).sum := by decide
  have hdescent : baseEnd_5012694 < baseStart_5012694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012712 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_5012712 : Nat := 118140960795 + 5012712 * 2 ^ 59
def prefixEnd_5012712 : Nat := 4983230072969 + 3 ^ 40 * 5012712 * 2
def baseEnd_5012712 : Nat := 2573930638560496974946963

theorem tailTrace_5012712 : CollatzResearch.WordTrace tailWord_5012712 prefixEnd_5012712 2573930638560496974946963 := by
  unfold tailWord_5012712
  simp only [CollatzResearch.WordTrace]
  refine ⟨91414313307904000948432195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121885751077205334597909593 91414313307904000948432195)
  ·
    refine ⟨137121469961856001422648293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91414313307904000948432195 137121469961856001422648293)
    ·
      refine ⟨25710275617848000266746555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137121469961856001422648293 25710275617848000266746555)
      ·
        refine ⟨38565413426772000400119833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25710275617848000266746555 38565413426772000400119833)
        ·
          refine ⟨28924060070079000300089875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38565413426772000400119833 28924060070079000300089875)
          ·
            refine ⟨43386090105118500450134813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28924060070079000300089875 43386090105118500450134813)
            ·
              refine ⟨16269783789419437668800555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43386090105118500450134813 16269783789419437668800555)
              ·
                refine ⟨24404675684129156503200833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16269783789419437668800555 24404675684129156503200833)
                ·
                  refine ⟨18303506763096867377400625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24404675684129156503200833 18303506763096867377400625)
                  ·
                    refine ⟨13727630072322650533050469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18303506763096867377400625 13727630072322650533050469)
                    ·
                      refine ⟨2573930638560496974946963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13727630072322650533050469 2573930638560496974946963)
                      ·
                        rfl

theorem cell23_5012712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_5012712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012712 prefixEnd_5012712 := by exact prefixLift 5012712
  have htrace : WordTrace (prefixWord ++ tailWord_5012712) baseStart_5012712 baseEnd_5012712 := by
    simpa [prefixWord, tailWord_5012712, baseEnd_5012712] using wordTrace_append hprefix tailTrace_5012712
  have hstable : (prefixWord ++ tailWord_5012712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012712).length < 2 ^ (prefixWord ++ tailWord_5012712).sum := by decide
  have hdescent : baseEnd_5012712 < baseStart_5012712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012716 : List Nat := [2, 2, 1, 1, 2, 4, 2, 3, 2, 2, 2]
def baseStart_5012716 : Nat := 118140960795 + 5012716 * 2 ^ 59
def prefixEnd_5012716 : Nat := 4983230072969 + 3 ^ 40 * 5012716 * 2
def baseEnd_5012716 : Nat := 2573932692483114959296945

theorem tailTrace_5012716 : CollatzResearch.WordTrace tailWord_5012716 prefixEnd_5012716 2573932692483114959296945 := by
  unfold tailWord_5012716
  simp only [CollatzResearch.WordTrace]
  refine ⟨91414386253896755290005001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121885848338529007053340001 91414386253896755290005001)
  ·
    refine ⟨68560789690422566467503751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91414386253896755290005001 68560789690422566467503751)
    ·
      refine ⟨102841184535633849701255627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68560789690422566467503751 102841184535633849701255627)
      ·
        refine ⟨154261776803450774551883441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102841184535633849701255627 154261776803450774551883441)
        ·
          refine ⟨115696332602588080913912581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154261776803450774551883441 115696332602588080913912581)
          ·
            refine ⟨21693062362985265171358609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115696332602588080913912581 21693062362985265171358609)
            ·
              refine ⟨16269796772238948878518957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21693062362985265171358609 16269796772238948878518957)
              ·
                refine ⟨6101173789589605829444609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16269796772238948878518957 6101173789589605829444609)
                ·
                  refine ⟨4575880342192204372083457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6101173789589605829444609 4575880342192204372083457)
                  ·
                    refine ⟨3431910256644153279062593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4575880342192204372083457 3431910256644153279062593)
                    ·
                      refine ⟨2573932692483114959296945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3431910256644153279062593 2573932692483114959296945)
                      ·
                        rfl

theorem cell23_5012716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 2, 2].length) (baseStart_5012716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012716 prefixEnd_5012716 := by exact prefixLift 5012716
  have htrace : WordTrace (prefixWord ++ tailWord_5012716) baseStart_5012716 baseEnd_5012716 := by
    simpa [prefixWord, tailWord_5012716, baseEnd_5012716] using wordTrace_append hprefix tailTrace_5012716
  have hstable : (prefixWord ++ tailWord_5012716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012716).length < 2 ^ (prefixWord ++ tailWord_5012716).sum := by decide
  have hdescent : baseEnd_5012716 < baseStart_5012716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012739 : List Nat := [1, 1, 1, 3, 2, 5, 2, 3, 5]
def baseStart_5012739 : Nat := 118140960795 + 5012739 * 2 ^ 59
def prefixEnd_5012739 : Nat := 4983230072969 + 3 ^ 40 * 5012739 * 2
def baseEnd_5012739 : Nat := 285993833615352041034371

theorem tailTrace_5012739 : CollatzResearch.WordTrace tailWord_5012739 prefixEnd_5012739 285993833615352041034371 := by
  unfold tailWord_5012739
  simp only [CollatzResearch.WordTrace]
  refine ⟨182829611386710185508097271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121886407591140123672064847 182829611386710185508097271)
  ·
    refine ⟨274244417080065278262145907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182829611386710185508097271 274244417080065278262145907)
    ·
      refine ⟨411366625620097917393218861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274244417080065278262145907 411366625620097917393218861)
      ·
        refine ⟨154262484607536719022457073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 411366625620097917393218861 154262484607536719022457073)
        ·
          refine ⟨115696863455652539266842805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154262484607536719022457073 115696863455652539266842805)
          ·
            refine ⟨10846580948967425556266513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115696863455652539266842805 10846580948967425556266513)
            ·
              refine ⟨8134935711725569167199885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10846580948967425556266513 8134935711725569167199885)
              ·
                refine ⟨3050600891897088437699957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8134935711725569167199885 3050600891897088437699957)
                ·
                  refine ⟨285993833615352041034371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3050600891897088437699957 285993833615352041034371)
                  ·
                    rfl

theorem cell23_5012739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 5].length) (baseStart_5012739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012739 prefixEnd_5012739 := by exact prefixLift 5012739
  have htrace : WordTrace (prefixWord ++ tailWord_5012739) baseStart_5012739 baseEnd_5012739 := by
    simpa [prefixWord, tailWord_5012739, baseEnd_5012739] using wordTrace_append hprefix tailTrace_5012739
  have hstable : (prefixWord ++ tailWord_5012739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012739).length < 2 ^ (prefixWord ++ tailWord_5012739).sum := by decide
  have hdescent : baseEnd_5012739 < baseStart_5012739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012772 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_5012772 : Nat := 118140960795 + 5012772 * 2 ^ 59
def prefixEnd_5012772 : Nat := 4983230072969 + 3 ^ 40 * 5012772 * 2
def baseEnd_5012772 : Nat := 2573961447399766740196687

theorem tailTrace_5012772 : CollatzResearch.WordTrace tailWord_5012772 prefixEnd_5012772 2573961447399766740196687 := by
  unfold tailWord_5012772
  simp only [CollatzResearch.WordTrace]
  refine ⟨91415407497795316072024285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121887209997060421429365713 91415407497795316072024285)
  ·
    refine ⟨34280777811673243527009107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91415407497795316072024285 34280777811673243527009107)
    ·
      refine ⟨51421166717509865290513661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34280777811673243527009107 51421166717509865290513661)
      ·
        refine ⟨19282937519066199483942623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51421166717509865290513661 19282937519066199483942623)
        ·
          refine ⟨28924406278599299225913935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19282937519066199483942623 28924406278599299225913935)
          ·
            refine ⟨43386609417898948838870903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28924406278599299225913935 43386609417898948838870903)
            ·
              refine ⟨65079914126848423258306355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43386609417898948838870903 65079914126848423258306355)
              ·
                refine ⟨97619871190272634887459533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65079914126848423258306355 97619871190272634887459533)
                ·
                  refine ⟨36607451696352238082797325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97619871190272634887459533 36607451696352238082797325)
                  ·
                    refine ⟨13727794386132089281048997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36607451696352238082797325 13727794386132089281048997)
                    ·
                      refine ⟨2573961447399766740196687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13727794386132089281048997 2573961447399766740196687)
                      ·
                        rfl

theorem cell23_5012772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_5012772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012772 prefixEnd_5012772 := by exact prefixLift 5012772
  have htrace : WordTrace (prefixWord ++ tailWord_5012772) baseStart_5012772 baseEnd_5012772 := by
    simpa [prefixWord, tailWord_5012772, baseEnd_5012772] using wordTrace_append hprefix tailTrace_5012772
  have hstable : (prefixWord ++ tailWord_5012772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012772).length < 2 ^ (prefixWord ++ tailWord_5012772).sum := by decide
  have hdescent : baseEnd_5012772 < baseStart_5012772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012790 : List Nat := [5, 1, 2, 3, 1, 2, 1, 3, 5]
def baseStart_5012790 : Nat := 118140960795 + 5012790 * 2 ^ 59
def prefixEnd_5012790 : Nat := 4983230072969 + 3 ^ 40 * 5012790 * 2
def baseEnd_5012790 : Nat := 285996743339060852196845

theorem tailTrace_5012790 : CollatzResearch.WordTrace tailWord_5012790 prefixEnd_5012790 285996743339060852196845 := by
  unfold tailWord_5012790
  simp only [CollatzResearch.WordTrace]
  refine ⟨11426966969345338826137739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121887647673016947478802549 11426966969345338826137739)
  ·
    refine ⟨17140450454018008239206609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11426966969345338826137739 17140450454018008239206609)
    ·
      refine ⟨12855337840513506179404957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17140450454018008239206609 12855337840513506179404957)
      ·
        refine ⟨4820751690192564817276859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12855337840513506179404957 4820751690192564817276859)
        ·
          refine ⟨7231127535288847225915289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4820751690192564817276859 7231127535288847225915289)
          ·
            refine ⟨5423345651466635419436467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7231127535288847225915289 5423345651466635419436467)
            ·
              refine ⟨8135018477199953129154701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5423345651466635419436467 8135018477199953129154701)
              ·
                refine ⟨3050631928949982423433013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8135018477199953129154701 3050631928949982423433013)
                ·
                  refine ⟨285996743339060852196845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3050631928949982423433013 285996743339060852196845)
                  ·
                    rfl

theorem cell23_5012790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_5012790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012790 prefixEnd_5012790 := by exact prefixLift 5012790
  have htrace : WordTrace (prefixWord ++ tailWord_5012790) baseStart_5012790 baseEnd_5012790 := by
    simpa [prefixWord, tailWord_5012790, baseEnd_5012790] using wordTrace_append hprefix tailTrace_5012790
  have hstable : (prefixWord ++ tailWord_5012790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012790).length < 2 ^ (prefixWord ++ tailWord_5012790).sum := by decide
  have hdescent : baseEnd_5012790 < baseStart_5012790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012812 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 8]
def baseStart_5012812 : Nat := 118140960795 + 5012812 * 2 ^ 59
def prefixEnd_5012812 : Nat := 4983230072969 + 3 ^ 40 * 5012812 * 2
def baseEnd_5012812 : Nat := 285997998513994064855167

theorem tailTrace_5012812 : CollatzResearch.WordTrace tailWord_5012812 prefixEnd_5012812 285997998513994064855167 := by
  unfold tailWord_5012812
  simp only [CollatzResearch.WordTrace]
  refine ⟨91416136957722859487752345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121888182610297145983669793 91416136957722859487752345)
  ·
    refine ⟨68562102718292144615814259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91416136957722859487752345 68562102718292144615814259)
    ·
      refine ⟨102843154077438216923721389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68562102718292144615814259 102843154077438216923721389)
      ·
        refine ⟨38566182779039331346395521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102843154077438216923721389 38566182779039331346395521)
        ·
          refine ⟨28924637084279498509796641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38566182779039331346395521 28924637084279498509796641)
          ·
            refine ⟨21693477813209623882347481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28924637084279498509796641 21693477813209623882347481)
            ·
              refine ⟨16270108359907217911760611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21693477813209623882347481 16270108359907217911760611)
              ·
                refine ⟨24405162539860826867640917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16270108359907217911760611 24405162539860826867640917)
                ·
                  refine ⟨285997998513994064855167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24405162539860826867640917 285997998513994064855167)
                  ·
                    rfl

theorem cell23_5012812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 8].length) (baseStart_5012812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012812 prefixEnd_5012812 := by exact prefixLift 5012812
  have htrace : WordTrace (prefixWord ++ tailWord_5012812) baseStart_5012812 baseEnd_5012812 := by
    simpa [prefixWord, tailWord_5012812, baseEnd_5012812] using wordTrace_append hprefix tailTrace_5012812
  have hstable : (prefixWord ++ tailWord_5012812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012812).length < 2 ^ (prefixWord ++ tailWord_5012812).sum := by decide
  have hdescent : baseEnd_5012812 < baseStart_5012812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012849 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 1, 5, 2]
def baseStart_5012849 : Nat := 118140960795 + 5012849 * 2 ^ 59
def prefixEnd_5012849 : Nat := 4983230072969 + 3 ^ 40 * 5012849 * 2
def baseEnd_5012849 : Nat := 2574000985410162938933833

theorem tailTrace_5012849 : CollatzResearch.WordTrace tailWord_5012849 prefixEnd_5012849 2574000985410162938933833 := by
  unfold tailWord_5012849
  simp only [CollatzResearch.WordTrace]
  refine ⟨182833623416311674294601601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121889082277541116196401067 182833623416311674294601601)
  ·
    refine ⟨137125217562233755720951201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182833623416311674294601601 137125217562233755720951201)
    ·
      refine ⟨102843913171675316790713401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137125217562233755720951201 102843913171675316790713401)
      ·
        refine ⟨77132934878756487593035051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102843913171675316790713401 77132934878756487593035051)
        ·
          refine ⟨115699402318134731389552577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77132934878756487593035051 115699402318134731389552577)
          ·
            refine ⟨86774551738601048542164433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115699402318134731389552577 86774551738601048542164433)
            ·
              refine ⟨65080913803950786406623325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86774551738601048542164433 65080913803950786406623325)
              ·
                refine ⟨24405342676481544902483747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65080913803950786406623325 24405342676481544902483747)
                ·
                  refine ⟨36608014014722317353725621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24405342676481544902483747 36608014014722317353725621)
                  ·
                    refine ⟨3432001313880217251911777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36608014014722317353725621 3432001313880217251911777)
                    ·
                      refine ⟨2574000985410162938933833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3432001313880217251911777 2574000985410162938933833)
                      ·
                        rfl

theorem cell23_5012849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_5012849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012849 prefixEnd_5012849 := by exact prefixLift 5012849
  have htrace : WordTrace (prefixWord ++ tailWord_5012849) baseStart_5012849 baseEnd_5012849 := by
    simpa [prefixWord, tailWord_5012849, baseEnd_5012849] using wordTrace_append hprefix tailTrace_5012849
  have hstable : (prefixWord ++ tailWord_5012849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012849).length < 2 ^ (prefixWord ++ tailWord_5012849).sum := by decide
  have hdescent : baseEnd_5012849 < baseStart_5012849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012889 : List Nat := [1, 2, 1, 2, 1, 6, 2, 1, 1, 6]
def baseStart_5012889 : Nat := 118140960795 + 5012889 * 2 ^ 59
def prefixEnd_5012889 : Nat := 4983230072969 + 3 ^ 40 * 5012889 * 2
def baseEnd_5012889 : Nat := 858007174878780927477883

theorem tailTrace_5012889 : CollatzResearch.WordTrace tailWord_5012889 prefixEnd_5012889 858007174878780927477883 := by
  unfold tailWord_5012889
  simp only [CollatzResearch.WordTrace]
  refine ⟨182835082336166761126057721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121890054890777840750705147 182835082336166761126057721)
  ·
    refine ⟨137126311752125070844543291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182835082336166761126057721 137126311752125070844543291)
    ·
      refine ⟨205689467628187606266814937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137126311752125070844543291 205689467628187606266814937)
      ·
        refine ⟨154267100721140704700111203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205689467628187606266814937 154267100721140704700111203)
        ·
          refine ⟨231400651081711057050166805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154267100721140704700111203 231400651081711057050166805)
          ·
            refine ⟨10846905519455205799226569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 231400651081711057050166805 10846905519455205799226569)
            ·
              refine ⟨8135179139591404349419927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10846905519455205799226569 8135179139591404349419927)
              ·
                refine ⟨12202768709387106524129891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8135179139591404349419927 12202768709387106524129891)
                ·
                  refine ⟨18304153064080659786194837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12202768709387106524129891 18304153064080659786194837)
                  ·
                    refine ⟨858007174878780927477883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18304153064080659786194837 858007174878780927477883)
                    ·
                      rfl

theorem cell23_5012889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 6].length) (baseStart_5012889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012889 prefixEnd_5012889 := by exact prefixLift 5012889
  have htrace : WordTrace (prefixWord ++ tailWord_5012889) baseStart_5012889 baseEnd_5012889 := by
    simpa [prefixWord, tailWord_5012889, baseEnd_5012889] using wordTrace_append hprefix tailTrace_5012889
  have hstable : (prefixWord ++ tailWord_5012889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012889).length < 2 ^ (prefixWord ++ tailWord_5012889).sum := by decide
  have hdescent : baseEnd_5012889 < baseStart_5012889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012899 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 3]
def baseStart_5012899 : Nat := 118140960795 + 5012899 * 2 ^ 59
def prefixEnd_5012899 : Nat := 4983230072969 + 3 ^ 40 * 5012899 * 2
def baseEnd_5012899 : Nat := 2574026659442887743308603

theorem tailTrace_5012899 : CollatzResearch.WordTrace tailWord_5012899 prefixEnd_5012899 2574026659442887743308603 := by
  unfold tailWord_5012899
  simp only [CollatzResearch.WordTrace]
  refine ⟨182835447066130532833921751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121890298044087021889281167 182835447066130532833921751)
  ·
    refine ⟨274253170599195799250882627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182835447066130532833921751 274253170599195799250882627)
    ·
      refine ⟨411379755898793698876323941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274253170599195799250882627 411379755898793698876323941)
      ·
        refine ⟨77133704231023818539310739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 411379755898793698876323941 77133704231023818539310739)
        ·
          refine ⟨115700556346535727808966109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77133704231023818539310739 115700556346535727808966109)
          ·
            refine ⟨43387708629950897928362291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115700556346535727808966109 43387708629950897928362291)
            ·
              refine ⟨65081562944926346892543437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43387708629950897928362291 65081562944926346892543437)
              ·
                refine ⟨24405586104347380084703789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65081562944926346892543437 24405586104347380084703789)
                ·
                  refine ⟨9152094789130267531763921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24405586104347380084703789 9152094789130267531763921)
                  ·
                    refine ⟨6864071091847700648822941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9152094789130267531763921 6864071091847700648822941)
                    ·
                      refine ⟨2574026659442887743308603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6864071091847700648822941 2574026659442887743308603)
                      ·
                        rfl

theorem cell23_5012899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_5012899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012899 prefixEnd_5012899 := by exact prefixLift 5012899
  have htrace : WordTrace (prefixWord ++ tailWord_5012899) baseStart_5012899 baseEnd_5012899 := by
    simpa [prefixWord, tailWord_5012899, baseEnd_5012899] using wordTrace_append hprefix tailTrace_5012899
  have hstable : (prefixWord ++ tailWord_5012899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012899).length < 2 ^ (prefixWord ++ tailWord_5012899).sum := by decide
  have hdescent : baseEnd_5012899 < baseStart_5012899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012922 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6]
def baseStart_5012922 : Nat := 118140960795 + 5012922 * 2 ^ 59
def prefixEnd_5012922 : Nat := 4983230072969 + 3 ^ 40 * 5012922 * 2
def baseEnd_5012922 : Nat := 2574038469497941153320997

theorem tailTrace_5012922 : CollatzResearch.WordTrace tailWord_5012922 prefixEnd_5012922 2574038469497941153320997 := by
  unfold tailWord_5012922
  simp only [CollatzResearch.WordTrace]
  refine ⟨45709071486261801940502255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121890857296698138508006013 45709071486261801940502255)
  ·
    refine ⟨68563607229392702910753383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45709071486261801940502255 68563607229392702910753383)
    ·
      refine ⟨102845410844089054366130075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68563607229392702910753383 102845410844089054366130075)
      ·
        refine ⟨154268116266133581549195113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102845410844089054366130075 154268116266133581549195113)
        ·
          refine ⟨115701087199600186161896335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154268116266133581549195113 115701087199600186161896335)
          ·
            refine ⟨173551630799400279242844503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115701087199600186161896335 173551630799400279242844503)
            ·
              refine ⟨260327446199100418864266755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173551630799400279242844503 260327446199100418864266755)
              ·
                refine ⟨390491169298650628296400133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260327446199100418864266755 390491169298650628296400133)
                ·
                  refine ⟨73217094243496992805575025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 390491169298650628296400133 73217094243496992805575025)
                  ·
                    refine ⟨54912820682622744604181269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73217094243496992805575025 54912820682622744604181269)
                    ·
                      refine ⟨2574038469497941153320997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54912820682622744604181269 2574038469497941153320997)
                      ·
                        rfl

theorem cell23_5012922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_5012922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012922 prefixEnd_5012922 := by exact prefixLift 5012922
  have htrace : WordTrace (prefixWord ++ tailWord_5012922) baseStart_5012922 baseEnd_5012922 := by
    simpa [prefixWord, tailWord_5012922, baseEnd_5012922] using wordTrace_append hprefix tailTrace_5012922
  have hstable : (prefixWord ++ tailWord_5012922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012922).length < 2 ^ (prefixWord ++ tailWord_5012922).sum := by decide
  have hdescent : baseEnd_5012922 < baseStart_5012922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012950 : List Nat := [5, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_5012950 : Nat := 118140960795 + 5012950 * 2 ^ 59
def prefixEnd_5012950 : Nat := 4983230072969 + 3 ^ 40 * 5012950 * 2
def baseEnd_5012950 : Nat := 2574052846956267043770869

theorem tailTrace_5012950 : CollatzResearch.WordTrace tailWord_5012950 prefixEnd_5012950 2574052846956267043770869 := by
  unfold tailWord_5012950
  simp only [CollatzResearch.WordTrace]
  refine ⟨11427331699309110534001769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121891538125963845696018869 11427331699309110534001769)
  ·
    refine ⟨8570498774481832900501327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11427331699309110534001769 8570498774481832900501327)
    ·
      refine ⟨12855748161722749350751991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8570498774481832900501327 12855748161722749350751991)
      ·
        refine ⟨19283622242584124026127987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12855748161722749350751991 19283622242584124026127987)
        ·
          refine ⟨28925433363876186039191981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19283622242584124026127987 28925433363876186039191981)
          ·
            refine ⟨10847037511453569764696993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28925433363876186039191981 10847037511453569764696993)
            ·
              refine ⟨8135278133590177323522745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10847037511453569764696993 8135278133590177323522745)
              ·
                refine ⟨6101458600192632992642059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8135278133590177323522745 6101458600192632992642059)
                ·
                  refine ⟨9152187900288949488963089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6101458600192632992642059 9152187900288949488963089)
                  ·
                    refine ⟨6864140925216712116722317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9152187900288949488963089 6864140925216712116722317)
                    ·
                      refine ⟨2574052846956267043770869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6864140925216712116722317 2574052846956267043770869)
                      ·
                        rfl

theorem cell23_5012950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_5012950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012950 prefixEnd_5012950 := by exact prefixLift 5012950
  have htrace : WordTrace (prefixWord ++ tailWord_5012950) baseStart_5012950 baseEnd_5012950 := by
    simpa [prefixWord, tailWord_5012950, baseEnd_5012950] using wordTrace_append hprefix tailTrace_5012950
  have hstable : (prefixWord ++ tailWord_5012950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012950).length < 2 ^ (prefixWord ++ tailWord_5012950).sum := by decide
  have hdescent : baseEnd_5012950 < baseStart_5012950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013043 : List Nat := [1, 1, 1, 2, 4, 3, 4, 2, 5]
def baseStart_5013043 : Nat := 118140960795 + 5013043 * 2 ^ 59
def prefixEnd_5013043 : Nat := 4983230072969 + 3 ^ 40 * 5013043 * 2
def baseEnd_5013043 : Nat := 286011177850792797767549

theorem tailTrace_5013043 : CollatzResearch.WordTrace tailWord_5013043 prefixEnd_5013043 286011177850792797767549 := by
  unfold tailWord_5013043
  simp only [CollatzResearch.WordTrace]
  refine ⟨182840699177608845427163783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121893799451739230284775855 182840699177608845427163783)
  ·
    refine ⟨274261048766413268140745675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182840699177608845427163783 274261048766413268140745675)
    ·
      refine ⟨411391573149619902211118513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274261048766413268140745675 411391573149619902211118513)
      ·
        refine ⟨308543679862214926658338885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 411391573149619902211118513 308543679862214926658338885)
        ·
          refine ⟨57851939974165298748438541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 308543679862214926658338885 57851939974165298748438541)
          ·
            refine ⟨21694477490311987030664453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57851939974165298748438541 21694477490311987030664453)
            ·
              refine ⟨4067714529433497568249585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21694477490311987030664453 4067714529433497568249585)
              ·
                refine ⟨3050785897075123176187189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4067714529433497568249585 3050785897075123176187189)
                ·
                  refine ⟨286011177850792797767549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3050785897075123176187189 286011177850792797767549)
                  ·
                    rfl

theorem cell23_5013043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 5].length) (baseStart_5013043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013043 prefixEnd_5013043 := by exact prefixLift 5013043
  have htrace : WordTrace (prefixWord ++ tailWord_5013043) baseStart_5013043 baseEnd_5013043 := by
    simpa [prefixWord, tailWord_5013043, baseEnd_5013043] using wordTrace_append hprefix tailTrace_5013043
  have hstable : (prefixWord ++ tailWord_5013043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013043).length < 2 ^ (prefixWord ++ tailWord_5013043).sum := by decide
  have hdescent : baseEnd_5013043 < baseStart_5013043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013053 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 2, 3, 3]
def baseStart_5013053 : Nat := 118140960795 + 5013053 * 2 ^ 59
def prefixEnd_5013053 : Nat := 4983230072969 + 3 ^ 40 * 5013053 * 2
def baseEnd_5013053 : Nat := 2574105735463680140782895

theorem tailTrace_5013053 : CollatzResearch.WordTrace tailWord_5013053 prefixEnd_5013053 2574105735463680140782895 := by
  unfold tailWord_5013053
  simp only [CollatzResearch.WordTrace]
  refine ⟨182841063907572617135027813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121894042605048411423351875 182841063907572617135027813)
  ·
    refine ⟨34282699482669865712817715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182841063907572617135027813 34282699482669865712817715)
    ·
      refine ⟨51424049224004798569226573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34282699482669865712817715 51424049224004798569226573)
      ·
        refine ⟨19284018459001799463459965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51424049224004798569226573 19284018459001799463459965)
        ·
          refine ⟨7231506922125674798797487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19284018459001799463459965 7231506922125674798797487)
          ·
            refine ⟨10847260383188512198196231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7231506922125674798797487 10847260383188512198196231)
            ·
              refine ⟨16270890574782768297294347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10847260383188512198196231 16270890574782768297294347)
              ·
                refine ⟨24406335862174152445941521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16270890574782768297294347 24406335862174152445941521)
                ·
                  refine ⟨18304751896630614334456141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24406335862174152445941521 18304751896630614334456141)
                  ·
                    refine ⟨6864281961236480375421053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18304751896630614334456141 6864281961236480375421053)
                    ·
                      refine ⟨2574105735463680140782895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6864281961236480375421053 2574105735463680140782895)
                      ·
                        rfl

theorem cell23_5013053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_5013053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013053 prefixEnd_5013053 := by exact prefixLift 5013053
  have htrace : WordTrace (prefixWord ++ tailWord_5013053) baseStart_5013053 baseEnd_5013053 := by
    simpa [prefixWord, tailWord_5013053, baseEnd_5013053] using wordTrace_append hprefix tailTrace_5013053
  have hstable : (prefixWord ++ tailWord_5013053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013053).length < 2 ^ (prefixWord ++ tailWord_5013053).sum := by decide
  have hdescent : baseEnd_5013053 < baseStart_5013053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013076 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_5013076 : Nat := 118140960795 + 5013076 * 2 ^ 59
def prefixEnd_5013076 : Nat := 4983230072969 + 3 ^ 40 * 5013076 * 2
def baseEnd_5013076 : Nat := 2574117545518733550795289

theorem tailTrace_5013076 : CollatzResearch.WordTrace tailWord_5013076 prefixEnd_5013076 2574117545518733550795289 := by
  unfold tailWord_5013076
  simp only [CollatzResearch.WordTrace]
  refine ⟨91420951393244646031557541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121894601857659528042076721 91420951393244646031557541)
  ·
    refine ⟨17141428386233371130917039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91420951393244646031557541 17141428386233371130917039)
    ·
      refine ⟨25712142579350056696375559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17141428386233371130917039 25712142579350056696375559)
      ·
        refine ⟨38568213869025085044563339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25712142579350056696375559 38568213869025085044563339)
        ·
          refine ⟨57852320803537627566845009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38568213869025085044563339 57852320803537627566845009)
          ·
            refine ⟨43389240602653220675133757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57852320803537627566845009 43389240602653220675133757)
            ·
              refine ⟨16270965225994957753175159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43389240602653220675133757 16270965225994957753175159)
              ·
                refine ⟨24406447838992436629762739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16270965225994957753175159 24406447838992436629762739)
                ·
                  refine ⟨36609671758488654944644109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24406447838992436629762739 36609671758488654944644109)
                  ·
                    refine ⟨13728626909433245604241541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36609671758488654944644109 13728626909433245604241541)
                    ·
                      refine ⟨2574117545518733550795289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13728626909433245604241541 2574117545518733550795289)
                      ·
                        rfl

theorem cell23_5013076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_5013076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013076 prefixEnd_5013076 := by exact prefixLift 5013076
  have htrace : WordTrace (prefixWord ++ tailWord_5013076) baseStart_5013076 baseEnd_5013076 := by
    simpa [prefixWord, tailWord_5013076, baseEnd_5013076] using wordTrace_append hprefix tailTrace_5013076
  have hstable : (prefixWord ++ tailWord_5013076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013076).length < 2 ^ (prefixWord ++ tailWord_5013076).sum := by decide
  have hdescent : baseEnd_5013076 < baseStart_5013076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013089 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_5013089 : Nat := 118140960795 + 5013089 * 2 ^ 59
def prefixEnd_5013089 : Nat := 4983230072969 + 3 ^ 40 * 5013089 * 2
def baseEnd_5013089 : Nat := 2574124220767241999932729

theorem tailTrace_5013089 : CollatzResearch.WordTrace tailWord_5013089 prefixEnd_5013089 2574124220767241999932729 := by
  unfold tailWord_5013089
  simp only [CollatzResearch.WordTrace]
  refine ⟨182842376935442195283338321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121894917956961463522225547 182842376935442195283338321)
  ·
    refine ⟨137131782701581646462503741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182842376935442195283338321 137131782701581646462503741)
    ·
      refine ⟨51424418513093117423438903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137131782701581646462503741 51424418513093117423438903)
      ·
        refine ⟨77136627769639676135158355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51424418513093117423438903 77136627769639676135158355)
        ·
          refine ⟨115704941654459514202737533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77136627769639676135158355 115704941654459514202737533)
          ·
            refine ⟨43389353120422317826026575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115704941654459514202737533 43389353120422317826026575)
            ·
              refine ⟨65084029680633476739039863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43389353120422317826026575 65084029680633476739039863)
              ·
                refine ⟨97626044520950215108559795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65084029680633476739039863 97626044520950215108559795)
                ·
                  refine ⟨146439066781425322662839693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97626044520950215108559795 146439066781425322662839693)
                  ·
                    refine ⟨54914650043034495998564885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146439066781425322662839693 54914650043034495998564885)
                    ·
                      refine ⟨2574124220767241999932729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54914650043034495998564885 2574124220767241999932729)
                      ·
                        rfl

theorem cell23_5013089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_5013089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013089 prefixEnd_5013089 := by exact prefixLift 5013089
  have htrace : WordTrace (prefixWord ++ tailWord_5013089) baseStart_5013089 baseEnd_5013089 := by
    simpa [prefixWord, tailWord_5013089, baseEnd_5013089] using wordTrace_append hprefix tailTrace_5013089
  have hstable : (prefixWord ++ tailWord_5013089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013089).length < 2 ^ (prefixWord ++ tailWord_5013089).sum := by decide
  have hdescent : baseEnd_5013089 < baseStart_5013089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013093 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 2, 4, 2]
def baseStart_5013093 : Nat := 118140960795 + 5013093 * 2 ^ 59
def prefixEnd_5013093 : Nat := 4983230072969 + 3 ^ 40 * 5013093 * 2
def baseEnd_5013093 : Nat := 2574126274689859984282711

theorem tailTrace_5013093 : CollatzResearch.WordTrace tailWord_5013093 prefixEnd_5013093 2574126274689859984282711 := by
  unfold tailWord_5013093
  simp only [CollatzResearch.WordTrace]
  refine ⟨182842522827427703966483933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121895015218285135977655955 182842522827427703966483933)
  ·
    refine ⟨68565946060285388987431475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182842522827427703966483933 68565946060285388987431475)
    ·
      refine ⟨102848919090428083481147213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68565946060285388987431475 102848919090428083481147213)
      ·
        refine ⟨38568344658910531305430205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102848919090428083481147213 38568344658910531305430205)
        ·
          refine ⟨14463129247091449239536327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38568344658910531305430205 14463129247091449239536327)
          ·
            refine ⟨21694693870637173859304491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14463129247091449239536327 21694693870637173859304491)
            ·
              refine ⟨32542040805955760788956737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21694693870637173859304491 32542040805955760788956737)
              ·
                refine ⟨24406530604466820591717553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32542040805955760788956737 24406530604466820591717553)
                ·
                  refine ⟨18304897953350115443788165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24406530604466820591717553 18304897953350115443788165)
                  ·
                    refine ⟨3432168366253146645710281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18304897953350115443788165 3432168366253146645710281)
                    ·
                      refine ⟨2574126274689859984282711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3432168366253146645710281 2574126274689859984282711)
                      ·
                        rfl

theorem cell23_5013093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_5013093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013093 prefixEnd_5013093 := by exact prefixLift 5013093
  have htrace : WordTrace (prefixWord ++ tailWord_5013093) baseStart_5013093 baseEnd_5013093 := by
    simpa [prefixWord, tailWord_5013093, baseEnd_5013093] using wordTrace_append hprefix tailTrace_5013093
  have hstable : (prefixWord ++ tailWord_5013093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013093).length < 2 ^ (prefixWord ++ tailWord_5013093).sum := by decide
  have hdescent : baseEnd_5013093 < baseStart_5013093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013110 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2]
def baseStart_5013110 : Nat := 118140960795 + 5013110 * 2 ^ 59
def prefixEnd_5013110 : Nat := 4983230072969 + 3 ^ 40 * 5013110 * 2
def baseEnd_5013110 : Nat := 2574135003860986417770133

theorem tailTrace_5013110 : CollatzResearch.WordTrace tailWord_5013110 prefixEnd_5013110 2574135003860986417770133 := by
  unfold tailWord_5013110
  simp only [CollatzResearch.WordTrace]
  refine ⟨11427696429272882241865799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121895428578910743913235189 11427696429272882241865799)
  ·
    refine ⟨17141544643909323362798699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11427696429272882241865799 17141544643909323362798699)
    ·
      refine ⟨25712316965863985044198049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17141544643909323362798699 25712316965863985044198049)
      ·
        refine ⟨19284237724397988783148537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25712316965863985044198049 19284237724397988783148537)
        ·
          refine ⟨14463178293298491587361403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19284237724397988783148537 14463178293298491587361403)
          ·
            refine ⟨21694767439947737381042105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14463178293298491587361403 21694767439947737381042105)
            ·
              refine ⟨16271075579960803035781579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21694767439947737381042105 16271075579960803035781579)
              ·
                refine ⟨24406613369941204553672369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16271075579960803035781579 24406613369941204553672369)
                ·
                  refine ⟨18304960027455903415254277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24406613369941204553672369 18304960027455903415254277)
                  ·
                    refine ⟨3432180005147981890360177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18304960027455903415254277 3432180005147981890360177)
                    ·
                      refine ⟨2574135003860986417770133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3432180005147981890360177 2574135003860986417770133)
                      ·
                        rfl

theorem cell23_5013110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_5013110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013110 prefixEnd_5013110 := by exact prefixLift 5013110
  have htrace : WordTrace (prefixWord ++ tailWord_5013110) baseStart_5013110 baseEnd_5013110 := by
    simpa [prefixWord, tailWord_5013110, baseEnd_5013110] using wordTrace_append hprefix tailTrace_5013110
  have hstable : (prefixWord ++ tailWord_5013110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013110).length < 2 ^ (prefixWord ++ tailWord_5013110).sum := by decide
  have hdescent : baseEnd_5013110 < baseStart_5013110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013139 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 5]
def baseStart_5013139 : Nat := 118140960795 + 5013139 * 2 ^ 59
def prefixEnd_5013139 : Nat := 4983230072969 + 3 ^ 40 * 5013139 * 2
def baseEnd_5013139 : Nat := 2574149894799966804307499

theorem tailTrace_5013139 : CollatzResearch.WordTrace tailWord_5013139 prefixEnd_5013139 2574149894799966804307499 := by
  unfold tailWord_5013139
  simp only [CollatzResearch.WordTrace]
  refine ⟨182844200585261053822658471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121896133723507369215105647 182844200585261053822658471)
  ·
    refine ⟨274266300877891580733987707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182844200585261053822658471 274266300877891580733987707)
    ·
      refine ⟨411399451316837371100981561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274266300877891580733987707 411399451316837371100981561)
      ·
        refine ⟨308549588487628028325736171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 411399451316837371100981561 308549588487628028325736171)
        ·
          refine ⟨462824382731442042488604257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308549588487628028325736171 462824382731442042488604257)
          ·
            refine ⟨347118287048581531866453193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462824382731442042488604257 347118287048581531866453193)
            ·
              refine ⟨260338715286436148899839895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347118287048581531866453193 260338715286436148899839895)
              ·
                refine ⟨390508072929654223349759843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260338715286436148899839895 390508072929654223349759843)
                ·
                  refine ⟨585762109394481335024639765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390508072929654223349759843 585762109394481335024639765)
                  ·
                    refine ⟨27457598877866312579279989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 585762109394481335024639765 27457598877866312579279989)
                    ·
                      refine ⟨2574149894799966804307499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27457598877866312579279989 2574149894799966804307499)
                      ·
                        rfl

theorem cell23_5013139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_5013139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013139 prefixEnd_5013139 := by exact prefixLift 5013139
  have htrace : WordTrace (prefixWord ++ tailWord_5013139) baseStart_5013139 baseEnd_5013139 := by
    simpa [prefixWord, tailWord_5013139, baseEnd_5013139] using wordTrace_append hprefix tailTrace_5013139
  have hstable : (prefixWord ++ tailWord_5013139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013139).length < 2 ^ (prefixWord ++ tailWord_5013139).sum := by decide
  have hdescent : baseEnd_5013139 < baseStart_5013139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013154 : List Nat := [3, 3, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_5013154 : Nat := 118140960795 + 5013154 * 2 ^ 59
def prefixEnd_5013154 : Nat := 4983230072969 + 3 ^ 40 * 5013154 * 2
def baseEnd_5013154 : Nat := 858052532336594748539977

theorem tailTrace_5013154 : CollatzResearch.WordTrace tailWord_5013154 prefixEnd_5013154 858052532336594748539977 := by
  unfold tailWord_5013154
  simp only [CollatzResearch.WordTrace]
  refine ⟨45711186920051677846113629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121896498453471140922969677 45711186920051677846113629)
  ·
    refine ⟨17141695095019379192292611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45711186920051677846113629 17141695095019379192292611)
    ·
      refine ⟨25712542642529068788438917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17141695095019379192292611 25712542642529068788438917)
      ·
        refine ⟨4821101745474200397832297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25712542642529068788438917 4821101745474200397832297)
        ·
          refine ⟨3615826309105650298374223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4821101745474200397832297 3615826309105650298374223)
          ·
            refine ⟨5423739463658475447561335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3615826309105650298374223 5423739463658475447561335)
            ·
              refine ⟨8135609195487713171342003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5423739463658475447561335 8135609195487713171342003)
              ·
                refine ⟨12203413793231569757013005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8135609195487713171342003 12203413793231569757013005)
                ·
                  refine ⟨4576280172461838658879877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12203413793231569757013005 4576280172461838658879877)
                  ·
                    refine ⟨858052532336594748539977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4576280172461838658879877 858052532336594748539977)
                    ·
                      rfl

theorem cell23_5013154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_5013154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013154 prefixEnd_5013154 := by exact prefixLift 5013154
  have htrace : WordTrace (prefixWord ++ tailWord_5013154) baseStart_5013154 baseEnd_5013154 := by
    simpa [prefixWord, tailWord_5013154, baseEnd_5013154] using wordTrace_append hprefix tailTrace_5013154
  have hstable : (prefixWord ++ tailWord_5013154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013154).length < 2 ^ (prefixWord ++ tailWord_5013154).sum := by decide
  have hdescent : baseEnd_5013154 < baseStart_5013154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013180 : List Nat := [2, 2, 2, 3, 1, 4, 1, 2, 1, 5]
def baseStart_5013180 : Nat := 118140960795 + 5013180 * 2 ^ 59
def prefixEnd_5013180 : Nat := 4983230072969 + 3 ^ 40 * 5013180 * 2
def baseEnd_5013180 : Nat := 858056982502267047964937

theorem tailTrace_5013180 : CollatzResearch.WordTrace tailWord_5013180 prefixEnd_5013180 858056982502267047964937 := by
  unfold tailWord_5013180
  simp only [CollatzResearch.WordTrace]
  refine ⟨91422847989056258912450497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121897130652075011883267329 91422847989056258912450497)
  ·
    refine ⟨68567135991792194184337873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91422847989056258912450497 68567135991792194184337873)
    ·
      refine ⟨51425351993844145638253405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68567135991792194184337873 51425351993844145638253405)
      ·
        refine ⟨19284506997691554614345027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51425351993844145638253405 19284506997691554614345027)
        ·
          refine ⟨28926760496537331921517541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19284506997691554614345027 28926760496537331921517541)
          ·
            refine ⟨5423767593100749735284539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28926760496537331921517541 5423767593100749735284539)
            ·
              refine ⟨8135651389651124602926809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5423767593100749735284539 8135651389651124602926809)
              ·
                refine ⟨6101738542238343452195107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8135651389651124602926809 6101738542238343452195107)
                ·
                  refine ⟨9152607813357515178292661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6101738542238343452195107 9152607813357515178292661)
                  ·
                    refine ⟨858056982502267047964937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9152607813357515178292661 858056982502267047964937)
                    ·
                      rfl

theorem cell23_5013180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_5013180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013180 prefixEnd_5013180 := by exact prefixLift 5013180
  have htrace : WordTrace (prefixWord ++ tailWord_5013180) baseStart_5013180 baseEnd_5013180 := by
    simpa [prefixWord, tailWord_5013180, baseEnd_5013180] using wordTrace_append hprefix tailTrace_5013180
  have hstable : (prefixWord ++ tailWord_5013180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013180).length < 2 ^ (prefixWord ++ tailWord_5013180).sum := by decide
  have hdescent : baseEnd_5013180 < baseStart_5013180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013210 : List Nat := [3, 1, 1, 2, 2, 4, 2, 2, 2, 4]
def baseStart_5013210 : Nat := 118140960795 + 5013210 * 2 ^ 59
def prefixEnd_5013210 : Nat := 4983230072969 + 3 ^ 40 * 5013210 * 2
def baseEnd_5013210 : Nat := 858062117308812008839891

theorem tailTrace_5013210 : CollatzResearch.WordTrace tailWord_5013210 prefixEnd_5013210 858062117308812008839891 := by
  unfold tailWord_5013210
  simp only [CollatzResearch.WordTrace]
  refine ⟨45711697542000958237123271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121897860112002555298995389 45711697542000958237123271)
  ·
    refine ⟨68567546313001437355684907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45711697542000958237123271 68567546313001437355684907)
    ·
      refine ⟨102851319469502156033527361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68567546313001437355684907 102851319469502156033527361)
      ·
        refine ⟨77138489602126617025145521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102851319469502156033527361 77138489602126617025145521)
        ·
          refine ⟨57853867201594962768859141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77138489602126617025145521 57853867201594962768859141)
          ·
            refine ⟨10847600100299055519161089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57853867201594962768859141 10847600100299055519161089)
            ·
              refine ⟨8135700075224291639370817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10847600100299055519161089 8135700075224291639370817)
              ·
                refine ⟨6101775056418218729528113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8135700075224291639370817 6101775056418218729528113)
                ·
                  refine ⟨4576331292313664047146085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6101775056418218729528113 4576331292313664047146085)
                  ·
                    refine ⟨858062117308812008839891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4576331292313664047146085 858062117308812008839891)
                    ·
                      rfl

theorem cell23_5013210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_5013210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013210 prefixEnd_5013210 := by exact prefixLift 5013210
  have htrace : WordTrace (prefixWord ++ tailWord_5013210) baseStart_5013210 baseEnd_5013210 := by
    simpa [prefixWord, tailWord_5013210, baseEnd_5013210] using wordTrace_append hprefix tailTrace_5013210
  have hstable : (prefixWord ++ tailWord_5013210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013210).length < 2 ^ (prefixWord ++ tailWord_5013210).sum := by decide
  have hdescent : baseEnd_5013210 < baseStart_5013210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013226 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_5013226 : Nat := 118140960795 + 5013226 * 2 ^ 59
def prefixEnd_5013226 : Nat := 4983230072969 + 3 ^ 40 * 5013226 * 2
def baseEnd_5013226 : Nat := 2574194567616907963919599

theorem tailTrace_5013226 : CollatzResearch.WordTrace tailWord_5013226 prefixEnd_5013226 2574194567616907963919599 := by
  unfold tailWord_5013226
  simp only [CollatzResearch.WordTrace]
  refine ⟨45711843433986466920268883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121898249157297245120717021 45711843433986466920268883)
  ·
    refine ⟨68567765150979700380403325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45711843433986466920268883 68567765150979700380403325)
    ·
      refine ⟨25712911931617387642651247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68567765150979700380403325 25712911931617387642651247)
      ·
        refine ⟨38569367897426081463976871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25712911931617387642651247 38569367897426081463976871)
        ·
          refine ⟨57854051846139122195965307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38569367897426081463976871 57854051846139122195965307)
          ·
            refine ⟨86781077769208683293947961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57854051846139122195965307 86781077769208683293947961)
            ·
              refine ⟨65085808326906512470460971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86781077769208683293947961 65085808326906512470460971)
              ·
                refine ⟨97628712490359768705691457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65085808326906512470460971 97628712490359768705691457)
                ·
                  refine ⟨73221534367769826529268593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97628712490359768705691457 73221534367769826529268593)
                  ·
                    refine ⟨54916150775827369896951445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73221534367769826529268593 54916150775827369896951445)
                    ·
                      refine ⟨2574194567616907963919599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54916150775827369896951445 2574194567616907963919599)
                      ·
                        rfl

theorem cell23_5013226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_5013226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013226 prefixEnd_5013226 := by exact prefixLift 5013226
  have htrace : WordTrace (prefixWord ++ tailWord_5013226) baseStart_5013226 baseEnd_5013226 := by
    simpa [prefixWord, tailWord_5013226, baseEnd_5013226] using wordTrace_append hprefix tailTrace_5013226
  have hstable : (prefixWord ++ tailWord_5013226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013226).length < 2 ^ (prefixWord ++ tailWord_5013226).sum := by decide
  have hdescent : baseEnd_5013226 < baseStart_5013226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013233 : List Nat := [1, 2, 2, 2, 2, 3, 1, 3, 1, 3, 3]
def baseStart_5013233 : Nat := 118140960795 + 5013233 * 2 ^ 59
def prefixEnd_5013233 : Nat := 4983230072969 + 3 ^ 40 * 5013233 * 2
def baseEnd_5013233 : Nat := 2574198161981489436532067

theorem tailTrace_5013233 : CollatzResearch.WordTrace tailWord_5013233 prefixEnd_5013233 2574198161981489436532067 := by
  unfold tailWord_5013233
  simp only [CollatzResearch.WordTrace]
  refine ⟨182847629046920507876580353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121898419364613671917720235 182847629046920507876580353)
  ·
    refine ⟨137135721785190380907435265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182847629046920507876580353 137135721785190380907435265)
    ·
      refine ⟨102851791338892785680576449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137135721785190380907435265 102851791338892785680576449)
      ·
        refine ⟨77138843504169589260432337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102851791338892785680576449 77138843504169589260432337)
        ·
          refine ⟨57854132628127191945324253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77138843504169589260432337 57854132628127191945324253)
          ·
            refine ⟨21695299735547696979496595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57854132628127191945324253 21695299735547696979496595)
            ·
              refine ⟨32542949603321545469244893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21695299735547696979496595 32542949603321545469244893)
              ·
                refine ⟨12203606101245579550966835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32542949603321545469244893 12203606101245579550966835)
                ·
                  refine ⟨18305409151868369326450253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12203606101245579550966835 18305409151868369326450253)
                  ·
                    refine ⟨6864528431950638497418845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18305409151868369326450253 6864528431950638497418845)
                    ·
                      refine ⟨2574198161981489436532067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6864528431950638497418845 2574198161981489436532067)
                      ·
                        rfl

theorem cell23_5013233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_5013233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013233 prefixEnd_5013233 := by exact prefixLift 5013233
  have htrace : WordTrace (prefixWord ++ tailWord_5013233) baseStart_5013233 baseEnd_5013233 := by
    simpa [prefixWord, tailWord_5013233, baseEnd_5013233] using wordTrace_append hprefix tailTrace_5013233
  have hstable : (prefixWord ++ tailWord_5013233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013233).length < 2 ^ (prefixWord ++ tailWord_5013233).sum := by decide
  have hdescent : baseEnd_5013233 < baseStart_5013233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013250 : List Nat := [3, 4, 1, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_5013250 : Nat := 118140960795 + 5013250 * 2 ^ 59
def prefixEnd_5013250 : Nat := 4983230072969 + 3 ^ 40 * 5013250 * 2
def baseEnd_5013250 : Nat := 2574206891152615870019489

theorem tailTrace_5013250 : CollatzResearch.WordTrace tailWord_5013250 prefixEnd_5013250 2574206891152615870019489 := by
  unfold tailWord_5013250
  simp only [CollatzResearch.WordTrace]
  refine ⟨45712062271964729944987301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121898832725239279853299469 45712062271964729944987301)
  ·
    refine ⟨8571011675993386864685119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45712062271964729944987301 8571011675993386864685119)
    ·
      refine ⟨12856517513990080297027679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8571011675993386864685119 12856517513990080297027679)
      ·
        refine ⟨19284776270985120445541519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12856517513990080297027679 19284776270985120445541519)
        ·
          refine ⟨28927164406477680668312279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19284776270985120445541519 28927164406477680668312279)
          ·
            refine ⟨43390746609716521002468419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28927164406477680668312279 43390746609716521002468419)
            ·
              refine ⟨65086119914574781503702629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43390746609716521002468419 65086119914574781503702629)
              ·
                refine ⟨12203647483982771531944243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65086119914574781503702629 12203647483982771531944243)
                ·
                  refine ⟨18305471225974157297916365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12203647483982771531944243 18305471225974157297916365)
                  ·
                    refine ⟨6864551709740308986718637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18305471225974157297916365 6864551709740308986718637)
                    ·
                      refine ⟨2574206891152615870019489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6864551709740308986718637 2574206891152615870019489)
                      ·
                        rfl

theorem cell23_5013250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_5013250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013250 prefixEnd_5013250 := by exact prefixLift 5013250
  have htrace : WordTrace (prefixWord ++ tailWord_5013250) baseStart_5013250 baseEnd_5013250 := by
    simpa [prefixWord, tailWord_5013250, baseEnd_5013250] using wordTrace_append hprefix tailTrace_5013250
  have hstable : (prefixWord ++ tailWord_5013250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013250).length < 2 ^ (prefixWord ++ tailWord_5013250).sum := by decide
  have hdescent : baseEnd_5013250 < baseStart_5013250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013261 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_5013261 : Nat := 118140960795 + 5013261 * 2 ^ 59
def prefixEnd_5013261 : Nat := 4983230072969 + 3 ^ 40 * 5013261 * 2
def baseEnd_5013261 : Nat := 858070846479938442327313

theorem tailTrace_5013261 : CollatzResearch.WordTrace tailWord_5013261 prefixEnd_5013261 858070846479938442327313 := by
  unfold tailWord_5013261
  simp only [CollatzResearch.WordTrace]
  refine ⟨182848650290819068658599637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121899100193879379105733091 182848650290819068658599637)
  ·
    refine ⟨4285515241191071921685929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 182848650290819068658599637 4285515241191071921685929)
    ·
      refine ⟨3214136430893303941264447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4285515241191071921685929 3214136430893303941264447)
      ·
        refine ⟨4821204646339955911896671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3214136430893303941264447 4821204646339955911896671)
        ·
          refine ⟨7231806969509933867845007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4821204646339955911896671 7231806969509933867845007)
          ·
            refine ⟨10847710454264900801767511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7231806969509933867845007 10847710454264900801767511)
            ·
              refine ⟨16271565681397351202651267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10847710454264900801767511 16271565681397351202651267)
              ·
                refine ⟨24407348522096026803976901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16271565681397351202651267 24407348522096026803976901)
                ·
                  refine ⟨4576377847893005025745669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24407348522096026803976901 4576377847893005025745669)
                  ·
                    refine ⟨858070846479938442327313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4576377847893005025745669 858070846479938442327313)
                    ·
                      rfl

theorem cell23_5013261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_5013261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013261 prefixEnd_5013261 := by exact prefixLift 5013261
  have htrace : WordTrace (prefixWord ++ tailWord_5013261) baseStart_5013261 baseEnd_5013261 := by
    simpa [prefixWord, tailWord_5013261, baseEnd_5013261] using wordTrace_append hprefix tailTrace_5013261
  have hstable : (prefixWord ++ tailWord_5013261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013261).length < 2 ^ (prefixWord ++ tailWord_5013261).sum := by decide
  have hdescent : baseEnd_5013261 < baseStart_5013261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013268 : List Nat := [2, 4, 4, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_5013268 : Nat := 118140960795 + 5013268 * 2 ^ 59
def prefixEnd_5013268 : Nat := 4983230072969 + 3 ^ 40 * 5013268 * 2
def baseEnd_5013268 : Nat := 2574216133804396799594407

theorem tailTrace_5013268 : CollatzResearch.WordTrace tailWord_5013268 prefixEnd_5013268 2574216133804396799594407 := by
  unfold tailWord_5013268
  simp only [CollatzResearch.WordTrace]
  refine ⟨91424452800896854427052229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121899270401195805902736305 91424452800896854427052229)
  ·
    refine ⟨17142084900168160205072293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91424452800896854427052229 17142084900168160205072293)
    ·
      refine ⟨3214140918781530038451055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17142084900168160205072293 3214140918781530038451055)
      ·
        refine ⟨4821211378172295057676583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3214140918781530038451055 4821211378172295057676583)
        ·
          refine ⟨7231817067258442586514875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4821211378172295057676583 7231817067258442586514875)
          ·
            refine ⟨10847725600887663879772313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7231817067258442586514875 10847725600887663879772313)
            ·
              refine ⟨8135794200665747909829235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10847725600887663879772313 8135794200665747909829235)
              ·
                refine ⟨12203691300998621864743853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8135794200665747909829235 12203691300998621864743853)
                ·
                  refine ⟨4576384237874483199278945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12203691300998621864743853 4576384237874483199278945)
                  ·
                    refine ⟨3432288178405862399459209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4576384237874483199278945 3432288178405862399459209)
                    ·
                      refine ⟨2574216133804396799594407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3432288178405862399459209 2574216133804396799594407)
                      ·
                        rfl

theorem cell23_5013268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_5013268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013268 prefixEnd_5013268 := by exact prefixLift 5013268
  have htrace : WordTrace (prefixWord ++ tailWord_5013268) baseStart_5013268 baseEnd_5013268 := by
    simpa [prefixWord, tailWord_5013268, baseEnd_5013268] using wordTrace_append hprefix tailTrace_5013268
  have hstable : (prefixWord ++ tailWord_5013268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013268).length < 2 ^ (prefixWord ++ tailWord_5013268).sum := by decide
  have hdescent : baseEnd_5013268 < baseStart_5013268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013284 : List Nat := [2, 3, 1, 3, 2, 2, 3, 1, 2, 1, 3]
def baseStart_5013284 : Nat := 118140960795 + 5013284 * 2 ^ 59
def prefixEnd_5013284 : Nat := 4983230072969 + 3 ^ 40 * 5013284 * 2
def baseEnd_5013284 : Nat := 2574224349494868736994333

theorem tailTrace_5013284 : CollatzResearch.WordTrace tailWord_5013284 prefixEnd_5013284 2574224349494868736994333 := by
  unfold tailWord_5013284
  simp only [CollatzResearch.WordTrace]
  refine ⟨91424744584867871793343453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121899659446490495724457937 91424744584867871793343453)
  ·
    refine ⟨34284279219325451922503795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91424744584867871793343453 34284279219325451922503795)
    ·
      refine ⟨51426418828988177883755693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34284279219325451922503795 51426418828988177883755693)
      ·
        refine ⟨19284907060870566706408385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51426418828988177883755693 19284907060870566706408385)
        ·
          refine ⟨14463680295652925029806289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19284907060870566706408385 14463680295652925029806289)
          ·
            refine ⟨10847760221739693772354717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14463680295652925029806289 10847760221739693772354717)
            ·
              refine ⟨4067910083152385164633019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10847760221739693772354717 4067910083152385164633019)
              ·
                refine ⟨6101865124728577746949529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4067910083152385164633019 6101865124728577746949529)
                ·
                  refine ⟨4576398843546433310212147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6101865124728577746949529 4576398843546433310212147)
                  ·
                    refine ⟨6864598265319649965318221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4576398843546433310212147 6864598265319649965318221)
                    ·
                      refine ⟨2574224349494868736994333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6864598265319649965318221 2574224349494868736994333)
                      ·
                        rfl

theorem cell23_5013284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_5013284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013284 prefixEnd_5013284 := by exact prefixLift 5013284
  have htrace : WordTrace (prefixWord ++ tailWord_5013284) baseStart_5013284 baseEnd_5013284 := by
    simpa [prefixWord, tailWord_5013284, baseEnd_5013284] using wordTrace_append hprefix tailTrace_5013284
  have hstable : (prefixWord ++ tailWord_5013284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013284).length < 2 ^ (prefixWord ++ tailWord_5013284).sum := by decide
  have hdescent : baseEnd_5013284 < baseStart_5013284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013310 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_5013310 : Nat := 118140960795 + 5013310 * 2 ^ 59
def prefixEnd_5013310 : Nat := 4983230072969 + 3 ^ 40 * 5013310 * 2
def baseEnd_5013310 : Nat := 2574237699991885635269213

theorem tailTrace_5013310 : CollatzResearch.WordTrace tailWord_5013310 prefixEnd_5013310 2574237699991885635269213 := by
  unfold tailWord_5013310
  simp only [CollatzResearch.WordTrace]
  refine ⟨22856304683455193753391673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121900291645094366684755589 22856304683455193753391673)
  ·
    refine ⟨17142228512591395315043755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22856304683455193753391673 17142228512591395315043755)
    ·
      refine ⟨25713342768887092972565633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17142228512591395315043755 25713342768887092972565633)
      ·
        refine ⟨19285007076665319729424225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25713342768887092972565633 19285007076665319729424225)
        ·
          refine ⟨14463755307498989797068169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19285007076665319729424225 14463755307498989797068169)
          ·
            refine ⟨10847816480624242347801127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14463755307498989797068169 10847816480624242347801127)
            ·
              refine ⟨16271724720936363521701691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10847816480624242347801127 16271724720936363521701691)
              ·
                refine ⟨24407587081404545282552537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16271724720936363521701691 24407587081404545282552537)
                ·
                  refine ⟨18305690311053408961914403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24407587081404545282552537 18305690311053408961914403)
                  ·
                    refine ⟨27458535466580113442871605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18305690311053408961914403 27458535466580113442871605)
                    ·
                      refine ⟨2574237699991885635269213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27458535466580113442871605 2574237699991885635269213)
                      ·
                        rfl

theorem cell23_5013310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_5013310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013310 prefixEnd_5013310 := by exact prefixLift 5013310
  have htrace : WordTrace (prefixWord ++ tailWord_5013310) baseStart_5013310 baseEnd_5013310 := by
    simpa [prefixWord, tailWord_5013310, baseEnd_5013310] using wordTrace_append hprefix tailTrace_5013310
  have hstable : (prefixWord ++ tailWord_5013310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013310).length < 2 ^ (prefixWord ++ tailWord_5013310).sum := by decide
  have hdescent : baseEnd_5013310 < baseStart_5013310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013330 : List Nat := [3, 2, 2, 1, 1, 5, 1, 1, 7]
def baseStart_5013330 : Nat := 118140960795 + 5013330 * 2 ^ 59
def prefixEnd_5013330 : Nat := 4983230072969 + 3 ^ 40 * 5013330 * 2
def baseEnd_5013330 : Nat := 286027552178330617446569

theorem tailTrace_5013330 : CollatzResearch.WordTrace tailWord_5013330 prefixEnd_5013330 286027552178330617446569 := by
  unfold tailWord_5013330
  simp only [CollatzResearch.WordTrace]
  refine ⟨45712791731892273360715361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121900777951712728961907629 45712791731892273360715361)
  ·
    refine ⟨34284593798919205020536521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45712791731892273360715361 34284593798919205020536521)
    ·
      refine ⟨25713445349189403765402391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34284593798919205020536521 25713445349189403765402391)
      ·
        refine ⟨38570168023784105648103587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25713445349189403765402391 38570168023784105648103587)
        ·
          refine ⟨57855252035676158472155381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38570168023784105648103587 57855252035676158472155381)
          ·
            refine ⟨5423929878344639856764567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57855252035676158472155381 5423929878344639856764567)
            ·
              refine ⟨8135894817516959785146851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5423929878344639856764567 8135894817516959785146851)
              ·
                refine ⟨12203842226275439677720277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8135894817516959785146851 12203842226275439677720277)
                ·
                  refine ⟨286027552178330617446569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12203842226275439677720277 286027552178330617446569)
                  ·
                    rfl

theorem cell23_5013330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_5013330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013330 prefixEnd_5013330 := by exact prefixLift 5013330
  have htrace : WordTrace (prefixWord ++ tailWord_5013330) baseStart_5013330 baseEnd_5013330 := by
    simpa [prefixWord, tailWord_5013330, baseEnd_5013330] using wordTrace_append hprefix tailTrace_5013330
  have hstable : (prefixWord ++ tailWord_5013330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013330).length < 2 ^ (prefixWord ++ tailWord_5013330).sum := by decide
  have hdescent : baseEnd_5013330 < baseStart_5013330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013380 : List Nat := [2, 3, 2, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_5013380 : Nat := 118140960795 + 5013380 * 2 ^ 59
def prefixEnd_5013380 : Nat := 4983230072969 + 3 ^ 40 * 5013380 * 2
def baseEnd_5013380 : Nat := 2574273643637700361393891

theorem tailTrace_5013380 : CollatzResearch.WordTrace tailWord_5013380 prefixEnd_5013380 2574273643637700361393891 := by
  unfold tailWord_5013380
  simp only [CollatzResearch.WordTrace]
  refine ⟨91426495288693975991090797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121901993718258634654787729 91426495288693975991090797)
  ·
    refine ⟨34284935733260240996659049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91426495288693975991090797 34284935733260240996659049)
    ·
      refine ⟨25713701799945180747494287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34284935733260240996659049 25713701799945180747494287)
      ·
        refine ⟨38570552699917771121241431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25713701799945180747494287 38570552699917771121241431)
        ·
          refine ⟨57855829049876656681862147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38570552699917771121241431 57855829049876656681862147)
          ·
            refine ⟨86783743574814985022793221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57855829049876656681862147 86783743574814985022793221)
            ·
              refine ⟨16271951920277809691773729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86783743574814985022793221 16271951920277809691773729)
              ·
                refine ⟨12203963940208357268830297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16271951920277809691773729 12203963940208357268830297)
                ·
                  refine ⟨9152972955156267951622723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12203963940208357268830297 9152972955156267951622723)
                  ·
                    refine ⟨13729459432734401927434085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9152972955156267951622723 13729459432734401927434085)
                    ·
                      refine ⟨2574273643637700361393891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13729459432734401927434085 2574273643637700361393891)
                      ·
                        rfl

theorem cell23_5013380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_5013380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013380 prefixEnd_5013380 := by exact prefixLift 5013380
  have htrace : WordTrace (prefixWord ++ tailWord_5013380) baseStart_5013380 baseEnd_5013380 := by
    simpa [prefixWord, tailWord_5013380, baseEnd_5013380] using wordTrace_append hprefix tailTrace_5013380
  have hstable : (prefixWord ++ tailWord_5013380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013380).length < 2 ^ (prefixWord ++ tailWord_5013380).sum := by decide
  have hdescent : baseEnd_5013380 < baseStart_5013380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013407 : List Nat := [1, 1, 2, 5, 3, 1, 1, 2, 3, 4]
def baseStart_5013407 : Nat := 118140960795 + 5013407 * 2 ^ 59
def prefixEnd_5013407 : Nat := 4983230072969 + 3 ^ 40 * 5013407 * 2
def baseEnd_5013407 : Nat := 858095835871790585252089

theorem tailTrace_5013407 : CollatzResearch.WordTrace tailWord_5013407 prefixEnd_5013407 858095835871790585252089 := by
  unfold tailWord_5013407
  simp only [CollatzResearch.WordTrace]
  refine ⟨182853975348290135593414475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121902650232193423728942983 182853975348290135593414475)
  ·
    refine ⟨274280963022435203390121713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182853975348290135593414475 274280963022435203390121713)
    ·
      refine ⟨205710722266826402542591285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274280963022435203390121713 205710722266826402542591285)
      ·
        refine ⟨19285380212514975238367933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 205710722266826402542591285 19285380212514975238367933)
        ·
          refine ⟨7232017579693115714387975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19285380212514975238367933 7232017579693115714387975)
          ·
            refine ⟨10848026369539673571581963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7232017579693115714387975 10848026369539673571581963)
            ·
              refine ⟨16272039554309510357372945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10848026369539673571581963 16272039554309510357372945)
              ·
                refine ⟨12204029665732132768029709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16272039554309510357372945 12204029665732132768029709)
                ·
                  refine ⟨4576511124649549788011141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12204029665732132768029709 4576511124649549788011141)
                  ·
                    refine ⟨858095835871790585252089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4576511124649549788011141 858095835871790585252089)
                    ·
                      rfl

theorem cell23_5013407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 4].length) (baseStart_5013407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013407 prefixEnd_5013407 := by exact prefixLift 5013407
  have htrace : WordTrace (prefixWord ++ tailWord_5013407) baseStart_5013407 baseEnd_5013407 := by
    simpa [prefixWord, tailWord_5013407, baseEnd_5013407] using wordTrace_append hprefix tailTrace_5013407
  have hstable : (prefixWord ++ tailWord_5013407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013407).length < 2 ^ (prefixWord ++ tailWord_5013407).sum := by decide
  have hdescent : baseEnd_5013407 < baseStart_5013407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013437 : List Nat := [1, 4, 1, 2, 3, 3, 1, 2, 6]
def baseStart_5013437 : Nat := 118140960795 + 5013437 * 2 ^ 59
def prefixEnd_5013437 : Nat := 4983230072969 + 3 ^ 40 * 5013437 * 2
def baseEnd_5013437 : Nat := 286033656892778515375681

theorem tailTrace_5013437 : CollatzResearch.WordTrace tailWord_5013437 prefixEnd_5013437 286033656892778515375681 := by
  unfold tailWord_5013437
  simp only [CollatzResearch.WordTrace]
  refine ⟨182855069538181450717006565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121903379692120967144671043 182855069538181450717006565)
  ·
    refine ⟨34285325538409022009438731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182855069538181450717006565 34285325538409022009438731)
    ·
      refine ⟨51427988307613533014158097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34285325538409022009438731 51427988307613533014158097)
      ·
        refine ⟨38570991230710149760618573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51427988307613533014158097 38570991230710149760618573)
        ·
          refine ⟨14464121711516306160231965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38570991230710149760618573 14464121711516306160231965)
          ·
            refine ⟨5424045641818614810086987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14464121711516306160231965 5424045641818614810086987)
            ·
              refine ⟨8136068462727922215130481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5424045641818614810086987 8136068462727922215130481)
              ·
                refine ⟨6102051347045941661347861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8136068462727922215130481 6102051347045941661347861)
                ·
                  refine ⟨286033656892778515375681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6102051347045941661347861 286033656892778515375681)
                  ·
                    rfl

theorem cell23_5013437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_5013437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013437 prefixEnd_5013437 := by exact prefixLift 5013437
  have htrace : WordTrace (prefixWord ++ tailWord_5013437) baseStart_5013437 baseEnd_5013437 := by
    simpa [prefixWord, tailWord_5013437, baseEnd_5013437] using wordTrace_append hprefix tailTrace_5013437
  have hstable : (prefixWord ++ tailWord_5013437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013437).length < 2 ^ (prefixWord ++ tailWord_5013437).sum := by decide
  have hdescent : baseEnd_5013437 < baseStart_5013437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013514 : List Nat := [3, 1, 2, 2, 4, 1, 1, 3, 2, 4]
def baseStart_5013514 : Nat := 118140960795 + 5013514 * 2 ^ 59
def prefixEnd_5013514 : Nat := 4983230072969 + 3 ^ 40 * 5013514 * 2
def baseEnd_5013514 : Nat := 858114150015134279039425

theorem tailTrace_5013514 : CollatzResearch.WordTrace tailWord_5013514 prefixEnd_5013514 858114150015134279039425 := by
  unfold tailWord_5013514
  simp only [CollatzResearch.WordTrace]
  refine ⟨45714469489725623216889899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121905251972601661911706397 45714469489725623216889899)
  ·
    refine ⟨68571704234588434825334849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45714469489725623216889899 68571704234588434825334849)
    ·
      refine ⟨51428778175941326119001137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68571704234588434825334849 51428778175941326119001137)
      ·
        refine ⟨38571583631955994589250853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51428778175941326119001137 38571583631955994589250853)
        ·
          refine ⟨7232171930991748985484535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38571583631955994589250853 7232171930991748985484535)
          ·
            refine ⟨10848257896487623478226803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7232171930991748985484535 10848257896487623478226803)
            ·
              refine ⟨16272386844731435217340205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10848257896487623478226803 16272386844731435217340205)
              ·
                refine ⟨6102145066774288206502577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16272386844731435217340205 6102145066774288206502577)
                ·
                  refine ⟨4576608800080716154876933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6102145066774288206502577 4576608800080716154876933)
                  ·
                    refine ⟨858114150015134279039425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4576608800080716154876933 858114150015134279039425)
                    ·
                      rfl

theorem cell23_5013514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_5013514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013514 prefixEnd_5013514 := by exact prefixLift 5013514
  have htrace : WordTrace (prefixWord ++ tailWord_5013514) baseStart_5013514 baseEnd_5013514 := by
    simpa [prefixWord, tailWord_5013514, baseEnd_5013514] using wordTrace_append hprefix tailTrace_5013514
  have hstable : (prefixWord ++ tailWord_5013514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013514).length < 2 ^ (prefixWord ++ tailWord_5013514).sum := by decide
  have hdescent : baseEnd_5013514 < baseStart_5013514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013554 : List Nat := [3, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3]
def baseStart_5013554 : Nat := 118140960795 + 5013554 * 2 ^ 59
def prefixEnd_5013554 : Nat := 4983230072969 + 3 ^ 40 * 5013554 * 2
def baseEnd_5013554 : Nat := 2574362989271582680618091

theorem tailTrace_5013554 : CollatzResearch.WordTrace tailWord_5013554 prefixEnd_5013554 2574362989271582680618091 := by
  unfold tailWord_5013554
  simp only [CollatzResearch.WordTrace]
  refine ⟨45714834219689394924753929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121906224585838386466010477 45714834219689394924753929)
  ·
    refine ⟨34286125664767046193565447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45714834219689394924753929 34286125664767046193565447)
    ·
      refine ⟨51429188497150569290348171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34286125664767046193565447 51429188497150569290348171)
      ·
        refine ⟨77143782745725853935522257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51429188497150569290348171 77143782745725853935522257)
        ·
          refine ⟨57857837059294390451641693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77143782745725853935522257 57857837059294390451641693)
          ·
            refine ⟨21696688897235396419365635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57857837059294390451641693 21696688897235396419365635)
            ·
              refine ⟨32545033345853094629048453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21696688897235396419365635 32545033345853094629048453)
              ·
                refine ⟨6102193752347455242946585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32545033345853094629048453 6102193752347455242946585)
                ·
                  refine ⟨4576645314260591432209939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6102193752347455242946585 4576645314260591432209939)
                  ·
                    refine ⟨6864967971390887148314909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4576645314260591432209939 6864967971390887148314909)
                    ·
                      refine ⟨2574362989271582680618091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6864967971390887148314909 2574362989271582680618091)
                      ·
                        rfl

theorem cell23_5013554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_5013554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013554 prefixEnd_5013554 := by exact prefixLift 5013554
  have htrace : WordTrace (prefixWord ++ tailWord_5013554) baseStart_5013554 baseEnd_5013554 := by
    simpa [prefixWord, tailWord_5013554, baseEnd_5013554] using wordTrace_append hprefix tailTrace_5013554
  have hstable : (prefixWord ++ tailWord_5013554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013554).length < 2 ^ (prefixWord ++ tailWord_5013554).sum := by decide
  have hdescent : baseEnd_5013554 < baseStart_5013554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013580 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 4, 1, 5]
def baseStart_5013580 : Nat := 118140960795 + 5013580 * 2 ^ 59
def prefixEnd_5013580 : Nat := 4983230072969 + 3 ^ 40 * 5013580 * 2
def baseEnd_5013580 : Nat := 2574376339768599578892971

theorem tailTrace_5013580 : CollatzResearch.WordTrace tailWord_5013580 prefixEnd_5013580 2574376339768599578892971 := by
  unfold tailWord_5013580
  simp only [CollatzResearch.WordTrace]
  refine ⟨91430142588331693069731097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121906856784442257426308129 91430142588331693069731097)
  ·
    refine ⟨68572606941248769802298323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91430142588331693069731097 68572606941248769802298323)
    ·
      refine ⟨102858910411873154703447485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68572606941248769802298323 102858910411873154703447485)
      ·
        refine ⟨38572091404452433013792807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102858910411873154703447485 38572091404452433013792807)
        ·
          refine ⟨57858137106678649520689211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38572091404452433013792807 57858137106678649520689211)
          ·
            refine ⟨86787205660017974281033817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57858137106678649520689211 86787205660017974281033817)
            ·
              refine ⟨65090404245013480710775363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86787205660017974281033817 65090404245013480710775363)
              ·
                refine ⟨97635606367520221066163045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65090404245013480710775363 97635606367520221066163045)
                ·
                  refine ⟨18306676193910041449905571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97635606367520221066163045 18306676193910041449905571)
                  ·
                    refine ⟨27460014290865062174858357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18306676193910041449905571 27460014290865062174858357)
                    ·
                      refine ⟨2574376339768599578892971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27460014290865062174858357 2574376339768599578892971)
                      ·
                        rfl

theorem cell23_5013580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_5013580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013580 prefixEnd_5013580 := by exact prefixLift 5013580
  have htrace : WordTrace (prefixWord ++ tailWord_5013580) baseStart_5013580 baseEnd_5013580 := by
    simpa [prefixWord, tailWord_5013580, baseEnd_5013580] using wordTrace_append hprefix tailTrace_5013580
  have hstable : (prefixWord ++ tailWord_5013580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013580).length < 2 ^ (prefixWord ++ tailWord_5013580).sum := by decide
  have hdescent : baseEnd_5013580 < baseStart_5013580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013581 : List Nat := [1, 6, 1, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_5013581 : Nat := 118140960795 + 5013581 * 2 ^ 59
def prefixEnd_5013581 : Nat := 4983230072969 + 3 ^ 40 * 5013581 * 2
def baseEnd_5013581 : Nat := 2574376853249254074980467

theorem tailTrace_5013581 : CollatzResearch.WordTrace tailWord_5013581 prefixEnd_5013581 2574376853249254074980467 := by
  unfold tailWord_5013581
  simp only [CollatzResearch.WordTrace]
  refine ⟨182860321649659763310248597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121906881099773175540165731 182860321649659763310248597)
  ·
    refine ⟨8571577577327801405167903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 182860321649659763310248597 8571577577327801405167903)
    ·
      refine ⟨12857366365991702107751855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8571577577327801405167903 12857366365991702107751855)
      ·
        refine ⟨19286049548987553161627783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12857366365991702107751855 19286049548987553161627783)
        ·
          refine ⟨28929074323481329742441675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19286049548987553161627783 28929074323481329742441675)
          ·
            refine ⟨43393611485221994613662513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28929074323481329742441675 43393611485221994613662513)
            ·
              refine ⟨32545208613916495960246885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43393611485221994613662513 32545208613916495960246885)
              ·
                refine ⟨6102226615109342992546291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32545208613916495960246885 6102226615109342992546291)
                ·
                  refine ⟨9153339922664014488819437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6102226615109342992546291 9153339922664014488819437)
                  ·
                    refine ⟨3432502470999005433307289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9153339922664014488819437 3432502470999005433307289)
                    ·
                      refine ⟨2574376853249254074980467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3432502470999005433307289 2574376853249254074980467)
                      ·
                        rfl

theorem cell23_5013581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_5013581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013581 prefixEnd_5013581 := by exact prefixLift 5013581
  have htrace : WordTrace (prefixWord ++ tailWord_5013581) baseStart_5013581 baseEnd_5013581 := by
    simpa [prefixWord, tailWord_5013581, baseEnd_5013581] using wordTrace_append hprefix tailTrace_5013581
  have hstable : (prefixWord ++ tailWord_5013581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013581).length < 2 ^ (prefixWord ++ tailWord_5013581).sum := by decide
  have hdescent : baseEnd_5013581 < baseStart_5013581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013594 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2]
def baseStart_5013594 : Nat := 118140960795 + 5013594 * 2 ^ 59
def prefixEnd_5013594 : Nat := 4983230072969 + 3 ^ 40 * 5013594 * 2
def baseEnd_5013594 : Nat := 2574383528497762524117907

theorem tailTrace_5013594 : CollatzResearch.WordTrace tailWord_5013594 prefixEnd_5013594 2574383528497762524117907 := by
  unfold tailWord_5013594
  simp only [CollatzResearch.WordTrace]
  refine ⟨45715198949653166632617959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121907197199075111020314557 45715198949653166632617959)
  ·
    refine ⟨68572798424479749948926939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45715198949653166632617959 68572798424479749948926939)
    ·
      refine ⟨102859197636719624923390409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68572798424479749948926939 102859197636719624923390409)
      ·
        refine ⟨77144398227539718692542807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102859197636719624923390409 77144398227539718692542807)
        ·
          refine ⟨115716597341309578038814211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77144398227539718692542807 115716597341309578038814211)
          ·
            refine ⟨173574896011964367058221317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115716597341309578038814211 173574896011964367058221317)
            ·
              refine ⟨32545293002243318823416497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173574896011964367058221317 32545293002243318823416497)
              ·
                refine ⟨24408969751682489117562373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32545293002243318823416497 24408969751682489117562373)
                ·
                  refine ⟨4576681828440466709542945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24408969751682489117562373 4576681828440466709542945)
                  ·
                    refine ⟨3432511371330350032157209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4576681828440466709542945 3432511371330350032157209)
                    ·
                      refine ⟨2574383528497762524117907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3432511371330350032157209 2574383528497762524117907)
                      ·
                        rfl

theorem cell23_5013594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_5013594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013594 prefixEnd_5013594 := by exact prefixLift 5013594
  have htrace : WordTrace (prefixWord ++ tailWord_5013594) baseStart_5013594 baseEnd_5013594 := by
    simpa [prefixWord, tailWord_5013594, baseEnd_5013594] using wordTrace_append hprefix tailTrace_5013594
  have hstable : (prefixWord ++ tailWord_5013594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013594).length < 2 ^ (prefixWord ++ tailWord_5013594).sum := by decide
  have hdescent : baseEnd_5013594 < baseStart_5013594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013617 : List Nat := [1, 2, 2, 2, 1, 1, 3, 6, 5]
def baseStart_5013617 : Nat := 118140960795 + 5013617 * 2 ^ 59
def prefixEnd_5013617 : Nat := 4983230072969 + 3 ^ 40 * 5013617 * 2
def baseEnd_5013617 : Nat := 286043926505868437125589

theorem tailTrace_5013617 : CollatzResearch.WordTrace tailWord_5013617 prefixEnd_5013617 286043926505868437125589 := by
  unfold tailWord_5013617
  simp only [CollatzResearch.WordTrace]
  refine ⟨182861634677529341458559105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121907756451686227639039403 182861634677529341458559105)
  ·
    refine ⟨137146226008147006093919329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182861634677529341458559105 137146226008147006093919329)
    ·
      refine ⟨102859669506110254570439497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137146226008147006093919329 102859669506110254570439497)
      ·
        refine ⟨77144752129582690927829623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102859669506110254570439497 77144752129582690927829623)
        ·
          refine ⟨115717128194374036391744435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77144752129582690927829623 115717128194374036391744435)
          ·
            refine ⟨173575692291561054587616653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115717128194374036391744435 173575692291561054587616653)
            ·
              refine ⟨65090884609335395470356245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173575692291561054587616653 65090884609335395470356245)
              ·
                refine ⟨3051135216062596662672949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65090884609335395470356245 3051135216062596662672949)
                ·
                  refine ⟨286043926505868437125589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3051135216062596662672949 286043926505868437125589)
                  ·
                    rfl

theorem cell23_5013617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 5].length) (baseStart_5013617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013617 prefixEnd_5013617 := by exact prefixLift 5013617
  have htrace : WordTrace (prefixWord ++ tailWord_5013617) baseStart_5013617 baseEnd_5013617 := by
    simpa [prefixWord, tailWord_5013617, baseEnd_5013617] using wordTrace_append hprefix tailTrace_5013617
  have hstable : (prefixWord ++ tailWord_5013617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013617).length < 2 ^ (prefixWord ++ tailWord_5013617).sum := by decide
  have hdescent : baseEnd_5013617 < baseStart_5013617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013628 : List Nat := [2, 2, 2, 1, 1, 5, 3, 1, 2, 2, 2]
def baseStart_5013628 : Nat := 118140960795 + 5013628 * 2 ^ 59
def prefixEnd_5013628 : Nat := 4983230072969 + 3 ^ 40 * 5013628 * 2
def baseEnd_5013628 : Nat := 2574400986840015391092751

theorem tailTrace_5013628 : CollatzResearch.WordTrace tailWord_5013628 prefixEnd_5013628 2574400986840015391092751 := by
  unfold tailWord_5013628
  simp only [CollatzResearch.WordTrace]
  refine ⟨91431017940244745168604769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121908023920326326891473025 91431017940244745168604769)
  ·
    refine ⟨68573263455183558876453577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91431017940244745168604769 68573263455183558876453577)
    ·
      refine ⟨51429947591387669157340183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68573263455183558876453577 51429947591387669157340183)
      ·
        refine ⟨77144921387081503736010275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51429947591387669157340183 77144921387081503736010275)
        ·
          refine ⟨115717382080622255604015413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77144921387081503736010275 115717382080622255604015413)
          ·
            refine ⟨10848504570058336462876445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115717382080622255604015413 10848504570058336462876445)
            ·
              refine ⟨4068189213771876173578667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10848504570058336462876445 4068189213771876173578667)
              ·
                refine ⟨6102283820657814260368001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4068189213771876173578667 6102283820657814260368001)
                ·
                  refine ⟨4576712865493360695276001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6102283820657814260368001 4576712865493360695276001)
                  ·
                    refine ⟨3432534649120020521457001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4576712865493360695276001 3432534649120020521457001)
                    ·
                      refine ⟨2574400986840015391092751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3432534649120020521457001 2574400986840015391092751)
                      ·
                        rfl

theorem cell23_5013628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_5013628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013628 prefixEnd_5013628 := by exact prefixLift 5013628
  have htrace : WordTrace (prefixWord ++ tailWord_5013628) baseStart_5013628 baseEnd_5013628 := by
    simpa [prefixWord, tailWord_5013628, baseEnd_5013628] using wordTrace_append hprefix tailTrace_5013628
  have hstable : (prefixWord ++ tailWord_5013628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013628).length < 2 ^ (prefixWord ++ tailWord_5013628).sum := by decide
  have hdescent : baseEnd_5013628 < baseStart_5013628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013698 : List Nat := [3, 5, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_5013698 : Nat := 118140960795 + 5013698 * 2 ^ 59
def prefixEnd_5013698 : Nat := 4983230072969 + 3 ^ 40 * 5013698 * 2
def baseEnd_5013698 : Nat := 858145643495276705739143

theorem tailTrace_5013698 : CollatzResearch.WordTrace tailWord_5013698 prefixEnd_5013698 858145643495276705739143 := by
  unfold tailWord_5013698
  simp only [CollatzResearch.WordTrace]
  refine ⟨45716147247558973073064437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121909725993490594861505165 45716147247558973073064437)
  ·
    refine ⟨4285888804458653725599791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45716147247558973073064437 4285888804458653725599791)
    ·
      refine ⟨6428833206687980588399687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4285888804458653725599791 6428833206687980588399687)
      ·
        refine ⟨9643249810031970882599531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6428833206687980588399687 9643249810031970882599531)
        ·
          refine ⟨14464874715047956323899297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9643249810031970882599531 14464874715047956323899297)
          ·
            refine ⟨10848656036285967242924473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14464874715047956323899297 10848656036285967242924473)
            ·
              refine ⟨8136492027214475432193355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10848656036285967242924473 8136492027214475432193355)
              ·
                refine ⟨12204738040821713148290033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8136492027214475432193355 12204738040821713148290033)
                ·
                  refine ⟨9153553530616284861217525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12204738040821713148290033 9153553530616284861217525)
                  ·
                    refine ⟨858145643495276705739143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9153553530616284861217525 858145643495276705739143)
                    ·
                      rfl

theorem cell23_5013698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_5013698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013698 prefixEnd_5013698 := by exact prefixLift 5013698
  have htrace : WordTrace (prefixWord ++ tailWord_5013698) baseStart_5013698 baseEnd_5013698 := by
    simpa [prefixWord, tailWord_5013698, baseEnd_5013698] using wordTrace_append hprefix tailTrace_5013698
  have hstable : (prefixWord ++ tailWord_5013698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013698).length < 2 ^ (prefixWord ++ tailWord_5013698).sum := by decide
  have hdescent : baseEnd_5013698 < baseStart_5013698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013744 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 4, 3, 2]
def baseStart_5013744 : Nat := 118140960795 + 5013744 * 2 ^ 59
def prefixEnd_5013744 : Nat := 4983230072969 + 3 ^ 40 * 5013744 * 2
def baseEnd_5013744 : Nat := 2574460550595936937242217

theorem tailTrace_5013744 : CollatzResearch.WordTrace tailWord_5013744 prefixEnd_5013744 2574460550595936937242217 := by
  unfold tailWord_5013744
  simp only [CollatzResearch.WordTrace]
  refine ⟨91433133374034621074216143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121910844498712828098954857 91433133374034621074216143)
  ·
    refine ⟨137149700061051931611324215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91433133374034621074216143 137149700061051931611324215)
    ·
      refine ⟨205724550091577897416986323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137149700061051931611324215 205724550091577897416986323)
      ·
        refine ⟨308586825137366846125479485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205724550091577897416986323 308586825137366846125479485)
        ·
          refine ⟨115720059426512567297054807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308586825137366846125479485 115720059426512567297054807)
          ·
            refine ⟨173580089139768850945582211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115720059426512567297054807 173580089139768850945582211)
            ·
              refine ⟨260370133709653276418373317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173580089139768850945582211 260370133709653276418373317)
              ·
                refine ⟨48819400070559989328444997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260370133709653276418373317 48819400070559989328444997)
                ·
                  refine ⟨9153637513229997999083437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48819400070559989328444997 9153637513229997999083437)
                  ·
                    refine ⟨3432614067461249249656289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9153637513229997999083437 3432614067461249249656289)
                    ·
                      refine ⟨2574460550595936937242217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3432614067461249249656289 2574460550595936937242217)
                      ·
                        rfl

theorem cell23_5013744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 4, 3, 2].length) (baseStart_5013744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013744 prefixEnd_5013744 := by exact prefixLift 5013744
  have htrace : WordTrace (prefixWord ++ tailWord_5013744) baseStart_5013744 baseEnd_5013744 := by
    simpa [prefixWord, tailWord_5013744, baseEnd_5013744] using wordTrace_append hprefix tailTrace_5013744
  have hstable : (prefixWord ++ tailWord_5013744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013744).length < 2 ^ (prefixWord ++ tailWord_5013744).sum := by decide
  have hdescent : baseEnd_5013744 < baseStart_5013744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013768 : List Nat := [2, 1, 3, 2, 3, 1, 1, 5, 1, 1, 3]
def baseStart_5013768 : Nat := 118140960795 + 5013768 * 2 ^ 59
def prefixEnd_5013768 : Nat := 4983230072969 + 3 ^ 40 * 5013768 * 2
def baseEnd_5013768 : Nat := 2574472874131644843342107

theorem tailTrace_5013768 : CollatzResearch.WordTrace tailWord_5013768 prefixEnd_5013768 2574472874131644843342107 := by
  unfold tailWord_5013768
  simp only [CollatzResearch.WordTrace]
  refine ⟨91433571049991147123652979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121911428066654862831537305 91433571049991147123652979)
  ·
    refine ⟨137150356574986720685479469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91433571049991147123652979 137150356574986720685479469)
    ·
      refine ⟨51431383715620020257054801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137150356574986720685479469 51431383715620020257054801)
      ·
        refine ⟨38573537786715015192791101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51431383715620020257054801 38573537786715015192791101)
        ·
          refine ⟨14465076670018130697296663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38573537786715015192791101 14465076670018130697296663)
          ·
            refine ⟨21697615005027196045944995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14465076670018130697296663 21697615005027196045944995)
            ·
              refine ⟨32546422507540794068917493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21697615005027196045944995 32546422507540794068917493)
              ·
                refine ⟨3051227110081949443961015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32546422507540794068917493 3051227110081949443961015)
                ·
                  refine ⟨4576840665122924165941523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3051227110081949443961015 4576840665122924165941523)
                  ·
                    refine ⟨6865260997684386248912285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4576840665122924165941523 6865260997684386248912285)
                    ·
                      refine ⟨2574472874131644843342107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6865260997684386248912285 2574472874131644843342107)
                      ·
                        rfl

theorem cell23_5013768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_5013768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013768 prefixEnd_5013768 := by exact prefixLift 5013768
  have htrace : WordTrace (prefixWord ++ tailWord_5013768) baseStart_5013768 baseEnd_5013768 := by
    simpa [prefixWord, tailWord_5013768, baseEnd_5013768] using wordTrace_append hprefix tailTrace_5013768
  have hstable : (prefixWord ++ tailWord_5013768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013768).length < 2 ^ (prefixWord ++ tailWord_5013768).sum := by decide
  have hdescent : baseEnd_5013768 < baseStart_5013768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013784 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 4, 4]
def baseStart_5013784 : Nat := 118140960795 + 5013784 * 2 ^ 59
def prefixEnd_5013784 : Nat := 4983230072969 + 3 ^ 40 * 5013784 * 2
def baseEnd_5013784 : Nat := 858160363274038926914011

theorem tailTrace_5013784 : CollatzResearch.WordTrace tailWord_5013784 prefixEnd_5013784 858160363274038926914011 := by
  unfold tailWord_5013784
  simp only [CollatzResearch.WordTrace]
  refine ⟨91433862833962164489944203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121911817111949552653258937 91433862833962164489944203)
  ·
    refine ⟨137150794250943246734916305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91433862833962164489944203 137150794250943246734916305)
    ·
      refine ⟨102863095688207435051187229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137150794250943246734916305 102863095688207435051187229)
      ·
        refine ⟨38573660883077788144195211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102863095688207435051187229 38573660883077788144195211)
        ·
          refine ⟨57860491324616682216292817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38573660883077788144195211 57860491324616682216292817)
          ·
            refine ⟨43395368493462511662219613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57860491324616682216292817 43395368493462511662219613)
            ·
              refine ⟨16273263185048441873332355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43395368493462511662219613 16273263185048441873332355)
              ·
                refine ⟨24409894777572662809998533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16273263185048441873332355 24409894777572662809998533)
                ·
                  refine ⟨4576855270794874276874725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24409894777572662809998533 4576855270794874276874725)
                  ·
                    refine ⟨858160363274038926914011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4576855270794874276874725 858160363274038926914011)
                    ·
                      rfl

theorem cell23_5013784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_5013784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013784 prefixEnd_5013784 := by exact prefixLift 5013784
  have htrace : WordTrace (prefixWord ++ tailWord_5013784) baseStart_5013784 baseEnd_5013784 := by
    simpa [prefixWord, tailWord_5013784, baseEnd_5013784] using wordTrace_append hprefix tailTrace_5013784
  have hstable : (prefixWord ++ tailWord_5013784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013784).length < 2 ^ (prefixWord ++ tailWord_5013784).sum := by decide
  have hdescent : baseEnd_5013784 < baseStart_5013784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013787 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 4]
def baseStart_5013787 : Nat := 118140960795 + 5013787 * 2 ^ 59
def prefixEnd_5013787 : Nat := 4983230072969 + 3 ^ 40 * 5013787 * 2
def baseEnd_5013787 : Nat := 2574482630264080269004519

theorem tailTrace_5013787 : CollatzResearch.WordTrace tailWord_5013787 prefixEnd_5013787 2574482630264080269004519 := by
  unfold tailWord_5013787
  simp only [CollatzResearch.WordTrace]
  refine ⟨182867835086913460492247615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121911890057942306994831743 182867835086913460492247615)
  ·
    refine ⟨274301752630370190738371423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182867835086913460492247615 274301752630370190738371423)
    ·
      refine ⟨411452628945555286107557135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274301752630370190738371423 411452628945555286107557135)
      ·
        refine ⟨617178943418332929161335703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411452628945555286107557135 617178943418332929161335703)
        ·
          refine ⟨925768415127499393742003555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617178943418332929161335703 925768415127499393742003555)
          ·
            refine ⟨1388652622691249090613005333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925768415127499393742003555 1388652622691249090613005333)
            ·
              refine ⟨65093091688652301122484625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1388652622691249090613005333 65093091688652301122484625)
              ·
                refine ⟨48819818766489225841863469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65093091688652301122484625 48819818766489225841863469)
                ·
                  refine ⟨18307432037433459690698801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48819818766489225841863469 18307432037433459690698801)
                  ·
                    refine ⟨13730574028075094768024101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18307432037433459690698801 13730574028075094768024101)
                    ·
                      refine ⟨2574482630264080269004519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13730574028075094768024101 2574482630264080269004519)
                      ·
                        rfl

theorem cell23_5013787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 4].length) (baseStart_5013787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013787 prefixEnd_5013787 := by exact prefixLift 5013787
  have htrace : WordTrace (prefixWord ++ tailWord_5013787) baseStart_5013787 baseEnd_5013787 := by
    simpa [prefixWord, tailWord_5013787, baseEnd_5013787] using wordTrace_append hprefix tailTrace_5013787
  have hstable : (prefixWord ++ tailWord_5013787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013787).length < 2 ^ (prefixWord ++ tailWord_5013787).sum := by decide
  have hdescent : baseEnd_5013787 < baseStart_5013787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013794 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_5013794 : Nat := 118140960795 + 5013794 * 2 ^ 59
def prefixEnd_5013794 : Nat := 4983230072969 + 3 ^ 40 * 5013794 * 2
def baseEnd_5013794 : Nat := 2574486224628661741616987

theorem tailTrace_5013794 : CollatzResearch.WordTrace tailWord_5013794 prefixEnd_5013794 2574486224628661741616987 := by
  unfold tailWord_5013794
  simp only [CollatzResearch.WordTrace]
  refine ⟨45717022599472025171938109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121912060265258733791834957 45717022599472025171938109)
  ·
    refine ⟨17143883474802009439476791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45717022599472025171938109 17143883474802009439476791)
    ·
      refine ⟨25715825212203014159215187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17143883474802009439476791 25715825212203014159215187)
      ·
        refine ⟨38573737818304521238822781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25715825212203014159215187 38573737818304521238822781)
        ·
          refine ⟨14465151681864195464558543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38573737818304521238822781 14465151681864195464558543)
          ·
            refine ⟨21697727522796293196837815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14465151681864195464558543 21697727522796293196837815)
            ·
              refine ⟨32546591284194439795256723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21697727522796293196837815 32546591284194439795256723)
              ·
                refine ⟨48819886926291659692885085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32546591284194439795256723 48819886926291659692885085)
                ·
                  refine ⟨18307457597359372384831907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48819886926291659692885085 18307457597359372384831907)
                  ·
                    refine ⟨27461186396039058577247861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18307457597359372384831907 27461186396039058577247861)
                    ·
                      refine ⟨2574486224628661741616987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27461186396039058577247861 2574486224628661741616987)
                      ·
                        rfl

theorem cell23_5013794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_5013794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013794 prefixEnd_5013794 := by exact prefixLift 5013794
  have htrace : WordTrace (prefixWord ++ tailWord_5013794) baseStart_5013794 baseEnd_5013794 := by
    simpa [prefixWord, tailWord_5013794, baseEnd_5013794] using wordTrace_append hprefix tailTrace_5013794
  have hstable : (prefixWord ++ tailWord_5013794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013794).length < 2 ^ (prefixWord ++ tailWord_5013794).sum := by decide
  have hdescent : baseEnd_5013794 < baseStart_5013794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013804 : List Nat := [2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 4]
def baseStart_5013804 : Nat := 118140960795 + 5013804 * 2 ^ 59
def prefixEnd_5013804 : Nat := 4983230072969 + 3 ^ 40 * 5013804 * 2
def baseEnd_5013804 : Nat := 2574491359435206702491941

theorem tailTrace_5013804 : CollatzResearch.WordTrace tailWord_5013804 prefixEnd_5013804 2574491359435206702491941 := by
  unfold tailWord_5013804
  simp only [CollatzResearch.WordTrace]
  refine ⟨91434227563925936197808233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121912303418567914930410977 91434227563925936197808233)
  ·
    refine ⟨68575670672944452148356175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91434227563925936197808233 68575670672944452148356175)
    ·
      refine ⟨102863506009416678222534263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68575670672944452148356175 102863506009416678222534263)
      ·
        refine ⟨154295259014125017333801395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102863506009416678222534263 154295259014125017333801395)
        ·
          refine ⟨231442888521187526000702093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154295259014125017333801395 231442888521187526000702093)
          ·
            refine ⟨86791083195445322250263285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231442888521187526000702093 86791083195445322250263285)
            ·
              refine ⟨8136664049572998960962183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86791083195445322250263285 8136664049572998960962183)
              ·
                refine ⟨12204996074359498441443275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8136664049572998960962183 12204996074359498441443275)
                ·
                  refine ⟨18307494111539247662164913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12204996074359498441443275 18307494111539247662164913)
                  ·
                    refine ⟨13730620583654435746623685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18307494111539247662164913 13730620583654435746623685)
                    ·
                      refine ⟨2574491359435206702491941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13730620583654435746623685 2574491359435206702491941)
                      ·
                        rfl

theorem cell23_5013804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_5013804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013804 prefixEnd_5013804 := by exact prefixLift 5013804
  have htrace : WordTrace (prefixWord ++ tailWord_5013804) baseStart_5013804 baseEnd_5013804 := by
    simpa [prefixWord, tailWord_5013804, baseEnd_5013804] using wordTrace_append hprefix tailTrace_5013804
  have hstable : (prefixWord ++ tailWord_5013804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013804).length < 2 ^ (prefixWord ++ tailWord_5013804).sum := by decide
  have hdescent : baseEnd_5013804 < baseStart_5013804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013811 : List Nat := [1, 1, 1, 2, 5, 1, 4, 2, 1, 2, 3]
def baseStart_5013811 : Nat := 118140960795 + 5013811 * 2 ^ 59
def prefixEnd_5013811 : Nat := 4983230072969 + 3 ^ 40 * 5013811 * 2
def baseEnd_5013811 : Nat := 2574494953799788175104409

theorem tailTrace_5013811 : CollatzResearch.WordTrace tailWord_5013811 prefixEnd_5013811 2574494953799788175104409 := by
  unfold tailWord_5013811
  simp only [CollatzResearch.WordTrace]
  refine ⟨182868710438826512591121287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121912473625884341727414191 182868710438826512591121287)
  ·
    refine ⟨274303065658239768886681931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182868710438826512591121287 274303065658239768886681931)
    ·
      refine ⟨411454598487359653330022897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274303065658239768886681931 411454598487359653330022897)
      ·
        refine ⟨308590948865519739997517173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 411454598487359653330022897 308590948865519739997517173)
        ·
          refine ⟨28930401456142475624767235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 308590948865519739997517173 28930401456142475624767235)
          ·
            refine ⟨43395602184213713437150853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28930401456142475624767235 43395602184213713437150853)
            ·
              refine ⟨8136675409540071269465785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43395602184213713437150853 8136675409540071269465785)
              ·
                refine ⟨6102506557155053452099339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8136675409540071269465785 6102506557155053452099339)
                ·
                  refine ⟨9153759835732580178149009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6102506557155053452099339 9153759835732580178149009)
                  ·
                    refine ⟨6865319876799435133611757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9153759835732580178149009 6865319876799435133611757)
                    ·
                      refine ⟨2574494953799788175104409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6865319876799435133611757 2574494953799788175104409)
                      ·
                        rfl

theorem cell23_5013811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 2, 3].length) (baseStart_5013811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013811 prefixEnd_5013811 := by exact prefixLift 5013811
  have htrace : WordTrace (prefixWord ++ tailWord_5013811) baseStart_5013811 baseEnd_5013811 := by
    simpa [prefixWord, tailWord_5013811, baseEnd_5013811] using wordTrace_append hprefix tailTrace_5013811
  have hstable : (prefixWord ++ tailWord_5013811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013811).length < 2 ^ (prefixWord ++ tailWord_5013811).sum := by decide
  have hdescent : baseEnd_5013811 < baseStart_5013811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013828 : List Nat := [2, 3, 4, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_5013828 : Nat := 118140960795 + 5013828 * 2 ^ 59
def prefixEnd_5013828 : Nat := 4983230072969 + 3 ^ 40 * 5013828 * 2
def baseEnd_5013828 : Nat := 2574503682970914608591831

theorem tailTrace_5013828 : CollatzResearch.WordTrace tailWord_5013828 prefixEnd_5013828 2574503682970914608591831 := by
  unfold tailWord_5013828
  simp only [CollatzResearch.WordTrace]
  refine ⟨91434665239882462247245069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121912886986509949662993425 91434665239882462247245069)
  ·
    refine ⟨34287999464955923342716901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91434665239882462247245069 34287999464955923342716901)
    ·
      refine ⟨6428999899679235626759419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34287999464955923342716901 6428999899679235626759419)
      ·
        refine ⟨9643499849518853440139129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6428999899679235626759419 9643499849518853440139129)
        ·
          refine ⟨7232624887139140080104347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9643499849518853440139129 7232624887139140080104347)
          ·
            refine ⟨10848937330708710120156521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7232624887139140080104347 10848937330708710120156521)
            ·
              refine ⟨8136702998031532590117391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10848937330708710120156521 8136702998031532590117391)
              ·
                refine ⟨12205054497047298885176087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8136702998031532590117391 12205054497047298885176087)
                ·
                  refine ⟨18307581745570948327764131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12205054497047298885176087 18307581745570948327764131)
                  ·
                    refine ⟨27461372618356422491646197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18307581745570948327764131 27461372618356422491646197)
                    ·
                      refine ⟨2574503682970914608591831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27461372618356422491646197 2574503682970914608591831)
                      ·
                        rfl

theorem cell23_5013828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_5013828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013828 prefixEnd_5013828 := by exact prefixLift 5013828
  have htrace : WordTrace (prefixWord ++ tailWord_5013828) baseStart_5013828 baseEnd_5013828 := by
    simpa [prefixWord, tailWord_5013828, baseEnd_5013828] using wordTrace_append hprefix tailTrace_5013828
  have hstable : (prefixWord ++ tailWord_5013828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013828).length < 2 ^ (prefixWord ++ tailWord_5013828).sum := by decide
  have hdescent : baseEnd_5013828 < baseStart_5013828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013841 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 4, 1, 3]
def baseStart_5013841 : Nat := 118140960795 + 5013841 * 2 ^ 59
def prefixEnd_5013841 : Nat := 4983230072969 + 3 ^ 40 * 5013841 * 2
def baseEnd_5013841 : Nat := 2574510358219423057729271

theorem tailTrace_5013841 : CollatzResearch.WordTrace tailWord_5013841 prefixEnd_5013841 2574510358219423057729271 := by
  unfold tailWord_5013841
  simp only [CollatzResearch.WordTrace]
  refine ⟨182869804628717827714713377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121913203085811885143142251 182869804628717827714713377)
  ·
    refine ⟨137152353471538370786035033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182869804628717827714713377 137152353471538370786035033)
    ·
      refine ⟨102864265103653778089526275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137152353471538370786035033 102864265103653778089526275)
      ·
        refine ⟨154296397655480667134289413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102864265103653778089526275 154296397655480667134289413)
        ·
          refine ⟨28930574560402625087679265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154296397655480667134289413 28930574560402625087679265)
          ·
            refine ⟨21697930920301968815759449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28930574560402625087679265 21697930920301968815759449)
            ·
              refine ⟨16273448190226476611819587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21697930920301968815759449 16273448190226476611819587)
              ·
                refine ⟨24410172285339714917729381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16273448190226476611819587 24410172285339714917729381)
                ·
                  refine ⟨4576907303501196547074259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24410172285339714917729381 4576907303501196547074259)
                  ·
                    refine ⟨6865360955251794820611389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4576907303501196547074259 6865360955251794820611389)
                    ·
                      refine ⟨2574510358219423057729271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6865360955251794820611389 2574510358219423057729271)
                      ·
                        rfl

theorem cell23_5013841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 1, 3].length) (baseStart_5013841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013841 prefixEnd_5013841 := by exact prefixLift 5013841
  have htrace : WordTrace (prefixWord ++ tailWord_5013841) baseStart_5013841 baseEnd_5013841 := by
    simpa [prefixWord, tailWord_5013841, baseEnd_5013841] using wordTrace_append hprefix tailTrace_5013841
  have hstable : (prefixWord ++ tailWord_5013841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013841).length < 2 ^ (prefixWord ++ tailWord_5013841).sum := by decide
  have hdescent : baseEnd_5013841 < baseStart_5013841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013852 : List Nat := [2, 2, 4, 3, 1, 2, 2, 1, 2, 4]
def baseStart_5013852 : Nat := 118140960795 + 5013852 * 2 ^ 59
def prefixEnd_5013852 : Nat := 4983230072969 + 3 ^ 40 * 5013852 * 2
def baseEnd_5013852 : Nat := 858172002168874171563907

theorem tailTrace_5013852 : CollatzResearch.WordTrace tailWord_5013852 prefixEnd_5013852 858172002168874171563907 := by
  unfold tailWord_5013852
  simp only [CollatzResearch.WordTrace]
  refine ⟨91435102915838988296681905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121913470554451984395575873 91435102915838988296681905)
  ·
    refine ⟨68576327186879241222511429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91435102915838988296681905 68576327186879241222511429)
    ·
      refine ⟨12858061347539857729220893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68576327186879241222511429 12858061347539857729220893)
      ·
        refine ⟨4821773005327446648457835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12858061347539857729220893 4821773005327446648457835)
        ·
          refine ⟨7232659507991169972686753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4821773005327446648457835 7232659507991169972686753)
          ·
            refine ⟨5424494630993377479515065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7232659507991169972686753 5424494630993377479515065)
            ·
              refine ⟨4068370973245033109636299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5424494630993377479515065 4068370973245033109636299)
              ·
                refine ⟨6102556459867549664454449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4068370973245033109636299 6102556459867549664454449)
                ·
                  refine ⟨4576917344900662248340837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6102556459867549664454449 4576917344900662248340837)
                  ·
                    refine ⟨858172002168874171563907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4576917344900662248340837 858172002168874171563907)
                    ·
                      rfl

theorem cell23_5013852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_5013852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013852 prefixEnd_5013852 := by exact prefixLift 5013852
  have htrace : WordTrace (prefixWord ++ tailWord_5013852) baseStart_5013852 baseEnd_5013852 := by
    simpa [prefixWord, tailWord_5013852, baseEnd_5013852] using wordTrace_append hprefix tailTrace_5013852
  have hstable : (prefixWord ++ tailWord_5013852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013852).length < 2 ^ (prefixWord ++ tailWord_5013852).sum := by decide
  have hdescent : baseEnd_5013852 < baseStart_5013852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013867 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 5]
def baseStart_5013867 : Nat := 118140960795 + 5013867 * 2 ^ 59
def prefixEnd_5013867 : Nat := 4983230072969 + 3 ^ 40 * 5013867 * 2
def baseEnd_5013867 : Nat := 2574523708716439956004151

theorem tailTrace_5013867 : CollatzResearch.WordTrace tailWord_5013867 prefixEnd_5013867 2574523708716439956004151 := by
  unfold tailWord_5013867
  simp only [CollatzResearch.WordTrace]
  refine ⟨182870752926623634155159855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121913835284415756103439903 182870752926623634155159855)
  ·
    refine ⟨274306129389935451232739783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182870752926623634155159855 274306129389935451232739783)
    ·
      refine ⟨411459194084903176849109675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274306129389935451232739783 411459194084903176849109675)
      ·
        refine ⟨617188791127354765273664513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411459194084903176849109675 617188791127354765273664513)
        ·
          refine ⟨462891593345516073955248385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 617188791127354765273664513 462891593345516073955248385)
          ·
            refine ⟨347168695009137055466436289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462891593345516073955248385 347168695009137055466436289)
            ·
              refine ⟨260376521256852791599827217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347168695009137055466436289 260376521256852791599827217)
              ·
                refine ⟨195282390942639593699870413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260376521256852791599827217 195282390942639593699870413)
                ·
                  refine ⟨73230896603489847637451405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195282390942639593699870413 73230896603489847637451405)
                  ·
                    refine ⟨27461586226308692864044277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73230896603489847637451405 27461586226308692864044277)
                    ·
                      refine ⟨2574523708716439956004151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27461586226308692864044277 2574523708716439956004151)
                      ·
                        rfl

theorem cell23_5013867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 5].length) (baseStart_5013867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013867 prefixEnd_5013867 := by exact prefixLift 5013867
  have htrace : WordTrace (prefixWord ++ tailWord_5013867) baseStart_5013867 baseEnd_5013867 := by
    simpa [prefixWord, tailWord_5013867, baseEnd_5013867] using wordTrace_append hprefix tailTrace_5013867
  have hstable : (prefixWord ++ tailWord_5013867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013867).length < 2 ^ (prefixWord ++ tailWord_5013867).sum := by decide
  have hdescent : baseEnd_5013867 < baseStart_5013867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013868 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 3, 3, 2]
def baseStart_5013868 : Nat := 118140960795 + 5013868 * 2 ^ 59
def prefixEnd_5013868 : Nat := 4983230072969 + 3 ^ 40 * 5013868 * 2
def baseEnd_5013868 : Nat := 2574524222197094452091647

theorem tailTrace_5013868 : CollatzResearch.WordTrace tailWord_5013868 prefixEnd_5013868 2574524222197094452091647 := by
  unfold tailWord_5013868
  simp only [CollatzResearch.WordTrace]
  refine ⟨91435394699810005662973129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121913859599746674217297505 91435394699810005662973129)
  ·
    refine ⟨68576546024857504247229847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91435394699810005662973129 68576546024857504247229847)
    ·
      refine ⟨102864819037286256370844771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68576546024857504247229847 102864819037286256370844771)
      ·
        refine ⟨154297228555929384556267157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102864819037286256370844771 154297228555929384556267157)
        ·
          refine ⟨7232682588559189901075023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 154297228555929384556267157 7232682588559189901075023)
          ·
            refine ⟨10849023882838784851612535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7232682588559189901075023 10849023882838784851612535)
            ·
              refine ⟨16273535824258177277418803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10849023882838784851612535 16273535824258177277418803)
              ·
                refine ⟨24410303736387265916128205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16273535824258177277418803 24410303736387265916128205)
                ·
                  refine ⟨9153863901145224718548077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24410303736387265916128205 9153863901145224718548077)
                  ·
                    refine ⟨3432698962929459269455529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9153863901145224718548077 3432698962929459269455529)
                    ·
                      refine ⟨2574524222197094452091647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3432698962929459269455529 2574524222197094452091647)
                      ·
                        rfl

theorem cell23_5013868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 3, 2].length) (baseStart_5013868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013868 prefixEnd_5013868 := by exact prefixLift 5013868
  have htrace : WordTrace (prefixWord ++ tailWord_5013868) baseStart_5013868 baseEnd_5013868 := by
    simpa [prefixWord, tailWord_5013868, baseEnd_5013868] using wordTrace_append hprefix tailTrace_5013868
  have hstable : (prefixWord ++ tailWord_5013868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013868).length < 2 ^ (prefixWord ++ tailWord_5013868).sum := by decide
  have hdescent : baseEnd_5013868 < baseStart_5013868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013885 : List Nat := [1, 4, 1, 1, 2, 4, 3, 1, 1, 3, 2]
def baseStart_5013885 : Nat := 118140960795 + 5013885 * 2 ^ 59
def prefixEnd_5013885 : Nat := 4983230072969 + 3 ^ 40 * 5013885 * 2
def baseEnd_5013885 : Nat := 2574532951368220885579069

theorem tailTrace_5013885 : CollatzResearch.WordTrace tailWord_5013885 prefixEnd_5013885 2574532951368220885579069 := by
  unfold tailWord_5013885
  simp only [CollatzResearch.WordTrace]
  refine ⟨182871409440558423229315109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121914272960372282152876739 182871409440558423229315109)
  ·
    refine ⟨34288389270104704355496583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182871409440558423229315109 34288389270104704355496583)
    ·
      refine ⟨51432583905157056533244875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34288389270104704355496583 51432583905157056533244875)
      ·
        refine ⟨77148875857735584799867313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51432583905157056533244875 77148875857735584799867313)
        ·
          refine ⟨57861656893301688599900485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77148875857735584799867313 57861656893301688599900485)
          ·
            refine ⟨10849060667494066612481341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57861656893301688599900485 10849060667494066612481341)
            ·
              refine ⟨4068397750310274979680503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10849060667494066612481341 4068397750310274979680503)
              ·
                refine ⟨6102596625465412469520755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4068397750310274979680503 6102596625465412469520755)
                ·
                  refine ⟨9153894938198118704281133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6102596625465412469520755 9153894938198118704281133)
                  ·
                    refine ⟨3432710601824294514105425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9153894938198118704281133 3432710601824294514105425)
                    ·
                      refine ⟨2574532951368220885579069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3432710601824294514105425 2574532951368220885579069)
                      ·
                        rfl

theorem cell23_5013885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_5013885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013885 prefixEnd_5013885 := by exact prefixLift 5013885
  have htrace : WordTrace (prefixWord ++ tailWord_5013885) baseStart_5013885 baseEnd_5013885 := by
    simpa [prefixWord, tailWord_5013885, baseEnd_5013885] using wordTrace_append hprefix tailTrace_5013885
  have hstable : (prefixWord ++ tailWord_5013885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013885).length < 2 ^ (prefixWord ++ tailWord_5013885).sum := by decide
  have hdescent : baseEnd_5013885 < baseStart_5013885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013887 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 9]
def baseStart_5013887 : Nat := 118140960795 + 5013887 * 2 ^ 59
def prefixEnd_5013887 : Nat := 4983230072969 + 3 ^ 40 * 5013887 * 2
def baseEnd_5013887 : Nat := 286059330925503319750451

theorem tailTrace_5013887 : CollatzResearch.WordTrace tailWord_5013887 prefixEnd_5013887 286059330925503319750451 := by
  unfold tailWord_5013887
  simp only [CollatzResearch.WordTrace]
  refine ⟨182871482386551177570887915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121914321591034118380591943 182871482386551177570887915)
  ·
    refine ⟨274307223579826766356331873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182871482386551177570887915 274307223579826766356331873)
    ·
      refine ⟨205730417684870074767248905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274307223579826766356331873 205730417684870074767248905)
      ·
        refine ⟨154297813263652556075436679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205730417684870074767248905 154297813263652556075436679)
        ·
          refine ⟨231446719895478834113155019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154297813263652556075436679 231446719895478834113155019)
          ·
            refine ⟨347170079843218251169732529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231446719895478834113155019 347170079843218251169732529)
            ·
              refine ⟨260377559882413688377299397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347170079843218251169732529 260377559882413688377299397)
              ·
                refine ⟨48820792477952566570743637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260377559882413688377299397 48820792477952566570743637)
                ·
                  refine ⟨286059330925503319750451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48820792477952566570743637 286059330925503319750451)
                  ·
                    rfl

theorem cell23_5013887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 9].length) (baseStart_5013887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013887 prefixEnd_5013887 := by exact prefixLift 5013887
  have htrace : WordTrace (prefixWord ++ tailWord_5013887) baseStart_5013887 baseEnd_5013887 := by
    simpa [prefixWord, tailWord_5013887, baseEnd_5013887] using wordTrace_append hprefix tailTrace_5013887
  have hstable : (prefixWord ++ tailWord_5013887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013887).length < 2 ^ (prefixWord ++ tailWord_5013887).sum := by decide
  have hdescent : baseEnd_5013887 < baseStart_5013887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013984 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 4]
def baseStart_5013984 : Nat := 118140960795 + 5013984 * 2 ^ 59
def prefixEnd_5013984 : Nat := 4983230072969 + 3 ^ 40 * 5013984 * 2
def baseEnd_5013984 : Nat := 2574583785953015998241113

theorem tailTrace_5013984 : CollatzResearch.WordTrace tailWord_5013984 prefixEnd_5013984 2574583785953015998241113 := by
  unfold tailWord_5013984
  simp only [CollatzResearch.WordTrace]
  refine ⟨91437510133599881568584503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121916680178133175424779337 91437510133599881568584503)
  ·
    refine ⟨137156265200399822352876755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91437510133599881568584503 137156265200399822352876755)
    ·
      refine ⟨205734397800599733529315133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137156265200399822352876755 205734397800599733529315133)
      ·
        refine ⟨77150399175224900073493175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205734397800599733529315133 77150399175224900073493175)
        ·
          refine ⟨115725598762837350110239763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77150399175224900073493175 115725598762837350110239763)
          ·
            refine ⟨173588398144256025165359645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115725598762837350110239763 173588398144256025165359645)
            ·
              refine ⟨65095649304096009437009867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173588398144256025165359645 65095649304096009437009867)
              ·
                refine ⟨97643473956144014155514801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65095649304096009437009867 97643473956144014155514801)
                ·
                  refine ⟨73232605467108010616636101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97643473956144014155514801 73232605467108010616636101)
                  ·
                    refine ⟨13731113525082751990619269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73232605467108010616636101 13731113525082751990619269)
                    ·
                      refine ⟨2574583785953015998241113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13731113525082751990619269 2574583785953015998241113)
                      ·
                        rfl

theorem cell23_5013984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_5013984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013984 prefixEnd_5013984 := by exact prefixLift 5013984
  have htrace : WordTrace (prefixWord ++ tailWord_5013984) baseStart_5013984 baseEnd_5013984 := by
    simpa [prefixWord, tailWord_5013984, baseEnd_5013984] using wordTrace_append hprefix tailTrace_5013984
  have hstable : (prefixWord ++ tailWord_5013984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013984).length < 2 ^ (prefixWord ++ tailWord_5013984).sum := by decide
  have hdescent : baseEnd_5013984 < baseStart_5013984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5013991 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_5013991 : Nat := 118140960795 + 5013991 * 2 ^ 59
def prefixEnd_5013991 : Nat := 4983230072969 + 3 ^ 40 * 5013991 * 2
def baseEnd_5013991 : Nat := 2574587380317597470853581

theorem tailTrace_5013991 : CollatzResearch.WordTrace tailWord_5013991 prefixEnd_5013991 2574587380317597470853581 := by
  unfold tailWord_5013991
  simp only [CollatzResearch.WordTrace]
  refine ⟨182875275578174403332673827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121916850385449602221782551 182875275578174403332673827)
  ·
    refine ⟨274312913367261604999010741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182875275578174403332673827 274312913367261604999010741)
    ·
      refine ⟨25716835628180775468657257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 274312913367261604999010741 25716835628180775468657257)
      ·
        refine ⟨19287626721135581601492943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25716835628180775468657257 19287626721135581601492943)
        ·
          refine ⟨28931440081703372402239415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19287626721135581601492943 28931440081703372402239415)
          ·
            refine ⟨43397160122555058603359123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28931440081703372402239415 43397160122555058603359123)
            ·
              refine ⟨65095740183832587905038685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43397160122555058603359123 65095740183832587905038685)
              ·
                refine ⟨24410902568937220464389507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65095740183832587905038685 24410902568937220464389507)
                ·
                  refine ⟨36616353853405830696584261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24410902568937220464389507 36616353853405830696584261)
                  ·
                    refine ⟨6865566347513593255609549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36616353853405830696584261 6865566347513593255609549)
                    ·
                      refine ⟨2574587380317597470853581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6865566347513593255609549 2574587380317597470853581)
                      ·
                        rfl

theorem cell23_5013991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_5013991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5013991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5013991 prefixEnd_5013991 := by exact prefixLift 5013991
  have htrace : WordTrace (prefixWord ++ tailWord_5013991) baseStart_5013991 baseEnd_5013991 := by
    simpa [prefixWord, tailWord_5013991, baseEnd_5013991] using wordTrace_append hprefix tailTrace_5013991
  have hstable : (prefixWord ++ tailWord_5013991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5013991).length < 2 ^ (prefixWord ++ tailWord_5013991).sum := by decide
  have hdescent : baseEnd_5013991 < baseStart_5013991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5013991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014005 : List Nat := [1, 3, 5, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_5014005 : Nat := 118140960795 + 5014005 * 2 ^ 59
def prefixEnd_5014005 : Nat := 4983230072969 + 3 ^ 40 * 5014005 * 2
def baseEnd_5014005 : Nat := 2574594569046760416078517

theorem tailTrace_5014005 : CollatzResearch.WordTrace tailWord_5014005 prefixEnd_5014005 2574594569046760416078517 := by
  unfold tailWord_5014005
  simp only [CollatzResearch.WordTrace]
  refine ⟨182875786200123683723683469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121917190800082455815788979 182875786200123683723683469)
  ·
    refine ⟨68578419825046381396381301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182875786200123683723683469 68578419825046381396381301)
    ·
      refine ⟨6429226858598098255910747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68578419825046381396381301 6429226858598098255910747)
      ·
        refine ⟨9643840287897147383866121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6429226858598098255910747 9643840287897147383866121)
        ·
          refine ⟨7232880215922860537899591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9643840287897147383866121 7232880215922860537899591)
          ·
            refine ⟨10849320323884290806849387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7232880215922860537899591 10849320323884290806849387)
            ·
              refine ⟨16273980485826436210274081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10849320323884290806849387 16273980485826436210274081)
              ·
                refine ⟨12205485364369827157705561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16273980485826436210274081 12205485364369827157705561)
                ·
                  refine ⟨9154114023277370368279171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12205485364369827157705561 9154114023277370368279171)
                  ·
                    refine ⟨13731171034916055552418757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9154114023277370368279171 13731171034916055552418757)
                    ·
                      refine ⟨2574594569046760416078517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13731171034916055552418757 2574594569046760416078517)
                      ·
                        rfl

theorem cell23_5014005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_5014005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014005 prefixEnd_5014005 := by exact prefixLift 5014005
  have htrace : WordTrace (prefixWord ++ tailWord_5014005) baseStart_5014005 baseEnd_5014005 := by
    simpa [prefixWord, tailWord_5014005, baseEnd_5014005] using wordTrace_append hprefix tailTrace_5014005
  have hstable : (prefixWord ++ tailWord_5014005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014005).length < 2 ^ (prefixWord ++ tailWord_5014005).sum := by decide
  have hdescent : baseEnd_5014005 < baseStart_5014005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014015 : List Nat := [1, 1, 2, 2, 1, 2, 7, 2, 1, 4]
def baseStart_5014015 : Nat := 118140960795 + 5014015 * 2 ^ 59
def prefixEnd_5014015 : Nat := 4983230072969 + 3 ^ 40 * 5014015 * 2
def baseEnd_5014015 : Nat := 858199901284435125651157

theorem tailTrace_5014015 : CollatzResearch.WordTrace tailWord_5014015 prefixEnd_5014015 858199901284435125651157 := by
  unfold tailWord_5014015
  simp only [CollatzResearch.WordTrace]
  refine ⟨182876150930087455431547499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121917433953391636954364999 182876150930087455431547499)
  ·
    refine ⟨274314226395131183147321249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182876150930087455431547499 274314226395131183147321249)
    ·
      refine ⟨205735669796348387360490937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274314226395131183147321249 205735669796348387360490937)
      ·
        refine ⟨154301752347261290520368203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205735669796348387360490937 154301752347261290520368203)
        ·
          refine ⟨231452628520891935780552305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154301752347261290520368203 231452628520891935780552305)
          ·
            refine ⟨173589471390668951835414229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231452628520891935780552305 173589471390668951835414229)
            ·
              refine ⟨4068503235718803558642521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 173589471390668951835414229 4068503235718803558642521)
              ·
                refine ⟨3051377426789102668981891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4068503235718803558642521 3051377426789102668981891)
                ·
                  refine ⟨4577066140183654003472837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3051377426789102668981891 4577066140183654003472837)
                  ·
                    refine ⟨858199901284435125651157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4577066140183654003472837 858199901284435125651157)
                    ·
                      rfl

theorem cell23_5014015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 1, 4].length) (baseStart_5014015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014015 prefixEnd_5014015 := by exact prefixLift 5014015
  have htrace : WordTrace (prefixWord ++ tailWord_5014015) baseStart_5014015 baseEnd_5014015 := by
    simpa [prefixWord, tailWord_5014015, baseEnd_5014015] using wordTrace_append hprefix tailTrace_5014015
  have hstable : (prefixWord ++ tailWord_5014015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014015).length < 2 ^ (prefixWord ++ tailWord_5014015).sum := by decide
  have hdescent : baseEnd_5014015 < baseStart_5014015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014024 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 2, 9]
def baseStart_5014024 : Nat := 118140960795 + 5014024 * 2 ^ 59
def prefixEnd_5014024 : Nat := 4983230072969 + 3 ^ 40 * 5014024 * 2
def baseEnd_5014024 : Nat := 858201441726398613913643

theorem tailTrace_5014024 : CollatzResearch.WordTrace tailWord_5014024 prefixEnd_5014024 858201441726398613913643 := by
  unfold tailWord_5014024
  simp only [CollatzResearch.WordTrace]
  refine ⟨91438239593527424984312563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121917652791369899979083417 91438239593527424984312563)
  ·
    refine ⟨137157359390291137476468845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91438239593527424984312563 137157359390291137476468845)
    ·
      refine ⟨51434009771359176553675817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137157359390291137476468845 51434009771359176553675817)
      ·
        refine ⟨38575507328519382415256863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51434009771359176553675817 38575507328519382415256863)
        ·
          refine ⟨57863260992779073622885295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38575507328519382415256863 57863260992779073622885295)
          ·
            refine ⟨86794891489168610434327943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57863260992779073622885295 86794891489168610434327943)
            ·
              refine ⟨130192337233752915651491915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86794891489168610434327943 130192337233752915651491915)
              ·
                refine ⟨195288505850629373477237873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130192337233752915651491915 195288505850629373477237873)
                ·
                  refine ⟨146466379387972030107928405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195288505850629373477237873 146466379387972030107928405)
                  ·
                    refine ⟨858201441726398613913643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 146466379387972030107928405 858201441726398613913643)
                    ·
                      rfl

theorem cell23_5014024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_5014024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014024 prefixEnd_5014024 := by exact prefixLift 5014024
  have htrace : WordTrace (prefixWord ++ tailWord_5014024) baseStart_5014024 baseEnd_5014024 := by
    simpa [prefixWord, tailWord_5014024, baseEnd_5014024] using wordTrace_append hprefix tailTrace_5014024
  have hstable : (prefixWord ++ tailWord_5014024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014024).length < 2 ^ (prefixWord ++ tailWord_5014024).sum := by decide
  have hdescent : baseEnd_5014024 < baseStart_5014024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014028 : List Nat := [2, 2, 1, 2, 4, 1, 4, 1, 6]
def baseStart_5014028 : Nat := 118140960795 + 5014028 * 2 ^ 59
def prefixEnd_5014028 : Nat := 4983230072969 + 3 ^ 40 * 5014028 * 2
def baseEnd_5014028 : Nat := 286067375455757091787879

theorem tailTrace_5014028 : CollatzResearch.WordTrace tailWord_5014028 prefixEnd_5014028 286067375455757091787879 := by
  unfold tailWord_5014028
  simp only [CollatzResearch.WordTrace]
  refine ⟨91438312539520179325885369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121917750052693572434513825 91438312539520179325885369)
  ·
    refine ⟨68578734404640134494414027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91438312539520179325885369 68578734404640134494414027)
    ·
      refine ⟨102868101606960201741621041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68578734404640134494414027 102868101606960201741621041)
      ·
        refine ⟨77151076205220151306215781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102868101606960201741621041 77151076205220151306215781)
        ·
          refine ⟨14465826788478778369915459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77151076205220151306215781 14465826788478778369915459)
          ·
            refine ⟨21698740182718167554873189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14465826788478778369915459 21698740182718167554873189)
            ·
              refine ⟨4068513784259656416538723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21698740182718167554873189 4068513784259656416538723)
              ·
                refine ⟨6102770676389484624808085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4068513784259656416538723 6102770676389484624808085)
                ·
                  refine ⟨286067375455757091787879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6102770676389484624808085 286067375455757091787879)
                  ·
                    rfl

theorem cell23_5014028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 6].length) (baseStart_5014028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014028 prefixEnd_5014028 := by exact prefixLift 5014028
  have htrace : WordTrace (prefixWord ++ tailWord_5014028) baseStart_5014028 baseEnd_5014028 := by
    simpa [prefixWord, tailWord_5014028, baseEnd_5014028] using wordTrace_append hprefix tailTrace_5014028
  have hstable : (prefixWord ++ tailWord_5014028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014028).length < 2 ^ (prefixWord ++ tailWord_5014028).sum := by decide
  have hdescent : baseEnd_5014028 < baseStart_5014028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014091 : List Nat := [1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 4]
def baseStart_5014091 : Nat := 118140960795 + 5014091 * 2 ^ 59
def prefixEnd_5014091 : Nat := 4983230072969 + 3 ^ 40 * 5014091 * 2
def baseEnd_5014091 : Nat := 2574638728383047079603121

theorem tailTrace_5014091 : CollatzResearch.WordTrace tailWord_5014091 prefixEnd_5014091 2574638728383047079603121 := by
  unfold tailWord_5014091
  simp only [CollatzResearch.WordTrace]
  refine ⟨182878922877812120411314127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121919281918541413607542751 182878922877812120411314127)
  ·
    refine ⟨274318384316718180616971191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182878922877812120411314127 274318384316718180616971191)
    ·
      refine ⟨411477576475077270925456787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274318384316718180616971191 411477576475077270925456787)
      ·
        refine ⟨617216364712615906388185181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411477576475077270925456787 617216364712615906388185181)
        ·
          refine ⟨231456136767230964895569443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 617216364712615906388185181 231456136767230964895569443)
          ·
            refine ⟨347184205150846447343354165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231456136767230964895569443 347184205150846447343354165)
            ·
              refine ⟨32548519232891854438439453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 347184205150846447343354165 32548519232891854438439453)
              ·
                refine ⟨12205694712334445414414795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32548519232891854438439453 12205694712334445414414795)
                ·
                  refine ⟨18308542068501668121622193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12205694712334445414414795 18308542068501668121622193)
                  ·
                    refine ⟨13731406551376251091216645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18308542068501668121622193 13731406551376251091216645)
                    ·
                      refine ⟨2574638728383047079603121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13731406551376251091216645 2574638728383047079603121)
                      ·
                        rfl

theorem cell23_5014091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 4].length) (baseStart_5014091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014091 prefixEnd_5014091 := by exact prefixLift 5014091
  have htrace : WordTrace (prefixWord ++ tailWord_5014091) baseStart_5014091 baseEnd_5014091 := by
    simpa [prefixWord, tailWord_5014091, baseEnd_5014091] using wordTrace_append hprefix tailTrace_5014091
  have hstable : (prefixWord ++ tailWord_5014091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014091).length < 2 ^ (prefixWord ++ tailWord_5014091).sum := by decide
  have hdescent : baseEnd_5014091 < baseStart_5014091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014098 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_5014098 : Nat := 118140960795 + 5014098 * 2 ^ 59
def prefixEnd_5014098 : Nat := 4983230072969 + 3 ^ 40 * 5014098 * 2
def baseEnd_5014098 : Nat := 2574642322747628552215589

theorem tailTrace_5014098 : CollatzResearch.WordTrace tailWord_5014098 prefixEnd_5014098 2574642322747628552215589 := by
  unfold tailWord_5014098
  simp only [CollatzResearch.WordTrace]
  refine ⟨45719794547196690151704737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121919452125857840404545965 45719794547196690151704737)
  ·
    refine ⟨34289845910397517613778553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45719794547196690151704737 34289845910397517613778553)
    ·
      refine ⟨25717384432798138210333915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34289845910397517613778553 25717384432798138210333915)
      ·
        refine ⟨38576076649197207315500873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25717384432798138210333915 38576076649197207315500873)
        ·
          refine ⟨28932057486897905486625655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38576076649197207315500873 28932057486897905486625655)
          ·
            refine ⟨43398086230346858229938483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28932057486897905486625655 43398086230346858229938483)
            ·
              refine ⟨65097129345520287344907725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43398086230346858229938483 65097129345520287344907725)
              ·
                refine ⟨24411423504570107754340397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65097129345520287344907725 24411423504570107754340397)
                ·
                  refine ⟨9154283814213790407877649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24411423504570107754340397 9154283814213790407877649)
                  ·
                    refine ⟨6865712860660342805908237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9154283814213790407877649 6865712860660342805908237)
                    ·
                      refine ⟨2574642322747628552215589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6865712860660342805908237 2574642322747628552215589)
                      ·
                        rfl

theorem cell23_5014098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_5014098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014098 prefixEnd_5014098 := by exact prefixLift 5014098
  have htrace : WordTrace (prefixWord ++ tailWord_5014098) baseStart_5014098 baseEnd_5014098 := by
    simpa [prefixWord, tailWord_5014098, baseEnd_5014098] using wordTrace_append hprefix tailTrace_5014098
  have hstable : (prefixWord ++ tailWord_5014098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014098).length < 2 ^ (prefixWord ++ tailWord_5014098).sum := by decide
  have hdescent : baseEnd_5014098 < baseStart_5014098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014112 : List Nat := [2, 1, 1, 3, 2, 1, 3, 5, 1, 2, 2]
def baseStart_5014112 : Nat := 118140960795 + 5014112 * 2 ^ 59
def prefixEnd_5014112 : Nat := 4983230072969 + 3 ^ 40 * 5014112 * 2
def baseEnd_5014112 : Nat := 2574649511476791497440525

theorem tailTrace_5014112 : CollatzResearch.WordTrace tailWord_5014112 prefixEnd_5014112 2574649511476791497440525 := by
  unfold tailWord_5014112
  simp only [CollatzResearch.WordTrace]
  refine ⟨91439844405368020498914295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121919792540490693998552393 91439844405368020498914295)
  ·
    refine ⟨137159766608052030748371443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91439844405368020498914295 137159766608052030748371443)
    ·
      refine ⟨205739649912078046122557165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137159766608052030748371443 205739649912078046122557165)
      ·
        refine ⟨77152368717029267295958937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205739649912078046122557165 77152368717029267295958937)
        ·
          refine ⟨57864276537771950471969203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77152368717029267295958937 57864276537771950471969203)
          ·
            refine ⟨86796414806657925707953805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57864276537771950471969203 86796414806657925707953805)
            ·
              refine ⟨32548655552496722140482677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86796414806657925707953805 32548655552496722140482677)
              ·
                refine ⟨3051436458046567700670251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32548655552496722140482677 3051436458046567700670251)
                ·
                  refine ⟨4577154687069851551005377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3051436458046567700670251 4577154687069851551005377)
                  ·
                    refine ⟨3432866015302388663254033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4577154687069851551005377 3432866015302388663254033)
                    ·
                      refine ⟨2574649511476791497440525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3432866015302388663254033 2574649511476791497440525)
                      ·
                        rfl

theorem cell23_5014112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_5014112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014112 prefixEnd_5014112 := by exact prefixLift 5014112
  have htrace : WordTrace (prefixWord ++ tailWord_5014112) baseStart_5014112 baseEnd_5014112 := by
    simpa [prefixWord, tailWord_5014112, baseEnd_5014112] using wordTrace_append hprefix tailTrace_5014112
  have hstable : (prefixWord ++ tailWord_5014112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014112).length < 2 ^ (prefixWord ++ tailWord_5014112).sum := by decide
  have hdescent : baseEnd_5014112 < baseStart_5014112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014146 : List Nat := [3, 4, 3, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_5014146 : Nat := 118140960795 + 5014146 * 2 ^ 59
def prefixEnd_5014146 : Nat := 4983230072969 + 3 ^ 40 * 5014146 * 2
def baseEnd_5014146 : Nat := 2574666969819044364415369

theorem tailTrace_5014146 : CollatzResearch.WordTrace tailWord_5014146 prefixEnd_5014146 2574666969819044364415369 := by
  unfold tailWord_5014146
  simp only [CollatzResearch.WordTrace]
  refine ⟨45720232223153216201141573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121920619261741909869710861 45720232223153216201141573)
  ·
    refine ⟨8572543541841228037714045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45720232223153216201141573 8572543541841228037714045)
    ·
      refine ⟨3214703828190460514142767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8572543541841228037714045 3214703828190460514142767)
      ·
        refine ⟨4822055742285690771214151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3214703828190460514142767 4822055742285690771214151)
        ·
          refine ⟨7233083613428536156821227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4822055742285690771214151 7233083613428536156821227)
          ·
            refine ⟨10849625420142804235231841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7233083613428536156821227 10849625420142804235231841)
            ·
              refine ⟨8137219065107103176423881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10849625420142804235231841 8137219065107103176423881)
              ·
                refine ⟨6102914298830327382317911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8137219065107103176423881 6102914298830327382317911)
                ·
                  refine ⟨9154371448245491073476867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6102914298830327382317911 9154371448245491073476867)
                  ·
                    refine ⟨13731557172368236610215301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9154371448245491073476867 13731557172368236610215301)
                    ·
                      refine ⟨2574666969819044364415369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13731557172368236610215301 2574666969819044364415369)
                      ·
                        rfl

theorem cell23_5014146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_5014146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014146 prefixEnd_5014146 := by exact prefixLift 5014146
  have htrace : WordTrace (prefixWord ++ tailWord_5014146) baseStart_5014146 baseEnd_5014146 := by
    simpa [prefixWord, tailWord_5014146, baseEnd_5014146] using wordTrace_append hprefix tailTrace_5014146
  have hstable : (prefixWord ++ tailWord_5014146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014146).length < 2 ^ (prefixWord ++ tailWord_5014146).sum := by decide
  have hdescent : baseEnd_5014146 < baseStart_5014146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014172 : List Nat := [2, 2, 3, 2, 2, 1, 2, 3, 1, 3, 2]
def baseStart_5014172 : Nat := 118140960795 + 5014172 * 2 ^ 59
def prefixEnd_5014172 : Nat := 4983230072969 + 3 ^ 40 * 5014172 * 2
def baseEnd_5014172 : Nat := 2574680320316061262690249

theorem tailTrace_5014172 : CollatzResearch.WordTrace tailWord_5014172 prefixEnd_5014172 2574680320316061262690249 := by
  unfold tailWord_5014172
  simp only [CollatzResearch.WordTrace]
  refine ⟨91440938595259335622506385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121921251460345780830008513 91440938595259335622506385)
  ·
    refine ⟨68580703946444501716879789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91440938595259335622506385 68580703946444501716879789)
    ·
      refine ⟨25717763979916688143829921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68580703946444501716879789 25717763979916688143829921)
      ·
        refine ⟨19288322984937516107872441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25717763979916688143829921 19288322984937516107872441)
        ·
          refine ⟨14466242238703137080904331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19288322984937516107872441 14466242238703137080904331)
          ·
            refine ⟨21699363358054705621356497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14466242238703137080904331 21699363358054705621356497)
            ·
              refine ⟨16274522518541029216017373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21699363358054705621356497 16274522518541029216017373)
              ·
                refine ⟨6102945944452885956006515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16274522518541029216017373 6102945944452885956006515)
                ·
                  refine ⟨9154418916679328934009773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6102945944452885956006515 9154418916679328934009773)
                  ·
                    refine ⟨3432907093754748350253665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9154418916679328934009773 3432907093754748350253665)
                    ·
                      refine ⟨2574680320316061262690249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3432907093754748350253665 2574680320316061262690249)
                      ·
                        rfl

theorem cell23_5014172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_5014172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014172 prefixEnd_5014172 := by exact prefixLift 5014172
  have htrace : WordTrace (prefixWord ++ tailWord_5014172) baseStart_5014172 baseEnd_5014172 := by
    simpa [prefixWord, tailWord_5014172, baseEnd_5014172] using wordTrace_append hprefix tailTrace_5014172
  have hstable : (prefixWord ++ tailWord_5014172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014172).length < 2 ^ (prefixWord ++ tailWord_5014172).sum := by decide
  have hdescent : baseEnd_5014172 < baseStart_5014172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014202 : List Nat := [3, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2]
def baseStart_5014202 : Nat := 118140960795 + 5014202 * 2 ^ 59
def prefixEnd_5014202 : Nat := 4983230072969 + 3 ^ 40 * 5014202 * 2
def baseEnd_5014202 : Nat := 2574695724735696145315111

theorem tailTrace_5014202 : CollatzResearch.WordTrace tailWord_5014202 prefixEnd_5014202 2574695724735696145315111 := by
  unfold tailWord_5014202
  simp only [CollatzResearch.WordTrace]
  refine ⟨45720742845102496592151215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121921980920273324245736573 45720742845102496592151215)
  ·
    refine ⟨68581114267653744888226823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45720742845102496592151215 68581114267653744888226823)
    ·
      refine ⟨102871671401480617332340235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68581114267653744888226823 102871671401480617332340235)
      ·
        refine ⟨154307507102220925998510353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102871671401480617332340235 154307507102220925998510353)
        ·
          refine ⟨115730630326665694498882765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154307507102220925998510353 115730630326665694498882765)
          ·
            refine ⟨43398986372499635437081037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115730630326665694498882765 43398986372499635437081037)
            ·
              refine ⟨16274619889687363288905389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43398986372499635437081037 16274619889687363288905389)
              ·
                refine ⟨6102982458632761233339521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16274619889687363288905389 6102982458632761233339521)
                ·
                  refine ⟨4577236843974570925004641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6102982458632761233339521 4577236843974570925004641)
                  ·
                    refine ⟨3432927632980928193753481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4577236843974570925004641 3432927632980928193753481)
                    ·
                      refine ⟨2574695724735696145315111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3432927632980928193753481 2574695724735696145315111)
                      ·
                        rfl

theorem cell23_5014202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2].length) (baseStart_5014202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014202 prefixEnd_5014202 := by exact prefixLift 5014202
  have htrace : WordTrace (prefixWord ++ tailWord_5014202) baseStart_5014202 baseEnd_5014202 := by
    simpa [prefixWord, tailWord_5014202, baseEnd_5014202] using wordTrace_append hprefix tailTrace_5014202
  have hstable : (prefixWord ++ tailWord_5014202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014202).length < 2 ^ (prefixWord ++ tailWord_5014202).sum := by decide
  have hdescent : baseEnd_5014202 < baseStart_5014202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014236 : List Nat := [2, 2, 5, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_5014236 : Nat := 118140960795 + 5014236 * 2 ^ 59
def prefixEnd_5014236 : Nat := 4983230072969 + 3 ^ 40 * 5014236 * 2
def baseEnd_5014236 : Nat := 2574713183077949012289955

theorem tailTrace_5014236 : CollatzResearch.WordTrace tailWord_5014236 prefixEnd_5014236 2574713183077949012289955 := by
  unfold tailWord_5014236
  simp only [CollatzResearch.WordTrace]
  refine ⟨91442105731143405087671281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121922807641524540116895041 91442105731143405087671281)
  ·
    refine ⟨68581579298357553815753461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91442105731143405087671281 68581579298357553815753461)
    ·
      refine ⟨6429523059221020670226887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68581579298357553815753461 6429523059221020670226887)
      ·
        refine ⟨9644284588831531005340331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6429523059221020670226887 9644284588831531005340331)
        ·
          refine ⟨14466426883247296508010497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9644284588831531005340331 14466426883247296508010497)
          ·
            refine ⟨10849820162435472381007873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14466426883247296508010497 10849820162435472381007873)
            ·
              refine ⟨8137365121826604285755905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10849820162435472381007873 8137365121826604285755905)
              ·
                refine ⟨6103023841369953214316929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8137365121826604285755905 6103023841369953214316929)
                ·
                  refine ⟨4577267881027464910737697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6103023841369953214316929 4577267881027464910737697)
                  ·
                    refine ⟨3432950910770598683053273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4577267881027464910737697 3432950910770598683053273)
                    ·
                      refine ⟨2574713183077949012289955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3432950910770598683053273 2574713183077949012289955)
                      ·
                        rfl

theorem cell23_5014236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_5014236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014236 prefixEnd_5014236 := by exact prefixLift 5014236
  have htrace : WordTrace (prefixWord ++ tailWord_5014236) baseStart_5014236 baseEnd_5014236 := by
    simpa [prefixWord, tailWord_5014236, baseEnd_5014236] using wordTrace_append hprefix tailTrace_5014236
  have hstable : (prefixWord ++ tailWord_5014236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014236).length < 2 ^ (prefixWord ++ tailWord_5014236).sum := by decide
  have hdescent : baseEnd_5014236 < baseStart_5014236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014245 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 2, 5, 2]
def baseStart_5014245 : Nat := 118140960795 + 5014245 * 2 ^ 59
def prefixEnd_5014245 : Nat := 4983230072969 + 3 ^ 40 * 5014245 * 2
def baseEnd_5014245 : Nat := 2574717804403839477077413

theorem tailTrace_5014245 : CollatzResearch.WordTrace tailWord_5014245 prefixEnd_5014245 2574717804403839477077413 := by
  unfold tailWord_5014245
  simp only [CollatzResearch.WordTrace]
  refine ⟨182884539719254204712420189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121923026479502803141613459 182884539719254204712420189)
  ·
    refine ⟨68581702394720326767157571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182884539719254204712420189 68581702394720326767157571)
    ·
      refine ⟨102872553592080490150736357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68581702394720326767157571 102872553592080490150736357)
      ·
        refine ⟨19288603798515091903263067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102872553592080490150736357 19288603798515091903263067)
        ·
          refine ⟨28932905697772637854894601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19288603798515091903263067 28932905697772637854894601)
          ·
            refine ⟨21699679273329478391170951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28932905697772637854894601 21699679273329478391170951)
            ·
              refine ⟨32549518909994217586756427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21699679273329478391170951 32549518909994217586756427)
              ·
                refine ⟨48824278364991326380134641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32549518909994217586756427 48824278364991326380134641)
                ·
                  refine ⟨36618208773743494785100981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48824278364991326380134641 36618208773743494785100981)
                  ·
                    refine ⟨3432957072538452636103217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36618208773743494785100981 3432957072538452636103217)
                    ·
                      refine ⟨2574717804403839477077413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3432957072538452636103217 2574717804403839477077413)
                      ·
                        rfl

theorem cell23_5014245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_5014245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014245 prefixEnd_5014245 := by exact prefixLift 5014245
  have htrace : WordTrace (prefixWord ++ tailWord_5014245) baseStart_5014245 baseEnd_5014245 := by
    simpa [prefixWord, tailWord_5014245, baseEnd_5014245] using wordTrace_append hprefix tailTrace_5014245
  have hstable : (prefixWord ++ tailWord_5014245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014245).length < 2 ^ (prefixWord ++ tailWord_5014245).sum := by decide
  have hdescent : baseEnd_5014245 < baseStart_5014245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014251 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 2, 8]
def baseStart_5014251 : Nat := 118140960795 + 5014251 * 2 ^ 59
def prefixEnd_5014251 : Nat := 4983230072969 + 3 ^ 40 * 5014251 * 2
def baseEnd_5014251 : Nat := 858240295095922151200795

theorem tailTrace_5014251 : CollatzResearch.WordTrace tailWord_5014251 prefixEnd_5014251 858240295095922151200795 := by
  unfold tailWord_5014251
  simp only [CollatzResearch.WordTrace]
  refine ⟨182884758557232467737138607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121923172371488311824759071 182884758557232467737138607)
  ·
    refine ⟨274327137835848701605707911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182884758557232467737138607 274327137835848701605707911)
    ·
      refine ⟨411490706753773052408561867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274327137835848701605707911 411490706753773052408561867)
      ·
        refine ⟨617236060130659578612842801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411490706753773052408561867 617236060130659578612842801)
        ·
          refine ⟨462927045097994683959632101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 617236060130659578612842801 462927045097994683959632101)
          ·
            refine ⟨86798820955874003242431019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 462927045097994683959632101 86798820955874003242431019)
            ·
              refine ⟨130198231433811004863646529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86798820955874003242431019 130198231433811004863646529)
              ·
                refine ⟨97648673575358253647734897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130198231433811004863646529 97648673575358253647734897)
                ·
                  refine ⟨73236505181518690235801173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97648673575358253647734897 73236505181518690235801173)
                  ·
                    refine ⟨858240295095922151200795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73236505181518690235801173 858240295095922151200795)
                    ·
                      rfl

theorem cell23_5014251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 8].length) (baseStart_5014251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014251 prefixEnd_5014251 := by exact prefixLift 5014251
  have htrace : WordTrace (prefixWord ++ tailWord_5014251) baseStart_5014251 baseEnd_5014251 := by
    simpa [prefixWord, tailWord_5014251, baseEnd_5014251] using wordTrace_append hprefix tailTrace_5014251
  have hstable : (prefixWord ++ tailWord_5014251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014251).length < 2 ^ (prefixWord ++ tailWord_5014251).sum := by decide
  have hdescent : baseEnd_5014251 < baseStart_5014251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014298 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 8]
def baseStart_5014298 : Nat := 118140960795 + 5014298 * 2 ^ 59
def prefixEnd_5014298 : Nat := 4983230072969 + 3 ^ 40 * 5014298 * 2
def baseEnd_5014298 : Nat := 286082779875391974412741

theorem tailTrace_5014298 : CollatzResearch.WordTrace tailWord_5014298 prefixEnd_5014298 286082779875391974412741 := by
  unfold tailWord_5014298
  simp only [CollatzResearch.WordTrace]
  refine ⟨45721618197015548691024887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121924315192041463176066365 45721618197015548691024887)
  ·
    refine ⟨68582427295523323036537331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45721618197015548691024887 68582427295523323036537331)
    ·
      refine ⟨102873640943284984554805997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68582427295523323036537331 102873640943284984554805997)
      ·
        refine ⟨38577615353731869208052249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102873640943284984554805997 38577615353731869208052249)
        ·
          refine ⟨28933211515298901906039187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38577615353731869208052249 28933211515298901906039187)
          ·
            refine ⟨43399817272948352859058781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28933211515298901906039187 43399817272948352859058781)
            ·
              refine ⟨16274931477355632322147043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43399817272948352859058781 16274931477355632322147043)
              ·
                refine ⟨24412397216033448483220565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16274931477355632322147043 24412397216033448483220565)
                ·
                  refine ⟨286082779875391974412741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24412397216033448483220565 286082779875391974412741)
                  ·
                    rfl

theorem cell23_5014298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 8].length) (baseStart_5014298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014298 prefixEnd_5014298 := by exact prefixLift 5014298
  have htrace : WordTrace (prefixWord ++ tailWord_5014298) baseStart_5014298 baseEnd_5014298 := by
    simpa [prefixWord, tailWord_5014298, baseEnd_5014298] using wordTrace_append hprefix tailTrace_5014298
  have hstable : (prefixWord ++ tailWord_5014298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014298).length < 2 ^ (prefixWord ++ tailWord_5014298).sum := by decide
  have hdescent : baseEnd_5014298 < baseStart_5014298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014345 : List Nat := [1, 2, 1, 1, 2, 5, 2, 3, 1, 5]
def baseStart_5014345 : Nat := 118140960795 + 5014345 * 2 ^ 59
def prefixEnd_5014345 : Nat := 4983230072969 + 3 ^ 40 * 5014345 * 2
def baseEnd_5014345 : Nat := 858256384156429695275651

theorem tailTrace_5014345 : CollatzResearch.WordTrace tailWord_5014345 prefixEnd_5014345 858256384156429695275651 := by
  unfold tailWord_5014345
  simp only [CollatzResearch.WordTrace]
  refine ⟨182888187018891921791060489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121925458012594614527373659 182888187018891921791060489)
  ·
    refine ⟨137166140264168941343295367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182888187018891921791060489 137166140264168941343295367)
    ·
      refine ⟨205749210396253412014943051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137166140264168941343295367 205749210396253412014943051)
      ·
        refine ⟨308623815594380118022414577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205749210396253412014943051 308623815594380118022414577)
        ·
          refine ⟨231467861695785088516810933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308623815594380118022414577 231467861695785088516810933)
          ·
            refine ⟨21700112033979852048451025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 231467861695785088516810933 21700112033979852048451025)
            ·
              refine ⟨16275084025484889036338269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21700112033979852048451025 16275084025484889036338269)
              ·
                refine ⟨6103156509556833388626851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16275084025484889036338269 6103156509556833388626851)
                ·
                  refine ⟨9154734764335250082940277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6103156509556833388626851 9154734764335250082940277)
                  ·
                    refine ⟨858256384156429695275651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9154734764335250082940277 858256384156429695275651)
                    ·
                      rfl

theorem cell23_5014345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 5].length) (baseStart_5014345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014345 prefixEnd_5014345 := by exact prefixLift 5014345
  have htrace : WordTrace (prefixWord ++ tailWord_5014345) baseStart_5014345 baseEnd_5014345 := by
    simpa [prefixWord, tailWord_5014345, baseEnd_5014345] using wordTrace_append hprefix tailTrace_5014345
  have hstable : (prefixWord ++ tailWord_5014345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014345).length < 2 ^ (prefixWord ++ tailWord_5014345).sum := by decide
  have hdescent : baseEnd_5014345 < baseStart_5014345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014359 : List Nat := [1, 1, 3, 2, 4, 3, 1, 1, 3, 1, 3]
def baseStart_5014359 : Nat := 118140960795 + 5014359 * 2 ^ 59
def prefixEnd_5014359 : Nat := 4983230072969 + 3 ^ 40 * 5014359 * 2
def baseEnd_5014359 : Nat := 2574776341198452031051889

theorem tailTrace_5014359 : CollatzResearch.WordTrace tailWord_5014359 prefixEnd_5014359 2574776341198452031051889 := by
  unfold tailWord_5014359
  simp only [CollatzResearch.WordTrace]
  refine ⟨182888697640841202182070131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121925798427227468121380087 182888697640841202182070131)
  ·
    refine ⟨274333046461261803273105197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182888697640841202182070131 274333046461261803273105197)
    ·
      refine ⟨102874892422973176227414449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274333046461261803273105197 102874892422973176227414449)
      ·
        refine ⟨77156169317229882170560837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102874892422973176227414449 77156169317229882170560837)
        ·
          refine ⟨14466781746980602906980157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77156169317229882170560837 14466781746980602906980157)
          ·
            refine ⟨5425043155117726090117559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14466781746980602906980157 5425043155117726090117559)
            ·
              refine ⟨8137564732676589135176339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5425043155117726090117559 8137564732676589135176339)
              ·
                refine ⟨12206347099014883702764509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8137564732676589135176339 12206347099014883702764509)
                ·
                  refine ⟨4577380162130581388536691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12206347099014883702764509 4577380162130581388536691)
                  ·
                    refine ⟨6866070243195872082805037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4577380162130581388536691 6866070243195872082805037)
                    ·
                      refine ⟨2574776341198452031051889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6866070243195872082805037 2574776341198452031051889)
                      ·
                        rfl

theorem cell23_5014359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_5014359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014359 prefixEnd_5014359 := by exact prefixLift 5014359
  have htrace : WordTrace (prefixWord ++ tailWord_5014359) baseStart_5014359 baseEnd_5014359 := by
    simpa [prefixWord, tailWord_5014359, baseEnd_5014359] using wordTrace_append hprefix tailTrace_5014359
  have hstable : (prefixWord ++ tailWord_5014359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014359).length < 2 ^ (prefixWord ++ tailWord_5014359).sum := by decide
  have hdescent : baseEnd_5014359 < baseStart_5014359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014482 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 2, 6]
def baseStart_5014482 : Nat := 118140960795 + 5014482 * 2 ^ 59
def prefixEnd_5014482 : Nat := 4983230072969 + 3 ^ 40 * 5014482 * 2
def baseEnd_5014482 : Nat := 858279833106318349937941

theorem tailTrace_5014482 : CollatzResearch.WordTrace tailWord_5014482 prefixEnd_5014482 858279833106318349937941 := by
  unfold tailWord_5014482
  simp only [CollatzResearch.WordTrace]
  refine ⟨45723295954848898547199425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121928789212930396125865133 45723295954848898547199425)
  ·
    refine ⟨34292471966136673910399569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45723295954848898547199425 34292471966136673910399569)
    ·
      refine ⟨25719353974602505432799677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34292471966136673910399569 25719353974602505432799677)
      ·
        refine ⟨9644757740475939537299879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25719353974602505432799677 9644757740475939537299879)
        ·
          refine ⟨14467136610713909305949819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9644757740475939537299879 14467136610713909305949819)
          ·
            refine ⟨21700704916070863958924729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14467136610713909305949819 21700704916070863958924729)
            ·
              refine ⟨16275528687053147969193547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21700704916070863958924729 16275528687053147969193547)
              ·
                refine ⟨24413293030579721953790321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16275528687053147969193547 24413293030579721953790321)
                ·
                  refine ⟨18309969772934791465342741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24413293030579721953790321 18309969772934791465342741)
                  ·
                    refine ⟨858279833106318349937941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18309969772934791465342741 858279833106318349937941)
                    ·
                      rfl

theorem cell23_5014482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_5014482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014482 prefixEnd_5014482 := by exact prefixLift 5014482
  have htrace : WordTrace (prefixWord ++ tailWord_5014482) baseStart_5014482 baseEnd_5014482 := by
    simpa [prefixWord, tailWord_5014482, baseEnd_5014482] using wordTrace_append hprefix tailTrace_5014482
  have hstable : (prefixWord ++ tailWord_5014482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014482).length < 2 ^ (prefixWord ++ tailWord_5014482).sum := by decide
  have hdescent : baseEnd_5014482 < baseStart_5014482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014489 : List Nat := [1, 2, 1, 2, 5, 1, 3, 1, 1, 4, 2]
def baseStart_5014489 : Nat := 118140960795 + 5014489 * 2 ^ 59
def prefixEnd_5014489 : Nat := 4983230072969 + 3 ^ 40 * 5014489 * 2
def baseEnd_5014489 : Nat := 2574843093683536522426291

theorem tailTrace_5014489 : CollatzResearch.WordTrace tailWord_5014489 prefixEnd_5014489 2574843093683536522426291 := by
  unfold tailWord_5014489
  simp only [CollatzResearch.WordTrace]
  refine ⟨182893439130370234384302521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121928959420246822922868347 182893439130370234384302521)
  ·
    refine ⟨137170079347777675788226891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182893439130370234384302521 137170079347777675788226891)
    ·
      refine ⟨205755119021666513682340337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137170079347777675788226891 205755119021666513682340337)
      ·
        refine ⟨154316339266249885261755253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205755119021666513682340337 154316339266249885261755253)
        ·
          refine ⟨14467156806210926743289555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 154316339266249885261755253 14467156806210926743289555)
          ·
            refine ⟨21700735209316390114934333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14467156806210926743289555 21700735209316390114934333)
            ·
              refine ⟨8137775703493646293100375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21700735209316390114934333 8137775703493646293100375)
              ·
                refine ⟨12206663555240469439650563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8137775703493646293100375 12206663555240469439650563)
                ·
                  refine ⟨18309995332860704159475845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12206663555240469439650563 18309995332860704159475845)
                  ·
                    refine ⟨3433124124911382029901721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18309995332860704159475845 3433124124911382029901721)
                    ·
                      refine ⟨2574843093683536522426291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3433124124911382029901721 2574843093683536522426291)
                      ·
                        rfl

theorem cell23_5014489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 4, 2].length) (baseStart_5014489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014489 prefixEnd_5014489 := by exact prefixLift 5014489
  have htrace : WordTrace (prefixWord ++ tailWord_5014489) baseStart_5014489 baseEnd_5014489 := by
    simpa [prefixWord, tailWord_5014489, baseEnd_5014489] using wordTrace_append hprefix tailTrace_5014489
  have hstable : (prefixWord ++ tailWord_5014489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014489).length < 2 ^ (prefixWord ++ tailWord_5014489).sum := by decide
  have hdescent : baseEnd_5014489 < baseStart_5014489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014545 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 4]
def baseStart_5014545 : Nat := 118140960795 + 5014545 * 2 ^ 59
def prefixEnd_5014545 : Nat := 4983230072969 + 3 ^ 40 * 5014545 * 2
def baseEnd_5014545 : Nat := 2574871848600188303326033

theorem tailTrace_5014545 : CollatzResearch.WordTrace tailWord_5014545 prefixEnd_5014545 2574871848600188303326033 := by
  unfold tailWord_5014545
  simp only [CollatzResearch.WordTrace]
  refine ⟨182895481618167355948341089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121930321078778237298894059 182895481618167355948341089)
  ·
    refine ⟨137171611213625516961255817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182895481618167355948341089 137171611213625516961255817)
    ·
      refine ⟨102878708410219137720941863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137171611213625516961255817 102878708410219137720941863)
      ·
        refine ⟨154318062615328706581412795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102878708410219137720941863 154318062615328706581412795)
        ·
          refine ⟨231477093922993059872119193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154318062615328706581412795 231477093922993059872119193)
          ·
            refine ⟨173607820442244794904089395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231477093922993059872119193 173607820442244794904089395)
            ·
              refine ⟨260411730663367192356134093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173607820442244794904089395 260411730663367192356134093)
              ·
                refine ⟨97654398998762697133550285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260411730663367192356134093 97654398998762697133550285)
                ·
                  refine ⟨36620399624536011425081357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97654398998762697133550285 36620399624536011425081357)
                  ·
                    refine ⟨13732649859201004284405509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36620399624536011425081357 13732649859201004284405509)
                    ·
                      refine ⟨2574871848600188303326033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13732649859201004284405509 2574871848600188303326033)
                      ·
                        rfl

theorem cell23_5014545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_5014545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014545 prefixEnd_5014545 := by exact prefixLift 5014545
  have htrace : WordTrace (prefixWord ++ tailWord_5014545) baseStart_5014545 baseEnd_5014545 := by
    simpa [prefixWord, tailWord_5014545, baseEnd_5014545] using wordTrace_append hprefix tailTrace_5014545
  have hstable : (prefixWord ++ tailWord_5014545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014545).length < 2 ^ (prefixWord ++ tailWord_5014545).sum := by decide
  have hdescent : baseEnd_5014545 < baseStart_5014545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014575 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 4]
def baseStart_5014575 : Nat := 118140960795 + 5014575 * 2 ^ 59
def prefixEnd_5014575 : Nat := 4983230072969 + 3 ^ 40 * 5014575 * 2
def baseEnd_5014575 : Nat := 2574887253019823185950895

theorem tailTrace_5014575 : CollatzResearch.WordTrace tailWord_5014575 prefixEnd_5014575 2574887253019823185950895 := by
  unfold tailWord_5014575
  simp only [CollatzResearch.WordTrace]
  refine ⟨182896575808058671071933179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121931050538705780714622119 182896575808058671071933179)
  ·
    refine ⟨274344863712088006607899769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182896575808058671071933179 274344863712088006607899769)
    ·
      refine ⟨205758647784066004955924827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274344863712088006607899769 205758647784066004955924827)
      ·
        refine ⟨308637971676099007433887241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205758647784066004955924827 308637971676099007433887241)
        ·
          refine ⟨231478478757074255575415431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308637971676099007433887241 231478478757074255575415431)
          ·
            refine ⟨347217718135611383363123147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231478478757074255575415431 347217718135611383363123147)
            ·
              refine ⟨520826577203417075044684721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347217718135611383363123147 520826577203417075044684721)
              ·
                refine ⟨390619932902562806283513541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 520826577203417075044684721 390619932902562806283513541)
                ·
                  refine ⟨73241237419230526178158789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 390619932902562806283513541 73241237419230526178158789)
                  ·
                    refine ⟨13732732016105723658404773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73241237419230526178158789 13732732016105723658404773)
                    ·
                      refine ⟨2574887253019823185950895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13732732016105723658404773 2574887253019823185950895)
                      ·
                        rfl

theorem cell23_5014575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_5014575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014575 prefixEnd_5014575 := by exact prefixLift 5014575
  have htrace : WordTrace (prefixWord ++ tailWord_5014575) baseStart_5014575 baseEnd_5014575 := by
    simpa [prefixWord, tailWord_5014575, baseEnd_5014575] using wordTrace_append hprefix tailTrace_5014575
  have hstable : (prefixWord ++ tailWord_5014575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014575).length < 2 ^ (prefixWord ++ tailWord_5014575).sum := by decide
  have hdescent : baseEnd_5014575 < baseStart_5014575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014602 : List Nat := [3, 1, 2, 1, 1, 2, 4, 3, 6]
def baseStart_5014602 : Nat := 118140960795 + 5014602 * 2 ^ 59
def prefixEnd_5014602 : Nat := 4983230072969 + 3 ^ 40 * 5014602 * 2
def baseEnd_5014602 : Nat := 286100124110832731145919

theorem tailTrace_5014602 : CollatzResearch.WordTrace tailWord_5014602 prefixEnd_5014602 286100124110832731145919 := by
  unfold tailWord_5014602
  simp only [CollatzResearch.WordTrace]
  refine ⟨45724390144740213670791515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121931707052640569788777373 45724390144740213670791515)
  ·
    refine ⟨68586585217110320506187273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45724390144740213670791515 68586585217110320506187273)
    ·
      refine ⟨51439938912832740379640455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68586585217110320506187273 51439938912832740379640455)
      ·
        refine ⟨77159908369249110569460683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51439938912832740379640455 77159908369249110569460683)
        ·
          refine ⟨115739862553873665854191025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77159908369249110569460683 115739862553873665854191025)
          ·
            refine ⟨86804896915405249390643269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115739862553873665854191025 86804896915405249390643269)
            ·
              refine ⟨16275918171638484260745613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86804896915405249390643269 16275918171638484260745613)
              ·
                refine ⟨6103469314364431597779605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16275918171638484260745613 6103469314364431597779605)
                ·
                  refine ⟨286100124110832731145919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6103469314364431597779605 286100124110832731145919)
                  ·
                    rfl

theorem cell23_5014602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 6].length) (baseStart_5014602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014602 prefixEnd_5014602 := by exact prefixLift 5014602
  have htrace : WordTrace (prefixWord ++ tailWord_5014602) baseStart_5014602 baseEnd_5014602 := by
    simpa [prefixWord, tailWord_5014602, baseEnd_5014602] using wordTrace_append hprefix tailTrace_5014602
  have hstable : (prefixWord ++ tailWord_5014602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014602).length < 2 ^ (prefixWord ++ tailWord_5014602).sum := by decide
  have hdescent : baseEnd_5014602 < baseStart_5014602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014629 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 5, 1, 3]
def baseStart_5014629 : Nat := 118140960795 + 5014629 * 2 ^ 59
def prefixEnd_5014629 : Nat := 4983230072969 + 3 ^ 40 * 5014629 * 2
def baseEnd_5014629 : Nat := 2574914980975165974675647

theorem tailTrace_5014629 : CollatzResearch.WordTrace tailWord_5014629 prefixEnd_5014629 2574914980975165974675647 := by
  unfold tailWord_5014629
  simp only [CollatzResearch.WordTrace]
  refine ⟨182898545349863038294398941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121932363566575358862932627 182898545349863038294398941)
  ·
    refine ⟨68586954506198639360399603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182898545349863038294398941 68586954506198639360399603)
    ·
      refine ⟨102880431759297959040599405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68586954506198639360399603 102880431759297959040599405)
      ·
        refine ⟨38580161909736734640224777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102880431759297959040599405 38580161909736734640224777)
        ·
          refine ⟨28935121432302550980168583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38580161909736734640224777 28935121432302550980168583)
          ·
            refine ⟨43402682148453826470252875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28935121432302550980168583 43402682148453826470252875)
            ·
              refine ⟨65104023222680739705379313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43402682148453826470252875 65104023222680739705379313)
              ·
                refine ⟨48828017417010554779034485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65104023222680739705379313 48828017417010554779034485)
                ·
                  refine ⟨4577626632844739510534483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48828017417010554779034485 4577626632844739510534483)
                  ·
                    refine ⟨6866439949267109265801725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4577626632844739510534483 6866439949267109265801725)
                    ·
                      refine ⟨2574914980975165974675647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6866439949267109265801725 2574914980975165974675647)
                      ·
                        rfl

theorem cell23_5014629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_5014629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014629 prefixEnd_5014629 := by exact prefixLift 5014629
  have htrace : WordTrace (prefixWord ++ tailWord_5014629) baseStart_5014629 baseEnd_5014629 := by
    simpa [prefixWord, tailWord_5014629, baseEnd_5014629] using wordTrace_append hprefix tailTrace_5014629
  have hstable : (prefixWord ++ tailWord_5014629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014629).length < 2 ^ (prefixWord ++ tailWord_5014629).sum := by decide
  have hdescent : baseEnd_5014629 < baseStart_5014629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014639 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 4, 3, 2]
def baseStart_5014639 : Nat := 118140960795 + 5014639 * 2 ^ 59
def prefixEnd_5014639 : Nat := 4983230072969 + 3 ^ 40 * 5014639 * 2
def baseEnd_5014639 : Nat := 2574920115781710935550601

theorem tailTrace_5014639 : CollatzResearch.WordTrace tailWord_5014639 prefixEnd_5014639 2574920115781710935550601 := by
  unfold tailWord_5014639
  simp only [CollatzResearch.WordTrace]
  refine ⟨182898910079826810002262971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121932606719884540001508647 182898910079826810002262971)
  ·
    refine ⟨274348365119740215003394457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182898910079826810002262971 274348365119740215003394457)
    ·
      refine ⟨205761273839805161252545843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274348365119740215003394457 205761273839805161252545843)
      ·
        refine ⟨308641910759707741878818765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205761273839805161252545843 308641910759707741878818765)
        ·
          refine ⟨115740716534890403204557037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308641910759707741878818765 115740716534890403204557037)
          ·
            refine ⟨43402768700583901201708889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115740716534890403204557037 43402768700583901201708889)
            ·
              refine ⟨32552076525437925901281667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43402768700583901201708889 32552076525437925901281667)
              ·
                refine ⟨48828114788156888851922501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32552076525437925901281667 48828114788156888851922501)
                ·
                  refine ⟨9155271522779416659735469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48828114788156888851922501 9155271522779416659735469)
                  ·
                    refine ⟨3433226821042281247400801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9155271522779416659735469 3433226821042281247400801)
                    ·
                      refine ⟨2574920115781710935550601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3433226821042281247400801 2574920115781710935550601)
                      ·
                        rfl

theorem cell23_5014639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 3, 2].length) (baseStart_5014639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014639 prefixEnd_5014639 := by exact prefixLift 5014639
  have htrace : WordTrace (prefixWord ++ tailWord_5014639) baseStart_5014639 baseEnd_5014639 := by
    simpa [prefixWord, tailWord_5014639, baseEnd_5014639] using wordTrace_append hprefix tailTrace_5014639
  have hstable : (prefixWord ++ tailWord_5014639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014639).length < 2 ^ (prefixWord ++ tailWord_5014639).sum := by decide
  have hdescent : baseEnd_5014639 < baseStart_5014639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014679 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 4, 4]
def baseStart_5014679 : Nat := 118140960795 + 5014679 * 2 ^ 59
def prefixEnd_5014679 : Nat := 4983230072969 + 3 ^ 40 * 5014679 * 2
def baseEnd_5014679 : Nat := 858313551669296926350139

theorem tailTrace_5014679 : CollatzResearch.WordTrace tailWord_5014679 prefixEnd_5014679 858313551669296926350139 := by
  unfold tailWord_5014679
  simp only [CollatzResearch.WordTrace]
  refine ⟨182900368999681896833719091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121933579333121264555812727 182900368999681896833719091)
  ·
    refine ⟨274350553499522845250578637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182900368999681896833719091 274350553499522845250578637)
    ·
      refine ⟨102881457562321066968966989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274350553499522845250578637 102881457562321066968966989)
      ·
        refine ⟨38580546585870400113362621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102881457562321066968966989 38580546585870400113362621)
        ·
          refine ⟨14467704969701400042510983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38580546585870400113362621 14467704969701400042510983)
          ·
            refine ⟨21701557454552100063766475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14467704969701400042510983 21701557454552100063766475)
            ·
              refine ⟨32552336181828150095649713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21701557454552100063766475 32552336181828150095649713)
              ·
                refine ⟨24414252136371112571737285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32552336181828150095649713 24414252136371112571737285)
                ·
                  refine ⟨4577672275569583607200741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24414252136371112571737285 4577672275569583607200741)
                  ·
                    refine ⟨858313551669296926350139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4577672275569583607200741 858313551669296926350139)
                    ·
                      rfl

theorem cell23_5014679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_5014679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014679 prefixEnd_5014679 := by exact prefixLift 5014679
  have htrace : WordTrace (prefixWord ++ tailWord_5014679) baseStart_5014679 baseEnd_5014679 := by
    simpa [prefixWord, tailWord_5014679, baseEnd_5014679] using wordTrace_append hprefix tailTrace_5014679
  have hstable : (prefixWord ++ tailWord_5014679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014679).length < 2 ^ (prefixWord ++ tailWord_5014679).sum := by decide
  have hdescent : baseEnd_5014679 < baseStart_5014679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014680 : List Nat := [2, 1, 2, 4, 2, 3, 1, 3, 1, 1, 3]
def baseStart_5014680 : Nat := 118140960795 + 5014680 * 2 ^ 59
def prefixEnd_5014680 : Nat := 4983230072969 + 3 ^ 40 * 5014680 * 2
def baseEnd_5014680 : Nat := 2574941168488545275137913

theorem tailTrace_5014680 : CollatzResearch.WordTrace tailWord_5014680 prefixEnd_5014680 2574941168488545275137913 := by
  unfold tailWord_5014680
  simp only [CollatzResearch.WordTrace]
  refine ⟨91450202736339137002252747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121933603648452182669670329 91450202736339137002252747)
  ·
    refine ⟨137175304104508705503379121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91450202736339137002252747 137175304104508705503379121)
    ·
      refine ⟨102881478078381529127534341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137175304104508705503379121 102881478078381529127534341)
      ·
        refine ⟨19290277139696536711412689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102881478078381529127534341 19290277139696536711412689)
        ·
          refine ⟨14467707854772402533559517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19290277139696536711412689 14467707854772402533559517)
          ·
            refine ⟨5425390445539650950084819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14467707854772402533559517 5425390445539650950084819)
            ·
              refine ⟨8138085668309476425127229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5425390445539650950084819 8138085668309476425127229)
              ·
                refine ⟨3051782125616053659422711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8138085668309476425127229 3051782125616053659422711)
                ·
                  refine ⟨4577673188424080489134067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3051782125616053659422711 4577673188424080489134067)
                  ·
                    refine ⟨6866509782636120733701101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4577673188424080489134067 6866509782636120733701101)
                    ·
                      refine ⟨2574941168488545275137913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6866509782636120733701101 2574941168488545275137913)
                      ·
                        rfl

theorem cell23_5014680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_5014680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014680 prefixEnd_5014680 := by exact prefixLift 5014680
  have htrace : WordTrace (prefixWord ++ tailWord_5014680) baseStart_5014680 baseEnd_5014680 := by
    simpa [prefixWord, tailWord_5014680, baseEnd_5014680] using wordTrace_append hprefix tailTrace_5014680
  have hstable : (prefixWord ++ tailWord_5014680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014680).length < 2 ^ (prefixWord ++ tailWord_5014680).sum := by decide
  have hdescent : baseEnd_5014680 < baseStart_5014680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014689 : List Nat := [1, 2, 3, 3, 1, 1, 4, 1, 1, 1, 5]
def baseStart_5014689 : Nat := 118140960795 + 5014689 * 2 ^ 59
def prefixEnd_5014689 : Nat := 4983230072969 + 3 ^ 40 * 5014689 * 2
def baseEnd_5014689 : Nat := 2574945789814435739925371

theorem tailTrace_5014689 : CollatzResearch.WordTrace tailWord_5014689 prefixEnd_5014689 2574945789814435739925371 := by
  unfold tailWord_5014689
  simp only [CollatzResearch.WordTrace]
  refine ⟨182900733729645668541583121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121933822486430445694388747 182900733729645668541583121)
  ·
    refine ⟨137175550297234251406187341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182900733729645668541583121 137175550297234251406187341)
    ·
      refine ⟨51440831361462844277320253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137175550297234251406187341 51440831361462844277320253)
      ·
        refine ⟨19290311760548566603995095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51440831361462844277320253 19290311760548566603995095)
        ·
          refine ⟨28935467640822849905992643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19290311760548566603995095 28935467640822849905992643)
          ·
            refine ⟨43403201461234274858988965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28935467640822849905992643 43403201461234274858988965)
            ·
              refine ⟨8138100273981426536060431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43403201461234274858988965 8138100273981426536060431)
              ·
                refine ⟨12207150410972139804090647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8138100273981426536060431 12207150410972139804090647)
                ·
                  refine ⟨18310725616458209706135971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12207150410972139804090647 18310725616458209706135971)
                  ·
                    refine ⟨27466088424687314559203957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18310725616458209706135971 27466088424687314559203957)
                    ·
                      refine ⟨2574945789814435739925371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27466088424687314559203957 2574945789814435739925371)
                      ·
                        rfl

theorem cell23_5014689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_5014689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014689 prefixEnd_5014689 := by exact prefixLift 5014689
  have htrace : WordTrace (prefixWord ++ tailWord_5014689) baseStart_5014689 baseEnd_5014689 := by
    simpa [prefixWord, tailWord_5014689, baseEnd_5014689] using wordTrace_append hprefix tailTrace_5014689
  have hstable : (prefixWord ++ tailWord_5014689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014689).length < 2 ^ (prefixWord ++ tailWord_5014689).sum := by decide
  have hdescent : baseEnd_5014689 < baseStart_5014689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014692 : List Nat := [2, 3, 1, 2, 3, 1, 11]
def baseStart_5014692 : Nat := 118140960795 + 5014692 * 2 ^ 59
def prefixEnd_5014692 : Nat := 4983230072969 + 3 ^ 40 * 5014692 * 2
def baseEnd_5014692 : Nat := 31789473213041965780097

theorem tailTrace_5014692 : CollatzResearch.WordTrace tailWord_5014692 prefixEnd_5014692 31789473213041965780097 := by
  unfold tailWord_5014692
  simp only [CollatzResearch.WordTrace]
  refine ⟨91450421574317400026971165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121933895432423200035961553 91450421574317400026971165)
  ·
    refine ⟨34293908090369025010114187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91450421574317400026971165 34293908090369025010114187)
    ·
      refine ⟨51440862135553537515171281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34293908090369025010114187 51440862135553537515171281)
      ·
        refine ⟨38580646601665153136378461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51440862135553537515171281 38580646601665153136378461)
        ·
          refine ⟨14467742475624432426141923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38580646601665153136378461 14467742475624432426141923)
          ·
            refine ⟨21701613713436648639212885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14467742475624432426141923 21701613713436648639212885)
            ·
              refine ⟨31789473213041965780097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 21701613713436648639212885 31789473213041965780097)
              ·
                rfl

theorem cell23_5014692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 11].length) (baseStart_5014692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014692 prefixEnd_5014692 := by exact prefixLift 5014692
  have htrace : WordTrace (prefixWord ++ tailWord_5014692) baseStart_5014692 baseEnd_5014692 := by
    simpa [prefixWord, tailWord_5014692, baseEnd_5014692] using wordTrace_append hprefix tailTrace_5014692
  have hstable : (prefixWord ++ tailWord_5014692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014692).length < 2 ^ (prefixWord ++ tailWord_5014692).sum := by decide
  have hdescent : baseEnd_5014692 < baseStart_5014692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014703 : List Nat := [1, 1, 2, 1, 2, 3, 2, 6, 1, 2, 2]
def baseStart_5014703 : Nat := 118140960795 + 5014703 * 2 ^ 59
def prefixEnd_5014703 : Nat := 4983230072969 + 3 ^ 40 * 5014703 * 2
def baseEnd_5014703 : Nat := 2574952978543598685150307

theorem tailTrace_5014703 : CollatzResearch.WordTrace tailWord_5014703 prefixEnd_5014703 2574952978543598685150307 := by
  unfold tailWord_5014703
  simp only [CollatzResearch.WordTrace]
  refine ⟨182901244351594948932592763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121934162901063299288395175 182901244351594948932592763)
  ·
    refine ⟨274351866527392423398889145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182901244351594948932592763 274351866527392423398889145)
    ·
      refine ⟨205763899895544317549166859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274351866527392423398889145 205763899895544317549166859)
      ·
        refine ⟨308645849843316476323750289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205763899895544317549166859 308645849843316476323750289)
        ·
          refine ⟨231484387382487357242812717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308645849843316476323750289 231484387382487357242812717)
          ·
            refine ⟨86806645268432758966054769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231484387382487357242812717 86806645268432758966054769)
            ·
              refine ⟨65104983951324569224541077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86806645268432758966054769 65104983951324569224541077)
              ·
                refine ⟨3051796122718339182400363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65104983951324569224541077 3051796122718339182400363)
                ·
                  refine ⟨4577694184077508773600545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3051796122718339182400363 4577694184077508773600545)
                  ·
                    refine ⟨3433270638058131580200409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4577694184077508773600545 3433270638058131580200409)
                    ·
                      refine ⟨2574952978543598685150307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3433270638058131580200409 2574952978543598685150307)
                      ·
                        rfl

theorem cell23_5014703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 1, 2, 2].length) (baseStart_5014703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014703 prefixEnd_5014703 := by exact prefixLift 5014703
  have htrace : WordTrace (prefixWord ++ tailWord_5014703) baseStart_5014703 baseEnd_5014703 := by
    simpa [prefixWord, tailWord_5014703, baseEnd_5014703] using wordTrace_append hprefix tailTrace_5014703
  have hstable : (prefixWord ++ tailWord_5014703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014703).length < 2 ^ (prefixWord ++ tailWord_5014703).sum := by decide
  have hdescent : baseEnd_5014703 < baseStart_5014703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014713 : List Nat := [1, 2, 1, 4, 1, 5, 2, 1, 2, 4]
def baseStart_5014713 : Nat := 118140960795 + 5014713 * 2 ^ 59
def prefixEnd_5014713 : Nat := 4983230072969 + 3 ^ 40 * 5014713 * 2
def baseEnd_5014713 : Nat := 858319371116714548675087

theorem tailTrace_5014713 : CollatzResearch.WordTrace tailWord_5014713 prefixEnd_5014713 858319371116714548675087 := by
  unfold tailWord_5014713
  simp only [CollatzResearch.WordTrace]
  refine ⟨182901609081558720640456793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121934406054372480426971195 182901609081558720640456793)
  ·
    refine ⟨137176206811169040480342595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182901609081558720640456793 137176206811169040480342595)
    ·
      refine ⟨205764310216753560720513893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137176206811169040480342595 205764310216753560720513893)
      ·
        refine ⟨38580808165641292635096355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205764310216753560720513893 38580808165641292635096355)
        ·
          refine ⟨57871212248461938952644533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38580808165641292635096355 57871212248461938952644533)
          ·
            refine ⟨5425426148293306776810425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57871212248461938952644533 5425426148293306776810425)
            ·
              refine ⟨4069069611219980082607819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5425426148293306776810425 4069069611219980082607819)
              ·
                refine ⟨6103604416829970123911729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4069069611219980082607819 6103604416829970123911729)
                ·
                  refine ⟨4577703312622477592933797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6103604416829970123911729 4577703312622477592933797)
                  ·
                    refine ⟨858319371116714548675087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4577703312622477592933797 858319371116714548675087)
                    ·
                      rfl

theorem cell23_5014713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 2, 4].length) (baseStart_5014713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014713 prefixEnd_5014713 := by exact prefixLift 5014713
  have htrace : WordTrace (prefixWord ++ tailWord_5014713) baseStart_5014713 baseEnd_5014713 := by
    simpa [prefixWord, tailWord_5014713, baseEnd_5014713] using wordTrace_append hprefix tailTrace_5014713
  have hstable : (prefixWord ++ tailWord_5014713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014713).length < 2 ^ (prefixWord ++ tailWord_5014713).sum := by decide
  have hdescent : baseEnd_5014713 < baseStart_5014713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014740 : List Nat := [2, 4, 1, 4, 2, 1, 1, 1, 1, 1, 5]
def baseStart_5014740 : Nat := 118140960795 + 5014740 * 2 ^ 59
def prefixEnd_5014740 : Nat := 4983230072969 + 3 ^ 40 * 5014740 * 2
def baseEnd_5014740 : Nat := 2574971977327815040387637

theorem tailTrace_5014740 : CollatzResearch.WordTrace tailWord_5014740 prefixEnd_5014740 2574971977327815040387637 := by
  unfold tailWord_5014740
  simp only [CollatzResearch.WordTrace]
  refine ⟨91451296926230452125844837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121935062568307269501126449 91451296926230452125844837)
  ·
    refine ⟨17147118173668209773595907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91451296926230452125844837 17147118173668209773595907)
    ·
      refine ⟨25720677260502314660393861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17147118173668209773595907 25720677260502314660393861)
      ·
        refine ⟨4822626986344183998823849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25720677260502314660393861 4822626986344183998823849)
        ·
          refine ⟨3616970239758137999117887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4822626986344183998823849 3616970239758137999117887)
          ·
            refine ⟨5425455359637206998676831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3616970239758137999117887 5425455359637206998676831)
            ·
              refine ⟨8138183039455810498015247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5425455359637206998676831 8138183039455810498015247)
              ·
                refine ⟨12207274559183715747022871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8138183039455810498015247 12207274559183715747022871)
                ·
                  refine ⟨18310911838775573620534307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12207274559183715747022871 18310911838775573620534307)
                  ·
                    refine ⟨27466367758163360430801461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18310911838775573620534307 27466367758163360430801461)
                    ·
                      refine ⟨2574971977327815040387637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27466367758163360430801461 2574971977327815040387637)
                      ·
                        rfl

theorem cell23_5014740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_5014740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014740 prefixEnd_5014740 := by exact prefixLift 5014740
  have htrace : WordTrace (prefixWord ++ tailWord_5014740) baseStart_5014740 baseEnd_5014740 := by
    simpa [prefixWord, tailWord_5014740, baseEnd_5014740] using wordTrace_append hprefix tailTrace_5014740
  have hstable : (prefixWord ++ tailWord_5014740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014740).length < 2 ^ (prefixWord ++ tailWord_5014740).sum := by decide
  have hdescent : baseEnd_5014740 < baseStart_5014740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014753 : List Nat := [1, 2, 3, 1, 3, 3, 2, 2, 2, 1, 3]
def baseStart_5014753 : Nat := 118140960795 + 5014753 * 2 ^ 59
def prefixEnd_5014753 : Nat := 4983230072969 + 3 ^ 40 * 5014753 * 2
def baseEnd_5014753 : Nat := 2574978652576323489525077

theorem tailTrace_5014753 : CollatzResearch.WordTrace tailWord_5014753 prefixEnd_5014753 2574978652576323489525077 := by
  unfold tailWord_5014753
  simp only [CollatzResearch.WordTrace]
  refine ⟨182903068001413807471912913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121935378667609204981275275 182903068001413807471912913)
  ·
    refine ⟨137177301001060355603934685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182903068001413807471912913 137177301001060355603934685)
    ·
      refine ⟨51441487875397633351475507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137177301001060355603934685 51441487875397633351475507)
      ·
        refine ⟨77162231813096450027213261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51441487875397633351475507 77162231813096450027213261)
        ·
          refine ⟨28935836929911168760204973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77162231813096450027213261 28935836929911168760204973)
          ·
            refine ⟨10850938848716688285076865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28935836929911168760204973 10850938848716688285076865)
            ·
              refine ⟨8138204136537516213807649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10850938848716688285076865 8138204136537516213807649)
              ·
                refine ⟨6103653102403137160355737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8138204136537516213807649 6103653102403137160355737)
                ·
                  refine ⟨4577739826802352870266803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6103653102403137160355737 4577739826802352870266803)
                  ·
                    refine ⟨6866609740203529305400205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4577739826802352870266803 6866609740203529305400205)
                    ·
                      refine ⟨2574978652576323489525077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6866609740203529305400205 2574978652576323489525077)
                      ·
                        rfl

theorem cell23_5014753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_5014753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014753 prefixEnd_5014753 := by exact prefixLift 5014753
  have htrace : WordTrace (prefixWord ++ tailWord_5014753) baseStart_5014753 baseEnd_5014753 := by
    simpa [prefixWord, tailWord_5014753, baseEnd_5014753] using wordTrace_append hprefix tailTrace_5014753
  have hstable : (prefixWord ++ tailWord_5014753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014753).length < 2 ^ (prefixWord ++ tailWord_5014753).sum := by decide
  have hdescent : baseEnd_5014753 < baseStart_5014753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014776 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 8, 2, 2]
def baseStart_5014776 : Nat := 118140960795 + 5014776 * 2 ^ 59
def prefixEnd_5014776 : Nat := 4983230072969 + 3 ^ 40 * 5014776 * 2
def baseEnd_5014776 : Nat := 2574990462631376899537471

theorem tailTrace_5014776 : CollatzResearch.WordTrace tailWord_5014776 prefixEnd_5014776 2574990462631376899537471 := by
  unfold tailWord_5014776
  simp only [CollatzResearch.WordTrace]
  refine ⟨91451953440165241200000091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121935937920220321600000121 91451953440165241200000091)
  ·
    refine ⟨137177930160247861800000137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91451953440165241200000091 137177930160247861800000137)
    ·
      refine ⟨102883447620185896350000103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137177930160247861800000137 102883447620185896350000103)
      ·
        refine ⟨154325171430278844525000155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102883447620185896350000103 154325171430278844525000155)
        ·
          refine ⟨231487757145418266787500233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154325171430278844525000155 231487757145418266787500233)
          ·
            refine ⟨173615817859063700090625175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231487757145418266787500233 173615817859063700090625175)
            ·
              refine ⟨260423726788595550135937763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173615817859063700090625175 260423726788595550135937763)
              ·
                refine ⟨390635590182893325203906645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260423726788595550135937763 390635590182893325203906645)
                ·
                  refine ⟨4577760822455781154733281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 390635590182893325203906645 4577760822455781154733281)
                  ·
                    refine ⟨3433320616841835866049961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4577760822455781154733281 3433320616841835866049961)
                    ·
                      refine ⟨2574990462631376899537471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3433320616841835866049961 2574990462631376899537471)
                      ·
                        rfl

theorem cell23_5014776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 8, 2, 2].length) (baseStart_5014776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014776 prefixEnd_5014776 := by exact prefixLift 5014776
  have htrace : WordTrace (prefixWord ++ tailWord_5014776) baseStart_5014776 baseEnd_5014776 := by
    simpa [prefixWord, tailWord_5014776, baseEnd_5014776] using wordTrace_append hprefix tailTrace_5014776
  have hstable : (prefixWord ++ tailWord_5014776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014776).length < 2 ^ (prefixWord ++ tailWord_5014776).sum := by decide
  have hdescent : baseEnd_5014776 < baseStart_5014776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014810 : List Nat := [3, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2]
def baseStart_5014810 : Nat := 118140960795 + 5014810 * 2 ^ 59
def prefixEnd_5014810 : Nat := 4983230072969 + 3 ^ 40 * 5014810 * 2
def baseEnd_5014810 : Nat := 2575007920973629766512315

theorem tailTrace_5014810 : CollatzResearch.WordTrace tailWord_5014810 prefixEnd_5014810 2575007920973629766512315 := by
  unfold tailWord_5014810
  simp only [CollatzResearch.WordTrace]
  refine ⟨45726286740551826551684471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121936764641471537471158589 45726286740551826551684471)
  ·
    refine ⟨68589430110827739827526707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45726286740551826551684471 68589430110827739827526707)
    ·
      refine ⟨102884145166241609741290061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68589430110827739827526707 102884145166241609741290061)
      ·
        refine ⟨38581554437340603652983773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102884145166241609741290061 38581554437340603652983773)
        ·
          refine ⟨14468082914002726369868915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38581554437340603652983773 14468082914002726369868915)
          ·
            refine ⟨21702124371004089554803373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14468082914002726369868915 21702124371004089554803373)
            ·
              refine ⟨8138296639126533583051265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21702124371004089554803373 8138296639126533583051265)
              ·
                refine ⟨6103722479344900187288449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8138296639126533583051265 6103722479344900187288449)
                ·
                  refine ⟨4577791859508675140466337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6103722479344900187288449 4577791859508675140466337)
                  ·
                    refine ⟨3433343894631506355349753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4577791859508675140466337 3433343894631506355349753)
                    ·
                      refine ⟨2575007920973629766512315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3433343894631506355349753 2575007920973629766512315)
                      ·
                        rfl

theorem cell23_5014810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_5014810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014810 prefixEnd_5014810 := by exact prefixLift 5014810
  have htrace : WordTrace (prefixWord ++ tailWord_5014810) baseStart_5014810 baseEnd_5014810 := by
    simpa [prefixWord, tailWord_5014810, baseEnd_5014810] using wordTrace_append hprefix tailTrace_5014810
  have hstable : (prefixWord ++ tailWord_5014810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014810).length < 2 ^ (prefixWord ++ tailWord_5014810).sum := by decide
  have hdescent : baseEnd_5014810 < baseStart_5014810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014816 : List Nat := [2, 1, 1, 5, 3, 1, 2, 1, 7]
def baseStart_5014816 : Nat := 118140960795 + 5014816 * 2 ^ 59
def prefixEnd_5014816 : Nat := 4983230072969 + 3 ^ 40 * 5014816 * 2
def baseEnd_5014816 : Nat := 286112333539728527004143

theorem tailTrace_5014816 : CollatzResearch.WordTrace tailWord_5014816 prefixEnd_5014816 286112333539728527004143 := by
  unfold tailWord_5014816
  simp only [CollatzResearch.WordTrace]
  refine ⟨91452682900092784615728151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121936910533457046154304201 91452682900092784615728151)
  ·
    refine ⟨137179024350139176923592227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91452682900092784615728151 137179024350139176923592227)
    ·
      refine ⟨205768536525208765385388341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137179024350139176923592227 205768536525208765385388341)
      ·
        refine ⟨19290800299238321754880157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 205768536525208765385388341 19290800299238321754880157)
        ·
          refine ⟨7234050112214370658080059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19290800299238321754880157 7234050112214370658080059)
          ·
            refine ⟨10851075168321555987120089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7234050112214370658080059 10851075168321555987120089)
            ·
              refine ⟨8138306376241166990340067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10851075168321555987120089 8138306376241166990340067)
              ·
                refine ⟨12207459564361750485510101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8138306376241166990340067 12207459564361750485510101)
                ·
                  refine ⟨286112333539728527004143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12207459564361750485510101 286112333539728527004143)
                  ·
                    rfl

theorem cell23_5014816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 7].length) (baseStart_5014816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014816 prefixEnd_5014816 := by exact prefixLift 5014816
  have htrace : WordTrace (prefixWord ++ tailWord_5014816) baseStart_5014816 baseEnd_5014816 := by
    simpa [prefixWord, tailWord_5014816, baseEnd_5014816] using wordTrace_append hprefix tailTrace_5014816
  have hstable : (prefixWord ++ tailWord_5014816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014816).length < 2 ^ (prefixWord ++ tailWord_5014816).sum := by decide
  have hdescent : baseEnd_5014816 < baseStart_5014816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014846 : List Nat := [4, 2, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_5014846 : Nat := 118140960795 + 5014846 * 2 ^ 59
def prefixEnd_5014846 : Nat := 4983230072969 + 3 ^ 40 * 5014846 * 2
def baseEnd_5014846 : Nat := 858342135425730541887383

theorem tailTrace_5014846 : CollatzResearch.WordTrace tailWord_5014846 prefixEnd_5014846 858342135425730541887383 := by
  unfold tailWord_5014846
  simp only [CollatzResearch.WordTrace]
  refine ⟨22863307498759610544381049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121937639993384589570032261 22863307498759610544381049)
  ·
    refine ⟨17147480624069707908285787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22863307498759610544381049 17147480624069707908285787)
    ·
      refine ⟨25721220936104561862428681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17147480624069707908285787 25721220936104561862428681)
      ·
        refine ⟨19290915702078421396821511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25721220936104561862428681 19290915702078421396821511)
        ·
          refine ⟨28936373553117632095232267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19290915702078421396821511 28936373553117632095232267)
          ·
            refine ⟨43404560329676448142848401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28936373553117632095232267 43404560329676448142848401)
            ·
              refine ⟨32553420247257336107136301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43404560329676448142848401 32553420247257336107136301)
              ·
                refine ⟨12207532592721501040176113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32553420247257336107136301 12207532592721501040176113)
                ·
                  refine ⟨9155649444541125780132085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12207532592721501040176113 9155649444541125780132085)
                  ·
                    refine ⟨858342135425730541887383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9155649444541125780132085 858342135425730541887383)
                    ·
                      rfl

theorem cell23_5014846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_5014846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014846 prefixEnd_5014846 := by exact prefixLift 5014846
  have htrace : WordTrace (prefixWord ++ tailWord_5014846) baseStart_5014846 baseEnd_5014846 := by
    simpa [prefixWord, tailWord_5014846, baseEnd_5014846] using wordTrace_append hprefix tailTrace_5014846
  have hstable : (prefixWord ++ tailWord_5014846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014846).length < 2 ^ (prefixWord ++ tailWord_5014846).sum := by decide
  have hdescent : baseEnd_5014846 < baseStart_5014846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014956 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 4]
def baseStart_5014956 : Nat := 118140960795 + 5014956 * 2 ^ 59
def prefixEnd_5014956 : Nat := 4983230072969 + 3 ^ 40 * 5014956 * 2
def baseEnd_5014956 : Nat := 2575082889149186195286643

theorem tailTrace_5014956 : CollatzResearch.WordTrace tailWord_5014956 prefixEnd_5014956 2575082889149186195286643 := by
  unfold tailWord_5014956
  simp only [CollatzResearch.WordTrace]
  refine ⟨91455236009839186570776361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121940314679785582094368481 91455236009839186570776361)
  ·
    refine ⟨68591427007379389928082271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91455236009839186570776361 68591427007379389928082271)
    ·
      refine ⟨102887140511069084892123407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68591427007379389928082271 102887140511069084892123407)
      ·
        refine ⟨154330710766603627338185111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102887140511069084892123407 154330710766603627338185111)
        ·
          refine ⟨231496066149905441007277667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154330710766603627338185111 231496066149905441007277667)
          ·
            refine ⟨347244099224858161510916501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231496066149905441007277667 347244099224858161510916501)
            ·
              refine ⟨16277067151165226320824211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 347244099224858161510916501 16277067151165226320824211)
              ·
                refine ⟨24415600726747839481236317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16277067151165226320824211 24415600726747839481236317)
                ·
                  refine ⟨9155850272530439805463619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24415600726747839481236317 9155850272530439805463619)
                  ·
                    refine ⟨13733775408795659708195429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9155850272530439805463619 13733775408795659708195429)
                    ·
                      refine ⟨2575082889149186195286643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13733775408795659708195429 2575082889149186195286643)
                      ·
                        rfl

theorem cell23_5014956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_5014956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014956 prefixEnd_5014956 := by exact prefixLift 5014956
  have htrace : WordTrace (prefixWord ++ tailWord_5014956) baseStart_5014956 baseEnd_5014956 := by
    simpa [prefixWord, tailWord_5014956, baseEnd_5014956] using wordTrace_append hprefix tailTrace_5014956
  have hstable : (prefixWord ++ tailWord_5014956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014956).length < 2 ^ (prefixWord ++ tailWord_5014956).sum := by decide
  have hdescent : baseEnd_5014956 < baseStart_5014956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014973 : List Nat := [1, 4, 1, 2, 2, 1, 3, 3, 1, 1, 4]
def baseStart_5014973 : Nat := 118140960795 + 5014973 * 2 ^ 59
def prefixEnd_5014973 : Nat := 4983230072969 + 3 ^ 40 * 5014973 * 2
def baseEnd_5014973 : Nat := 2575091618320312628774065

theorem tailTrace_5014973 : CollatzResearch.WordTrace tailWord_5014973 prefixEnd_5014973 2575091618320312628774065 := by
  unfold tailWord_5014973
  simp only [CollatzResearch.WordTrace]
  refine ⟨182911092060616785044921573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121940728040411190029947715 182911092060616785044921573)
  ·
    refine ⟨34295829761365647195922795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182911092060616785044921573 34295829761365647195922795)
    ·
      refine ⟨51443744642048470793884193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34295829761365647195922795 51443744642048470793884193)
      ·
        refine ⟨38582808481536353095413145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51443744642048470793884193 38582808481536353095413145)
        ·
          refine ⟨28937106361152264821559859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38582808481536353095413145 28937106361152264821559859)
          ·
            refine ⟨43405659541728397232339789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28937106361152264821559859 43405659541728397232339789)
            ·
              refine ⟨16277122328148148962127421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43405659541728397232339789 16277122328148148962127421)
              ·
                refine ⟨6103920873055555860797783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16277122328148148962127421 6103920873055555860797783)
                ·
                  refine ⟨9155881309583333791196675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6103920873055555860797783 9155881309583333791196675)
                  ·
                    refine ⟨13733821964375000686795013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9155881309583333791196675 13733821964375000686795013)
                    ·
                      refine ⟨2575091618320312628774065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13733821964375000686795013 2575091618320312628774065)
                      ·
                        rfl

theorem cell23_5014973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_5014973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014973 prefixEnd_5014973 := by exact prefixLift 5014973
  have htrace : WordTrace (prefixWord ++ tailWord_5014973) baseStart_5014973 baseEnd_5014973 := by
    simpa [prefixWord, tailWord_5014973, baseEnd_5014973] using wordTrace_append hprefix tailTrace_5014973
  have hstable : (prefixWord ++ tailWord_5014973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014973).length < 2 ^ (prefixWord ++ tailWord_5014973).sum := by decide
  have hdescent : baseEnd_5014973 < baseStart_5014973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014990 : List Nat := [4, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2]
def baseStart_5014990 : Nat := 118140960795 + 5014990 * 2 ^ 59
def prefixEnd_5014990 : Nat := 4983230072969 + 3 ^ 40 * 5014990 * 2
def baseEnd_5014990 : Nat := 2575100347491439062261487

theorem tailTrace_5014990 : CollatzResearch.WordTrace tailWord_5014990 prefixEnd_5014990 2575100347491439062261487 := by
  unfold tailWord_5014990
  simp only [CollatzResearch.WordTrace]
  refine ⟨22863964012694399618536303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121941141401036797965526949 22863964012694399618536303)
  ·
    refine ⟨34295946019041599427804455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22863964012694399618536303 34295946019041599427804455)
    ·
      refine ⟨51443919028562399141706683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34295946019041599427804455 51443919028562399141706683)
      ·
        refine ⟨77165878542843598712560025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51443919028562399141706683 77165878542843598712560025)
        ·
          refine ⟨57874408907132699034420019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77165878542843598712560025 57874408907132699034420019)
          ·
            refine ⟨86811613360699048551630029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57874408907132699034420019 86811613360699048551630029)
            ·
              refine ⟨32554355010262143206861261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86811613360699048551630029 32554355010262143206861261)
              ·
                refine ⟨12207883128848303702572973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32554355010262143206861261 12207883128848303702572973)
                ·
                  refine ⟨4577956173318113888464865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12207883128848303702572973 4577956173318113888464865)
                  ·
                    refine ⟨3433467129988585416348649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4577956173318113888464865 3433467129988585416348649)
                    ·
                      refine ⟨2575100347491439062261487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3433467129988585416348649 2575100347491439062261487)
                      ·
                        rfl

theorem cell23_5014990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_5014990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5014990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5014990 prefixEnd_5014990 := by exact prefixLift 5014990
  have htrace : WordTrace (prefixWord ++ tailWord_5014990) baseStart_5014990 baseEnd_5014990 := by
    simpa [prefixWord, tailWord_5014990, baseEnd_5014990] using wordTrace_append hprefix tailTrace_5014990
  have hstable : (prefixWord ++ tailWord_5014990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014990).length < 2 ^ (prefixWord ++ tailWord_5014990).sum := by decide
  have hdescent : baseEnd_5014990 < baseStart_5014990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015013 : List Nat := [1, 3, 1, 5, 1, 1, 4, 7]
def baseStart_5015013 : Nat := 118140960795 + 5015013 * 2 ^ 59
def prefixEnd_5015013 : Nat := 4983230072969 + 3 ^ 40 * 5015013 * 2
def baseEnd_5015013 : Nat := 95374524353573795269403

theorem tailTrace_5015013 : CollatzResearch.WordTrace tailWord_5015013 prefixEnd_5015013 95374524353573795269403 := by
  unfold tailWord_5015013
  simp only [CollatzResearch.WordTrace]
  refine ⟨182912550980471871876377693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121941700653647914584251795 182912550980471871876377693)
  ·
    refine ⟨68592206617676951953641635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182912550980471871876377693 68592206617676951953641635)
    ·
      refine ⟨102888309926515427930462453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68592206617676951953641635 102888309926515427930462453)
      ·
        refine ⟨9645779055610821368480855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102888309926515427930462453 9645779055610821368480855)
        ·
          refine ⟨14468668583416232052721283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9645779055610821368480855 14468668583416232052721283)
          ·
            refine ⟨21703002875124348079081925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14468668583416232052721283 21703002875124348079081925)
            ·
              refine ⟨4069313039085815264827861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21703002875124348079081925 4069313039085815264827861)
              ·
                refine ⟨95374524353573795269403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4069313039085815264827861 95374524353573795269403)
                ·
                  rfl

theorem cell23_5015013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 7].length) (baseStart_5015013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015013 prefixEnd_5015013 := by exact prefixLift 5015013
  have htrace : WordTrace (prefixWord ++ tailWord_5015013) baseStart_5015013 baseEnd_5015013 := by
    simpa [prefixWord, tailWord_5015013, baseEnd_5015013] using wordTrace_append hprefix tailTrace_5015013
  have hstable : (prefixWord ++ tailWord_5015013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015013).length < 2 ^ (prefixWord ++ tailWord_5015013).sum := by decide
  have hdescent : baseEnd_5015013 < baseStart_5015013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015023 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 4, 1, 3]
def baseStart_5015023 : Nat := 118140960795 + 5015023 * 2 ^ 59
def prefixEnd_5015023 : Nat := 4983230072969 + 3 ^ 40 * 5015023 * 2
def baseEnd_5015023 : Nat := 2575117292353037433148835

theorem tailTrace_5015023 : CollatzResearch.WordTrace tailWord_5015023 prefixEnd_5015023 2575117292353037433148835 := by
  unfold tailWord_5015023
  simp only [CollatzResearch.WordTrace]
  refine ⟨182912915710435643584241723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121941943806957095722827815 182912915710435643584241723)
  ·
    refine ⟨274369373565653465376362585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182912915710435643584241723 274369373565653465376362585)
    ·
      refine ⟨205777030174240099032271939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274369373565653465376362585 205777030174240099032271939)
      ·
        refine ⟨308665545261360148548407909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205777030174240099032271939 308665545261360148548407909)
        ·
          refine ⟨57874789736505027852826483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 308665545261360148548407909 57874789736505027852826483)
          ·
            refine ⟨86812184604757541779239725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57874789736505027852826483 86812184604757541779239725)
            ·
              refine ⟨32554569226784078167214897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86812184604757541779239725 32554569226784078167214897)
              ·
                refine ⟨24415926920088058625411173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32554569226784078167214897 24415926920088058625411173)
                ·
                  refine ⟨4577986297516510992264595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24415926920088058625411173 4577986297516510992264595)
                  ·
                    refine ⟨6866979446274766488396893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4577986297516510992264595 6866979446274766488396893)
                    ·
                      refine ⟨2575117292353037433148835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6866979446274766488396893 2575117292353037433148835)
                      ·
                        rfl

theorem cell23_5015023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 1, 3].length) (baseStart_5015023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015023 prefixEnd_5015023 := by exact prefixLift 5015023
  have htrace : WordTrace (prefixWord ++ tailWord_5015023) baseStart_5015023 baseEnd_5015023 := by
    simpa [prefixWord, tailWord_5015023, baseEnd_5015023] using wordTrace_append hprefix tailTrace_5015023
  have hstable : (prefixWord ++ tailWord_5015023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015023).length < 2 ^ (prefixWord ++ tailWord_5015023).sum := by decide
  have hdescent : baseEnd_5015023 < baseStart_5015023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015024 : List Nat := [2, 1, 1, 1, 3, 6, 1, 3, 1, 2, 2]
def baseStart_5015024 : Nat := 118140960795 + 5015024 * 2 ^ 59
def prefixEnd_5015024 : Nat := 4983230072969 + 3 ^ 40 * 5015024 * 2
def baseEnd_5015024 : Nat := 2575117805833691929236331

theorem tailTrace_5015024 : CollatzResearch.WordTrace tailWord_5015024 prefixEnd_5015024 2575117805833691929236331 := by
  unfold tailWord_5015024
  simp only [CollatzResearch.WordTrace]
  refine ⟨91456476091716010377514063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121941968122288013836685417 91456476091716010377514063)
  ·
    refine ⟨137184714137574015566271095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91456476091716010377514063 137184714137574015566271095)
    ·
      refine ⟨205777071206361023349406643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137184714137574015566271095 205777071206361023349406643)
      ·
        refine ⟨308665606809541535024109965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205777071206361023349406643 308665606809541535024109965)
        ·
          refine ⟨115749602553578075634041237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308665606809541535024109965 115749602553578075634041237)
          ·
            refine ⟨5425762619698972295345683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115749602553578075634041237 5425762619698972295345683)
            ·
              refine ⟨8138643929548458443018525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5425762619698972295345683 8138643929548458443018525)
              ·
                refine ⟨3051991473580671916131947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8138643929548458443018525 3051991473580671916131947)
                ·
                  refine ⟨4577987210371007874197921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3051991473580671916131947 4577987210371007874197921)
                  ·
                    refine ⟨3433490407778255905648441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4577987210371007874197921 3433490407778255905648441)
                    ·
                      refine ⟨2575117805833691929236331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3433490407778255905648441 2575117805833691929236331)
                      ·
                        rfl

theorem cell23_5015024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 1, 2, 2].length) (baseStart_5015024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015024 prefixEnd_5015024 := by exact prefixLift 5015024
  have htrace : WordTrace (prefixWord ++ tailWord_5015024) baseStart_5015024 baseEnd_5015024 := by
    simpa [prefixWord, tailWord_5015024, baseEnd_5015024] using wordTrace_append hprefix tailTrace_5015024
  have hstable : (prefixWord ++ tailWord_5015024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015024).length < 2 ^ (prefixWord ++ tailWord_5015024).sum := by decide
  have hdescent : baseEnd_5015024 < baseStart_5015024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015033 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 5, 3, 2]
def baseStart_5015033 : Nat := 118140960795 + 5015033 * 2 ^ 59
def prefixEnd_5015033 : Nat := 4983230072969 + 3 ^ 40 * 5015033 * 2
def baseEnd_5015033 : Nat := 2575122427159582394023789

theorem tailTrace_5015033 : CollatzResearch.WordTrace tailWord_5015033 prefixEnd_5015033 2575122427159582394023789 := by
  unfold tailWord_5015033
  simp only [CollatzResearch.WordTrace]
  refine ⟨182913280440399415292105753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121942186960266276861403835 182913280440399415292105753)
  ·
    refine ⟨137184960330299561469079315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182913280440399415292105753 137184960330299561469079315)
    ·
      refine ⟨205777440495449342203618973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137184960330299561469079315 205777440495449342203618973)
      ·
        refine ⟨77166540185793503326357115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205777440495449342203618973 77166540185793503326357115)
        ·
          refine ⟨115749810278690254989535673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77166540185793503326357115 115749810278690254989535673)
          ·
            refine ⟨86812357709017691242151755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115749810278690254989535673 86812357709017691242151755)
            ·
              refine ⟨130218536563526536863227633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86812357709017691242151755 130218536563526536863227633)
              ·
                refine ⟨97663902422644902647420725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130218536563526536863227633 97663902422644902647420725)
                ·
                  refine ⟨9155990852122959623195693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97663902422644902647420725 9155990852122959623195693)
                  ·
                    refine ⟨3433496569546109858698385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9155990852122959623195693 3433496569546109858698385)
                    ·
                      refine ⟨2575122427159582394023789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3433496569546109858698385 2575122427159582394023789)
                      ·
                        rfl

theorem cell23_5015033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_5015033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015033 prefixEnd_5015033 := by exact prefixLift 5015033
  have htrace : WordTrace (prefixWord ++ tailWord_5015033) baseStart_5015033 baseEnd_5015033 := by
    simpa [prefixWord, tailWord_5015033, baseEnd_5015033] using wordTrace_append hprefix tailTrace_5015033
  have hstable : (prefixWord ++ tailWord_5015033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015033).length < 2 ^ (prefixWord ++ tailWord_5015033).sum := by decide
  have hdescent : baseEnd_5015033 < baseStart_5015033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015041 : List Nat := [1, 2, 4, 1, 4, 1, 3, 2, 1, 2, 2]
def baseStart_5015041 : Nat := 118140960795 + 5015041 * 2 ^ 59
def prefixEnd_5015041 : Nat := 4983230072969 + 3 ^ 40 * 5015041 * 2
def baseEnd_5015041 : Nat := 2575126535004818362723753

theorem tailTrace_5015041 : CollatzResearch.WordTrace tailWord_5015041 prefixEnd_5015041 2575126535004818362723753 := by
  unfold tailWord_5015041
  simp only [CollatzResearch.WordTrace]
  refine ⟨182913572224370432658396977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121942381482913621772264651 182913572224370432658396977)
  ·
    refine ⟨137185179168277824493797733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182913572224370432658396977 137185179168277824493797733)
    ·
      refine ⟨25722221094052092092587075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137185179168277824493797733 25722221094052092092587075)
      ·
        refine ⟨38583331641078138138880613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25722221094052092092587075 38583331641078138138880613)
        ·
          refine ⟨7234374682702150901040115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38583331641078138138880613 7234374682702150901040115)
          ·
            refine ⟨10851562024053226351560173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7234374682702150901040115 10851562024053226351560173)
            ·
              refine ⟨4069335759019959881835065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10851562024053226351560173 4069335759019959881835065)
              ·
                refine ⟨3052001819264969911376299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4069335759019959881835065 3052001819264969911376299)
                ·
                  refine ⟨4578002728897454867064449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3052001819264969911376299 4578002728897454867064449)
                  ·
                    refine ⟨3433502046673091150298337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4578002728897454867064449 3433502046673091150298337)
                    ·
                      refine ⟨2575126535004818362723753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3433502046673091150298337 2575126535004818362723753)
                      ·
                        rfl

theorem cell23_5015041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_5015041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015041 prefixEnd_5015041 := by exact prefixLift 5015041
  have htrace : WordTrace (prefixWord ++ tailWord_5015041) baseStart_5015041 baseEnd_5015041 := by
    simpa [prefixWord, tailWord_5015041, baseEnd_5015041] using wordTrace_append hprefix tailTrace_5015041
  have hstable : (prefixWord ++ tailWord_5015041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015041).length < 2 ^ (prefixWord ++ tailWord_5015041).sum := by decide
  have hdescent : baseEnd_5015041 < baseStart_5015041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015097 : List Nat := [1, 2, 1, 5, 1, 2, 1, 4, 2, 2, 2]
def baseStart_5015097 : Nat := 118140960795 + 5015097 * 2 ^ 59
def prefixEnd_5015097 : Nat := 4983230072969 + 3 ^ 40 * 5015097 * 2
def baseEnd_5015097 : Nat := 2575155289921470143623495

theorem tailTrace_5015097 : CollatzResearch.WordTrace tailWord_5015097 prefixEnd_5015097 2575155289921470143623495 := by
  unfold tailWord_5015097
  simp only [CollatzResearch.WordTrace]
  refine ⟨182915614712167554222435545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121943743141445036148290363 182915614712167554222435545)
  ·
    refine ⟨137186711034125665666826659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182915614712167554222435545 137186711034125665666826659)
    ·
      refine ⟨205780066551188498500239989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137186711034125665666826659 205780066551188498500239989)
      ·
        refine ⟨19291881239173921734397499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 205780066551188498500239989 19291881239173921734397499)
        ·
          refine ⟨28937821858760882601596249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19291881239173921734397499 28937821858760882601596249)
          ·
            refine ⟨21703366394070661951197187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28937821858760882601596249 21703366394070661951197187)
            ·
              refine ⟨32555049591105992926795781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21703366394070661951197187 32555049591105992926795781)
              ·
                refine ⟨6104071798332373673774209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32555049591105992926795781 6104071798332373673774209)
                ·
                  refine ⟨4578053848749280255330657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6104071798332373673774209 4578053848749280255330657)
                  ·
                    refine ⟨3433540386561960191497993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4578053848749280255330657 3433540386561960191497993)
                    ·
                      refine ⟨2575155289921470143623495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3433540386561960191497993 2575155289921470143623495)
                      ·
                        rfl

theorem cell23_5015097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_5015097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015097 prefixEnd_5015097 := by exact prefixLift 5015097
  have htrace : WordTrace (prefixWord ++ tailWord_5015097) baseStart_5015097 baseEnd_5015097 := by
    simpa [prefixWord, tailWord_5015097, baseEnd_5015097] using wordTrace_append hprefix tailTrace_5015097
  have hstable : (prefixWord ++ tailWord_5015097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015097).length < 2 ^ (prefixWord ++ tailWord_5015097).sum := by decide
  have hdescent : baseEnd_5015097 < baseStart_5015097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015153 : List Nat := [1, 2, 2, 2, 1, 1, 1, 6, 2, 1, 4]
def baseStart_5015153 : Nat := 118140960795 + 5015153 * 2 ^ 59
def prefixEnd_5015153 : Nat := 4983230072969 + 3 ^ 40 * 5015153 * 2
def baseEnd_5015153 : Nat := 2575184044838121924523237

theorem tailTrace_5015153 : CollatzResearch.WordTrace tailWord_5015153 prefixEnd_5015153 2575184044838121924523237 := by
  unfold tailWord_5015153
  simp only [CollatzResearch.WordTrace]
  refine ⟨182917657199964675786474113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121945104799976450524316075 182917657199964675786474113)
  ·
    refine ⟨137188242899973506839855585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182917657199964675786474113 137188242899973506839855585)
    ·
      refine ⟨102891182174980130129891689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137188242899973506839855585 102891182174980130129891689)
      ·
        refine ⟨77168386631235097597418767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102891182174980130129891689 77168386631235097597418767)
        ·
          refine ⟨115752579946852646396128151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77168386631235097597418767 115752579946852646396128151)
          ·
            refine ⟨173628869920278969594192227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115752579946852646396128151 173628869920278969594192227)
            ·
              refine ⟨260443304880418454391288341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173628869920278969594192227 260443304880418454391288341)
              ·
                refine ⟨12208279916269615049591641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 260443304880418454391288341 12208279916269615049591641)
                ·
                  refine ⟨9156209937202211287193731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12208279916269615049591641 9156209937202211287193731)
                  ·
                    refine ⟨13734314905803316930790597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9156209937202211287193731 13734314905803316930790597)
                    ·
                      refine ⟨2575184044838121924523237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13734314905803316930790597 2575184044838121924523237)
                      ·
                        rfl

theorem cell23_5015153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_5015153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015153 prefixEnd_5015153 := by exact prefixLift 5015153
  have htrace : WordTrace (prefixWord ++ tailWord_5015153) baseStart_5015153 baseEnd_5015153 := by
    simpa [prefixWord, tailWord_5015153, baseEnd_5015153] using wordTrace_append hprefix tailTrace_5015153
  have hstable : (prefixWord ++ tailWord_5015153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015153).length < 2 ^ (prefixWord ++ tailWord_5015153).sum := by decide
  have hdescent : baseEnd_5015153 < baseStart_5015153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015173 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 3, 4, 3]
def baseStart_5015173 : Nat := 118140960795 + 5015173 * 2 ^ 59
def prefixEnd_5015173 : Nat := 4983230072969 + 3 ^ 40 * 5015173 * 2
def baseEnd_5015173 : Nat := 2575194314451211846273145

theorem tailTrace_5015173 : CollatzResearch.WordTrace tailWord_5015173 prefixEnd_5015173 2575194314451211846273145 := by
  unfold tailWord_5015173
  simp only [CollatzResearch.WordTrace]
  refine ⟨182918386659892219202202173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121945591106594812801468115 182918386659892219202202173)
  ·
    refine ⟨68594394997459582200825815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182918386659892219202202173 68594394997459582200825815)
    ·
      refine ⟨102891592496189373301238723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68594394997459582200825815 102891592496189373301238723)
      ·
        refine ⟨154337388744284059951858085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102891592496189373301238723 154337388744284059951858085)
        ·
          refine ⟨28938260389553261240973391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154337388744284059951858085 28938260389553261240973391)
          ·
            refine ⟨43407390584329891861460087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28938260389553261240973391 43407390584329891861460087)
            ·
              refine ⟨65111085876494837792190131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43407390584329891861460087 65111085876494837792190131)
              ·
                refine ⟨97666628814742256688285197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65111085876494837792190131 97666628814742256688285197)
                ·
                  refine ⟨36624985805528346258106949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97666628814742256688285197 36624985805528346258106949)
                  ·
                    refine ⟨6867184838536564923395053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36624985805528346258106949 6867184838536564923395053)
                    ·
                      refine ⟨2575194314451211846273145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6867184838536564923395053 2575194314451211846273145)
                      ·
                        rfl

theorem cell23_5015173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_5015173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015173 prefixEnd_5015173 := by exact prefixLift 5015173
  have htrace : WordTrace (prefixWord ++ tailWord_5015173) baseStart_5015173 baseEnd_5015173 := by
    simpa [prefixWord, tailWord_5015173, baseEnd_5015173] using wordTrace_append hprefix tailTrace_5015173
  have hstable : (prefixWord ++ tailWord_5015173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015173).length < 2 ^ (prefixWord ++ tailWord_5015173).sum := by decide
  have hdescent : baseEnd_5015173 < baseStart_5015173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015257 : List Nat := [1, 2, 1, 2, 3, 4, 3, 1, 1, 5]
def baseStart_5015257 : Nat := 118140960795 + 5015257 * 2 ^ 59
def prefixEnd_5015257 : Nat := 4983230072969 + 3 ^ 40 * 5015257 * 2
def baseEnd_5015257 : Nat := 858412482275396505874253

theorem tailTrace_5015257 : CollatzResearch.WordTrace tailWord_5015257 prefixEnd_5015257 858412482275396505874253 := by
  unfold tailWord_5015257
  simp only [CollatzResearch.WordTrace]
  refine ⟨182921450391587901548260025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121947633594391934365506683 182921450391587901548260025)
  ·
    refine ⟨137191087793690926161195019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182921450391587901548260025 137191087793690926161195019)
    ·
      refine ⟨205786631690536389241792529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137191087793690926161195019 205786631690536389241792529)
      ·
        refine ⟨154339973767902291931344397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205786631690536389241792529 154339973767902291931344397)
        ·
          refine ⟨57877490162963359474254149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154339973767902291931344397 57877490162963359474254149)
          ·
            refine ⟨10852029405555629901422653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57877490162963359474254149 10852029405555629901422653)
            ·
              refine ⟨4069511027083361213033495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10852029405555629901422653 4069511027083361213033495)
              ·
                refine ⟨6104266540625041819550243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4069511027083361213033495 6104266540625041819550243)
                ·
                  refine ⟨9156399810937562729325365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6104266540625041819550243 9156399810937562729325365)
                  ·
                    refine ⟨858412482275396505874253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9156399810937562729325365 858412482275396505874253)
                    ·
                      rfl

theorem cell23_5015257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 1, 5].length) (baseStart_5015257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015257 prefixEnd_5015257 := by exact prefixLift 5015257
  have htrace : WordTrace (prefixWord ++ tailWord_5015257) baseStart_5015257 baseEnd_5015257 := by
    simpa [prefixWord, tailWord_5015257, baseEnd_5015257] using wordTrace_append hprefix tailTrace_5015257
  have hstable : (prefixWord ++ tailWord_5015257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015257).length < 2 ^ (prefixWord ++ tailWord_5015257).sum := by decide
  have hdescent : baseEnd_5015257 < baseStart_5015257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015273 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 5, 2, 4]
def baseStart_5015273 : Nat := 118140960795 + 5015273 * 2 ^ 59
def prefixEnd_5015273 : Nat := 4983230072969 + 3 ^ 40 * 5015273 * 2
def baseEnd_5015273 : Nat := 2575245662516661455022685

theorem tailTrace_5015273 : CollatzResearch.WordTrace tailWord_5015273 prefixEnd_5015273 2575245662516661455022685 := by
  unfold tailWord_5015273
  simp only [CollatzResearch.WordTrace]
  refine ⟨182922033959529936280842473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121948022639686624187228315 182922033959529936280842473)
  ·
    refine ⟨137191525469647452210631855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182922033959529936280842473 137191525469647452210631855)
    ·
      refine ⟨205787288204471178315947783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137191525469647452210631855 205787288204471178315947783)
      ·
        refine ⟨308680932306706767473921675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205787288204471178315947783 308680932306706767473921675)
        ·
          refine ⟨463021398460060151210882513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308680932306706767473921675 463021398460060151210882513)
          ·
            refine ⟨347266048845045113408161885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 463021398460060151210882513 347266048845045113408161885)
            ·
              refine ⟨130224768316891917528060707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 347266048845045113408161885 130224768316891917528060707)
              ·
                refine ⟨195337152475337876292091061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130224768316891917528060707 195337152475337876292091061)
                ·
                  refine ⟨18312858044562925902383537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 195337152475337876292091061 18312858044562925902383537)
                  ·
                    refine ⟨13734643533422194426787653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18312858044562925902383537 13734643533422194426787653)
                    ·
                      refine ⟨2575245662516661455022685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13734643533422194426787653 2575245662516661455022685)
                      ·
                        rfl

theorem cell23_5015273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_5015273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015273 prefixEnd_5015273 := by exact prefixLift 5015273
  have htrace : WordTrace (prefixWord ++ tailWord_5015273) baseStart_5015273 baseEnd_5015273 := by
    simpa [prefixWord, tailWord_5015273, baseEnd_5015273] using wordTrace_append hprefix tailTrace_5015273
  have hstable : (prefixWord ++ tailWord_5015273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015273).length < 2 ^ (prefixWord ++ tailWord_5015273).sum := by decide
  have hdescent : baseEnd_5015273 < baseStart_5015273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015283 : List Nat := [1, 1, 1, 2, 2, 3, 5, 8]
def baseStart_5015283 : Nat := 118140960795 + 5015283 * 2 ^ 59
def prefixEnd_5015283 : Nat := 4983230072969 + 3 ^ 40 * 5015283 * 2
def baseEnd_5015283 : Nat := 95379659160118756144357

theorem tailTrace_5015283 : CollatzResearch.WordTrace tailWord_5015283 prefixEnd_5015283 95379659160118756144357 := by
  unfold tailWord_5015283
  simp only [CollatzResearch.WordTrace]
  refine ⟨182922398689493707988706503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121948265792995805325804335 182922398689493707988706503)
  ·
    refine ⟨274383598034240561983059755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182922398689493707988706503 274383598034240561983059755)
    ·
      refine ⟨411575397051360842974589633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274383598034240561983059755 411575397051360842974589633)
      ·
        refine ⟨308681547788520632230942225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 411575397051360842974589633 308681547788520632230942225)
        ·
          refine ⟨231511160841390474173206669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308681547788520632230942225 231511160841390474173206669)
          ·
            refine ⟨86816685315521427814952501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231511160841390474173206669 86816685315521427814952501)
            ·
              refine ⟨8139064248330133857651797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86816685315521427814952501 8139064248330133857651797)
              ·
                refine ⟨95379659160118756144357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8139064248330133857651797 95379659160118756144357)
                ·
                  rfl

theorem cell23_5015283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 8].length) (baseStart_5015283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015283 prefixEnd_5015283 := by exact prefixLift 5015283
  have htrace : WordTrace (prefixWord ++ tailWord_5015283) baseStart_5015283 baseEnd_5015283 := by
    simpa [prefixWord, tailWord_5015283, baseEnd_5015283] using wordTrace_append hprefix tailTrace_5015283
  have hstable : (prefixWord ++ tailWord_5015283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015283).length < 2 ^ (prefixWord ++ tailWord_5015283).sum := by decide
  have hdescent : baseEnd_5015283 < baseStart_5015283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015323 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 5]
def baseStart_5015323 : Nat := 118140960795 + 5015323 * 2 ^ 59
def prefixEnd_5015323 : Nat := 4983230072969 + 3 ^ 40 * 5015323 * 2
def baseEnd_5015323 : Nat := 2575271336549386259397455

theorem tailTrace_5015323 : CollatzResearch.WordTrace tailWord_5015323 prefixEnd_5015323 2575271336549386259397455 := by
  unfold tailWord_5015323
  simp only [CollatzResearch.WordTrace]
  refine ⟨182923857609348794820162623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121949238406232529880108415 182923857609348794820162623)
  ·
    refine ⟨274385786414023192230243935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182923857609348794820162623 274385786414023192230243935)
    ·
      refine ⟨411578679621034788345365903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274385786414023192230243935 411578679621034788345365903)
      ·
        refine ⟨617368019431552182518048855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411578679621034788345365903 617368019431552182518048855)
        ·
          refine ⟨926052029147328273777073283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617368019431552182518048855 926052029147328273777073283)
          ·
            refine ⟨1389078043720992410665609925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926052029147328273777073283 1389078043720992410665609925)
            ·
              refine ⟨260452133197686076999801861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1389078043720992410665609925 260452133197686076999801861)
              ·
                refine ⟨48834774974566139437462849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260452133197686076999801861 48834774974566139437462849)
                ·
                  refine ⟨36626081230924604578097137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48834774974566139437462849 36626081230924604578097137)
                  ·
                    refine ⟨27469560923193453433572853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36626081230924604578097137 27469560923193453433572853)
                    ·
                      refine ⟨2575271336549386259397455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27469560923193453433572853 2575271336549386259397455)
                      ·
                        rfl

theorem cell23_5015323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 5].length) (baseStart_5015323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015323 prefixEnd_5015323 := by exact prefixLift 5015323
  have htrace : WordTrace (prefixWord ++ tailWord_5015323) baseStart_5015323 baseEnd_5015323 := by
    simpa [prefixWord, tailWord_5015323, baseEnd_5015323] using wordTrace_append hprefix tailTrace_5015323
  have hstable : (prefixWord ++ tailWord_5015323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015323).length < 2 ^ (prefixWord ++ tailWord_5015323).sum := by decide
  have hdescent : baseEnd_5015323 < baseStart_5015323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015327 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 4, 1, 3]
def baseStart_5015327 : Nat := 118140960795 + 5015327 * 2 ^ 59
def prefixEnd_5015327 : Nat := 4983230072969 + 3 ^ 40 * 5015327 * 2
def baseEnd_5015327 : Nat := 2575273390472004243747437

theorem tailTrace_5015327 : CollatzResearch.WordTrace tailWord_5015327 prefixEnd_5015327 2575273390472004243747437 := by
  unfold tailWord_5015327
  simp only [CollatzResearch.WordTrace]
  refine ⟨182924003501334303503308235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121949335667556202335538823 182924003501334303503308235)
  ·
    refine ⟨274386005252001455254962353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182924003501334303503308235 274386005252001455254962353)
    ·
      refine ⟨205789503939001091441221765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274386005252001455254962353 205789503939001091441221765)
      ·
        refine ⟨38585531988562704645229081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205789503939001091441221765 38585531988562704645229081)
        ·
          refine ⟨28939148991422028483921811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38585531988562704645229081 28939148991422028483921811)
          ·
            refine ⟨43408723487133042725882717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28939148991422028483921811 43408723487133042725882717)
            ·
              refine ⟨16278271307674891022206019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43408723487133042725882717 16278271307674891022206019)
              ·
                refine ⟨24417406961512336533309029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16278271307674891022206019 24417406961512336533309029)
                ·
                  refine ⟨4578263805283563099995443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24417406961512336533309029 4578263805283563099995443)
                  ·
                    refine ⟨6867395707925344649993165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4578263805283563099995443 6867395707925344649993165)
                    ·
                      refine ⟨2575273390472004243747437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6867395707925344649993165 2575273390472004243747437)
                      ·
                        rfl

theorem cell23_5015327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_5015327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015327 prefixEnd_5015327 := by exact prefixLift 5015327
  have htrace : WordTrace (prefixWord ++ tailWord_5015327) baseStart_5015327 baseEnd_5015327 := by
    simpa [prefixWord, tailWord_5015327, baseEnd_5015327] using wordTrace_append hprefix tailTrace_5015327
  have hstable : (prefixWord ++ tailWord_5015327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015327).length < 2 ^ (prefixWord ++ tailWord_5015327).sum := by decide
  have hdescent : baseEnd_5015327 < baseStart_5015327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015354 : List Nat := [3, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2]
def baseStart_5015354 : Nat := 118140960795 + 5015354 * 2 ^ 59
def prefixEnd_5015354 : Nat := 4983230072969 + 3 ^ 40 * 5015354 * 2
def baseEnd_5015354 : Nat := 2575287254449675638109813

theorem tailTrace_5015354 : CollatzResearch.WordTrace tailWord_5015354 prefixEnd_5015354 2575287254449675638109813 := by
  unfold tailWord_5015354
  simp only [CollatzResearch.WordTrace]
  refine ⟨45731247068059121778635279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121949992181490991409694077 45731247068059121778635279)
  ·
    refine ⟨68596870602088682667952919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45731247068059121778635279 68596870602088682667952919)
    ·
      refine ⟨102895305903133024001929379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68596870602088682667952919 102895305903133024001929379)
      ·
        refine ⟨154342958854699536002894069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102895305903133024001929379 154342958854699536002894069)
        ·
          refine ⟨14469652392628081500271319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 154342958854699536002894069 14469652392628081500271319)
          ·
            refine ⟨21704478588942122250406979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14469652392628081500271319 21704478588942122250406979)
            ·
              refine ⟨32556717883413183375610469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21704478588942122250406979 32556717883413183375610469)
              ·
                refine ⟨6104384603139971882926963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32556717883413183375610469 6104384603139971882926963)
                ·
                  refine ⟨9156576904709957824390445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6104384603139971882926963 9156576904709957824390445)
                  ·
                    refine ⟨3433716339266234184146417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9156576904709957824390445 3433716339266234184146417)
                    ·
                      refine ⟨2575287254449675638109813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3433716339266234184146417 2575287254449675638109813)
                      ·
                        rfl

theorem cell23_5015354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2].length) (baseStart_5015354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015354 prefixEnd_5015354 := by exact prefixLift 5015354
  have htrace : WordTrace (prefixWord ++ tailWord_5015354) baseStart_5015354 baseEnd_5015354 := by
    simpa [prefixWord, tailWord_5015354, baseEnd_5015354] using wordTrace_append hprefix tailTrace_5015354
  have hstable : (prefixWord ++ tailWord_5015354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015354).length < 2 ^ (prefixWord ++ tailWord_5015354).sum := by decide
  have hdescent : baseEnd_5015354 < baseStart_5015354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015367 : List Nat := [1, 1, 4, 1, 2, 1, 2, 4, 1, 4, 2]
def baseStart_5015367 : Nat := 118140960795 + 5015367 * 2 ^ 59
def prefixEnd_5015367 : Nat := 4983230072969 + 3 ^ 40 * 5015367 * 2
def baseEnd_5015367 : Nat := 2575293929698184087247253

theorem tailTrace_5015367 : CollatzResearch.WordTrace tailWord_5015367 prefixEnd_5015367 2575293929698184087247253 := by
  unfold tailWord_5015367
  simp only [CollatzResearch.WordTrace]
  refine ⟨182925462421189390334764355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121950308280792926889842903 182925462421189390334764355)
  ·
    refine ⟨274388193631784085502146533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182925462421189390334764355 274388193631784085502146533)
    ·
      refine ⟨51447786305959516031652475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 274388193631784085502146533 51447786305959516031652475)
      ·
        refine ⟨77171679458939274047478713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51447786305959516031652475 77171679458939274047478713)
        ·
          refine ⟨57878759594204455535609035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77171679458939274047478713 57878759594204455535609035)
          ·
            refine ⟨86818139391306683303413553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57878759594204455535609035 86818139391306683303413553)
            ·
              refine ⟨65113604543480012477560165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86818139391306683303413553 65113604543480012477560165)
              ·
                refine ⟨12208800851902502339542531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65113604543480012477560165 12208800851902502339542531)
                ·
                  refine ⟨18313201277853753509313797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12208800851902502339542531 18313201277853753509313797)
                  ·
                    refine ⟨3433725239597578782996337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18313201277853753509313797 3433725239597578782996337)
                    ·
                      refine ⟨2575293929698184087247253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3433725239597578782996337 2575293929698184087247253)
                      ·
                        rfl

theorem cell23_5015367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_5015367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015367 prefixEnd_5015367 := by exact prefixLift 5015367
  have htrace : WordTrace (prefixWord ++ tailWord_5015367) baseStart_5015367 baseEnd_5015367 := by
    simpa [prefixWord, tailWord_5015367, baseEnd_5015367] using wordTrace_append hprefix tailTrace_5015367
  have hstable : (prefixWord ++ tailWord_5015367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015367).length < 2 ^ (prefixWord ++ tailWord_5015367).sum := by decide
  have hdescent : baseEnd_5015367 < baseStart_5015367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015370 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_5015370 : Nat := 118140960795 + 5015370 * 2 ^ 59
def prefixEnd_5015370 : Nat := 4983230072969 + 3 ^ 40 * 5015370 * 2
def baseEnd_5015370 : Nat := 2575295470140147575509739

theorem tailTrace_5015370 : CollatzResearch.WordTrace tailWord_5015370 prefixEnd_5015370 2575295470140147575509739 := by
  unfold tailWord_5015370
  simp only [CollatzResearch.WordTrace]
  refine ⟨45731392960044630461780891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121950381226785681231415709 45731392960044630461780891)
  ·
    refine ⟨68597089440066945692671337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45731392960044630461780891 68597089440066945692671337)
    ·
      refine ⟨51447817080050209269503503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68597089440066945692671337 51447817080050209269503503)
      ·
        refine ⟨77171725620075313904255255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51447817080050209269503503 77171725620075313904255255)
        ·
          refine ⟨115757588430112970856382883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77171725620075313904255255 115757588430112970856382883)
          ·
            refine ⟨173636382645169456284574325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115757588430112970856382883 173636382645169456284574325)
            ·
              refine ⟨16278410872984636526678843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 173636382645169456284574325 16278410872984636526678843)
              ·
                refine ⟨24417616309476954790018265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16278410872984636526678843 24417616309476954790018265)
                ·
                  refine ⟨18313212232107716092513699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24417616309476954790018265 18313212232107716092513699)
                  ·
                    refine ⟨27469818348161574138770549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18313212232107716092513699 27469818348161574138770549)
                    ·
                      refine ⟨2575295470140147575509739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27469818348161574138770549 2575295470140147575509739)
                      ·
                        rfl

theorem cell23_5015370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_5015370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015370 prefixEnd_5015370 := by exact prefixLift 5015370
  have htrace : WordTrace (prefixWord ++ tailWord_5015370) baseStart_5015370 baseEnd_5015370 := by
    simpa [prefixWord, tailWord_5015370, baseEnd_5015370] using wordTrace_append hprefix tailTrace_5015370
  have hstable : (prefixWord ++ tailWord_5015370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015370).length < 2 ^ (prefixWord ++ tailWord_5015370).sum := by decide
  have hdescent : baseEnd_5015370 < baseStart_5015370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015444 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_5015444 : Nat := 118140960795 + 5015444 * 2 ^ 59
def prefixEnd_5015444 : Nat := 4983230072969 + 3 ^ 40 * 5015444 * 2
def baseEnd_5015444 : Nat := 2575333467708580285984399

theorem tailTrace_5015444 : CollatzResearch.WordTrace tailWord_5015444 prefixEnd_5015444 2575333467708580285984399 := by
  unfold tailWord_5015444
  simp only [CollatzResearch.WordTrace]
  refine ⟨91464135420955216242658693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121952180561273621656878257 91464135420955216242658693)
  ·
    refine ⟨17149525391429103045498505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91464135420955216242658693 17149525391429103045498505)
    ·
      refine ⟨12862144043571827284123879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17149525391429103045498505 12862144043571827284123879)
      ·
        refine ⟨19293216065357740926185819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12862144043571827284123879 19293216065357740926185819)
        ·
          refine ⟨28939824098036611389278729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19293216065357740926185819 28939824098036611389278729)
          ·
            refine ⟨21704868073527458541959047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28939824098036611389278729 21704868073527458541959047)
            ·
              refine ⟨32557302110291187812938571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21704868073527458541959047 32557302110291187812938571)
              ·
                refine ⟨48835953165436781719407857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32557302110291187812938571 48835953165436781719407857)
                ·
                  refine ⟨36626964874077586289555893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48835953165436781719407857 36626964874077586289555893)
                  ·
                    refine ⟨3433777956944773714645865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36626964874077586289555893 3433777956944773714645865)
                    ·
                      refine ⟨2575333467708580285984399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3433777956944773714645865 2575333467708580285984399)
                      ·
                        rfl

theorem cell23_5015444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_5015444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015444 prefixEnd_5015444 := by exact prefixLift 5015444
  have htrace : WordTrace (prefixWord ++ tailWord_5015444) baseStart_5015444 baseEnd_5015444 := by
    simpa [prefixWord, tailWord_5015444, baseEnd_5015444] using wordTrace_append hprefix tailTrace_5015444
  have hstable : (prefixWord ++ tailWord_5015444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015444).length < 2 ^ (prefixWord ++ tailWord_5015444).sum := by decide
  have hdescent : baseEnd_5015444 < baseStart_5015444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015480 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 8]
def baseStart_5015480 : Nat := 118140960795 + 5015480 * 2 ^ 59
def prefixEnd_5015480 : Nat := 4983230072969 + 3 ^ 40 * 5015480 * 2
def baseEnd_5015480 : Nat := 286150217001349127237137

theorem tailTrace_5015480 : CollatzResearch.WordTrace tailWord_5015480 prefixEnd_5015480 286150217001349127237137 := by
  unfold tailWord_5015480
  simp only [CollatzResearch.WordTrace]
  refine ⟨91464791934890005316813947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121953055913186673755751929 91464791934890005316813947)
  ·
    refine ⟨137197187902335007975220921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91464791934890005316813947 137197187902335007975220921)
    ·
      refine ⟨102897890926751255981415691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137197187902335007975220921 102897890926751255981415691)
      ·
        refine ⟨154346836390126883972123537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102897890926751255981415691 154346836390126883972123537)
        ·
          refine ⟨115760127292595162979092653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154346836390126883972123537 115760127292595162979092653)
          ·
            refine ⟨43410047734723186117159745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115760127292595162979092653 43410047734723186117159745)
            ·
              refine ⟨32557535801042389587869809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43410047734723186117159745 32557535801042389587869809)
              ·
                refine ⟨24418151850781792190902357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32557535801042389587869809 24418151850781792190902357)
                ·
                  refine ⟨286150217001349127237137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24418151850781792190902357 286150217001349127237137)
                  ·
                    rfl

theorem cell23_5015480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 8].length) (baseStart_5015480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015480 prefixEnd_5015480 := by exact prefixLift 5015480
  have htrace : WordTrace (prefixWord ++ tailWord_5015480) baseStart_5015480 baseEnd_5015480 := by
    simpa [prefixWord, tailWord_5015480, baseEnd_5015480] using wordTrace_append hprefix tailTrace_5015480
  have hstable : (prefixWord ++ tailWord_5015480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015480).length < 2 ^ (prefixWord ++ tailWord_5015480).sum := by decide
  have hdescent : baseEnd_5015480 < baseStart_5015480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015520 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 7]
def baseStart_5015520 : Nat := 118140960795 + 5015520 * 2 ^ 59
def prefixEnd_5015520 : Nat := 4983230072969 + 3 ^ 40 * 5015520 * 2
def baseEnd_5015520 : Nat := 2575372492238321988634049

theorem tailTrace_5015520 : CollatzResearch.WordTrace tailWord_5015520 prefixEnd_5015520 2575372492238321988634049 := by
  unfold tailWord_5015520
  simp only [CollatzResearch.WordTrace]
  refine ⟨91465521394817548732542007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121954028526423398310056009 91465521394817548732542007)
  ·
    refine ⟨137198282092226323098813011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91465521394817548732542007 137198282092226323098813011)
    ·
      refine ⟨205797423138339484648219517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137198282092226323098813011 205797423138339484648219517)
      ·
        refine ⟨77174033676877306743082319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205797423138339484648219517 77174033676877306743082319)
        ·
          refine ⟨115761050515315960114623479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77174033676877306743082319 115761050515315960114623479)
          ·
            refine ⟨173641575772973940171935219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115761050515315960114623479 173641575772973940171935219)
            ·
              refine ⟨260462363659460910257902829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173641575772973940171935219 260462363659460910257902829)
              ·
                refine ⟨97673386372297841346713561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260462363659460910257902829 97673386372297841346713561)
                ·
                  refine ⟨73255039779223381010035171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97673386372297841346713561 73255039779223381010035171)
                  ·
                    refine ⟨109882559668835071515052757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73255039779223381010035171 109882559668835071515052757)
                    ·
                      refine ⟨2575372492238321988634049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109882559668835071515052757 2575372492238321988634049)
                      ·
                        rfl

theorem cell23_5015520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_5015520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015520 prefixEnd_5015520 := by exact prefixLift 5015520
  have htrace : WordTrace (prefixWord ++ tailWord_5015520) baseStart_5015520 baseEnd_5015520 := by
    simpa [prefixWord, tailWord_5015520, baseEnd_5015520] using wordTrace_append hprefix tailTrace_5015520
  have hstable : (prefixWord ++ tailWord_5015520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015520).length < 2 ^ (prefixWord ++ tailWord_5015520).sum := by decide
  have hdescent : baseEnd_5015520 < baseStart_5015520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015524 : List Nat := [2, 3, 1, 1, 1, 1, 3, 4, 3, 1, 3]
def baseStart_5015524 : Nat := 118140960795 + 5015524 * 2 ^ 59
def prefixEnd_5015524 : Nat := 4983230072969 + 3 ^ 40 * 5015524 * 2
def baseEnd_5015524 : Nat := 2575374546160939972984031

theorem tailTrace_5015524 : CollatzResearch.WordTrace tailWord_5015524 prefixEnd_5015524 2575374546160939972984031 := by
  unfold tailWord_5015524
  simp only [CollatzResearch.WordTrace]
  refine ⟨91465594340810303074114813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121954125787747070765486417 91465594340810303074114813)
  ·
    refine ⟨34299597877803863652793055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91465594340810303074114813 34299597877803863652793055)
    ·
      refine ⟨51449396816705795479189583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34299597877803863652793055 51449396816705795479189583)
      ·
        refine ⟨77174095225058693218784375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51449396816705795479189583 77174095225058693218784375)
        ·
          refine ⟨115761142837588039828176563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77174095225058693218784375 115761142837588039828176563)
          ·
            refine ⟨173641714256382059742264845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115761142837588039828176563 173641714256382059742264845)
            ·
              refine ⟨65115642846143272403349317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173641714256382059742264845 65115642846143272403349317)
              ·
                refine ⟨12209183033651863575627997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65115642846143272403349317 12209183033651863575627997)
                ·
                  refine ⟨4578443637619448840860499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12209183033651863575627997 4578443637619448840860499)
                  ·
                    refine ⟨6867665456429173261290749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4578443637619448840860499 6867665456429173261290749)
                    ·
                      refine ⟨2575374546160939972984031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6867665456429173261290749 2575374546160939972984031)
                      ·
                        rfl

theorem cell23_5015524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_5015524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015524 prefixEnd_5015524 := by exact prefixLift 5015524
  have htrace : WordTrace (prefixWord ++ tailWord_5015524) baseStart_5015524 baseEnd_5015524 := by
    simpa [prefixWord, tailWord_5015524, baseEnd_5015524] using wordTrace_append hprefix tailTrace_5015524
  have hstable : (prefixWord ++ tailWord_5015524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015524).length < 2 ^ (prefixWord ++ tailWord_5015524).sum := by decide
  have hdescent : baseEnd_5015524 < baseStart_5015524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015577 : List Nat := [1, 2, 1, 2, 1, 1, 3, 5, 1, 2, 4]
def baseStart_5015577 : Nat := 118140960795 + 5015577 * 2 ^ 59
def prefixEnd_5015577 : Nat := 4983230072969 + 3 ^ 40 * 5015577 * 2
def baseEnd_5015577 : Nat := 2575401760635628265621287

theorem tailTrace_5015577 : CollatzResearch.WordTrace tailWord_5015577 prefixEnd_5015577 2575401760635628265621287 := by
  unfold tailWord_5015577
  simp only [CollatzResearch.WordTrace]
  refine ⟨182933121750428596199908985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121955414500285730799939323 182933121750428596199908985)
  ·
    refine ⟨137199841312821447149931739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182933121750428596199908985 137199841312821447149931739)
    ·
      refine ⟨205799761969232170724897609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137199841312821447149931739 205799761969232170724897609)
      ·
        refine ⟨154349821476924128043673207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205799761969232170724897609 154349821476924128043673207)
        ·
          refine ⟨231524732215386192065509811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154349821476924128043673207 231524732215386192065509811)
          ·
            refine ⟨347287098323079288098264717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231524732215386192065509811 347287098323079288098264717)
            ·
              refine ⟨130232661871154733036849269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 347287098323079288098264717 130232661871154733036849269)
              ·
                refine ⟨12209312050420756222204619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 130232661871154733036849269 12209312050420756222204619)
                ·
                  refine ⟨18313968075631134333306929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12209312050420756222204619 18313968075631134333306929)
                  ·
                    refine ⟨13735476056723350749980197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18313968075631134333306929 13735476056723350749980197)
                    ·
                      refine ⟨2575401760635628265621287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13735476056723350749980197 2575401760635628265621287)
                      ·
                        rfl

theorem cell23_5015577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_5015577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015577 prefixEnd_5015577 := by exact prefixLift 5015577
  have htrace : WordTrace (prefixWord ++ tailWord_5015577) baseStart_5015577 baseEnd_5015577 := by
    simpa [prefixWord, tailWord_5015577, baseEnd_5015577] using wordTrace_append hprefix tailTrace_5015577
  have hstable : (prefixWord ++ tailWord_5015577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015577).length < 2 ^ (prefixWord ++ tailWord_5015577).sum := by decide
  have hdescent : baseEnd_5015577 < baseStart_5015577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015581 : List Nat := [1, 4, 2, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_5015581 : Nat := 118140960795 + 5015581 * 2 ^ 59
def prefixEnd_5015581 : Nat := 4983230072969 + 3 ^ 40 * 5015581 * 2
def baseEnd_5015581 : Nat := 2575403814558246249971269

theorem tailTrace_5015581 : CollatzResearch.WordTrace tailWord_5015581 prefixEnd_5015581 2575403814558246249971269 := by
  unfold tailWord_5015581
  simp only [CollatzResearch.WordTrace]
  refine ⟨182933267642414104883054597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121955511761609403255369731 182933267642414104883054597)
  ·
    refine ⟨34299987682952644665572737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182933267642414104883054597 34299987682952644665572737)
    ·
      refine ⟨25724990762214483499179553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34299987682952644665572737 25724990762214483499179553)
      ·
        refine ⟨19293743071660862624384665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25724990762214483499179553 19293743071660862624384665)
        ·
          refine ⟨14470307303745646968288499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19293743071660862624384665 14470307303745646968288499)
          ·
            refine ⟨21705460955618470452432749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14470307303745646968288499 21705460955618470452432749)
            ·
              refine ⟨8139547858356926419662281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21705460955618470452432749 8139547858356926419662281)
              ·
                refine ⟨6104660893767694814746711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8139547858356926419662281 6104660893767694814746711)
                ·
                  refine ⟨9156991340651542222120067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6104660893767694814746711 9156991340651542222120067)
                  ·
                    refine ⟨13735487010977313333180101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9156991340651542222120067 13735487010977313333180101)
                    ·
                      refine ⟨2575403814558246249971269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13735487010977313333180101 2575403814558246249971269)
                      ·
                        rfl

theorem cell23_5015581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_5015581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015581 prefixEnd_5015581 := by exact prefixLift 5015581
  have htrace : WordTrace (prefixWord ++ tailWord_5015581) baseStart_5015581 baseEnd_5015581 := by
    simpa [prefixWord, tailWord_5015581, baseEnd_5015581] using wordTrace_append hprefix tailTrace_5015581
  have hstable : (prefixWord ++ tailWord_5015581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015581).length < 2 ^ (prefixWord ++ tailWord_5015581).sum := by decide
  have hdescent : baseEnd_5015581 < baseStart_5015581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015591 : List Nat := [1, 1, 7, 1, 2, 1, 1, 2, 1, 6]
def baseStart_5015591 : Nat := 118140960795 + 5015591 * 2 ^ 59
def prefixEnd_5015591 : Nat := 4983230072969 + 3 ^ 40 * 5015591 * 2
def baseEnd_5015591 : Nat := 858469649788263736948741

theorem tailTrace_5015591 : CollatzResearch.WordTrace tailWord_5015591 prefixEnd_5015591 858469649788263736948741 := by
  unfold tailWord_5015591
  simp only [CollatzResearch.WordTrace]
  refine ⟨182933632372377876590918627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121955754914918584393945751 182933632372377876590918627)
  ·
    refine ⟨274400448558566814886377941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182933632372377876590918627 274400448558566814886377941)
    ·
      refine ⟨6431260513091409723899483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 274400448558566814886377941 6431260513091409723899483)
      ·
        refine ⟨9646890769637114585849225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6431260513091409723899483 9646890769637114585849225)
        ·
          refine ⟨7235168077227835939386919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9646890769637114585849225 7235168077227835939386919)
          ·
            refine ⟨10852752115841753909080379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7235168077227835939386919 10852752115841753909080379)
            ·
              refine ⟨16279128173762630863620569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10852752115841753909080379 16279128173762630863620569)
              ·
                refine ⟨12209346130321973147715427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16279128173762630863620569 12209346130321973147715427)
                ·
                  refine ⟨18314019195482959721573141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12209346130321973147715427 18314019195482959721573141)
                  ·
                    refine ⟨858469649788263736948741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18314019195482959721573141 858469649788263736948741)
                    ·
                      rfl

theorem cell23_5015591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_5015591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015591 prefixEnd_5015591 := by exact prefixLift 5015591
  have htrace : WordTrace (prefixWord ++ tailWord_5015591) baseStart_5015591 baseEnd_5015591 := by
    simpa [prefixWord, tailWord_5015591, baseEnd_5015591] using wordTrace_append hprefix tailTrace_5015591
  have hstable : (prefixWord ++ tailWord_5015591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015591).length < 2 ^ (prefixWord ++ tailWord_5015591).sum := by decide
  have hdescent : baseEnd_5015591 < baseStart_5015591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015594 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_5015594 : Nat := 118140960795 + 5015594 * 2 ^ 59
def prefixEnd_5015594 : Nat := 4983230072969 + 3 ^ 40 * 5015594 * 2
def baseEnd_5015594 : Nat := 2575410489806754699108709

theorem tailTrace_5015594 : CollatzResearch.WordTrace tailWord_5015594 prefixEnd_5015594 2575410489806754699108709 := by
  unfold tailWord_5015594
  simp only [CollatzResearch.WordTrace]
  refine ⟨45733435447841752025819459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121955827860911338735518557 45733435447841752025819459)
  ·
    refine ⟨68600153171762628038729189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45733435447841752025819459 68600153171762628038729189)
    ·
      refine ⟨12862528719705492757261723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68600153171762628038729189 12862528719705492757261723)
      ·
        refine ⟨19293793079558239135892585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12862528719705492757261723 19293793079558239135892585)
        ·
          refine ⟨14470344809668679351919439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19293793079558239135892585 14470344809668679351919439)
          ·
            refine ⟨21705517214503019027879159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14470344809668679351919439 21705517214503019027879159)
            ·
              refine ⟨32558275821754528541818739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21705517214503019027879159 32558275821754528541818739)
              ·
                refine ⟨48837413732631792812728109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32558275821754528541818739 48837413732631792812728109)
                ·
                  refine ⟨18314030149736922304773041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48837413732631792812728109 18314030149736922304773041)
                  ·
                    refine ⟨13735522612302691728579781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18314030149736922304773041 13735522612302691728579781)
                    ·
                      refine ⟨2575410489806754699108709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13735522612302691728579781 2575410489806754699108709)
                      ·
                        rfl

theorem cell23_5015594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_5015594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015594 prefixEnd_5015594 := by exact prefixLift 5015594
  have htrace : WordTrace (prefixWord ++ tailWord_5015594) baseStart_5015594 baseEnd_5015594 := by
    simpa [prefixWord, tailWord_5015594, baseEnd_5015594] using wordTrace_append hprefix tailTrace_5015594
  have hstable : (prefixWord ++ tailWord_5015594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015594).length < 2 ^ (prefixWord ++ tailWord_5015594).sum := by decide
  have hdescent : baseEnd_5015594 < baseStart_5015594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015598 : List Nat := [4, 1, 3, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_5015598 : Nat := 118140960795 + 5015598 * 2 ^ 59
def prefixEnd_5015598 : Nat := 4983230072969 + 3 ^ 40 * 5015598 * 2
def baseEnd_5015598 : Nat := 2575412543729372683458691

theorem tailTrace_5015598 : CollatzResearch.WordTrace tailWord_5015598 prefixEnd_5015598 2575412543729372683458691 := by
  unfold tailWord_5015598
  simp only [CollatzResearch.WordTrace]
  refine ⟨22866735960419064598302931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121955925122235011190948965 22866735960419064598302931)
  ·
    refine ⟨34300103940628596897454397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22866735960419064598302931 34300103940628596897454397)
    ·
      refine ⟨12862538977735723836545399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34300103940628596897454397 12862538977735723836545399)
      ·
        refine ⟨19293808466603585754818099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12862538977735723836545399 19293808466603585754818099)
        ·
          refine ⟨28940712699905378632227149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19293808466603585754818099 28940712699905378632227149)
          ·
            refine ⟨10852767262464516987085181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28940712699905378632227149 10852767262464516987085181)
            ·
              refine ⟨4069787723424193870156943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10852767262464516987085181 4069787723424193870156943)
              ·
                refine ⟨6104681585136290805235415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4069787723424193870156943 6104681585136290805235415)
                ·
                  refine ⟨9157022377704436207853123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6104681585136290805235415 9157022377704436207853123)
                  ·
                    refine ⟨13735533566556654311779685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9157022377704436207853123 13735533566556654311779685)
                    ·
                      refine ⟨2575412543729372683458691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13735533566556654311779685 2575412543729372683458691)
                      ·
                        rfl

theorem cell23_5015598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_5015598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015598 prefixEnd_5015598 := by exact prefixLift 5015598
  have htrace : WordTrace (prefixWord ++ tailWord_5015598) baseStart_5015598 baseEnd_5015598 := by
    simpa [prefixWord, tailWord_5015598, baseEnd_5015598] using wordTrace_append hprefix tailTrace_5015598
  have hstable : (prefixWord ++ tailWord_5015598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015598).length < 2 ^ (prefixWord ++ tailWord_5015598).sum := by decide
  have hdescent : baseEnd_5015598 < baseStart_5015598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015604 : List Nat := [2, 5, 1, 2, 2, 11]
def baseStart_5015604 : Nat := 118140960795 + 5015604 * 2 ^ 59
def prefixEnd_5015604 : Nat := 4983230072969 + 3 ^ 40 * 5015604 * 2
def baseEnd_5015604 : Nat := 10598418208285183785941

theorem tailTrace_5015604 : CollatzResearch.WordTrace tailWord_5015604 prefixEnd_5015604 10598418208285183785941 := by
  unfold tailWord_5015604
  simp only [CollatzResearch.WordTrace]
  refine ⟨91467053260665389905570933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121956071014220519874094577 91467053260665389905570933)
  ·
    refine ⟨8575036243187380303647275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91467053260665389905570933 8575036243187380303647275)
    ·
      refine ⟨12862554364781070455470913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8575036243187380303647275 12862554364781070455470913)
      ·
        refine ⟨9646915773585802841603185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12862554364781070455470913 9646915773585802841603185)
        ·
          refine ⟨7235186830189352131202389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9646915773585802841603185 7235186830189352131202389)
          ·
            refine ⟨10598418208285183785941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7235186830189352131202389 10598418208285183785941)
            ·
              rfl

theorem cell23_5015604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 11].length) (baseStart_5015604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015604 prefixEnd_5015604 := by exact prefixLift 5015604
  have htrace : WordTrace (prefixWord ++ tailWord_5015604) baseStart_5015604 baseEnd_5015604 := by
    simpa [prefixWord, tailWord_5015604, baseEnd_5015604] using wordTrace_append hprefix tailTrace_5015604
  have hstable : (prefixWord ++ tailWord_5015604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015604).length < 2 ^ (prefixWord ++ tailWord_5015604).sum := by decide
  have hdescent : baseEnd_5015604 < baseStart_5015604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015615 : List Nat := [1, 1, 2, 2, 3, 1, 6, 2, 1, 2, 2]
def baseStart_5015615 : Nat := 118140960795 + 5015615 * 2 ^ 59
def prefixEnd_5015615 : Nat := 4983230072969 + 3 ^ 40 * 5015615 * 2
def baseEnd_5015615 : Nat := 2575421272900499116946113

theorem tailTrace_5015615 : CollatzResearch.WordTrace tailWord_5015615 prefixEnd_5015615 2575421272900499116946113 := by
  unfold tailWord_5015615
  simp only [CollatzResearch.WordTrace]
  refine ⟨182934507724290928689792299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121956338482860619126528199 182934507724290928689792299)
  ·
    refine ⟨274401761586436393034688449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182934507724290928689792299 274401761586436393034688449)
    ·
      refine ⟨205801321189827294776016337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274401761586436393034688449 205801321189827294776016337)
      ·
        refine ⟨154350990892370471082012253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205801321189827294776016337 154350990892370471082012253)
        ·
          refine ⟨57881621584638926655754595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154350990892370471082012253 57881621584638926655754595)
          ·
            refine ⟨86822432376958389983631893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57881621584638926655754595 86822432376958389983631893)
            ·
              refine ⟨4069801517669924530482745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86822432376958389983631893 4069801517669924530482745)
              ·
                refine ⟨3052351138252443397862059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4069801517669924530482745 3052351138252443397862059)
                ·
                  refine ⟨4578526707378665096793089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3052351138252443397862059 4578526707378665096793089)
                  ·
                    refine ⟨3433895030533998822594817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4578526707378665096793089 3433895030533998822594817)
                    ·
                      refine ⟨2575421272900499116946113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3433895030533998822594817 2575421272900499116946113)
                      ·
                        rfl

theorem cell23_5015615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 1, 2, 2].length) (baseStart_5015615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015615 prefixEnd_5015615 := by exact prefixLift 5015615
  have htrace : WordTrace (prefixWord ++ tailWord_5015615) baseStart_5015615 baseEnd_5015615 := by
    simpa [prefixWord, tailWord_5015615, baseEnd_5015615] using wordTrace_append hprefix tailTrace_5015615
  have hstable : (prefixWord ++ tailWord_5015615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015615).length < 2 ^ (prefixWord ++ tailWord_5015615).sum := by decide
  have hdescent : baseEnd_5015615 < baseStart_5015615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015638 : List Nat := [5, 2, 2, 1, 1, 2, 3, 7]
def baseStart_5015638 : Nat := 118140960795 + 5015638 * 2 ^ 59
def prefixEnd_5015638 : Nat := 4983230072969 + 3 ^ 40 * 5015638 * 2
def baseEnd_5015638 : Nat := 95386410479835278776241

theorem tailTrace_5015638 : CollatzResearch.WordTrace tailWord_5015638 prefixEnd_5015638 95386410479835278776241 := by
  unfold tailWord_5015638
  simp only [CollatzResearch.WordTrace]
  refine ⟨11433459162700475226117473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121956897735471735745253045 11433459162700475226117473)
  ·
    refine ⟨8575094372025356419588105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11433459162700475226117473 8575094372025356419588105)
    ·
      refine ⟨6431320779019017314691079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8575094372025356419588105 6431320779019017314691079)
      ·
        refine ⟨9646981168528525972036619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6431320779019017314691079 9646981168528525972036619)
        ·
          refine ⟨14470471752792788958054929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9646981168528525972036619 14470471752792788958054929)
          ·
            refine ⟨10852853814594591718541197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14470471752792788958054929 10852853814594591718541197)
            ·
              refine ⟨4069820180472971894452949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10852853814594591718541197 4069820180472971894452949)
              ·
                refine ⟨95386410479835278776241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4069820180472971894452949 95386410479835278776241)
                ·
                  rfl

theorem cell23_5015638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_5015638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015638 prefixEnd_5015638 := by exact prefixLift 5015638
  have htrace : WordTrace (prefixWord ++ tailWord_5015638) baseStart_5015638 baseEnd_5015638 := by
    simpa [prefixWord, tailWord_5015638, baseEnd_5015638] using wordTrace_append hprefix tailTrace_5015638
  have hstable : (prefixWord ++ tailWord_5015638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015638).length < 2 ^ (prefixWord ++ tailWord_5015638).sum := by decide
  have hdescent : baseEnd_5015638 < baseStart_5015638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015641 : List Nat := [1, 2, 1, 2, 2, 1, 4, 4, 1, 3, 2]
def baseStart_5015641 : Nat := 118140960795 + 5015641 * 2 ^ 59
def prefixEnd_5015641 : Nat := 4983230072969 + 3 ^ 40 * 5015641 * 2
def baseEnd_5015641 : Nat := 2575434623397516015220993

theorem tailTrace_5015641 : CollatzResearch.WordTrace tailWord_5015641 prefixEnd_5015641 2575434623397516015220993 := by
  unfold tailWord_5015641
  simp only [CollatzResearch.WordTrace]
  refine ⟨182935456022196735130238777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121956970681464490086825851 182935456022196735130238777)
  ·
    refine ⟨137201592016647551347679083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182935456022196735130238777 137201592016647551347679083)
    ·
      refine ⟨205802388024971327021518625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137201592016647551347679083 205802388024971327021518625)
      ·
        refine ⟨154351791018728495266138969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205802388024971327021518625 154351791018728495266138969)
        ·
          refine ⟨115763843264046371449604227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154351791018728495266138969 115763843264046371449604227)
          ·
            refine ⟨173645764896069557174406341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115763843264046371449604227 173645764896069557174406341)
            ·
              refine ⟨32558580918013041970201189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173645764896069557174406341 32558580918013041970201189)
              ·
                refine ⟨6104733922127445369412723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32558580918013041970201189 6104733922127445369412723)
                ·
                  refine ⟨9157100883191168054119085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6104733922127445369412723 9157100883191168054119085)
                  ·
                    refine ⟨3433912831196688020294657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9157100883191168054119085 3433912831196688020294657)
                    ·
                      refine ⟨2575434623397516015220993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3433912831196688020294657 2575434623397516015220993)
                      ·
                        rfl

theorem cell23_5015641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 3, 2].length) (baseStart_5015641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015641 prefixEnd_5015641 := by exact prefixLift 5015641
  have htrace : WordTrace (prefixWord ++ tailWord_5015641) baseStart_5015641 baseEnd_5015641 := by
    simpa [prefixWord, tailWord_5015641, baseEnd_5015641] using wordTrace_append hprefix tailTrace_5015641
  have hstable : (prefixWord ++ tailWord_5015641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015641).length < 2 ^ (prefixWord ++ tailWord_5015641).sum := by decide
  have hdescent : baseEnd_5015641 < baseStart_5015641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015657 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 1, 3, 5]
def baseStart_5015657 : Nat := 118140960795 + 5015657 * 2 ^ 59
def prefixEnd_5015657 : Nat := 4983230072969 + 3 ^ 40 * 5015657 * 2
def baseEnd_5015657 : Nat := 2575442839087987952620919

theorem tailTrace_5015657 : CollatzResearch.WordTrace tailWord_5015657 prefixEnd_5015657 2575442839087987952620919 := by
  unfold tailWord_5015657
  simp only [CollatzResearch.WordTrace]
  refine ⟨182936039590138769862821225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121957359726759179908547483 182936039590138769862821225)
  ·
    refine ⟨137202029692604077397115919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182936039590138769862821225 137202029692604077397115919)
    ·
      refine ⟨205803044538906116095673879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137202029692604077397115919 205803044538906116095673879)
      ·
        refine ⟨308704566808359174143510819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205803044538906116095673879 308704566808359174143510819)
        ·
          refine ⟨463056850212538761215266229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308704566808359174143510819 463056850212538761215266229)
          ·
            refine ⟨43411579707425508863931209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 463056850212538761215266229 43411579707425508863931209)
            ·
              refine ⟨32558684780569131647948407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43411579707425508863931209 32558684780569131647948407)
              ·
                refine ⟨48838027170853697471922611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32558684780569131647948407 48838027170853697471922611)
                ·
                  refine ⟨73257040756280546207883917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48838027170853697471922611 73257040756280546207883917)
                  ·
                    refine ⟨27471390283605204827956469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73257040756280546207883917 27471390283605204827956469)
                    ·
                      refine ⟨2575442839087987952620919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27471390283605204827956469 2575442839087987952620919)
                      ·
                        rfl

theorem cell23_5015657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_5015657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015657 prefixEnd_5015657 := by exact prefixLift 5015657
  have htrace : WordTrace (prefixWord ++ tailWord_5015657) baseStart_5015657 baseEnd_5015657 := by
    simpa [prefixWord, tailWord_5015657, baseEnd_5015657] using wordTrace_append hprefix tailTrace_5015657
  have hstable : (prefixWord ++ tailWord_5015657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015657).length < 2 ^ (prefixWord ++ tailWord_5015657).sum := by decide
  have hdescent : baseEnd_5015657 < baseStart_5015657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015684 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_5015684 : Nat := 118140960795 + 5015684 * 2 ^ 59
def prefixEnd_5015684 : Nat := 4983230072969 + 3 ^ 40 * 5015684 * 2
def baseEnd_5015684 : Nat := 2575456703065659346983295

theorem tailTrace_5015684 : CollatzResearch.WordTrace tailWord_5015684 prefixEnd_5015684 2575456703065659346983295 := by
  unfold tailWord_5015684
  simp only [CollatzResearch.WordTrace]
  refine ⟨91468512180520476737027053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121958016240693968982702737 91468512180520476737027053)
  ·
    refine ⟨34300692067695178776385145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91468512180520476737027053 34300692067695178776385145)
    ·
      refine ⟨25725519050771384082288859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34300692067695178776385145 25725519050771384082288859)
      ·
        refine ⟨38588278576157076123433289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25725519050771384082288859 38588278576157076123433289)
        ·
          refine ⟨28941208932117807092574967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38588278576157076123433289 28941208932117807092574967)
          ·
            refine ⟨43411813398176710638862451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28941208932117807092574967 43411813398176710638862451)
            ·
              refine ⟨65117720097265065958293677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43411813398176710638862451 65117720097265065958293677)
              ·
                refine ⟨24419145036474399734360129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65117720097265065958293677 24419145036474399734360129)
                ·
                  refine ⟨18314358777355799800770097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24419145036474399734360129 18314358777355799800770097)
                  ·
                    refine ⟨13735769083016849850577573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18314358777355799800770097 13735769083016849850577573)
                    ·
                      refine ⟨2575456703065659346983295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13735769083016849850577573 2575456703065659346983295)
                      ·
                        rfl

theorem cell23_5015684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_5015684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015684 prefixEnd_5015684 := by exact prefixLift 5015684
  have htrace : WordTrace (prefixWord ++ tailWord_5015684) baseStart_5015684 baseEnd_5015684 := by
    simpa [prefixWord, tailWord_5015684, baseEnd_5015684] using wordTrace_append hprefix tailTrace_5015684
  have hstable : (prefixWord ++ tailWord_5015684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015684).length < 2 ^ (prefixWord ++ tailWord_5015684).sum := by decide
  have hdescent : baseEnd_5015684 < baseStart_5015684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015688 : List Nat := [2, 1, 3, 4, 1, 1, 3, 1, 1, 4, 2]
def baseStart_5015688 : Nat := 118140960795 + 5015688 * 2 ^ 59
def prefixEnd_5015688 : Nat := 4983230072969 + 3 ^ 40 * 5015688 * 2
def baseEnd_5015688 : Nat := 2575458756988277331333277

theorem tailTrace_5015688 : CollatzResearch.WordTrace tailWord_5015688 prefixEnd_5015688 2575458756988277331333277 := by
  unfold tailWord_5015688
  simp only [CollatzResearch.WordTrace]
  refine ⟨91468585126513231078599859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121958113502017641438133145 91468585126513231078599859)
  ·
    refine ⟨137202877689769846617899789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91468585126513231078599859 137202877689769846617899789)
    ·
      refine ⟨51451079133663692481712421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137202877689769846617899789 51451079133663692481712421)
      ·
        refine ⟨9647077337561942340321079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51451079133663692481712421 9647077337561942340321079)
        ·
          refine ⟨14470616006342913510481619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9647077337561942340321079 14470616006342913510481619)
          ·
            refine ⟨21705924009514370265722429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14470616006342913510481619 21705924009514370265722429)
            ·
              refine ⟨8139721503567888849645911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21705924009514370265722429 8139721503567888849645911)
              ·
                refine ⟨12209582255351833274468867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8139721503567888849645911 12209582255351833274468867)
                ·
                  refine ⟨18314373383027749911703301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12209582255351833274468867 18314373383027749911703301)
                  ·
                    refine ⟨3433945009317703108444369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18314373383027749911703301 3433945009317703108444369)
                    ·
                      refine ⟨2575458756988277331333277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3433945009317703108444369 2575458756988277331333277)
                      ·
                        rfl

theorem cell23_5015688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_5015688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015688 prefixEnd_5015688 := by exact prefixLift 5015688
  have htrace : WordTrace (prefixWord ++ tailWord_5015688) baseStart_5015688 baseEnd_5015688 := by
    simpa [prefixWord, tailWord_5015688, baseEnd_5015688] using wordTrace_append hprefix tailTrace_5015688
  have hstable : (prefixWord ++ tailWord_5015688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015688).length < 2 ^ (prefixWord ++ tailWord_5015688).sum := by decide
  have hdescent : baseEnd_5015688 < baseStart_5015688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015707 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 1, 7]
def baseStart_5015707 : Nat := 118140960795 + 5015707 * 2 ^ 59
def prefixEnd_5015707 : Nat := 4983230072969 + 3 ^ 40 * 5015707 * 2
def baseEnd_5015707 : Nat := 858489504373570918998563

theorem tailTrace_5015707 : CollatzResearch.WordTrace tailWord_5015707 prefixEnd_5015707 858489504373570918998563 := by
  unfold tailWord_5015707
  simp only [CollatzResearch.WordTrace]
  refine ⟨182937863239957628402141375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121958575493305085601427583 182937863239957628402141375)
  ·
    refine ⟨274406794859936442603212063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182937863239957628402141375 274406794859936442603212063)
    ·
      refine ⟨411610192289904663904818095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274406794859936442603212063 411610192289904663904818095)
      ·
        refine ⟨617415288434856995857227143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411610192289904663904818095 617415288434856995857227143)
        ·
          refine ⟨926122932652285493785840715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617415288434856995857227143 926122932652285493785840715)
          ·
            refine ⟨1389184398978428240678761073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926122932652285493785840715 1389184398978428240678761073)
            ·
              refine ⟨1041888299233821180509070805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1389184398978428240678761073 1041888299233821180509070805)
              ·
                refine ⟨24419257013292683918181347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1041888299233821180509070805 24419257013292683918181347)
                ·
                  refine ⟨36628885519939025877272021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24419257013292683918181347 36628885519939025877272021)
                  ·
                    refine ⟨858489504373570918998563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36628885519939025877272021 858489504373570918998563)
                    ·
                      rfl

theorem cell23_5015707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 7].length) (baseStart_5015707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015707 prefixEnd_5015707 := by exact prefixLift 5015707
  have htrace : WordTrace (prefixWord ++ tailWord_5015707) baseStart_5015707 baseEnd_5015707 := by
    simpa [prefixWord, tailWord_5015707, baseEnd_5015707] using wordTrace_append hprefix tailTrace_5015707
  have hstable : (prefixWord ++ tailWord_5015707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015707).length < 2 ^ (prefixWord ++ tailWord_5015707).sum := by decide
  have hdescent : baseEnd_5015707 < baseStart_5015707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015747 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 9]
def baseStart_5015747 : Nat := 118140960795 + 5015747 * 2 ^ 59
def prefixEnd_5015747 : Nat := 4983230072969 + 3 ^ 40 * 5015747 * 2
def baseEnd_5015747 : Nat := 2575489052346892600495505

theorem tailTrace_5015747 : CollatzResearch.WordTrace tailWord_5015747 prefixEnd_5015747 2575489052346892600495505 := by
  unfold tailWord_5015747
  simp only [CollatzResearch.WordTrace]
  refine ⟨182939322159812715233597495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121959548106541810155731663 182939322159812715233597495)
  ·
    refine ⟨274408983239719072850396243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182939322159812715233597495 274408983239719072850396243)
    ·
      refine ⟨411613474859578609275594365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274408983239719072850396243 411613474859578609275594365)
      ·
        refine ⟨154355053072341978478347887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 411613474859578609275594365 154355053072341978478347887)
        ·
          refine ⟨231532579608512967717521831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154355053072341978478347887 231532579608512967717521831)
          ·
            refine ⟨347298869412769451576282747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231532579608512967717521831 347298869412769451576282747)
            ·
              refine ⟨520948304119154177364424121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347298869412769451576282747 520948304119154177364424121)
              ·
                refine ⟨390711228089365633023318091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 520948304119154177364424121 390711228089365633023318091)
                ·
                  refine ⟨586066842134048449534977137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390711228089365633023318091 586066842134048449534977137)
                  ·
                    refine ⟨439550131600536337151232853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 586066842134048449534977137 439550131600536337151232853)
                    ·
                      refine ⟨2575489052346892600495505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 439550131600536337151232853 2575489052346892600495505)
                      ·
                        rfl

theorem cell23_5015747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_5015747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015747 prefixEnd_5015747 := by exact prefixLift 5015747
  have htrace : WordTrace (prefixWord ++ tailWord_5015747) baseStart_5015747 baseEnd_5015747 := by
    simpa [prefixWord, tailWord_5015747, baseEnd_5015747] using wordTrace_append hprefix tailTrace_5015747
  have hstable : (prefixWord ++ tailWord_5015747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015747).length < 2 ^ (prefixWord ++ tailWord_5015747).sum := by decide
  have hdescent : baseEnd_5015747 < baseStart_5015747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015788 : List Nat := [2, 2, 1, 1, 2, 3, 3, 4, 1, 4]
def baseStart_5015788 : Nat := 118140960795 + 5015788 * 2 ^ 59
def prefixEnd_5015788 : Nat := 4983230072969 + 3 ^ 40 * 5015788 * 2
def baseEnd_5015788 : Nat := 858503368351242313360939

theorem tailTrace_5015788 : CollatzResearch.WordTrace tailWord_5015788 prefixEnd_5015788 858503368351242313360939 := by
  unfold tailWord_5015788
  simp only [CollatzResearch.WordTrace]
  refine ⟨91470408776332089617920009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121960545035109452823893345 91470408776332089617920009)
  ·
    refine ⟨68602806582249067213440007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91470408776332089617920009 68602806582249067213440007)
    ·
      refine ⟨102904209873373600820160011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68602806582249067213440007 102904209873373600820160011)
      ·
        refine ⟨154356314810060401230240017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102904209873373600820160011 154356314810060401230240017)
        ·
          refine ⟨115767236107545300922680013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154356314810060401230240017 115767236107545300922680013)
          ·
            refine ⟨43412713540329487846005005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115767236107545300922680013 43412713540329487846005005)
            ·
              refine ⟨16279767577623557942251877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43412713540329487846005005 16279767577623557942251877)
              ·
                refine ⟨3052456420804417114172227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16279767577623557942251877 3052456420804417114172227)
                ·
                  refine ⟨4578684631206625671258341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3052456420804417114172227 4578684631206625671258341)
                  ·
                    refine ⟨858503368351242313360939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4578684631206625671258341 858503368351242313360939)
                    ·
                      rfl

theorem cell23_5015788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 1, 4].length) (baseStart_5015788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015788 prefixEnd_5015788 := by exact prefixLift 5015788
  have htrace : WordTrace (prefixWord ++ tailWord_5015788) baseStart_5015788 baseEnd_5015788 := by
    simpa [prefixWord, tailWord_5015788, baseEnd_5015788] using wordTrace_append hprefix tailTrace_5015788
  have hstable : (prefixWord ++ tailWord_5015788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015788).length < 2 ^ (prefixWord ++ tailWord_5015788).sum := by decide
  have hdescent : baseEnd_5015788 < baseStart_5015788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015838 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_5015838 : Nat := 118140960795 + 5015838 * 2 ^ 59
def prefixEnd_5015838 : Nat := 4983230072969 + 3 ^ 40 * 5015838 * 2
def baseEnd_5015838 : Nat := 2575535779086451744457587

theorem tailTrace_5015838 : CollatzResearch.WordTrace tailWord_5015838 prefixEnd_5015838 2575535779086451744457587 := by
  unfold tailWord_5015838
  simp only [CollatzResearch.WordTrace]
  refine ⟨22867830150310379721895021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121961760801655358516773445 22867830150310379721895021)
  ·
    refine ⟨8575436306366392395710633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22867830150310379721895021 8575436306366392395710633)
    ·
      refine ⟨6431577229774794296782975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8575436306366392395710633 6431577229774794296782975)
      ·
        refine ⟨9647365844662191445174463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6431577229774794296782975 9647365844662191445174463)
        ·
          refine ⟨14471048766993287167761695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9647365844662191445174463 14471048766993287167761695)
          ·
            refine ⟨21706573150489930751642543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14471048766993287167761695 21706573150489930751642543)
            ·
              refine ⟨32559859725734896127463815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21706573150489930751642543 32559859725734896127463815)
              ·
                refine ⟨48839789588602344191195723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32559859725734896127463815 48839789588602344191195723)
                ·
                  refine ⟨73259684382903516286793585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48839789588602344191195723 73259684382903516286793585)
                  ·
                    refine ⟨54944763287177637215095189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73259684382903516286793585 54944763287177637215095189)
                    ·
                      refine ⟨2575535779086451744457587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54944763287177637215095189 2575535779086451744457587)
                      ·
                        rfl

theorem cell23_5015838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_5015838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015838 prefixEnd_5015838 := by exact prefixLift 5015838
  have htrace : WordTrace (prefixWord ++ tailWord_5015838) baseStart_5015838 baseEnd_5015838 := by
    simpa [prefixWord, tailWord_5015838, baseEnd_5015838] using wordTrace_append hprefix tailTrace_5015838
  have hstable : (prefixWord ++ tailWord_5015838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015838).length < 2 ^ (prefixWord ++ tailWord_5015838).sum := by decide
  have hdescent : baseEnd_5015838 < baseStart_5015838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015845 : List Nat := [1, 3, 1, 2, 5, 1, 2, 1, 3, 1, 3]
def baseStart_5015845 : Nat := 118140960795 + 5015845 * 2 ^ 59
def prefixEnd_5015845 : Nat := 4983230072969 + 3 ^ 40 * 5015845 * 2
def baseEnd_5015845 : Nat := 2575539373451033217070055

theorem tailTrace_5015845 : CollatzResearch.WordTrace tailWord_5015845 prefixEnd_5015845 2575539373451033217070055 := by
  unfold tailWord_5015845
  simp only [CollatzResearch.WordTrace]
  refine ⟨182942896513457677970664989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121961931008971785313776659 182942896513457677970664989)
  ·
    refine ⟨68603586192546629238999371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182942896513457677970664989 68603586192546629238999371)
    ·
      refine ⟨102905379288819943858499057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68603586192546629238999371 102905379288819943858499057)
      ·
        refine ⟨77179034466614957893874293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102905379288819943858499057 77179034466614957893874293)
        ·
          refine ⟨7235534481245152302550715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77179034466614957893874293 7235534481245152302550715)
          ·
            refine ⟨10853301721867728453826073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7235534481245152302550715 10853301721867728453826073)
            ·
              refine ⟨8139976291400796340369555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10853301721867728453826073 8139976291400796340369555)
              ·
                refine ⟨12209964437101194510554333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8139976291400796340369555 12209964437101194510554333)
                ·
                  refine ⟨4578736663912947941457875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12209964437101194510554333 4578736663912947941457875)
                  ·
                    refine ⟨6868104995869421912186813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4578736663912947941457875 6868104995869421912186813)
                    ·
                      refine ⟨2575539373451033217070055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6868104995869421912186813 2575539373451033217070055)
                      ·
                        rfl

theorem cell23_5015845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_5015845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015845 prefixEnd_5015845 := by exact prefixLift 5015845
  have htrace : WordTrace (prefixWord ++ tailWord_5015845) baseStart_5015845 baseEnd_5015845 := by
    simpa [prefixWord, tailWord_5015845, baseEnd_5015845] using wordTrace_append hprefix tailTrace_5015845
  have hstable : (prefixWord ++ tailWord_5015845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015845).length < 2 ^ (prefixWord ++ tailWord_5015845).sum := by decide
  have hdescent : baseEnd_5015845 < baseStart_5015845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015868 : List Nat := [2, 2, 2, 2, 1, 2, 4, 2, 1, 1, 4]
def baseStart_5015868 : Nat := 118140960795 + 5015868 * 2 ^ 59
def prefixEnd_5015868 : Nat := 4983230072969 + 3 ^ 40 * 5015868 * 2
def baseEnd_5015868 : Nat := 2575551183506086627082449

theorem tailTrace_5015868 : CollatzResearch.WordTrace tailWord_5015868 prefixEnd_5015868 2575551183506086627082449 := by
  unfold tailWord_5015868
  simp only [CollatzResearch.WordTrace]
  refine ⟨91471867696187176449376129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121962490261582901932501505 91471867696187176449376129)
  ·
    refine ⟨68603900772140382337032097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91471867696187176449376129 68603900772140382337032097)
    ·
      refine ⟨51452925579105286752774073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68603900772140382337032097 51452925579105286752774073)
      ·
        refine ⟨38589694184328965064580555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51452925579105286752774073 38589694184328965064580555)
        ·
          refine ⟨57884541276493447596870833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38589694184328965064580555 57884541276493447596870833)
          ·
            refine ⟨43413405957370085697653125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57884541276493447596870833 43413405957370085697653125)
            ·
              refine ⟨8140013617006891068309961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43413405957370085697653125 8140013617006891068309961)
              ·
                refine ⟨6105010212755168301232471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8140013617006891068309961 6105010212755168301232471)
                ·
                  refine ⟨9157515319132752451848707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6105010212755168301232471 9157515319132752451848707)
                  ·
                    refine ⟨13736272978699128677773061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9157515319132752451848707 13736272978699128677773061)
                    ·
                      refine ⟨2575551183506086627082449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13736272978699128677773061 2575551183506086627082449)
                      ·
                        rfl

theorem cell23_5015868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_5015868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015868 prefixEnd_5015868 := by exact prefixLift 5015868
  have htrace : WordTrace (prefixWord ++ tailWord_5015868) baseStart_5015868 baseEnd_5015868 := by
    simpa [prefixWord, tailWord_5015868, baseEnd_5015868] using wordTrace_append hprefix tailTrace_5015868
  have hstable : (prefixWord ++ tailWord_5015868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015868).length < 2 ^ (prefixWord ++ tailWord_5015868).sum := by decide
  have hdescent : baseEnd_5015868 < baseStart_5015868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015888 : List Nat := [2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 3]
def baseStart_5015888 : Nat := 118140960795 + 5015888 * 2 ^ 59
def prefixEnd_5015888 : Nat := 4983230072969 + 3 ^ 40 * 5015888 * 2
def baseEnd_5015888 : Nat := 2575561453119176548832357

theorem tailTrace_5015888 : CollatzResearch.WordTrace tailWord_5015888 prefixEnd_5015888 2575561453119176548832357 := by
  unfold tailWord_5015888
  simp only [CollatzResearch.WordTrace]
  refine ⟨91472232426150948157240159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121962976568201264209653545 91472232426150948157240159)
  ·
    refine ⟨137208348639226422235860239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91472232426150948157240159 137208348639226422235860239)
    ·
      refine ⟨205812522958839633353790359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137208348639226422235860239 205812522958839633353790359)
      ·
        refine ⟨308718784438259450030685539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205812522958839633353790359 308718784438259450030685539)
        ·
          refine ⟨463078176657389175046028309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308718784438259450030685539 463078176657389175046028309)
          ·
            refine ⟨21706789530815117580282577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 463078176657389175046028309 21706789530815117580282577)
            ·
              refine ⟨16280092148111338185211933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21706789530815117580282577 16280092148111338185211933)
              ·
                refine ⟨6105034555541751819454475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16280092148111338185211933 6105034555541751819454475)
                ·
                  refine ⟨9157551833312627729181713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6105034555541751819454475 9157551833312627729181713)
                  ·
                    refine ⟨6868163874984470796886285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9157551833312627729181713 6868163874984470796886285)
                    ·
                      refine ⟨2575561453119176548832357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6868163874984470796886285 2575561453119176548832357)
                      ·
                        rfl

theorem cell23_5015888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 3].length) (baseStart_5015888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015888 prefixEnd_5015888 := by exact prefixLift 5015888
  have htrace : WordTrace (prefixWord ++ tailWord_5015888) baseStart_5015888 baseEnd_5015888 := by
    simpa [prefixWord, tailWord_5015888, baseEnd_5015888] using wordTrace_append hprefix tailTrace_5015888
  have hstable : (prefixWord ++ tailWord_5015888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015888).length < 2 ^ (prefixWord ++ tailWord_5015888).sum := by decide
  have hdescent : baseEnd_5015888 < baseStart_5015888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015912 : List Nat := [2, 1, 4, 2, 2, 3, 2, 1, 2, 4]
def baseStart_5015912 : Nat := 118140960795 + 5015912 * 2 ^ 59
def prefixEnd_5015912 : Nat := 4983230072969 + 3 ^ 40 * 5015912 * 2
def baseEnd_5015912 : Nat := 858524592218294818310749

theorem tailTrace_5015912 : CollatzResearch.WordTrace tailWord_5015912 prefixEnd_5015912 858524592218294818310749 := by
  unfold tailWord_5015912
  simp only [CollatzResearch.WordTrace]
  refine ⟨91472670102107474206676995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121963560136143298942235993 91472670102107474206676995)
  ·
    refine ⟨137209005153161211310015493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91472670102107474206676995 137209005153161211310015493)
    ·
      refine ⟨25726688466217727120627905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137209005153161211310015493 25726688466217727120627905)
      ·
        refine ⟨19295016349663295340470929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25726688466217727120627905 19295016349663295340470929)
        ·
          refine ⟨14471262262247471505353197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19295016349663295340470929 14471262262247471505353197)
          ·
            refine ⟨5426723348342801814507449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14471262262247471505353197 5426723348342801814507449)
            ·
              refine ⟨4070042511257101360880587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5426723348342801814507449 4070042511257101360880587)
              ·
                refine ⟨6105063766885652041320881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4070042511257101360880587 6105063766885652041320881)
                ·
                  refine ⟨4578797825164239030990661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6105063766885652041320881 4578797825164239030990661)
                  ·
                    refine ⟨858524592218294818310749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4578797825164239030990661 858524592218294818310749)
                    ·
                      rfl

theorem cell23_5015912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_5015912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015912 prefixEnd_5015912 := by exact prefixLift 5015912
  have htrace : WordTrace (prefixWord ++ tailWord_5015912) baseStart_5015912 baseEnd_5015912 := by
    simpa [prefixWord, tailWord_5015912, baseEnd_5015912] using wordTrace_append hprefix tailTrace_5015912
  have hstable : (prefixWord ++ tailWord_5015912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015912).length < 2 ^ (prefixWord ++ tailWord_5015912).sum := by decide
  have hdescent : baseEnd_5015912 < baseStart_5015912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015961 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 1, 6, 3]
def baseStart_5015961 : Nat := 118140960795 + 5015961 * 2 ^ 59
def prefixEnd_5015961 : Nat := 4983230072969 + 3 ^ 40 * 5015961 * 2
def baseEnd_5015961 : Nat := 2575598937206954763219521

theorem tailTrace_5015961 : CollatzResearch.WordTrace tailWord_5015961 prefixEnd_5015961 2575598937206954763219521 := by
  unfold tailWord_5015961
  simp only [CollatzResearch.WordTrace]
  refine ⟨182947127381037429781887737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121964751587358286521258491 182947127381037429781887737)
  ·
    refine ⟨137210345535778072336415803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182947127381037429781887737 137210345535778072336415803)
    ·
      refine ⟨205815518303667108504623705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137210345535778072336415803 205815518303667108504623705)
      ·
        refine ⟨154361638727750331378467779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205815518303667108504623705 154361638727750331378467779)
        ·
          refine ⟨231542458091625497067701669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154361638727750331378467779 231542458091625497067701669)
          ·
            refine ⟨43414210892179780700194063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 231542458091625497067701669 43414210892179780700194063)
            ·
              refine ⟨65121316338269671050291095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43414210892179780700194063 65121316338269671050291095)
              ·
                refine ⟨97681974507404506575436643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65121316338269671050291095 97681974507404506575436643)
                ·
                  refine ⟨146522961761106759863154965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97681974507404506575436643 146522961761106759863154965)
                  ·
                    refine ⟨6868263832551879368585389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 146522961761106759863154965 6868263832551879368585389)
                    ·
                      refine ⟨2575598937206954763219521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6868263832551879368585389 2575598937206954763219521)
                      ·
                        rfl

theorem cell23_5015961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_5015961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015961 prefixEnd_5015961 := by exact prefixLift 5015961
  have htrace : WordTrace (prefixWord ++ tailWord_5015961) baseStart_5015961 baseEnd_5015961 := by
    simpa [prefixWord, tailWord_5015961, baseEnd_5015961] using wordTrace_append hprefix tailTrace_5015961
  have hstable : (prefixWord ++ tailWord_5015961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015961).length < 2 ^ (prefixWord ++ tailWord_5015961).sum := by decide
  have hdescent : baseEnd_5015961 < baseStart_5015961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015971 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 4]
def baseStart_5015971 : Nat := 118140960795 + 5015971 * 2 ^ 59
def prefixEnd_5015971 : Nat := 4983230072969 + 3 ^ 40 * 5015971 * 2
def baseEnd_5015971 : Nat := 2575604072013499724094475

theorem tailTrace_5015971 : CollatzResearch.WordTrace tailWord_5015971 prefixEnd_5015971 2575604072013499724094475 := by
  unfold tailWord_5015971
  simp only [CollatzResearch.WordTrace]
  refine ⟨182947492111001201489751767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121964994740667467659834511 182947492111001201489751767)
  ·
    refine ⟨274421238166501802234627651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182947492111001201489751767 274421238166501802234627651)
    ·
      refine ⟨411631857249752703351941477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274421238166501802234627651 411631857249752703351941477)
      ·
        refine ⟨77180973234328631878489027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 411631857249752703351941477 77180973234328631878489027)
        ·
          refine ⟨115771459851492947817733541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77180973234328631878489027 115771459851492947817733541)
          ·
            refine ⟨21707148722154927715825039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115771459851492947817733541 21707148722154927715825039)
            ·
              refine ⟨32560723083232391573737559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21707148722154927715825039 32560723083232391573737559)
              ·
                refine ⟨48841084624848587360606339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32560723083232391573737559 48841084624848587360606339)
                ·
                  refine ⟨73261626937272881040909509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48841084624848587360606339 73261626937272881040909509)
                  ·
                    refine ⟨13736555050738665195170533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73261626937272881040909509 13736555050738665195170533)
                    ·
                      refine ⟨2575604072013499724094475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13736555050738665195170533 2575604072013499724094475)
                      ·
                        rfl

theorem cell23_5015971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_5015971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015971 prefixEnd_5015971 := by exact prefixLift 5015971
  have htrace : WordTrace (prefixWord ++ tailWord_5015971) baseStart_5015971 baseEnd_5015971 := by
    simpa [prefixWord, tailWord_5015971, baseEnd_5015971] using wordTrace_append hprefix tailTrace_5015971
  have hstable : (prefixWord ++ tailWord_5015971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015971).length < 2 ^ (prefixWord ++ tailWord_5015971).sum := by decide
  have hdescent : baseEnd_5015971 < baseStart_5015971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5015975 : List Nat := [1, 1, 6, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_5015975 : Nat := 118140960795 + 5015975 * 2 ^ 59
def prefixEnd_5015975 : Nat := 4983230072969 + 3 ^ 40 * 5015975 * 2
def baseEnd_5015975 : Nat := 2575606125936117708444457

theorem tailTrace_5015975 : CollatzResearch.WordTrace tailWord_5015975 prefixEnd_5015975 2575606125936117708444457 := by
  unfold tailWord_5015975
  simp only [CollatzResearch.WordTrace]
  refine ⟨182947638002986710172897379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121965092001991140115264919 182947638002986710172897379)
  ·
    refine ⟨274421457004480065259346069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182947638002986710172897379 274421457004480065259346069)
    ·
      refine ⟨12863505797085003059031847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 274421457004480065259346069 12863505797085003059031847)
      ·
        refine ⟨19295258695627504588547771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12863505797085003059031847 19295258695627504588547771)
        ·
          refine ⟨28942888043441256882821657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19295258695627504588547771 28942888043441256882821657)
          ·
            refine ⟨21707166032580942662116243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28942888043441256882821657 21707166032580942662116243)
            ·
              refine ⟨32560749048871413993174365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21707166032580942662116243 32560749048871413993174365)
              ·
                refine ⟨12210280893326780247440387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32560749048871413993174365 12210280893326780247440387)
                ·
                  refine ⟨18315421339990170371160581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12210280893326780247440387 18315421339990170371160581)
                  ·
                    refine ⟨3434141501248156944592609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18315421339990170371160581 3434141501248156944592609)
                    ·
                      refine ⟨2575606125936117708444457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3434141501248156944592609 2575606125936117708444457)
                      ·
                        rfl

theorem cell23_5015975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_5015975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5015975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5015975 prefixEnd_5015975 := by exact prefixLift 5015975
  have htrace : WordTrace (prefixWord ++ tailWord_5015975) baseStart_5015975 baseEnd_5015975 := by
    simpa [prefixWord, tailWord_5015975, baseEnd_5015975] using wordTrace_append hprefix tailTrace_5015975
  have hstable : (prefixWord ++ tailWord_5015975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5015975).length < 2 ^ (prefixWord ++ tailWord_5015975).sum := by decide
  have hdescent : baseEnd_5015975 < baseStart_5015975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5015975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016008 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 2, 3, 3]
def baseStart_5016008 : Nat := 118140960795 + 5016008 * 2 ^ 59
def prefixEnd_5016008 : Nat := 4983230072969 + 3 ^ 40 * 5016008 * 2
def baseEnd_5016008 : Nat := 2575623070797716079331805

theorem tailTrace_5016008 : CollatzResearch.WordTrace tailWord_5016008 prefixEnd_5016008 2575623070797716079331805 := by
  unfold tailWord_5016008
  simp only [CollatzResearch.WordTrace]
  refine ⟨91474420805933578404424339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121965894407911437872565785 91474420805933578404424339)
  ·
    refine ⟨137211631208900367606636509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91474420805933578404424339 137211631208900367606636509)
    ·
      refine ⟨51454361703337637852488691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137211631208900367606636509 51454361703337637852488691)
      ·
        refine ⟨77181542555006456778733037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51454361703337637852488691 77181542555006456778733037)
        ·
          refine ⟨28943078458127421292024889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77181542555006456778733037 28943078458127421292024889)
          ·
            refine ⟨21707308843595565969018667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28943078458127421292024889 21707308843595565969018667)
            ·
              refine ⟨32560963265393348953528001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21707308843595565969018667 32560963265393348953528001)
              ·
                refine ⟨24420722449045011715146001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32560963265393348953528001 24420722449045011715146001)
                ·
                  refine ⟨18315541836783758786359501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24420722449045011715146001 18315541836783758786359501)
                  ·
                    refine ⟨6868328188793909544884813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18315541836783758786359501 6868328188793909544884813)
                    ·
                      refine ⟨2575623070797716079331805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6868328188793909544884813 2575623070797716079331805)
                      ·
                        rfl

theorem cell23_5016008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_5016008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016008 prefixEnd_5016008 := by exact prefixLift 5016008
  have htrace : WordTrace (prefixWord ++ tailWord_5016008) baseStart_5016008 baseEnd_5016008 := by
    simpa [prefixWord, tailWord_5016008, baseEnd_5016008] using wordTrace_append hprefix tailTrace_5016008
  have hstable : (prefixWord ++ tailWord_5016008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016008).length < 2 ^ (prefixWord ++ tailWord_5016008).sum := by decide
  have hdescent : baseEnd_5016008 < baseStart_5016008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016011 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 4, 5]
def baseStart_5016011 : Nat := 118140960795 + 5016011 * 2 ^ 59
def prefixEnd_5016011 : Nat := 4983230072969 + 3 ^ 40 * 5016011 * 2
def baseEnd_5016011 : Nat := 858541537079893189198097

theorem tailTrace_5016011 : CollatzResearch.WordTrace tailWord_5016011 prefixEnd_5016011 858541537079893189198097 := by
  unfold tailWord_5016011
  simp only [CollatzResearch.WordTrace]
  refine ⟨182948951030856288321207887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121965967353904192214138591 182948951030856288321207887)
  ·
    refine ⟨274423426546284432481811831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182948951030856288321207887 274423426546284432481811831)
    ·
      refine ⟨411635139819426648722717747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274423426546284432481811831 411635139819426648722717747)
      ·
        refine ⟨617452709729139973084076621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411635139819426648722717747 617452709729139973084076621)
        ·
          refine ⟨231544766148427489906528733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 617452709729139973084076621 231544766148427489906528733)
          ·
            refine ⟨86829287305660308714948275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231544766148427489906528733 86829287305660308714948275)
            ·
              refine ⟨130243930958490463072422413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86829287305660308714948275 130243930958490463072422413)
              ·
                refine ⟨48841474109433923652158405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130243930958490463072422413 48841474109433923652158405)
                ·
                  refine ⟨9157776395518860684779701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48841474109433923652158405 9157776395518860684779701)
                  ·
                    refine ⟨858541537079893189198097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9157776395518860684779701 858541537079893189198097)
                    ·
                      rfl

theorem cell23_5016011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 5].length) (baseStart_5016011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016011 prefixEnd_5016011 := by exact prefixLift 5016011
  have htrace : WordTrace (prefixWord ++ tailWord_5016011) baseStart_5016011 baseEnd_5016011 := by
    simpa [prefixWord, tailWord_5016011, baseEnd_5016011] using wordTrace_append hprefix tailTrace_5016011
  have hstable : (prefixWord ++ tailWord_5016011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016011).length < 2 ^ (prefixWord ++ tailWord_5016011).sum := by decide
  have hdescent : baseEnd_5016011 < baseStart_5016011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016048 : List Nat := [2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 4]
def baseStart_5016048 : Nat := 118140960795 + 5016048 * 2 ^ 59
def prefixEnd_5016048 : Nat := 4983230072969 + 3 ^ 40 * 5016048 * 2
def baseEnd_5016048 : Nat := 2575643610023895922831621

theorem tailTrace_5016048 : CollatzResearch.WordTrace tailWord_5016048 prefixEnd_5016048 2575643610023895922831621 := by
  unfold tailWord_5016048
  simp only [CollatzResearch.WordTrace]
  refine ⟨91475150265861121820152399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121966867021148162426869865 91475150265861121820152399)
  ·
    refine ⟨137212725398791682730228599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91475150265861121820152399 137212725398791682730228599)
    ·
      refine ⟨205819088098187524095342899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137212725398791682730228599 205819088098187524095342899)
      ·
        refine ⟨308728632147281286143014349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205819088098187524095342899 308728632147281286143014349)
        ·
          refine ⟨115773237055230482303630381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308728632147281286143014349 115773237055230482303630381)
          ·
            refine ⟨43414963895711430863861393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115773237055230482303630381 43414963895711430863861393)
            ·
              refine ⟨32561222921783573147896045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43414963895711430863861393 32561222921783573147896045)
              ·
                refine ⟨12210458595668839930461017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32561222921783573147896045 12210458595668839930461017)
                ·
                  refine ⟨9157843946751629947845763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12210458595668839930461017 9157843946751629947845763)
                  ·
                    refine ⟨13736765920127444921768645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9157843946751629947845763 13736765920127444921768645)
                    ·
                      refine ⟨2575643610023895922831621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13736765920127444921768645 2575643610023895922831621)
                      ·
                        rfl

theorem cell23_5016048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 4].length) (baseStart_5016048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016048 prefixEnd_5016048 := by exact prefixLift 5016048
  have htrace : WordTrace (prefixWord ++ tailWord_5016048) baseStart_5016048 baseEnd_5016048 := by
    simpa [prefixWord, tailWord_5016048, baseEnd_5016048] using wordTrace_append hprefix tailTrace_5016048
  have hstable : (prefixWord ++ tailWord_5016048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016048).length < 2 ^ (prefixWord ++ tailWord_5016048).sum := by decide
  have hdescent : baseEnd_5016048 < baseStart_5016048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016065 : List Nat := [1, 2, 4, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_5016065 : Nat := 118140960795 + 5016065 * 2 ^ 59
def prefixEnd_5016065 : Nat := 4983230072969 + 3 ^ 40 * 5016065 * 2
def baseEnd_5016065 : Nat := 2575652339195022356319043

theorem tailTrace_5016065 : CollatzResearch.WordTrace tailWord_5016065 prefixEnd_5016065 2575652339195022356319043 := by
  unfold tailWord_5016065
  simp only [CollatzResearch.WordTrace]
  refine ⟨182950920572660655543673649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121967280381773770362449099 182950920572660655543673649)
  ·
    refine ⟨137213190429495491657755237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182950920572660655543673649 137213190429495491657755237)
    ·
      refine ⟨25727473205530404685829107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137213190429495491657755237 25727473205530404685829107)
      ·
        refine ⟨38591209808295607028743661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25727473205530404685829107 38591209808295607028743661)
        ·
          refine ⟨14471703678110852635778873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38591209808295607028743661 14471703678110852635778873)
          ·
            refine ⟨10853777758583139476834155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14471703678110852635778873 10853777758583139476834155)
            ·
              refine ⟨16280666637874709215251233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10853777758583139476834155 16280666637874709215251233)
              ·
                refine ⟨12210499978406031911438425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16280666637874709215251233 12210499978406031911438425)
                ·
                  refine ⟨9157874983804523933578819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12210499978406031911438425 9157874983804523933578819)
                  ·
                    refine ⟨13736812475706785900368229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9157874983804523933578819 13736812475706785900368229)
                    ·
                      refine ⟨2575652339195022356319043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13736812475706785900368229 2575652339195022356319043)
                      ·
                        rfl

theorem cell23_5016065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_5016065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016065 prefixEnd_5016065 := by exact prefixLift 5016065
  have htrace : WordTrace (prefixWord ++ tailWord_5016065) baseStart_5016065 baseEnd_5016065 := by
    simpa [prefixWord, tailWord_5016065, baseEnd_5016065] using wordTrace_append hprefix tailTrace_5016065
  have hstable : (prefixWord ++ tailWord_5016065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016065).length < 2 ^ (prefixWord ++ tailWord_5016065).sum := by decide
  have hdescent : baseEnd_5016065 < baseStart_5016065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016075 : List Nat := [1, 1, 1, 1, 7, 1, 3, 1, 3, 4]
def baseStart_5016075 : Nat := 118140960795 + 5016075 * 2 ^ 59
def prefixEnd_5016075 : Nat := 4983230072969 + 3 ^ 40 * 5016075 * 2
def baseEnd_5016075 : Nat := 858552491333855772397999

theorem tailTrace_5016075 : CollatzResearch.WordTrace tailWord_5016075 prefixEnd_5016075 858552491333855772397999 := by
  unfold tailWord_5016075
  simp only [CollatzResearch.WordTrace]
  refine ⟨182951285302624427251537679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121967523535082951501025119 182951285302624427251537679)
  ·
    refine ⟨274426927953936640877306519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182951285302624427251537679 274426927953936640877306519)
    ·
      refine ⟨411640391930904961315959779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274426927953936640877306519 411640391930904961315959779)
      ·
        refine ⟨617460587896357441973939669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411640391930904961315959779 617460587896357441973939669)
        ·
          refine ⟨14471732528820877546264211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 617460587896357441973939669 14471732528820877546264211)
          ·
            refine ⟨21707598793231316319396317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14471732528820877546264211 21707598793231316319396317)
            ·
              refine ⟨8140349547461743619773619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21707598793231316319396317 8140349547461743619773619)
              ·
                refine ⟨12210524321192615429660429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8140349547461743619773619 12210524321192615429660429)
                ·
                  refine ⟨4578946620447230786122661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12210524321192615429660429 4578946620447230786122661)
                  ·
                    refine ⟨858552491333855772397999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4578946620447230786122661 858552491333855772397999)
                    ·
                      rfl

theorem cell23_5016075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 4].length) (baseStart_5016075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016075 prefixEnd_5016075 := by exact prefixLift 5016075
  have htrace : WordTrace (prefixWord ++ tailWord_5016075) baseStart_5016075 baseEnd_5016075 := by
    simpa [prefixWord, tailWord_5016075, baseEnd_5016075] using wordTrace_append hprefix tailTrace_5016075
  have hstable : (prefixWord ++ tailWord_5016075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016075).length < 2 ^ (prefixWord ++ tailWord_5016075).sum := by decide
  have hdescent : baseEnd_5016075 < baseStart_5016075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016111 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 7]
def baseStart_5016111 : Nat := 118140960795 + 5016111 * 2 ^ 59
def prefixEnd_5016111 : Nat := 4983230072969 + 3 ^ 40 * 5016111 * 2
def baseEnd_5016111 : Nat := 2575675959305129176343831

theorem tailTrace_5016111 : CollatzResearch.WordTrace tailWord_5016111 prefixEnd_5016111 2575675959305129176343831 := by
  unfold tailWord_5016111
  simp only [CollatzResearch.WordTrace]
  refine ⟨182952598330494005399848187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121968398886996003599898791 182952598330494005399848187)
  ·
    refine ⟨274428897495741008099772281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182952598330494005399848187 274428897495741008099772281)
    ·
      refine ⟨205821673121805756074829211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274428897495741008099772281 205821673121805756074829211)
      ·
        refine ⟨308732509682708634112243817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205821673121805756074829211 308732509682708634112243817)
        ·
          refine ⟨231549382262031475584182863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308732509682708634112243817 231549382262031475584182863)
          ·
            refine ⟨347324073393047213376274295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231549382262031475584182863 347324073393047213376274295)
            ·
              refine ⟨520986110089570820064411443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347324073393047213376274295 520986110089570820064411443)
              ·
                refine ⟨781479165134356230096617165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520986110089570820064411443 781479165134356230096617165)
                ·
                  refine ⟨293054686925383586286231437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 781479165134356230096617165 293054686925383586286231437)
                  ·
                    refine ⟨109895507597018844857336789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 293054686925383586286231437 109895507597018844857336789)
                    ·
                      refine ⟨2575675959305129176343831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109895507597018844857336789 2575675959305129176343831)
                      ·
                        rfl

theorem cell23_5016111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_5016111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016111 prefixEnd_5016111 := by exact prefixLift 5016111
  have htrace : WordTrace (prefixWord ++ tailWord_5016111) baseStart_5016111 baseEnd_5016111 := by
    simpa [prefixWord, tailWord_5016111, baseEnd_5016111] using wordTrace_append hprefix tailTrace_5016111
  have hstable : (prefixWord ++ tailWord_5016111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016111).length < 2 ^ (prefixWord ++ tailWord_5016111).sum := by decide
  have hdescent : baseEnd_5016111 < baseStart_5016111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016126 : List Nat := [4, 2, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_5016126 : Nat := 118140960795 + 5016126 * 2 ^ 59
def prefixEnd_5016126 : Nat := 4983230072969 + 3 ^ 40 * 5016126 * 2
def baseEnd_5016126 : Nat := 858561220504982205885421

theorem tailTrace_5016126 : CollatzResearch.WordTrace tailWord_5016126 prefixEnd_5016126 858561220504982205885421 := by
  unfold tailWord_5016126
  simp only [CollatzResearch.WordTrace]
  refine ⟨22869143178179957870205529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121968763616959775307762821 22869143178179957870205529)
  ·
    refine ⟨17151857383634968402654147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22869143178179957870205529 17151857383634968402654147)
    ·
      refine ⟨25727786075452452603981221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17151857383634968402654147 25727786075452452603981221)
      ·
        refine ⟨4823959889147334863246479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25727786075452452603981221 4823959889147334863246479)
        ·
          refine ⟨7235939833721002294869719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4823959889147334863246479 7235939833721002294869719)
          ·
            refine ⟨10853909750581503442304579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7235939833721002294869719 10853909750581503442304579)
            ·
              refine ⟨16280864625872255163456869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10853909750581503442304579 16280864625872255163456869)
              ·
                refine ⟨3052662117351047843148163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16280864625872255163456869 3052662117351047843148163)
                ·
                  refine ⟨4578993176026571764722245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3052662117351047843148163 4578993176026571764722245)
                  ·
                    refine ⟨858561220504982205885421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4578993176026571764722245 858561220504982205885421)
                    ·
                      rfl

theorem cell23_5016126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_5016126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016126 prefixEnd_5016126 := by exact prefixLift 5016126
  have htrace : WordTrace (prefixWord ++ tailWord_5016126) baseStart_5016126 baseEnd_5016126 := by
    simpa [prefixWord, tailWord_5016126, baseEnd_5016126] using wordTrace_append hprefix tailTrace_5016126
  have hstable : (prefixWord ++ tailWord_5016126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016126).length < 2 ^ (prefixWord ++ tailWord_5016126).sum := by decide
  have hdescent : baseEnd_5016126 < baseStart_5016126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016172 : List Nat := [2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 4]
def baseStart_5016172 : Nat := 118140960795 + 5016172 * 2 ^ 59
def prefixEnd_5016172 : Nat := 4983230072969 + 3 ^ 40 * 5016172 * 2
def baseEnd_5016172 : Nat := 2575707281625053437681051

theorem tailTrace_5016172 : CollatzResearch.WordTrace tailWord_5016172 prefixEnd_5016172 2575707281625053437681051 := by
  unfold tailWord_5016172
  simp only [CollatzResearch.WordTrace]
  refine ⟨91477411591636506408909385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121969882122182008545212513 91477411591636506408909385)
  ·
    refine ⟨68608058693727379806682039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91477411591636506408909385 68608058693727379806682039)
    ·
      refine ⟨102912088040591069710023059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68608058693727379806682039 102912088040591069710023059)
      ·
        refine ⟨154368132060886604565034589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102912088040591069710023059 154368132060886604565034589)
        ·
          refine ⟨57888049522832476711887971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154368132060886604565034589 57888049522832476711887971)
          ·
            refine ⟨86832074284248715067831957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57888049522832476711887971 86832074284248715067831957)
            ·
              refine ⟨4070253482074158518804623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86832074284248715067831957 4070253482074158518804623)
              ·
                refine ⟨6105380223111237778206935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4070253482074158518804623 6105380223111237778206935)
                ·
                  refine ⟨9158070334666856667310403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6105380223111237778206935 9158070334666856667310403)
                  ·
                    refine ⟨13737105502000285000965605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9158070334666856667310403 13737105502000285000965605)
                    ·
                      refine ⟨2575707281625053437681051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13737105502000285000965605 2575707281625053437681051)
                      ·
                        rfl

theorem cell23_5016172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 4].length) (baseStart_5016172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016172 prefixEnd_5016172 := by exact prefixLift 5016172
  have htrace : WordTrace (prefixWord ++ tailWord_5016172) baseStart_5016172 baseEnd_5016172 := by
    simpa [prefixWord, tailWord_5016172, baseEnd_5016172] using wordTrace_append hprefix tailTrace_5016172
  have hstable : (prefixWord ++ tailWord_5016172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016172).length < 2 ^ (prefixWord ++ tailWord_5016172).sum := by decide
  have hdescent : baseEnd_5016172 < baseStart_5016172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016212 : List Nat := [2, 4, 2, 2, 1, 1, 4, 7]
def baseStart_5016212 : Nat := 118140960795 + 5016212 * 2 ^ 59
def prefixEnd_5016212 : Nat := 4983230072969 + 3 ^ 40 * 5016212 * 2
def baseEnd_5016212 : Nat := 95397326698193825228921

theorem tailTrace_5016212 : CollatzResearch.WordTrace tailWord_5016212 prefixEnd_5016212 95397326698193825228921 := by
  unfold tailWord_5016212
  simp only [CollatzResearch.WordTrace]
  refine ⟨91478141051564049824637445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121970854735418733099516593 91478141051564049824637445)
  ·
    refine ⟨17152151447168259342119521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91478141051564049824637445 17152151447168259342119521)
    ·
      refine ⟨12864113585376194506589641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17152151447168259342119521 12864113585376194506589641)
      ·
        refine ⟨9648085189032145879942231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12864113585376194506589641 9648085189032145879942231)
        ·
          refine ⟨14472127783548218819913347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9648085189032145879942231 14472127783548218819913347)
          ·
            refine ⟨21708191675322328229870021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14472127783548218819913347 21708191675322328229870021)
            ·
              refine ⟨4070285939122936543100629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21708191675322328229870021 4070285939122936543100629)
              ·
                refine ⟨95397326698193825228921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4070285939122936543100629 95397326698193825228921)
                ·
                  rfl

theorem cell23_5016212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 7].length) (baseStart_5016212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016212 prefixEnd_5016212 := by exact prefixLift 5016212
  have htrace : WordTrace (prefixWord ++ tailWord_5016212) baseStart_5016212 baseEnd_5016212 := by
    simpa [prefixWord, tailWord_5016212, baseEnd_5016212] using wordTrace_append hprefix tailTrace_5016212
  have hstable : (prefixWord ++ tailWord_5016212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016212).length < 2 ^ (prefixWord ++ tailWord_5016212).sum := by decide
  have hdescent : baseEnd_5016212 < baseStart_5016212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016222 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_5016222 : Nat := 118140960795 + 5016222 * 2 ^ 59
def prefixEnd_5016222 : Nat := 4983230072969 + 3 ^ 40 * 5016222 * 2
def baseEnd_5016222 : Nat := 2575732955657778242055821

theorem tailTrace_5016222 : CollatzResearch.WordTrace tailWord_5016222 prefixEnd_5016222 2575732955657778242055821 := by
  unfold tailWord_5016222
  simp only [CollatzResearch.WordTrace]
  refine ⟨22869580854136483919642365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121971097888727914238092613 22869580854136483919642365)
  ·
    refine ⟨8576092820301181469865887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22869580854136483919642365 8576092820301181469865887)
    ·
      refine ⟨12864139230451772204798831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8576092820301181469865887 12864139230451772204798831)
      ·
        refine ⟨19296208845677658307198247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12864139230451772204798831 19296208845677658307198247)
        ·
          refine ⟨28944313268516487460797371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19296208845677658307198247 28944313268516487460797371)
          ·
            refine ⟨43416469902774731191196057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28944313268516487460797371 43416469902774731191196057)
            ·
              refine ⟨32562352427081048393397043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43416469902774731191196057 32562352427081048393397043)
              ·
                refine ⟨48843528640621572590095565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32562352427081048393397043 48843528640621572590095565)
                ·
                  refine ⟨18316323240233089721285837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48843528640621572590095565 18316323240233089721285837)
                  ·
                    refine ⟨6868621215087408645482189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18316323240233089721285837 6868621215087408645482189)
                    ·
                      refine ⟨2575732955657778242055821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6868621215087408645482189 2575732955657778242055821)
                      ·
                        rfl

theorem cell23_5016222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_5016222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016222 prefixEnd_5016222 := by exact prefixLift 5016222
  have htrace : WordTrace (prefixWord ++ tailWord_5016222) baseStart_5016222 baseEnd_5016222 := by
    simpa [prefixWord, tailWord_5016222, baseEnd_5016222] using wordTrace_append hprefix tailTrace_5016222
  have hstable : (prefixWord ++ tailWord_5016222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016222).length < 2 ^ (prefixWord ++ tailWord_5016222).sum := by decide
  have hdescent : baseEnd_5016222 < baseStart_5016222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016256 : List Nat := [2, 1, 1, 2, 4, 4, 2, 1, 2, 1, 3]
def baseStart_5016256 : Nat := 118140960795 + 5016256 * 2 ^ 59
def prefixEnd_5016256 : Nat := 4983230072969 + 3 ^ 40 * 5016256 * 2
def baseEnd_5016256 : Nat := 2575750414000031109030665

theorem tailTrace_5016256 : CollatzResearch.WordTrace tailWord_5016256 prefixEnd_5016256 2575750414000031109030665 := by
  unfold tailWord_5016256
  simp only [CollatzResearch.WordTrace]
  refine ⟨91478943457484347581938311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121971924609979130109251081 91478943457484347581938311)
  ·
    refine ⟨137218415186226521372907467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91478943457484347581938311 137218415186226521372907467)
    ·
      refine ⟨205827622779339782059361201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137218415186226521372907467 205827622779339782059361201)
      ·
        refine ⟨154370717084504836544520901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205827622779339782059361201 154370717084504836544520901)
        ·
          refine ⟨28944509453344656852097669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154370717084504836544520901 28944509453344656852097669)
          ·
            refine ⟨5427095522502123159768313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28944509453344656852097669 5427095522502123159768313)
            ·
              refine ⟨4070321641876592369826235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5427095522502123159768313 4070321641876592369826235)
              ·
                refine ⟨6105482462814888554739353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4070321641876592369826235 6105482462814888554739353)
                ·
                  refine ⟨4579111847111166416054515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6105482462814888554739353 4579111847111166416054515)
                  ·
                    refine ⟨6868667770666749624081773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4579111847111166416054515 6868667770666749624081773)
                    ·
                      refine ⟨2575750414000031109030665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6868667770666749624081773 2575750414000031109030665)
                      ·
                        rfl

theorem cell23_5016256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 2, 1, 3].length) (baseStart_5016256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016256 prefixEnd_5016256 := by exact prefixLift 5016256
  have htrace : WordTrace (prefixWord ++ tailWord_5016256) baseStart_5016256 baseEnd_5016256 := by
    simpa [prefixWord, tailWord_5016256, baseEnd_5016256] using wordTrace_append hprefix tailTrace_5016256
  have hstable : (prefixWord ++ tailWord_5016256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016256).length < 2 ^ (prefixWord ++ tailWord_5016256).sum := by decide
  have hdescent : baseEnd_5016256 < baseStart_5016256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016266 : List Nat := [3, 1, 2, 1, 4, 3, 1, 2, 1, 3, 2]
def baseStart_5016266 : Nat := 118140960795 + 5016266 * 2 ^ 59
def prefixEnd_5016266 : Nat := 4983230072969 + 3 ^ 40 * 5016266 * 2
def baseEnd_5016266 : Nat := 2575755548806576069905619

theorem tailTrace_5016266 : CollatzResearch.WordTrace tailWord_5016266 prefixEnd_5016266 2575755548806576069905619 := by
  unfold tailWord_5016266
  simp only [CollatzResearch.WordTrace]
  refine ⟨45739562911233116717935163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121972167763288311247827101 45739562911233116717935163)
  ·
    refine ⟨68609344366849675076902745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45739562911233116717935163 68609344366849675076902745)
    ·
      refine ⟨51457008275137256307677059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68609344366849675076902745 51457008275137256307677059)
      ·
        refine ⟨77185512412705884461515589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51457008275137256307677059 77185512412705884461515589)
        ·
          refine ⟨14472283577382353336534173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77185512412705884461515589 14472283577382353336534173)
          ·
            refine ⟨5427106341518382501200315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14472283577382353336534173 5427106341518382501200315)
            ·
              refine ⟨8140659512277573751800473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5427106341518382501200315 8140659512277573751800473)
              ·
                refine ⟨6105494634208180313850355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8140659512277573751800473 6105494634208180313850355)
                ·
                  refine ⟨9158241951312270470775533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6105494634208180313850355 9158241951312270470775533)
                  ·
                    refine ⟨3434340731742101426540825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9158241951312270470775533 3434340731742101426540825)
                    ·
                      refine ⟨2575755548806576069905619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3434340731742101426540825 2575755548806576069905619)
                      ·
                        rfl

theorem cell23_5016266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_5016266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016266 prefixEnd_5016266 := by exact prefixLift 5016266
  have htrace : WordTrace (prefixWord ++ tailWord_5016266) baseStart_5016266 baseEnd_5016266 := by
    simpa [prefixWord, tailWord_5016266, baseEnd_5016266] using wordTrace_append hprefix tailTrace_5016266
  have hstable : (prefixWord ++ tailWord_5016266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016266).length < 2 ^ (prefixWord ++ tailWord_5016266).sum := by decide
  have hdescent : baseEnd_5016266 < baseStart_5016266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016335 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 4]
def baseStart_5016335 : Nat := 118140960795 + 5016335 * 2 ^ 59
def prefixEnd_5016335 : Nat := 4983230072969 + 3 ^ 40 * 5016335 * 2
def baseEnd_5016335 : Nat := 2575790978971736299942801

theorem tailTrace_5016335 : CollatzResearch.WordTrace tailWord_5016335 prefixEnd_5016335 2575790978971736299942801 := by
  unfold tailWord_5016335
  simp only [CollatzResearch.WordTrace]
  refine ⟨182960768281682491656002459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121973845521121661104001639 182960768281682491656002459)
  ·
    refine ⟨274441152422523737484003689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182960768281682491656002459 274441152422523737484003689)
    ·
      refine ⟨205830864316892803113002767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274441152422523737484003689 205830864316892803113002767)
      ·
        refine ⟨308746296475339204669504151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205830864316892803113002767 308746296475339204669504151)
        ·
          refine ⟨463119444713008807004256227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308746296475339204669504151 463119444713008807004256227)
          ·
            refine ⟨694679167069513210506384341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463119444713008807004256227 694679167069513210506384341)
            ·
              refine ⟨16281542978191715871243383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 694679167069513210506384341 16281542978191715871243383)
              ·
                refine ⟨24422314467287573806865075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16281542978191715871243383 24422314467287573806865075)
                ·
                  refine ⟨36633471700931360710297613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24422314467287573806865075 36633471700931360710297613)
                  ·
                    refine ⟨13737551887849260266361605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36633471700931360710297613 13737551887849260266361605)
                    ·
                      refine ⟨2575790978971736299942801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13737551887849260266361605 2575790978971736299942801)
                      ·
                        rfl

theorem cell23_5016335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_5016335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016335 prefixEnd_5016335 := by exact prefixLift 5016335
  have htrace : WordTrace (prefixWord ++ tailWord_5016335) baseStart_5016335 baseEnd_5016335 := by
    simpa [prefixWord, tailWord_5016335, baseEnd_5016335] using wordTrace_append hprefix tailTrace_5016335
  have hstable : (prefixWord ++ tailWord_5016335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016335).length < 2 ^ (prefixWord ++ tailWord_5016335).sum := by decide
  have hdescent : baseEnd_5016335 < baseStart_5016335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016396 : List Nat := [2, 2, 1, 3, 3, 1, 3, 3, 1, 4]
def baseStart_5016396 : Nat := 118140960795 + 5016396 * 2 ^ 59
def prefixEnd_5016396 : Nat := 4983230072969 + 3 ^ 40 * 5016396 * 2
def baseEnd_5016396 : Nat := 858607433763886853760007

theorem tailTrace_5016396 : CollatzResearch.WordTrace tailWord_5016396 prefixEnd_5016396 858607433763886853760007 := by
  unfold tailWord_5016396
  simp only [CollatzResearch.WordTrace]
  refine ⟨91481496567230749536986521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121975328756307666049315361 91481496567230749536986521)
  ·
    refine ⟨68611122425423062152739891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91481496567230749536986521 68611122425423062152739891)
    ·
      refine ⟨102916683638134593229109837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68611122425423062152739891 102916683638134593229109837)
      ·
        refine ⟨38593756364300472460916189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102916683638134593229109837 38593756364300472460916189)
        ·
          refine ⟨14472658636612677172843571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38593756364300472460916189 14472658636612677172843571)
          ·
            refine ⟨21708987954919015759265357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14472658636612677172843571 21708987954919015759265357)
            ·
              refine ⟨8140870483094630909724509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21708987954919015759265357 8140870483094630909724509)
              ·
                refine ⟨3052826431160486591146691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8140870483094630909724509 3052826431160486591146691)
                ·
                  refine ⟨4579239646740729886720037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3052826431160486591146691 4579239646740729886720037)
                  ·
                    refine ⟨858607433763886853760007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4579239646740729886720037 858607433763886853760007)
                    ·
                      rfl

theorem cell23_5016396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 1, 4].length) (baseStart_5016396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016396 prefixEnd_5016396 := by exact prefixLift 5016396
  have htrace : WordTrace (prefixWord ++ tailWord_5016396) baseStart_5016396 baseEnd_5016396 := by
    simpa [prefixWord, tailWord_5016396, baseEnd_5016396] using wordTrace_append hprefix tailTrace_5016396
  have hstable : (prefixWord ++ tailWord_5016396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016396).length < 2 ^ (prefixWord ++ tailWord_5016396).sum := by decide
  have hdescent : baseEnd_5016396 < baseStart_5016396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016425 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 1, 7, 4]
def baseStart_5016425 : Nat := 118140960795 + 5016425 * 2 ^ 59
def prefixEnd_5016425 : Nat := 4983230072969 + 3 ^ 40 * 5016425 * 2
def baseEnd_5016425 : Nat := 2575837192230640947817387

theorem tailTrace_5016425 : CollatzResearch.WordTrace tailWord_5016425 prefixEnd_5016425 2575837192230640947817387 := by
  unfold tailWord_5016425
  simp only [CollatzResearch.WordTrace]
  refine ⟨182964050851356437026778729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121976033900904291351185819 182964050851356437026778729)
  ·
    refine ⟨137223038138517327770084047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182964050851356437026778729 137223038138517327770084047)
    ·
      refine ⟨205834557207775991655126071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137223038138517327770084047 205834557207775991655126071)
      ·
        refine ⟨308751835811663987482689107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205834557207775991655126071 308751835811663987482689107)
        ·
          refine ⟨463127753717495981224033661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308751835811663987482689107 463127753717495981224033661)
          ·
            refine ⟨173672907644060992959012623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 463127753717495981224033661 173672907644060992959012623)
            ·
              refine ⟨260509361466091489438518935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173672907644060992959012623 260509361466091489438518935)
              ·
                refine ⟨390764042199137234157778403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260509361466091489438518935 390764042199137234157778403)
                ·
                  refine ⟨586146063298705851236667605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390764042199137234157778403 586146063298705851236667605)
                  ·
                    refine ⟨13737798358563418388359397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 586146063298705851236667605 13737798358563418388359397)
                    ·
                      refine ⟨2575837192230640947817387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13737798358563418388359397 2575837192230640947817387)
                      ·
                        rfl

theorem cell23_5016425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_5016425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016425 prefixEnd_5016425 := by exact prefixLift 5016425
  have htrace : WordTrace (prefixWord ++ tailWord_5016425) baseStart_5016425 baseEnd_5016425 := by
    simpa [prefixWord, tailWord_5016425, baseEnd_5016425] using wordTrace_append hprefix tailTrace_5016425
  have hstable : (prefixWord ++ tailWord_5016425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016425).length < 2 ^ (prefixWord ++ tailWord_5016425).sum := by decide
  have hdescent : baseEnd_5016425 < baseStart_5016425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016429 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 6, 3, 2]
def baseStart_5016429 : Nat := 118140960795 + 5016429 * 2 ^ 59
def prefixEnd_5016429 : Nat := 4983230072969 + 3 ^ 40 * 5016429 * 2
def baseEnd_5016429 : Nat := 2575839246153258932167369

theorem tailTrace_5016429 : CollatzResearch.WordTrace tailWord_5016429 prefixEnd_5016429 2575839246153258932167369 := by
  unfold tailWord_5016429
  simp only [CollatzResearch.WordTrace]
  refine ⟨182964196743341945709924341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121976131162227963806616227 182964196743341945709924341)
  ·
    refine ⟨17152893444688307410305407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 182964196743341945709924341 17152893444688307410305407)
    ·
      refine ⟨25729340167032461115458111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17152893444688307410305407 25729340167032461115458111)
      ·
        refine ⟨38594010250548691673187167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25729340167032461115458111 38594010250548691673187167)
        ·
          refine ⟨57891015375823037509780751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38594010250548691673187167 57891015375823037509780751)
          ·
            refine ⟨86836523063734556264671127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57891015375823037509780751 86836523063734556264671127)
            ·
              refine ⟨130254784595601834397006691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86836523063734556264671127 130254784595601834397006691)
              ·
                refine ⟨195382176893402751595510037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130254784595601834397006691 195382176893402751595510037)
                ·
                  refine ⟨9158539541878253981039533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 195382176893402751595510037 9158539541878253981039533)
                  ·
                    refine ⟨3434452328204345242889825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9158539541878253981039533 3434452328204345242889825)
                    ·
                      refine ⟨2575839246153258932167369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3434452328204345242889825 2575839246153258932167369)
                      ·
                        rfl

theorem cell23_5016429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_5016429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016429 prefixEnd_5016429 := by exact prefixLift 5016429
  have htrace : WordTrace (prefixWord ++ tailWord_5016429) baseStart_5016429 baseEnd_5016429 := by
    simpa [prefixWord, tailWord_5016429, baseEnd_5016429] using wordTrace_append hprefix tailTrace_5016429
  have hstable : (prefixWord ++ tailWord_5016429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016429).length < 2 ^ (prefixWord ++ tailWord_5016429).sum := by decide
  have hdescent : baseEnd_5016429 < baseStart_5016429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016456 : List Nat := [2, 1, 3, 3, 2, 2, 3, 1, 1, 5]
def baseStart_5016456 : Nat := 118140960795 + 5016456 * 2 ^ 59
def prefixEnd_5016456 : Nat := 4983230072969 + 3 ^ 40 * 5016456 * 2
def baseEnd_5016456 : Nat := 858617703376976775509915

theorem tailTrace_5016456 : CollatzResearch.WordTrace tailWord_5016456 prefixEnd_5016456 858617703376976775509915 := by
  unfold tailWord_5016456
  simp only [CollatzResearch.WordTrace]
  refine ⟨91482590757122064660578611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121976787676162752880771481 91482590757122064660578611)
  ·
    refine ⟨137223886135683096990867917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91482590757122064660578611 137223886135683096990867917)
    ·
      refine ⟨51458957300881161371575469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137223886135683096990867917 51458957300881161371575469)
      ·
        refine ⟨19297108987830435514340801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51458957300881161371575469 19297108987830435514340801)
        ·
          refine ⟨14472831740872826635755601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19297108987830435514340801 14472831740872826635755601)
          ·
            refine ⟨10854623805654619976816701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14472831740872826635755601 10854623805654619976816701)
            ·
              refine ⟨4070483927120482491306263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10854623805654619976816701 4070483927120482491306263)
              ·
                refine ⟨6105725890680723736959395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4070483927120482491306263 6105725890680723736959395)
                ·
                  refine ⟨9158588836021085605439093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6105725890680723736959395 9158588836021085605439093)
                  ·
                    refine ⟨858617703376976775509915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9158588836021085605439093 858617703376976775509915)
                    ·
                      rfl

theorem cell23_5016456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_5016456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016456 prefixEnd_5016456 := by exact prefixLift 5016456
  have htrace : WordTrace (prefixWord ++ tailWord_5016456) baseStart_5016456 baseEnd_5016456 := by
    simpa [prefixWord, tailWord_5016456, baseEnd_5016456] using wordTrace_append hprefix tailTrace_5016456
  have hstable : (prefixWord ++ tailWord_5016456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016456).length < 2 ^ (prefixWord ++ tailWord_5016456).sum := by decide
  have hdescent : baseEnd_5016456 < baseStart_5016456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016469 : List Nat := [1, 3, 2, 1, 1, 4, 1, 4, 2, 4]
def baseStart_5016469 : Nat := 118140960795 + 5016469 * 2 ^ 59
def prefixEnd_5016469 : Nat := 4983230072969 + 3 ^ 40 * 5016469 * 2
def baseEnd_5016469 : Nat := 858619928459812925222395

theorem tailTrace_5016469 : CollatzResearch.WordTrace tailWord_5016469 prefixEnd_5016469 858619928459812925222395 := by
  unfold tailWord_5016469
  simp only [CollatzResearch.WordTrace]
  refine ⟨182965655663197032541380461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121977103775464688360920307 182965655663197032541380461)
  ·
    refine ⟨68612120873698887203017673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182965655663197032541380461 68612120873698887203017673)
    ·
      refine ⟨51459090655274165402263255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68612120873698887203017673 51459090655274165402263255)
      ·
        refine ⟨77188635982911248103394883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51459090655274165402263255 77188635982911248103394883)
        ·
          refine ⟨115782953974366872155092325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77188635982911248103394883 115782953974366872155092325)
          ·
            refine ⟨21709303870193788529079811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115782953974366872155092325 21709303870193788529079811)
            ·
              refine ⟨32563955805290682793619717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21709303870193788529079811 32563955805290682793619717)
              ·
                refine ⟨6105741713492003023803697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32563955805290682793619717 6105741713492003023803697)
                ·
                  refine ⟨4579306285119002267852773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6105741713492003023803697 4579306285119002267852773)
                  ·
                    refine ⟨858619928459812925222395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4579306285119002267852773 858619928459812925222395)
                    ·
                      rfl

theorem cell23_5016469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_5016469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016469 prefixEnd_5016469 := by exact prefixLift 5016469
  have htrace : WordTrace (prefixWord ++ tailWord_5016469) baseStart_5016469 baseEnd_5016469 := by
    simpa [prefixWord, tailWord_5016469, baseEnd_5016469] using wordTrace_append hprefix tailTrace_5016469
  have hstable : (prefixWord ++ tailWord_5016469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016469).length < 2 ^ (prefixWord ++ tailWord_5016469).sum := by decide
  have hdescent : baseEnd_5016469 < baseStart_5016469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016479 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 3]
def baseStart_5016479 : Nat := 118140960795 + 5016479 * 2 ^ 59
def prefixEnd_5016479 : Nat := 4983230072969 + 3 ^ 40 * 5016479 * 2
def baseEnd_5016479 : Nat := 2575864920185983736542139

theorem tailTrace_5016479 : CollatzResearch.WordTrace tailWord_5016479 prefixEnd_5016479 2575864920185983736542139 := by
  unfold tailWord_5016479
  simp only [CollatzResearch.WordTrace]
  refine ⟨182966020393160804249244491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121977346928773869499496327 182966020393160804249244491)
  ·
    refine ⟨274449030589741206373866737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182966020393160804249244491 274449030589741206373866737)
    ·
      refine ⟨205836772942305904780400053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274449030589741206373866737 205836772942305904780400053)
      ·
        refine ⟨19297197463341178573162505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 205836772942305904780400053 19297197463341178573162505)
        ·
          refine ⟨14472898097505883929871879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19297197463341178573162505 14472898097505883929871879)
          ·
            refine ⟨21709347146258825894807819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14472898097505883929871879 21709347146258825894807819)
            ·
              refine ⟨32564020719388238842211729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21709347146258825894807819 32564020719388238842211729)
              ·
                refine ⟨24423015539541179131658797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32564020719388238842211729 24423015539541179131658797)
                ·
                  refine ⟨9158630827327942174372049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24423015539541179131658797 9158630827327942174372049)
                  ·
                    refine ⟨6868973120495956630779037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9158630827327942174372049 6868973120495956630779037)
                    ·
                      refine ⟨2575864920185983736542139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6868973120495956630779037 2575864920185983736542139)
                      ·
                        rfl

theorem cell23_5016479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_5016479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016479 prefixEnd_5016479 := by exact prefixLift 5016479
  have htrace : WordTrace (prefixWord ++ tailWord_5016479) baseStart_5016479 baseEnd_5016479 := by
    simpa [prefixWord, tailWord_5016479, baseEnd_5016479] using wordTrace_append hprefix tailTrace_5016479
  have hstable : (prefixWord ++ tailWord_5016479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016479).length < 2 ^ (prefixWord ++ tailWord_5016479).sum := by decide
  have hdescent : baseEnd_5016479 < baseStart_5016479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016492 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 3]
def baseStart_5016492 : Nat := 118140960795 + 5016492 * 2 ^ 59
def prefixEnd_5016492 : Nat := 4983230072969 + 3 ^ 40 * 5016492 * 2
def baseEnd_5016492 : Nat := 2575871595434492185679579

theorem tailTrace_5016492 : CollatzResearch.WordTrace tailWord_5016492 prefixEnd_5016492 2575871595434492185679579 := by
  unfold tailWord_5016492
  simp only [CollatzResearch.WordTrace]
  refine ⟨91483247271056853734733865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121977663028075804979645153 91483247271056853734733865)
  ·
    refine ⟨68612435453292640301050399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91483247271056853734733865 68612435453292640301050399)
    ·
      refine ⟨102918653179938960451575599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68612435453292640301050399 102918653179938960451575599)
      ·
        refine ⟨154377979769908440677363399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102918653179938960451575599 154377979769908440677363399)
        ·
          refine ⟨231566969654862661016045099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154377979769908440677363399 231566969654862661016045099)
          ·
            refine ⟨347350454482293991524067649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231566969654862661016045099 347350454482293991524067649)
            ·
              refine ⟨260512840861720493643050737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347350454482293991524067649 260512840861720493643050737)
              ·
                refine ⟨195384630646290370232288053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260512840861720493643050737 195384630646290370232288053)
                ·
                  refine ⟨18317309123089722209277005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 195384630646290370232288053 18317309123089722209277005)
                  ·
                    refine ⟨6868990921158645828478877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18317309123089722209277005 6868990921158645828478877)
                    ·
                      refine ⟨2575871595434492185679579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6868990921158645828478877 2575871595434492185679579)
                      ·
                        rfl

theorem cell23_5016492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_5016492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016492 prefixEnd_5016492 := by exact prefixLift 5016492
  have htrace : WordTrace (prefixWord ++ tailWord_5016492) baseStart_5016492 baseEnd_5016492 := by
    simpa [prefixWord, tailWord_5016492, baseEnd_5016492] using wordTrace_append hprefix tailTrace_5016492
  have hstable : (prefixWord ++ tailWord_5016492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016492).length < 2 ^ (prefixWord ++ tailWord_5016492).sum := by decide
  have hdescent : baseEnd_5016492 < baseStart_5016492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016510 : List Nat := [4, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2]
def baseStart_5016510 : Nat := 118140960795 + 5016510 * 2 ^ 59
def prefixEnd_5016510 : Nat := 4983230072969 + 3 ^ 40 * 5016510 * 2
def baseEnd_5016510 : Nat := 2575880838086273115254497

theorem tailTrace_5016510 : CollatzResearch.WordTrace tailWord_5016510 prefixEnd_5016510 2575880838086273115254497 := by
  unfold tailWord_5016510
  simp only [CollatzResearch.WordTrace]
  refine ⟨22870893882006062067952873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121978100704032331029081989 22870893882006062067952873)
  ·
    refine ⟨17153170411504546550964655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22870893882006062067952873 17153170411504546550964655)
    ·
      refine ⟨25729755617256819826446983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17153170411504546550964655 25729755617256819826446983)
      ·
        refine ⟨38594633425885229739670475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25729755617256819826446983 38594633425885229739670475)
        ·
          refine ⟨57891950138827844609505713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38594633425885229739670475 57891950138827844609505713)
          ·
            refine ⟨43418962604120883457129285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57891950138827844609505713 43418962604120883457129285)
            ·
              refine ⟨8141055488272665648211741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43418962604120883457129285 8141055488272665648211741)
              ·
                refine ⟨3052895808102249618079403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8141055488272665648211741 3052895808102249618079403)
                ·
                  refine ⟨4579343712153374427119105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3052895808102249618079403 4579343712153374427119105)
                  ·
                    refine ⟨3434507784115030820339329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4579343712153374427119105 3434507784115030820339329)
                    ·
                      refine ⟨2575880838086273115254497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3434507784115030820339329 2575880838086273115254497)
                      ·
                        rfl

theorem cell23_5016510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_5016510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016510 prefixEnd_5016510 := by exact prefixLift 5016510
  have htrace : WordTrace (prefixWord ++ tailWord_5016510) baseStart_5016510 baseEnd_5016510 := by
    simpa [prefixWord, tailWord_5016510, baseEnd_5016510] using wordTrace_append hprefix tailTrace_5016510
  have hstable : (prefixWord ++ tailWord_5016510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016510).length < 2 ^ (prefixWord ++ tailWord_5016510).sum := by decide
  have hdescent : baseEnd_5016510 < baseStart_5016510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016526 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3]
def baseStart_5016526 : Nat := 118140960795 + 5016526 * 2 ^ 59
def prefixEnd_5016526 : Nat := 4983230072969 + 3 ^ 40 * 5016526 * 2
def baseEnd_5016526 : Nat := 2575889053776745052654423

theorem tailTrace_5016526 : CollatzResearch.WordTrace tailWord_5016526 prefixEnd_5016526 2575889053776745052654423 := by
  unfold tailWord_5016526
  simp only [CollatzResearch.WordTrace]
  refine ⟨22870966827998816409525679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121978489749327020850803621 22870966827998816409525679)
  ·
    refine ⟨34306450241998224614288519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22870966827998816409525679 34306450241998224614288519)
    ·
      refine ⟨51459675362997336921432779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34306450241998224614288519 51459675362997336921432779)
      ·
        refine ⟨77189513044496005382149169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51459675362997336921432779 77189513044496005382149169)
        ·
          refine ⟨57892134783372004036611877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77189513044496005382149169 57892134783372004036611877)
          ·
            refine ⟨10854775271882250756864727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57892134783372004036611877 10854775271882250756864727)
            ·
              refine ⟨16282162907823376135297091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10854775271882250756864727 16282162907823376135297091)
              ·
                refine ⟨24423244361735064202945637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16282162907823376135297091 24423244361735064202945637)
                ·
                  refine ⟨4579358317825324538052307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24423244361735064202945637 4579358317825324538052307)
                  ·
                    refine ⟨6869037476737986807078461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4579358317825324538052307 6869037476737986807078461)
                    ·
                      refine ⟨2575889053776745052654423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6869037476737986807078461 2575889053776745052654423)
                      ·
                        rfl

theorem cell23_5016526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_5016526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016526 prefixEnd_5016526 := by exact prefixLift 5016526
  have htrace : WordTrace (prefixWord ++ tailWord_5016526) baseStart_5016526 baseEnd_5016526 := by
    simpa [prefixWord, tailWord_5016526, baseEnd_5016526] using wordTrace_append hprefix tailTrace_5016526
  have hstable : (prefixWord ++ tailWord_5016526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016526).length < 2 ^ (prefixWord ++ tailWord_5016526).sum := by decide
  have hdescent : baseEnd_5016526 < baseStart_5016526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016543 : List Nat := [1, 1, 2, 3, 6, 1, 1, 1, 1, 3, 3]
def baseStart_5016543 : Nat := 118140960795 + 5016543 * 2 ^ 59
def prefixEnd_5016543 : Nat := 4983230072969 + 3 ^ 40 * 5016543 * 2
def baseEnd_5016543 : Nat := 2575897782947871486141845

theorem tailTrace_5016543 : CollatzResearch.WordTrace tailWord_5016543 prefixEnd_5016543 2575897782947871486141845 := by
  unfold tailWord_5016543
  simp only [CollatzResearch.WordTrace]
  refine ⟨182968354664928943179574283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121978903109952628786382855 182968354664928943179574283)
  ·
    refine ⟨274452531997393414769361425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182968354664928943179574283 274452531997393414769361425)
    ·
      refine ⟨205839398998045061077021069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274452531997393414769361425 205839398998045061077021069)
      ·
        refine ⟨77189774624266897903882901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205839398998045061077021069 77189774624266897903882901)
        ·
          refine ⟨3618270685512510839244511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 77189774624266897903882901 3618270685512510839244511)
          ·
            refine ⟨5427406028268766258866767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3618270685512510839244511 5427406028268766258866767)
            ·
              refine ⟨8141109042403149388300151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5427406028268766258866767 8141109042403149388300151)
              ·
                refine ⟨12211663563604724082450227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8141109042403149388300151 12211663563604724082450227)
                ·
                  refine ⟨18317495345407086123675341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12211663563604724082450227 18317495345407086123675341)
                  ·
                    refine ⟨6869060754527657296378253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18317495345407086123675341 6869060754527657296378253)
                    ·
                      refine ⟨2575897782947871486141845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6869060754527657296378253 2575897782947871486141845)
                      ·
                        rfl

theorem cell23_5016543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_5016543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016543 prefixEnd_5016543 := by exact prefixLift 5016543
  have htrace : WordTrace (prefixWord ++ tailWord_5016543) baseStart_5016543 baseEnd_5016543 := by
    simpa [prefixWord, tailWord_5016543, baseEnd_5016543] using wordTrace_append hprefix tailTrace_5016543
  have hstable : (prefixWord ++ tailWord_5016543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016543).length < 2 ^ (prefixWord ++ tailWord_5016543).sum := by decide
  have hdescent : baseEnd_5016543 < baseStart_5016543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016583 : List Nat := [1, 1, 4, 3, 1, 1, 2, 4, 2, 2, 2]
def baseStart_5016583 : Nat := 118140960795 + 5016583 * 2 ^ 59
def prefixEnd_5016583 : Nat := 4983230072969 + 3 ^ 40 * 5016583 * 2
def baseEnd_5016583 : Nat := 2575918322174051329641661

theorem tailTrace_5016583 : CollatzResearch.WordTrace tailWord_5016583 prefixEnd_5016583 2575918322174051329641661 := by
  unfold tailWord_5016583
  simp only [CollatzResearch.WordTrace]
  refine ⟨182969813584784030011030403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121979875723189353340686935 182969813584784030011030403)
  ·
    refine ⟨274454720377176045016545605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182969813584784030011030403 274454720377176045016545605)
    ·
      refine ⟨51460260070720508440602301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 274454720377176045016545605 51460260070720508440602301)
      ·
        refine ⟨19297597526520190665225863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51460260070720508440602301 19297597526520190665225863)
        ·
          refine ⟨28946396289780285997838795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19297597526520190665225863 28946396289780285997838795)
          ·
            refine ⟨43419594434670428996758193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28946396289780285997838795 43419594434670428996758193)
            ·
              refine ⟨32564695826002821747568645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43419594434670428996758193 32564695826002821747568645)
              ·
                refine ⟨6105880467375529077669121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32564695826002821747568645 6105880467375529077669121)
                ·
                  refine ⟨4579410350531646808251841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6105880467375529077669121 4579410350531646808251841)
                  ·
                    refine ⟨3434557762898735106188881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4579410350531646808251841 3434557762898735106188881)
                    ·
                      refine ⟨2575918322174051329641661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3434557762898735106188881 2575918322174051329641661)
                      ·
                        rfl

theorem cell23_5016583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_5016583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016583 prefixEnd_5016583 := by exact prefixLift 5016583
  have htrace : WordTrace (prefixWord ++ tailWord_5016583) baseStart_5016583 baseEnd_5016583 := by
    simpa [prefixWord, tailWord_5016583, baseEnd_5016583] using wordTrace_append hprefix tailTrace_5016583
  have hstable : (prefixWord ++ tailWord_5016583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016583).length < 2 ^ (prefixWord ++ tailWord_5016583).sum := by decide
  have hdescent : baseEnd_5016583 < baseStart_5016583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016600 : List Nat := [2, 1, 2, 3, 2, 2, 4, 1, 2, 2, 2]
def baseStart_5016600 : Nat := 118140960795 + 5016600 * 2 ^ 59
def prefixEnd_5016600 : Nat := 4983230072969 + 3 ^ 40 * 5016600 * 2
def baseEnd_5016600 : Nat := 2575927051345177763129083

theorem tailTrace_5016600 : CollatzResearch.WordTrace tailWord_5016600 prefixEnd_5016600 2575927051345177763129083 := by
  unfold tailWord_5016600
  simp only [CollatzResearch.WordTrace]
  refine ⟨91485216812861220957199627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121980289083814961276266169 91485216812861220957199627)
  ·
    refine ⟨137227825219291831435799441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91485216812861220957199627 137227825219291831435799441)
    ·
      refine ⟨102920868914468873576849581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137227825219291831435799441 102920868914468873576849581)
      ·
        refine ⟨38595325842925827591318593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102920868914468873576849581 38595325842925827591318593)
        ·
          refine ⟨28946494382194370693488945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38595325842925827591318593 28946494382194370693488945)
          ·
            refine ⟨21709870786645778020116709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28946494382194370693488945 21709870786645778020116709)
            ·
              refine ⟨4070600772496083378771883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21709870786645778020116709 4070600772496083378771883)
              ·
                refine ⟨6105901158744125068157825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4070600772496083378771883 6105901158744125068157825)
                ·
                  refine ⟨4579425869058093801118369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6105901158744125068157825 4579425869058093801118369)
                  ·
                    refine ⟨3434569401793570350838777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4579425869058093801118369 3434569401793570350838777)
                    ·
                      refine ⟨2575927051345177763129083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3434569401793570350838777 2575927051345177763129083)
                      ·
                        rfl

theorem cell23_5016600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_5016600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016600 prefixEnd_5016600 := by exact prefixLift 5016600
  have htrace : WordTrace (prefixWord ++ tailWord_5016600) baseStart_5016600 baseEnd_5016600 := by
    simpa [prefixWord, tailWord_5016600, baseEnd_5016600] using wordTrace_append hprefix tailTrace_5016600
  have hstable : (prefixWord ++ tailWord_5016600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016600).length < 2 ^ (prefixWord ++ tailWord_5016600).sum := by decide
  have hdescent : baseEnd_5016600 < baseStart_5016600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016619 : List Nat := [1, 1, 1, 1, 2, 1, 8, 1, 2, 5]
def baseStart_5016619 : Nat := 118140960795 + 5016619 * 2 ^ 59
def prefixEnd_5016619 : Nat := 4983230072969 + 3 ^ 40 * 5016619 * 2
def baseEnd_5016619 : Nat := 858645602492537729597165

theorem tailTrace_5016619 : CollatzResearch.WordTrace tailWord_5016619 prefixEnd_5016619 858645602492537729597165 := by
  unfold tailWord_5016619
  simp only [CollatzResearch.WordTrace]
  refine ⟨182971126612653608159340911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121980751075102405439560607 182971126612653608159340911)
  ·
    refine ⟨274456689918980412239011367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182971126612653608159340911 274456689918980412239011367)
    ·
      refine ⟨411685034878470618358517051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274456689918980412239011367 411685034878470618358517051)
      ·
        refine ⟨617527552317705927537775577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411685034878470618358517051 617527552317705927537775577)
        ·
          refine ⟨463145664238279445653331683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 617527552317705927537775577 463145664238279445653331683)
          ·
            refine ⟨694718496357419168479997525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463145664238279445653331683 694718496357419168479997525)
            ·
              refine ⟨8141232379188505880624971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 694718496357419168479997525 8141232379188505880624971)
              ·
                refine ⟨12211848568782758820937457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8141232379188505880624971 12211848568782758820937457)
                ·
                  refine ⟨9158886426587069115703093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12211848568782758820937457 9158886426587069115703093)
                  ·
                    refine ⟨858645602492537729597165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9158886426587069115703093 858645602492537729597165)
                    ·
                      rfl

theorem cell23_5016619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 5].length) (baseStart_5016619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016619 prefixEnd_5016619 := by exact prefixLift 5016619
  have htrace : WordTrace (prefixWord ++ tailWord_5016619) baseStart_5016619 baseEnd_5016619 := by
    simpa [prefixWord, tailWord_5016619, baseEnd_5016619] using wordTrace_append hprefix tailTrace_5016619
  have hstable : (prefixWord ++ tailWord_5016619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016619).length < 2 ^ (prefixWord ++ tailWord_5016619).sum := by decide
  have hdescent : baseEnd_5016619 < baseStart_5016619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016659 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 3]
def baseStart_5016659 : Nat := 118140960795 + 5016659 * 2 ^ 59
def prefixEnd_5016659 : Nat := 4983230072969 + 3 ^ 40 * 5016659 * 2
def baseEnd_5016659 : Nat := 2575957346703793032291311

theorem tailTrace_5016659 : CollatzResearch.WordTrace tailWord_5016659 prefixEnd_5016659 2575957346703793032291311 := by
  unfold tailWord_5016659
  simp only [CollatzResearch.WordTrace]
  refine ⟨182972585532508694990797031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121981723688339129993864687 182972585532508694990797031)
  ·
    refine ⟨274458878298763042486195547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182972585532508694990797031 274458878298763042486195547)
    ·
      refine ⟨411688317448144563729293321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274458878298763042486195547 411688317448144563729293321)
      ·
        refine ⟨308766238086108422796969991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 411688317448144563729293321 308766238086108422796969991)
        ·
          refine ⟨463149357129162634195454987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308766238086108422796969991 463149357129162634195454987)
          ·
            refine ⟨694724035693743951293182481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463149357129162634195454987 694724035693743951293182481)
            ·
              refine ⟨521043026770307963469886861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 694724035693743951293182481 521043026770307963469886861)
              ·
                refine ⟨195391135038865486301207573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 521043026770307963469886861 195391135038865486301207573)
                ·
                  refine ⟨9158959454946819670369105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 195391135038865486301207573 9158959454946819670369105)
                  ·
                    refine ⟨6869219591210114752776829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9158959454946819670369105 6869219591210114752776829)
                    ·
                      refine ⟨2575957346703793032291311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6869219591210114752776829 2575957346703793032291311)
                      ·
                        rfl

theorem cell23_5016659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 3].length) (baseStart_5016659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016659 prefixEnd_5016659 := by exact prefixLift 5016659
  have htrace : WordTrace (prefixWord ++ tailWord_5016659) baseStart_5016659 baseEnd_5016659 := by
    simpa [prefixWord, tailWord_5016659, baseEnd_5016659] using wordTrace_append hprefix tailTrace_5016659
  have hstable : (prefixWord ++ tailWord_5016659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016659).length < 2 ^ (prefixWord ++ tailWord_5016659).sum := by decide
  have hdescent : baseEnd_5016659 < baseStart_5016659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016670 : List Nat := [4, 4, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_5016670 : Nat := 118140960795 + 5016670 * 2 ^ 59
def prefixEnd_5016670 : Nat := 4983230072969 + 3 ^ 40 * 5016670 * 2
def baseEnd_5016670 : Nat := 858654331663664163084587

theorem tailTrace_5016670 : CollatzResearch.WordTrace tailWord_5016670 prefixEnd_5016670 858654331663664163084587 := by
  unfold tailWord_5016670
  simp only [CollatzResearch.WordTrace]
  refine ⟨22871623341933605483680933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121981991156979229246298309 22871623341933605483680933)
  ·
    refine ⟨4288429376612551028190175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22871623341933605483680933 4288429376612551028190175)
    ·
      refine ⟨6432644064918826542285263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4288429376612551028190175 6432644064918826542285263)
      ·
        refine ⟨9648966097378239813427895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6432644064918826542285263 9648966097378239813427895)
        ·
          refine ⟨14473449146067359720141843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9648966097378239813427895 14473449146067359720141843)
          ·
            refine ⟨21710173719101039580212765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14473449146067359720141843 21710173719101039580212765)
            ·
              refine ⟨8141315144662889842579787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21710173719101039580212765 8141315144662889842579787)
              ·
                refine ⟨12211972716994334763869681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8141315144662889842579787 12211972716994334763869681)
                ·
                  refine ⟨9158979537745751072902261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12211972716994334763869681 9158979537745751072902261)
                  ·
                    refine ⟨858654331663664163084587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9158979537745751072902261 858654331663664163084587)
                    ·
                      rfl

theorem cell23_5016670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_5016670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016670 prefixEnd_5016670 := by exact prefixLift 5016670
  have htrace : WordTrace (prefixWord ++ tailWord_5016670) baseStart_5016670 baseEnd_5016670 := by
    simpa [prefixWord, tailWord_5016670, baseEnd_5016670] using wordTrace_append hprefix tailTrace_5016670
  have hstable : (prefixWord ++ tailWord_5016670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016670).length < 2 ^ (prefixWord ++ tailWord_5016670).sum := by decide
  have hdescent : baseEnd_5016670 < baseStart_5016670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016733 : List Nat := [1, 4, 2, 1, 1, 2, 2, 3, 2, 3, 2]
def baseStart_5016733 : Nat := 118140960795 + 5016733 * 2 ^ 59
def prefixEnd_5016733 : Nat := 4983230072969 + 3 ^ 40 * 5016733 * 2
def baseEnd_5016733 : Nat := 2575995344272225742765971

theorem tailTrace_5016733 : CollatzResearch.WordTrace tailWord_5016733 prefixEnd_5016733 2575995344272225742765971 := by
  unfold tailWord_5016733
  simp only [CollatzResearch.WordTrace]
  refine ⟨182975284534240605628990853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121983523022827070419327235 182975284534240605628990853)
  ·
    refine ⟨34307865850170113555435785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182975284534240605628990853 34307865850170113555435785)
    ·
      refine ⟨25730899387627585166576839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34307865850170113555435785 25730899387627585166576839)
      ·
        refine ⟨38596349081441377749865259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25730899387627585166576839 38596349081441377749865259)
        ·
          refine ⟨57894523622162066624797889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38596349081441377749865259 57894523622162066624797889)
          ·
            refine ⟨43420892716621549968598417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57894523622162066624797889 43420892716621549968598417)
            ·
              refine ⟨32565669537466162476448813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43420892716621549968598417 32565669537466162476448813)
              ·
                refine ⟨12212126076549810928668305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32565669537466162476448813 12212126076549810928668305)
                ·
                  refine ⟨9159094557412358196501229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12212126076549810928668305 9159094557412358196501229)
                  ·
                    refine ⟨3434660459029634323687961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9159094557412358196501229 3434660459029634323687961)
                    ·
                      refine ⟨2575995344272225742765971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3434660459029634323687961 2575995344272225742765971)
                      ·
                        rfl

theorem cell23_5016733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_5016733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016733 prefixEnd_5016733 := by exact prefixLift 5016733
  have htrace : WordTrace (prefixWord ++ tailWord_5016733) baseStart_5016733 baseEnd_5016733 := by
    simpa [prefixWord, tailWord_5016733, baseEnd_5016733] using wordTrace_append hprefix tailTrace_5016733
  have hstable : (prefixWord ++ tailWord_5016733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016733).length < 2 ^ (prefixWord ++ tailWord_5016733).sum := by decide
  have hdescent : baseEnd_5016733 < baseStart_5016733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016739 : List Nat := [1, 1, 1, 4, 1, 1, 1, 6, 1, 6]
def baseStart_5016739 : Nat := 118140960795 + 5016739 * 2 ^ 59
def prefixEnd_5016739 : Nat := 4983230072969 + 3 ^ 40 * 5016739 * 2
def baseEnd_5016739 : Nat := 858666141718717573096981

theorem tailTrace_5016739 : CollatzResearch.WordTrace tailWord_5016739 prefixEnd_5016739 858666141718717573096981 := by
  unfold tailWord_5016739
  simp only [CollatzResearch.WordTrace]
  refine ⟨182975503372218868653709271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121983668914812579102472847 182975503372218868653709271)
  ·
    refine ⟨274463255058328302980563907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182975503372218868653709271 274463255058328302980563907)
    ·
      refine ⟨411694882587492454470845861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274463255058328302980563907 411694882587492454470845861)
      ·
        refine ⟨77192790485154835213283599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 411694882587492454470845861 77192790485154835213283599)
        ·
          refine ⟨115789185727732252819925399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77192790485154835213283599 115789185727732252819925399)
          ·
            refine ⟨173683778591598379229888099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115789185727732252819925399 173683778591598379229888099)
            ·
              refine ⟨260525667887397568844832149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173683778591598379229888099 260525667887397568844832149)
              ·
                refine ⟨12212140682221761039601507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 260525667887397568844832149 12212140682221761039601507)
                ·
                  refine ⟨18318211023332641559402261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12212140682221761039601507 18318211023332641559402261)
                  ·
                    refine ⟨858666141718717573096981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18318211023332641559402261 858666141718717573096981)
                    ·
                      rfl

theorem cell23_5016739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 6].length) (baseStart_5016739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016739 prefixEnd_5016739 := by exact prefixLift 5016739
  have htrace : WordTrace (prefixWord ++ tailWord_5016739) baseStart_5016739 baseEnd_5016739 := by
    simpa [prefixWord, tailWord_5016739, baseEnd_5016739] using wordTrace_append hprefix tailTrace_5016739
  have hstable : (prefixWord ++ tailWord_5016739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016739).length < 2 ^ (prefixWord ++ tailWord_5016739).sum := by decide
  have hdescent : baseEnd_5016739 < baseStart_5016739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016743 : List Nat := [1, 1, 6, 2, 1, 1, 2, 3, 1, 5]
def baseStart_5016743 : Nat := 118140960795 + 5016743 * 2 ^ 59
def prefixEnd_5016743 : Nat := 4983230072969 + 3 ^ 40 * 5016743 * 2
def baseEnd_5016743 : Nat := 858666826359590234546975

theorem tailTrace_5016743 : CollatzResearch.WordTrace tailWord_5016743 prefixEnd_5016743 858666826359590234546975 := by
  unfold tailWord_5016743
  simp only [CollatzResearch.WordTrace]
  refine ⟨182975649264204377336854883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121983766176136251557903255 182975649264204377336854883)
  ·
    refine ⟨274463473896306566005282325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182975649264204377336854883 274463473896306566005282325)
    ·
      refine ⟨12865475338889370281497609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 274463473896306566005282325 12865475338889370281497609)
      ·
        refine ⟨9649106504167027711123207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12865475338889370281497609 9649106504167027711123207)
        ·
          refine ⟨14473659756250541566684811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9649106504167027711123207 14473659756250541566684811)
          ·
            refine ⟨21710489634375812350027217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14473659756250541566684811 21710489634375812350027217)
            ·
              refine ⟨16282867225781859262520413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21710489634375812350027217 16282867225781859262520413)
              ·
                refine ⟨6106075209668197223445155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16282867225781859262520413 6106075209668197223445155)
                ·
                  refine ⟨9159112814502295835167733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6106075209668197223445155 9159112814502295835167733)
                  ·
                    refine ⟨858666826359590234546975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9159112814502295835167733 858666826359590234546975)
                    ·
                      rfl

theorem cell23_5016743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_5016743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016743 prefixEnd_5016743 := by exact prefixLift 5016743
  have htrace : WordTrace (prefixWord ++ tailWord_5016743) baseStart_5016743 baseEnd_5016743 := by
    simpa [prefixWord, tailWord_5016743, baseEnd_5016743] using wordTrace_append hprefix tailTrace_5016743
  have hstable : (prefixWord ++ tailWord_5016743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016743).length < 2 ^ (prefixWord ++ tailWord_5016743).sum := by decide
  have hdescent : baseEnd_5016743 < baseStart_5016743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016759 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 6]
def baseStart_5016759 : Nat := 118140960795 + 5016759 * 2 ^ 59
def prefixEnd_5016759 : Nat := 4983230072969 + 3 ^ 40 * 5016759 * 2
def baseEnd_5016759 : Nat := 2576008694769242641040851

theorem tailTrace_5016759 : CollatzResearch.WordTrace tailWord_5016759 prefixEnd_5016759 2576008694769242641040851 := by
  unfold tailWord_5016759
  simp only [CollatzResearch.WordTrace]
  refine ⟨182976232832146412069437331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121984155221430941379624887 182976232832146412069437331)
  ·
    refine ⟨274464349248219618104155997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182976232832146412069437331 274464349248219618104155997)
    ·
      refine ⟨102924130968082356789058499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274464349248219618104155997 102924130968082356789058499)
      ·
        refine ⟨154386196452123535183587749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102924130968082356789058499 154386196452123535183587749)
        ·
          refine ⟨28947411834773162846922703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154386196452123535183587749 28947411834773162846922703)
          ·
            refine ⟨43421117752159744270384055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28947411834773162846922703 43421117752159744270384055)
            ·
              refine ⟨65131676628239616405576083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43421117752159744270384055 65131676628239616405576083)
              ·
                refine ⟨97697514942359424608364125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65131676628239616405576083 97697514942359424608364125)
                ·
                  refine ⟨36636568103384784228136547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97697514942359424608364125 36636568103384784228136547)
                  ·
                    refine ⟨54954852155077176342204821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36636568103384784228136547 54954852155077176342204821)
                    ·
                      refine ⟨2576008694769242641040851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54954852155077176342204821 2576008694769242641040851)
                      ·
                        rfl

theorem cell23_5016759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_5016759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016759 prefixEnd_5016759 := by exact prefixLift 5016759
  have htrace : WordTrace (prefixWord ++ tailWord_5016759) baseStart_5016759 baseEnd_5016759 := by
    simpa [prefixWord, tailWord_5016759, baseEnd_5016759] using wordTrace_append hprefix tailTrace_5016759
  have hstable : (prefixWord ++ tailWord_5016759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016759).length < 2 ^ (prefixWord ++ tailWord_5016759).sum := by decide
  have hdescent : baseEnd_5016759 < baseStart_5016759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016763 : List Nat := [1, 1, 1, 1, 1, 2, 4, 5, 3, 2, 2]
def baseStart_5016763 : Nat := 118140960795 + 5016763 * 2 ^ 59
def prefixEnd_5016763 : Nat := 4983230072969 + 3 ^ 40 * 5016763 * 2
def baseEnd_5016763 : Nat := 2576010748691860625390833

theorem tailTrace_5016763 : CollatzResearch.WordTrace tailWord_5016763 prefixEnd_5016763 2576010748691860625390833 := by
  unfold tailWord_5016763
  simp only [CollatzResearch.WordTrace]
  refine ⟨182976378724131920752582943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121984252482754613835055295 182976378724131920752582943)
  ·
    refine ⟨274464568086197881128874415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182976378724131920752582943 274464568086197881128874415)
    ·
      refine ⟨411696852129296821693311623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274464568086197881128874415 411696852129296821693311623)
      ·
        refine ⟨617545278193945232539967435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411696852129296821693311623 617545278193945232539967435)
        ·
          refine ⟨926317917290917848809951153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617545278193945232539967435 926317917290917848809951153)
          ·
            refine ⟨694738437968188386607463365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 926317917290917848809951153 694738437968188386607463365)
            ·
              refine ⟨130263457119035322488899381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 694738437968188386607463365 130263457119035322488899381)
              ·
                refine ⟨12212199104909561483334317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 130263457119035322488899381 12212199104909561483334317)
                ·
                  refine ⟨4579574664341085556250369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12212199104909561483334317 4579574664341085556250369)
                  ·
                    refine ⟨3434680998255814167187777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4579574664341085556250369 3434680998255814167187777)
                    ·
                      refine ⟨2576010748691860625390833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3434680998255814167187777 2576010748691860625390833)
                      ·
                        rfl

theorem cell23_5016763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 2, 2].length) (baseStart_5016763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016763 prefixEnd_5016763 := by exact prefixLift 5016763
  have htrace : WordTrace (prefixWord ++ tailWord_5016763) baseStart_5016763 baseEnd_5016763 := by
    simpa [prefixWord, tailWord_5016763, baseEnd_5016763] using wordTrace_append hprefix tailTrace_5016763
  have hstable : (prefixWord ++ tailWord_5016763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016763).length < 2 ^ (prefixWord ++ tailWord_5016763).sum := by decide
  have hdescent : baseEnd_5016763 < baseStart_5016763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016790 : List Nat := [5, 2, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_5016790 : Nat := 118140960795 + 5016790 * 2 ^ 59
def prefixEnd_5016790 : Nat := 4983230072969 + 3 ^ 40 * 5016790 * 2
def baseEnd_5016790 : Nat := 858674870889844006584403

theorem tailTrace_5016790 : CollatzResearch.WordTrace tailWord_5016790 prefixEnd_5016790 858674870889844006584403 := by
  unfold tailWord_5016790
  simp only [CollatzResearch.WordTrace]
  refine ⟨11436085218439631522738489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121984908996689402909210549 11436085218439631522738489)
  ·
    refine ⟨8577063913829723642053867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11436085218439631522738489 8577063913829723642053867)
    ·
      refine ⟨12865595870744585463080801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8577063913829723642053867 12865595870744585463080801)
      ·
        refine ⟨9649196903058439097310601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12865595870744585463080801 9649196903058439097310601)
        ·
          refine ⟨7236897677293829322982951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9649196903058439097310601 7236897677293829322982951)
          ·
            refine ⟨10855346515940743984474427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7236897677293829322982951 10855346515940743984474427)
            ·
              refine ⟨16283019773911115976711641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10855346515940743984474427 16283019773911115976711641)
              ·
                refine ⟨12212264830433336982533731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16283019773911115976711641 12212264830433336982533731)
                ·
                  refine ⟨18318397245650005473800597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12212264830433336982533731 18318397245650005473800597)
                  ·
                    refine ⟨858674870889844006584403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18318397245650005473800597 858674870889844006584403)
                    ·
                      rfl

theorem cell23_5016790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_5016790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016790 prefixEnd_5016790 := by exact prefixLift 5016790
  have htrace : WordTrace (prefixWord ++ tailWord_5016790) baseStart_5016790 baseEnd_5016790 := by
    simpa [prefixWord, tailWord_5016790, baseEnd_5016790] using wordTrace_append hprefix tailTrace_5016790
  have hstable : (prefixWord ++ tailWord_5016790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016790).length < 2 ^ (prefixWord ++ tailWord_5016790).sum := by decide
  have hdescent : baseEnd_5016790 < baseStart_5016790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016797 : List Nat := [1, 4, 3, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_5016797 : Nat := 118140960795 + 5016797 * 2 ^ 59
def prefixEnd_5016797 : Nat := 4983230072969 + 3 ^ 40 * 5016797 * 2
def baseEnd_5016797 : Nat := 2576028207034113492365677

theorem tailTrace_5016797 : CollatzResearch.WordTrace tailWord_5016797 prefixEnd_5016797 2576028207034113492365677 := by
  unfold tailWord_5016797
  simp only [CollatzResearch.WordTrace]
  refine ⟨182977618806008744559320645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121985079204005829706213763 182977618806008744559320645)
  ·
    refine ⟨34308303526126639604872621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182977618806008744559320645 34308303526126639604872621)
    ·
      refine ⟨12865613822297489851827233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34308303526126639604872621 12865613822297489851827233)
      ·
        refine ⟨9649210366723117388870425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12865613822297489851827233 9649210366723117388870425)
        ·
          refine ⟨7236907775042338041652819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9649210366723117388870425 7236907775042338041652819)
          ·
            refine ⟨10855361662563507062479229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7236907775042338041652819 10855361662563507062479229)
            ·
              refine ⟨4070760623461315148429711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10855361662563507062479229 4070760623461315148429711)
              ·
                refine ⟨6106140935191972722644567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4070760623461315148429711 6106140935191972722644567)
                ·
                  refine ⟨9159211402787959083966851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6106140935191972722644567 9159211402787959083966851)
                  ·
                    refine ⟨13738817104181938625950277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9159211402787959083966851 13738817104181938625950277)
                    ·
                      refine ⟨2576028207034113492365677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13738817104181938625950277 2576028207034113492365677)
                      ·
                        rfl

theorem cell23_5016797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_5016797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016797 prefixEnd_5016797 := by exact prefixLift 5016797
  have htrace : WordTrace (prefixWord ++ tailWord_5016797) baseStart_5016797 baseEnd_5016797 := by
    simpa [prefixWord, tailWord_5016797, baseEnd_5016797] using wordTrace_append hprefix tailTrace_5016797
  have hstable : (prefixWord ++ tailWord_5016797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016797).length < 2 ^ (prefixWord ++ tailWord_5016797).sum := by decide
  have hdescent : baseEnd_5016797 < baseStart_5016797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016800 : List Nat := [2, 1, 1, 3, 1, 5, 3, 1, 1, 2, 3]
def baseStart_5016800 : Nat := 118140960795 + 5016800 * 2 ^ 59
def prefixEnd_5016800 : Nat := 4983230072969 + 3 ^ 40 * 5016800 * 2
def baseEnd_5016800 : Nat := 2576029747476076980628163

theorem tailTrace_5016800 : CollatzResearch.WordTrace tailWord_5016800 prefixEnd_5016800 2576029747476076980628163 := by
  unfold tailWord_5016800
  simp only [CollatzResearch.WordTrace]
  refine ⟨91488864112498938035839927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121985152149998584047786569 91488864112498938035839927)
  ·
    refine ⟨137233296168748407053759891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91488864112498938035839927 137233296168748407053759891)
    ·
      refine ⟨205849944253122610580639837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137233296168748407053759891 205849944253122610580639837)
      ·
        refine ⟨77193729094920978967739939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205849944253122610580639837 77193729094920978967739939)
        ·
          refine ⟨115790593642381468451609909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77193729094920978967739939 115790593642381468451609909)
          ·
            refine ⟨10855368153973262667338429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115790593642381468451609909 10855368153973262667338429)
            ·
              refine ⟨4070763057739973500251911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10855368153973262667338429 4070763057739973500251911)
              ·
                refine ⟨6106144586609960250377867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4070763057739973500251911 6106144586609960250377867)
                ·
                  refine ⟨9159216879914940375566801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6106144586609960250377867 9159216879914940375566801)
                  ·
                    refine ⟨6869412659936205281675101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9159216879914940375566801 6869412659936205281675101)
                    ·
                      refine ⟨2576029747476076980628163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6869412659936205281675101 2576029747476076980628163)
                      ·
                        rfl

theorem cell23_5016800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_5016800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016800 prefixEnd_5016800 := by exact prefixLift 5016800
  have htrace : WordTrace (prefixWord ++ tailWord_5016800) baseStart_5016800 baseEnd_5016800 := by
    simpa [prefixWord, tailWord_5016800, baseEnd_5016800] using wordTrace_append hprefix tailTrace_5016800
  have hstable : (prefixWord ++ tailWord_5016800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016800).length < 2 ^ (prefixWord ++ tailWord_5016800).sum := by decide
  have hdescent : baseEnd_5016800 < baseStart_5016800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016814 : List Nat := [4, 1, 2, 1, 1, 1, 6, 2, 1, 2, 2]
def baseStart_5016814 : Nat := 118140960795 + 5016814 * 2 ^ 59
def prefixEnd_5016814 : Nat := 4983230072969 + 3 ^ 40 * 5016814 * 2
def baseEnd_5016814 : Nat := 2576036936205239925853099

theorem tailTrace_5016814 : CollatzResearch.WordTrace tailWord_5016814 prefixEnd_5016814 2576036936205239925853099 := by
  unfold tailWord_5016814
  simp only [CollatzResearch.WordTrace]
  refine ⟨22872279855868394557836187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121985492564631437641792997 22872279855868394557836187)
  ·
    refine ⟨34308419783802591836754281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22872279855868394557836187 34308419783802591836754281)
    ·
      refine ⟨25731314837851943877565711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34308419783802591836754281 25731314837851943877565711)
      ·
        refine ⟨38596972256777915816348567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25731314837851943877565711 38596972256777915816348567)
        ·
          refine ⟨57895458385166873724522851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38596972256777915816348567 57895458385166873724522851)
          ·
            refine ⟨86843187577750310586784277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57895458385166873724522851 86843187577750310586784277)
            ·
              refine ⟨4070774417707045808755513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86843187577750310586784277 4070774417707045808755513)
              ·
                refine ⟨3053080813280284356566635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4070774417707045808755513 3053080813280284356566635)
                ·
                  refine ⟨4579621219920426534849953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3053080813280284356566635 4579621219920426534849953)
                  ·
                    refine ⟨3434715914940319901137465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4579621219920426534849953 3434715914940319901137465)
                    ·
                      refine ⟨2576036936205239925853099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3434715914940319901137465 2576036936205239925853099)
                      ·
                        rfl

theorem cell23_5016814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_5016814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016814 prefixEnd_5016814 := by exact prefixLift 5016814
  have htrace : WordTrace (prefixWord ++ tailWord_5016814) baseStart_5016814 baseEnd_5016814 := by
    simpa [prefixWord, tailWord_5016814, baseEnd_5016814] using wordTrace_append hprefix tailTrace_5016814
  have hstable : (prefixWord ++ tailWord_5016814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016814).length < 2 ^ (prefixWord ++ tailWord_5016814).sum := by decide
  have hdescent : baseEnd_5016814 < baseStart_5016814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016830 : List Nat := [4, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_5016830 : Nat := 118140960795 + 5016830 * 2 ^ 59
def prefixEnd_5016830 : Nat := 4983230072969 + 3 ^ 40 * 5016830 * 2
def baseEnd_5016830 : Nat := 2576045151895711863253025

theorem tailTrace_5016830 : CollatzResearch.WordTrace tailWord_5016830 prefixEnd_5016830 2576045151895711863253025 := by
  unfold tailWord_5016830
  simp only [CollatzResearch.WordTrace]
  refine ⟨22872352801861148899408993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121985881609926127463514629 22872352801861148899408993)
  ·
    refine ⟨17154264601395861674556745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22872352801861148899408993 17154264601395861674556745)
    ·
      refine ⟨12865698451046896255917559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17154264601395861674556745 12865698451046896255917559)
      ·
        refine ⟨19298547676570344383876339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12865698451046896255917559 19298547676570344383876339)
        ·
          refine ⟨28947821514855516575814509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19298547676570344383876339 28947821514855516575814509)
          ·
            refine ⟨10855433068070818715930441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28947821514855516575814509 10855433068070818715930441)
            ·
              refine ⟨8141574801053114036947831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10855433068070818715930441 8141574801053114036947831)
              ·
                refine ⟨12212362201579671055421747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8141574801053114036947831 12212362201579671055421747)
                ·
                  refine ⟨18318543302369506583132621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12212362201579671055421747 18318543302369506583132621)
                  ·
                    refine ⟨6869453738388564968674733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18318543302369506583132621 6869453738388564968674733)
                    ·
                      refine ⟨2576045151895711863253025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6869453738388564968674733 2576045151895711863253025)
                      ·
                        rfl

theorem cell23_5016830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_5016830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016830 prefixEnd_5016830 := by exact prefixLift 5016830
  have htrace : WordTrace (prefixWord ++ tailWord_5016830) baseStart_5016830 baseEnd_5016830 := by
    simpa [prefixWord, tailWord_5016830, baseEnd_5016830] using wordTrace_append hprefix tailTrace_5016830
  have hstable : (prefixWord ++ tailWord_5016830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016830).length < 2 ^ (prefixWord ++ tailWord_5016830).sum := by decide
  have hdescent : baseEnd_5016830 < baseStart_5016830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016859 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 11]
def baseStart_5016859 : Nat := 118140960795 + 5016859 * 2 ^ 59
def prefixEnd_5016859 : Nat := 4983230072969 + 3 ^ 40 * 5016859 * 2
def baseEnd_5016859 : Nat := 286228893648299138865599

theorem tailTrace_5016859 : CollatzResearch.WordTrace tailWord_5016859 prefixEnd_5016859 286228893648299138865599 := by
  unfold tailWord_5016859
  simp only [CollatzResearch.WordTrace]
  refine ⟨182979880131784129148077631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121986586754522752765385087 182979880131784129148077631)
  ·
    refine ⟨274469820197676193722116447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182979880131784129148077631 274469820197676193722116447)
    ·
      refine ⟨411704730296514290583174671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274469820197676193722116447 411704730296514290583174671)
      ·
        refine ⟨617557095444771435874762007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411704730296514290583174671 617557095444771435874762007)
        ·
          refine ⟨926335643167157153812143011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617557095444771435874762007 926335643167157153812143011)
          ·
            refine ⟨1389503464750735730718214517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926335643167157153812143011 1389503464750735730718214517)
            ·
              refine ⟨130265949820381474754832611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1389503464750735730718214517 130265949820381474754832611)
              ·
                refine ⟨195398924730572212132248917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130265949820381474754832611 195398924730572212132248917)
                ·
                  refine ⟨286228893648299138865599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 195398924730572212132248917 286228893648299138865599)
                  ·
                    rfl

theorem cell23_5016859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 11].length) (baseStart_5016859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016859 prefixEnd_5016859 := by exact prefixLift 5016859
  have htrace : WordTrace (prefixWord ++ tailWord_5016859) baseStart_5016859 baseEnd_5016859 := by
    simpa [prefixWord, tailWord_5016859, baseEnd_5016859] using wordTrace_append hprefix tailTrace_5016859
  have hstable : (prefixWord ++ tailWord_5016859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016859).length < 2 ^ (prefixWord ++ tailWord_5016859).sum := by decide
  have hdescent : baseEnd_5016859 < baseStart_5016859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016864 : List Nat := [2, 1, 1, 5, 4, 1, 1, 2, 2, 1, 3]
def baseStart_5016864 : Nat := 118140960795 + 5016864 * 2 ^ 59
def prefixEnd_5016864 : Nat := 4983230072969 + 3 ^ 40 * 5016864 * 2
def baseEnd_5016864 : Nat := 2576062610237964730227869

theorem tailTrace_5016864 : CollatzResearch.WordTrace tailWord_5016864 prefixEnd_5016864 2576062610237964730227869 := by
  unfold tailWord_5016864
  simp only [CollatzResearch.WordTrace]
  refine ⟨91490031248383007501004823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121986708331177343334673097 91490031248383007501004823)
  ·
    refine ⟨137235046872574511251507235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91490031248383007501004823 137235046872574511251507235)
    ·
      refine ⟨205852570308861766877260853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137235046872574511251507235 205852570308861766877260853)
      ·
        refine ⟨19298678466455790644743205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 205852570308861766877260853 19298678466455790644743205)
        ·
          refine ⟨3618502212460460745889351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19298678466455790644743205 3618502212460460745889351)
          ·
            refine ⟨5427753318690691118834027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3618502212460460745889351 5427753318690691118834027)
            ·
              refine ⟨8141629978036036678251041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5427753318690691118834027 8141629978036036678251041)
              ·
                refine ⟨6106222483527027508688281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8141629978036036678251041 6106222483527027508688281)
                ·
                  refine ⟨4579666862645270631516211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6106222483527027508688281 4579666862645270631516211)
                  ·
                    refine ⟨6869500293967905947274317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4579666862645270631516211 6869500293967905947274317)
                    ·
                      refine ⟨2576062610237964730227869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6869500293967905947274317 2576062610237964730227869)
                      ·
                        rfl

theorem cell23_5016864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_5016864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016864 prefixEnd_5016864 := by exact prefixLift 5016864
  have htrace : WordTrace (prefixWord ++ tailWord_5016864) baseStart_5016864 baseEnd_5016864 := by
    simpa [prefixWord, tailWord_5016864, baseEnd_5016864] using wordTrace_append hprefix tailTrace_5016864
  have hstable : (prefixWord ++ tailWord_5016864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016864).length < 2 ^ (prefixWord ++ tailWord_5016864).sum := by decide
  have hdescent : baseEnd_5016864 < baseStart_5016864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016906 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 6, 5]
def baseStart_5016906 : Nat := 118140960795 + 5016906 * 2 ^ 59
def prefixEnd_5016906 : Nat := 4983230072969 + 3 ^ 40 * 5016906 * 2
def baseEnd_5016906 : Nat := 858694725475151188634225

theorem tailTrace_5016906 : CollatzResearch.WordTrace tailWord_5016906 prefixEnd_5016906 858694725475151188634225 := by
  unfold tailWord_5016906
  simp only [CollatzResearch.WordTrace]
  refine ⟨45745398590653464043759643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121987729575075904116692381 45745398590653464043759643)
  ·
    refine ⟨68618097885980196065639465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45745398590653464043759643 68618097885980196065639465)
    ·
      refine ⟨51463573414485147049229599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68618097885980196065639465 51463573414485147049229599)
      ·
        refine ⟨77195360121727720573844399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51463573414485147049229599 77195360121727720573844399)
        ·
          refine ⟨115793040182591580860766599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77195360121727720573844399 115793040182591580860766599)
          ·
            refine ⟨173689560273887371291149899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115793040182591580860766599 173689560273887371291149899)
            ·
              refine ⟨260534340410831056936724849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173689560273887371291149899 260534340410831056936724849)
              ·
                refine ⟨195400755308123292702543637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260534340410831056936724849 195400755308123292702543637)
                ·
                  refine ⟨9159410405068279345431733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 195400755308123292702543637 9159410405068279345431733)
                  ·
                    refine ⟨858694725475151188634225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9159410405068279345431733 858694725475151188634225)
                    ·
                      rfl

theorem cell23_5016906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_5016906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016906 prefixEnd_5016906 := by exact prefixLift 5016906
  have htrace : WordTrace (prefixWord ++ tailWord_5016906) baseStart_5016906 baseEnd_5016906 := by
    simpa [prefixWord, tailWord_5016906, baseEnd_5016906] using wordTrace_append hprefix tailTrace_5016906
  have hstable : (prefixWord ++ tailWord_5016906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016906).length < 2 ^ (prefixWord ++ tailWord_5016906).sum := by decide
  have hdescent : baseEnd_5016906 < baseStart_5016906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016930 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_5016930 : Nat := 118140960795 + 5016930 * 2 ^ 59
def prefixEnd_5016930 : Nat := 4983230072969 + 3 ^ 40 * 5016930 * 2
def baseEnd_5016930 : Nat := 2576096499961161472002565

theorem tailTrace_5016930 : CollatzResearch.WordTrace tailWord_5016930 prefixEnd_5016930 2576096499961161472002565 := by
  unfold tailWord_5016930
  simp only [CollatzResearch.WordTrace]
  refine ⟨45745617428631727068478061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121988313143017938849274829 45745617428631727068478061)
  ·
    refine ⟨17154606535736897650679273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45745617428631727068478061 17154606535736897650679273)
    ·
      refine ⟨12865954901802673238009455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17154606535736897650679273 12865954901802673238009455)
      ·
        refine ⟨19298932352704009857014183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12865954901802673238009455 19298932352704009857014183)
        ·
          refine ⟨28948398529056014785521275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19298932352704009857014183 28948398529056014785521275)
          ·
            refine ⟨43422597793584022178281913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28948398529056014785521275 43422597793584022178281913)
            ·
              refine ⟨32566948345188016633711435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43422597793584022178281913 32566948345188016633711435)
              ·
                refine ⟨48850422517782024950567153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32566948345188016633711435 48850422517782024950567153)
                ·
                  refine ⟨36637816888336518712925365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48850422517782024950567153 36637816888336518712925365)
                  ·
                    refine ⟨3434795333281548629336753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36637816888336518712925365 3434795333281548629336753)
                    ·
                      refine ⟨2576096499961161472002565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3434795333281548629336753 2576096499961161472002565)
                      ·
                        rfl

theorem cell23_5016930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_5016930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016930 prefixEnd_5016930 := by exact prefixLift 5016930
  have htrace : WordTrace (prefixWord ++ tailWord_5016930) baseStart_5016930 baseEnd_5016930 := by
    simpa [prefixWord, tailWord_5016930, baseEnd_5016930] using wordTrace_append hprefix tailTrace_5016930
  have hstable : (prefixWord ++ tailWord_5016930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016930).length < 2 ^ (prefixWord ++ tailWord_5016930).sum := by decide
  have hdescent : baseEnd_5016930 < baseStart_5016930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016938 : List Nat := [3, 1, 3, 3, 3, 1, 2, 1, 2, 2, 2]
def baseStart_5016938 : Nat := 118140960795 + 5016938 * 2 ^ 59
def prefixEnd_5016938 : Nat := 4983230072969 + 3 ^ 40 * 5016938 * 2
def baseEnd_5016938 : Nat := 2576100607806397440702529

theorem tailTrace_5016938 : CollatzResearch.WordTrace tailWord_5016938 prefixEnd_5016938 2576100607806397440702529 := by
  unfold tailWord_5016938
  simp only [CollatzResearch.WordTrace]
  refine ⟨45745690374624481410050867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121988507665665283760135645 45745690374624481410050867)
  ·
    refine ⟨68618535561936722115076301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45745690374624481410050867 68618535561936722115076301)
    ·
      refine ⟨25731950835726270793153613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68618535561936722115076301 25731950835726270793153613)
      ·
        refine ⟨9649481563397351547432605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25731950835726270793153613 9649481563397351547432605)
        ·
          refine ⟨3618555586274006830287227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9649481563397351547432605 3618555586274006830287227)
          ·
            refine ⟨5427833379411010245430841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3618555586274006830287227 5427833379411010245430841)
            ·
              refine ⟨4070875034558257684073131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5427833379411010245430841 4070875034558257684073131)
              ·
                refine ⟨6106312551837386526109697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4070875034558257684073131 6106312551837386526109697)
                ·
                  refine ⟨4579734413878039894582273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6106312551837386526109697 4579734413878039894582273)
                  ·
                    refine ⟨3434800810408529920936705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4579734413878039894582273 3434800810408529920936705)
                    ·
                      refine ⟨2576100607806397440702529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3434800810408529920936705 2576100607806397440702529)
                      ·
                        rfl

theorem cell23_5016938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_5016938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016938 prefixEnd_5016938 := by exact prefixLift 5016938
  have htrace : WordTrace (prefixWord ++ tailWord_5016938) baseStart_5016938 baseEnd_5016938 := by
    simpa [prefixWord, tailWord_5016938, baseEnd_5016938] using wordTrace_append hprefix tailTrace_5016938
  have hstable : (prefixWord ++ tailWord_5016938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016938).length < 2 ^ (prefixWord ++ tailWord_5016938).sum := by decide
  have hdescent : baseEnd_5016938 < baseStart_5016938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016943 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 1, 6, 2]
def baseStart_5016943 : Nat := 118140960795 + 5016943 * 2 ^ 59
def prefixEnd_5016943 : Nat := 4983230072969 + 3 ^ 40 * 5016943 * 2
def baseEnd_5016943 : Nat := 2576103175209669921140005

theorem tailTrace_5016943 : CollatzResearch.WordTrace tailWord_5016943 prefixEnd_5016943 2576103175209669921140005 := by
  unfold tailWord_5016943
  simp only [CollatzResearch.WordTrace]
  refine ⟨182982943863479811494135483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121988629242319874329423655 182982943863479811494135483)
  ·
    refine ⟨274474415795219717241203225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182982943863479811494135483 274474415795219717241203225)
    ·
      refine ⟨205855811846414787930902419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274474415795219717241203225 205855811846414787930902419)
      ·
        refine ⟨308783717769622181896353629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205855811846414787930902419 308783717769622181896353629)
        ·
          refine ⟨115793894163608318211132611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308783717769622181896353629 115793894163608318211132611)
          ·
            refine ⟨173690841245412477316698917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115793894163608318211132611 173690841245412477316698917)
            ·
              refine ⟨32567032733514839496881047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173690841245412477316698917 32567032733514839496881047)
              ·
                refine ⟨48850549100272259245321571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32567032733514839496881047 48850549100272259245321571)
                ·
                  refine ⟨73275823650408388867982357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48850549100272259245321571 73275823650408388867982357)
                  ·
                    refine ⟨3434804233612893228186673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73275823650408388867982357 3434804233612893228186673)
                    ·
                      refine ⟨2576103175209669921140005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3434804233612893228186673 2576103175209669921140005)
                      ·
                        rfl

theorem cell23_5016943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 6, 2].length) (baseStart_5016943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016943 prefixEnd_5016943 := by exact prefixLift 5016943
  have htrace : WordTrace (prefixWord ++ tailWord_5016943) baseStart_5016943 baseEnd_5016943 := by
    simpa [prefixWord, tailWord_5016943, baseEnd_5016943] using wordTrace_append hprefix tailTrace_5016943
  have hstable : (prefixWord ++ tailWord_5016943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016943).length < 2 ^ (prefixWord ++ tailWord_5016943).sum := by decide
  have hdescent : baseEnd_5016943 < baseStart_5016943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5016953 : List Nat := [1, 2, 1, 3, 2, 1, 2, 4, 3, 4]
def baseStart_5016953 : Nat := 118140960795 + 5016953 * 2 ^ 59
def prefixEnd_5016953 : Nat := 4983230072969 + 3 ^ 40 * 5016953 * 2
def baseEnd_5016953 : Nat := 858702770005404960671653

theorem tailTrace_5016953 : CollatzResearch.WordTrace tailWord_5016953 prefixEnd_5016953 858702770005404960671653 := by
  unfold tailWord_5016953
  simp only [CollatzResearch.WordTrace]
  refine ⟨182983308593443583201999513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121988872395629055467999675 182983308593443583201999513)
  ·
    refine ⟨137237481445082687401499635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182983308593443583201999513 137237481445082687401499635)
    ·
      refine ⟨205856222167624031102249453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137237481445082687401499635 205856222167624031102249453)
      ·
        refine ⟨77196083312859011663343545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205856222167624031102249453 77196083312859011663343545)
        ·
          refine ⟨57897062484644258747507659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77196083312859011663343545 57897062484644258747507659)
          ·
            refine ⟨86845593726966388121261489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57897062484644258747507659 86845593726966388121261489)
            ·
              refine ⟨65134195295224791090946117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86845593726966388121261489 65134195295224791090946117)
              ·
                refine ⟨12212661617854648329552397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65134195295224791090946117 12212661617854648329552397)
                ·
                  refine ⟨4579748106695493123582149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12212661617854648329552397 4579748106695493123582149)
                  ·
                    refine ⟨858702770005404960671653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4579748106695493123582149 858702770005404960671653)
                    ·
                      rfl

theorem cell23_5016953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 4].length) (baseStart_5016953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5016953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5016953 prefixEnd_5016953 := by exact prefixLift 5016953
  have htrace : WordTrace (prefixWord ++ tailWord_5016953) baseStart_5016953 baseEnd_5016953 := by
    simpa [prefixWord, tailWord_5016953, baseEnd_5016953] using wordTrace_append hprefix tailTrace_5016953
  have hstable : (prefixWord ++ tailWord_5016953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5016953).length < 2 ^ (prefixWord ++ tailWord_5016953).sum := by decide
  have hdescent : baseEnd_5016953 < baseStart_5016953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5016953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017003 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 2, 9, 2]
def baseStart_5017003 : Nat := 118140960795 + 5017003 * 2 ^ 59
def prefixEnd_5017003 : Nat := 4983230072969 + 3 ^ 40 * 5017003 * 2
def baseEnd_5017003 : Nat := 2576133984048939686389729

theorem tailTrace_5017003 : CollatzResearch.WordTrace tailWord_5017003 prefixEnd_5017003 2576133984048939686389729 := by
  unfold tailWord_5017003
  simp only [CollatzResearch.WordTrace]
  refine ⟨182985132243262441741319663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121990088162174961160879775 182985132243262441741319663)
  ·
    refine ⟨274477698364893662611979495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182985132243262441741319663 274477698364893662611979495)
    ·
      refine ⟨411716547547340493917969243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274477698364893662611979495 411716547547340493917969243)
      ·
        refine ⟨617574821321010740876953865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411716547547340493917969243 617574821321010740876953865)
        ·
          refine ⟨463181115990758055657715399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 617574821321010740876953865 463181115990758055657715399)
          ·
            refine ⟨694771673986137083486573099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463181115990758055657715399 694771673986137083486573099)
            ·
              refine ⟨1042157510979205625229859649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694771673986137083486573099 1042157510979205625229859649)
              ·
                refine ⟨781618133234404218922394737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1042157510979205625229859649 781618133234404218922394737)
                ·
                  refine ⟨586213599925803164191796053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 781618133234404218922394737 586213599925803164191796053)
                  ·
                    refine ⟨3434845312065252915186305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 586213599925803164191796053 3434845312065252915186305)
                    ·
                      refine ⟨2576133984048939686389729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3434845312065252915186305 2576133984048939686389729)
                      ·
                        rfl

theorem cell23_5017003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 9, 2].length) (baseStart_5017003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017003 prefixEnd_5017003 := by exact prefixLift 5017003
  have htrace : WordTrace (prefixWord ++ tailWord_5017003) baseStart_5017003 baseEnd_5017003 := by
    simpa [prefixWord, tailWord_5017003, baseEnd_5017003] using wordTrace_append hprefix tailTrace_5017003
  have hstable : (prefixWord ++ tailWord_5017003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017003).length < 2 ^ (prefixWord ++ tailWord_5017003).sum := by decide
  have hdescent : baseEnd_5017003 < baseStart_5017003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017027 : List Nat := [1, 1, 1, 3, 1, 1, 5, 5, 1, 1, 3]
def baseStart_5017027 : Nat := 118140960795 + 5017027 * 2 ^ 59
def prefixEnd_5017027 : Nat := 4983230072969 + 3 ^ 40 * 5017027 * 2
def baseEnd_5017027 : Nat := 2576146307584647592489619

theorem tailTrace_5017027 : CollatzResearch.WordTrace tailWord_5017027 prefixEnd_5017027 2576146307584647592489619 := by
  unfold tailWord_5017027
  simp only [CollatzResearch.WordTrace]
  refine ⟨182986007595175493840193335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121990671730116995893462223 182986007595175493840193335)
  ·
    refine ⟨274479011392763240760290003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182986007595175493840193335 274479011392763240760290003)
    ·
      refine ⟨411718517089144861140435005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274479011392763240760290003 411718517089144861140435005)
      ·
        refine ⟨154394443908429322927663127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 411718517089144861140435005 154394443908429322927663127)
        ·
          refine ⟨231591665862643984391494691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154394443908429322927663127 231591665862643984391494691)
          ·
            refine ⟨347387498793965976587242037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231591665862643984391494691 347387498793965976587242037)
            ·
              refine ⟨32567578011934310305053941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 347387498793965976587242037 32567578011934310305053941)
              ·
                refine ⟨3053210438618841591098807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32567578011934310305053941 3053210438618841591098807)
                ·
                  refine ⟨4579815657928262386648211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3053210438618841591098807 4579815657928262386648211)
                  ·
                    refine ⟨6869723486892393579972317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4579815657928262386648211 6869723486892393579972317)
                    ·
                      refine ⟨2576146307584647592489619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6869723486892393579972317 2576146307584647592489619)
                      ·
                        rfl

theorem cell23_5017027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 1, 1, 3].length) (baseStart_5017027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017027 prefixEnd_5017027 := by exact prefixLift 5017027
  have htrace : WordTrace (prefixWord ++ tailWord_5017027) baseStart_5017027 baseEnd_5017027 := by
    simpa [prefixWord, tailWord_5017027, baseEnd_5017027] using wordTrace_append hprefix tailTrace_5017027
  have hstable : (prefixWord ++ tailWord_5017027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017027).length < 2 ^ (prefixWord ++ tailWord_5017027).sum := by decide
  have hdescent : baseEnd_5017027 < baseStart_5017027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017044 : List Nat := [2, 4, 1, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_5017044 : Nat := 118140960795 + 5017044 * 2 ^ 59
def prefixEnd_5017044 : Nat := 4983230072969 + 3 ^ 40 * 5017044 * 2
def baseEnd_5017044 : Nat := 2576155036755774025977041

theorem tailTrace_5017044 : CollatzResearch.WordTrace tailWord_5017044 prefixEnd_5017044 2576155036755774025977041 := by
  unfold tailWord_5017044
  simp only [CollatzResearch.WordTrace]
  refine ⟨91493313818056952871781093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121991085090742603829041457 91493313818056952871781093)
  ·
    refine ⟨17154996340885678663458955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91493313818056952871781093 17154996340885678663458955)
    ·
      refine ⟨25732494511328517995188433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17154996340885678663458955 25732494511328517995188433)
      ·
        refine ⟨19299370883496388496391325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25732494511328517995188433 19299370883496388496391325)
        ·
          refine ⟨7237264081311145686146747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19299370883496388496391325 7237264081311145686146747)
          ·
            refine ⟨10855896121966718529220121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7237264081311145686146747 10855896121966718529220121)
            ·
              refine ⟨8141922091475038896915091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10855896121966718529220121 8141922091475038896915091)
              ·
                refine ⟨12212883137212558345372637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8141922091475038896915091 12212883137212558345372637)
                ·
                  refine ⟨4579831176454709379514739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12212883137212558345372637 4579831176454709379514739)
                  ·
                    refine ⟨6869746764682064069272109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4579831176454709379514739 6869746764682064069272109)
                    ·
                      refine ⟨2576155036755774025977041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6869746764682064069272109 2576155036755774025977041)
                      ·
                        rfl

theorem cell23_5017044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_5017044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017044 prefixEnd_5017044 := by exact prefixLift 5017044
  have htrace : WordTrace (prefixWord ++ tailWord_5017044) baseStart_5017044 baseEnd_5017044 := by
    simpa [prefixWord, tailWord_5017044, baseEnd_5017044] using wordTrace_append hprefix tailTrace_5017044
  have hstable : (prefixWord ++ tailWord_5017044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017044).length < 2 ^ (prefixWord ++ tailWord_5017044).sum := by decide
  have hdescent : baseEnd_5017044 < baseStart_5017044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017060 : List Nat := [2, 3, 1, 1, 1, 1, 1, 7, 2, 4]
def baseStart_5017060 : Nat := 118140960795 + 5017060 * 2 ^ 59
def prefixEnd_5017060 : Nat := 4983230072969 + 3 ^ 40 * 5017060 * 2
def baseEnd_5017060 : Nat := 858721084148748654458989

theorem tailTrace_5017060 : CollatzResearch.WordTrace tailWord_5017060 prefixEnd_5017060 858721084148748654458989 := by
  unfold tailWord_5017060
  simp only [CollatzResearch.WordTrace]
  refine ⟨91493605602027970238072317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121991474136037293650763089 91493605602027970238072317)
  ·
    refine ⟨34310102100760488839277119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91493605602027970238072317 34310102100760488839277119)
    ·
      refine ⟨51465153151140733258915679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34310102100760488839277119 51465153151140733258915679)
      ·
        refine ⟨77197729726711099888373519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51465153151140733258915679 77197729726711099888373519)
        ·
          refine ⟨115796594590066649832560279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77197729726711099888373519 115796594590066649832560279)
          ·
            refine ⟨173694891885099974748840419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115796594590066649832560279 173694891885099974748840419)
            ·
              refine ⟨260542337827649962123260629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173694891885099974748840419 260542337827649962123260629)
              ·
                refine ⟨6106461042835545987263921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 260542337827649962123260629 6106461042835545987263921)
                ·
                  refine ⟨4579845782126659490447941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6106461042835545987263921 4579845782126659490447941)
                  ·
                    refine ⟨858721084148748654458989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4579845782126659490447941 858721084148748654458989)
                    ·
                      rfl

theorem cell23_5017060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_5017060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017060 prefixEnd_5017060 := by exact prefixLift 5017060
  have htrace : WordTrace (prefixWord ++ tailWord_5017060) baseStart_5017060 baseEnd_5017060 := by
    simpa [prefixWord, tailWord_5017060, baseEnd_5017060] using wordTrace_append hprefix tailTrace_5017060
  have hstable : (prefixWord ++ tailWord_5017060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017060).length < 2 ^ (prefixWord ++ tailWord_5017060).sum := by decide
  have hdescent : baseEnd_5017060 < baseStart_5017060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017073 : List Nat := [1, 2, 2, 2, 3, 3, 1, 9]
def baseStart_5017073 : Nat := 118140960795 + 5017073 * 2 ^ 59
def prefixEnd_5017073 : Nat := 4983230072969 + 3 ^ 40 * 5017073 * 2
def baseEnd_5017073 : Nat := 95413701025731644907941

theorem tailTrace_5017073 : CollatzResearch.WordTrace tailWord_5017073 prefixEnd_5017073 95413701025731644907941 := by
  unfold tailWord_5017073
  simp only [CollatzResearch.WordTrace]
  refine ⟨182987685353008843696367873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121991790235339229130911915 182987685353008843696367873)
  ·
    refine ⟨137240764014756632772275905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182987685353008843696367873 137240764014756632772275905)
    ·
      refine ⟨102930573011067474579206929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137240764014756632772275905 102930573011067474579206929)
      ·
        refine ⟨77197929758300605934405197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102930573011067474579206929 77197929758300605934405197)
        ·
          refine ⟨28949223659362727225401949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77197929758300605934405197 28949223659362727225401949)
          ·
            refine ⟨10855958872261022709525731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28949223659362727225401949 10855958872261022709525731)
            ·
              refine ⟨16283938308391534064288597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10855958872261022709525731 16283938308391534064288597)
              ·
                refine ⟨95413701025731644907941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16283938308391534064288597 95413701025731644907941)
                ·
                  rfl

theorem cell23_5017073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 9].length) (baseStart_5017073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017073 prefixEnd_5017073 := by exact prefixLift 5017073
  have htrace : WordTrace (prefixWord ++ tailWord_5017073) baseStart_5017073 baseEnd_5017073 := by
    simpa [prefixWord, tailWord_5017073, baseEnd_5017073] using wordTrace_append hprefix tailTrace_5017073
  have hstable : (prefixWord ++ tailWord_5017073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017073).length < 2 ^ (prefixWord ++ tailWord_5017073).sum := by decide
  have hdescent : baseEnd_5017073 < baseStart_5017073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017077 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 4, 4]
def baseStart_5017077 : Nat := 118140960795 + 5017077 * 2 ^ 59
def prefixEnd_5017077 : Nat := 4983230072969 + 3 ^ 40 * 5017077 * 2
def baseEnd_5017077 : Nat := 858723993872457465621463

theorem tailTrace_5017077 : CollatzResearch.WordTrace tailWord_5017077 prefixEnd_5017077 858723993872457465621463 := by
  unfold tailWord_5017077
  simp only [CollatzResearch.WordTrace]
  refine ⟨182987831244994352379513485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121991887496662901586342323 182987831244994352379513485)
  ·
    refine ⟨68620436716872882142317557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182987831244994352379513485 68620436716872882142317557)
    ·
      refine ⟨6433165942206832700842271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68620436716872882142317557 6433165942206832700842271)
      ·
        refine ⟨9649748913310249051263407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6433165942206832700842271 9649748913310249051263407)
        ·
          refine ⟨14474623369965373576895111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9649748913310249051263407 14474623369965373576895111)
          ·
            refine ⟨21711935054948060365342667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14474623369965373576895111 21711935054948060365342667)
            ·
              refine ⟨32567902582422090548014001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21711935054948060365342667 32567902582422090548014001)
              ·
                refine ⟨24425926936816567911010501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32567902582422090548014001 24425926936816567911010501)
                ·
                  refine ⟨4579861300653106483314469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24425926936816567911010501 4579861300653106483314469)
                  ·
                    refine ⟨858723993872457465621463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4579861300653106483314469 858723993872457465621463)
                    ·
                      rfl

theorem cell23_5017077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_5017077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017077 prefixEnd_5017077 := by exact prefixLift 5017077
  have htrace : WordTrace (prefixWord ++ tailWord_5017077) baseStart_5017077 baseEnd_5017077 := by
    simpa [prefixWord, tailWord_5017077, baseEnd_5017077] using wordTrace_append hprefix tailTrace_5017077
  have hstable : (prefixWord ++ tailWord_5017077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017077).length < 2 ^ (prefixWord ++ tailWord_5017077).sum := by decide
  have hdescent : baseEnd_5017077 < baseStart_5017077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017090 : List Nat := [3, 4, 1, 2, 1, 1, 11]
def baseStart_5017090 : Nat := 118140960795 + 5017090 * 2 ^ 59
def prefixEnd_5017090 : Nat := 4983230072969 + 3 ^ 40 * 5017090 * 2
def baseEnd_5017090 : Nat := 31804674776121985753109

theorem tailTrace_5017090 : CollatzResearch.WordTrace tailWord_5017090 prefixEnd_5017090 31804674776121985753109 := by
  unfold tailWord_5017090
  simp only [CollatzResearch.WordTrace]
  refine ⟨45747076348486813899934181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121992203595964837066491149 45747076348486813899934181)
  ·
    refine ⟨8577576815341277606237659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45747076348486813899934181 8577576815341277606237659)
    ·
      refine ⟨12866365223011916409356489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8577576815341277606237659 12866365223011916409356489)
      ·
        refine ⟨9649773917258937307017367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12866365223011916409356489 9649773917258937307017367)
        ·
          refine ⟨14474660875888405960526051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9649773917258937307017367 14474660875888405960526051)
          ·
            refine ⟨21711991313832608940789077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14474660875888405960526051 21711991313832608940789077)
            ·
              refine ⟨31804674776121985753109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 21711991313832608940789077 31804674776121985753109)
              ·
                rfl

theorem cell23_5017090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 11].length) (baseStart_5017090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017090 prefixEnd_5017090 := by exact prefixLift 5017090
  have htrace : WordTrace (prefixWord ++ tailWord_5017090) baseStart_5017090 baseEnd_5017090 := by
    simpa [prefixWord, tailWord_5017090, baseEnd_5017090] using wordTrace_append hprefix tailTrace_5017090
  have hstable : (prefixWord ++ tailWord_5017090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017090).length < 2 ^ (prefixWord ++ tailWord_5017090).sum := by decide
  have hdescent : baseEnd_5017090 < baseStart_5017090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017163 : List Nat := [1, 1, 1, 1, 3, 1, 3, 5, 7]
def baseStart_5017163 : Nat := 118140960795 + 5017163 * 2 ^ 59
def prefixEnd_5017163 : Nat := 4983230072969 + 3 ^ 40 * 5017163 * 2
def baseEnd_5017163 : Nat := 286246237883739895598777

theorem tailTrace_5017163 : CollatzResearch.WordTrace tailWord_5017163 prefixEnd_5017163 286246237883739895598777 := by
  unfold tailWord_5017163
  simp only [CollatzResearch.WordTrace]
  refine ⟨182990967922682789067144143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121993978615121859378096095 182990967922682789067144143)
  ·
    refine ⟨274486451884024183600716215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182990967922682789067144143 274486451884024183600716215)
    ·
      refine ⟨411729677826036275401074323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274486451884024183600716215 411729677826036275401074323)
      ·
        refine ⟨617594516739054413101611485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411729677826036275401074323 617594516739054413101611485)
        ·
          refine ⟨231597943777145404913104307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 617594516739054413101611485 231597943777145404913104307)
          ·
            refine ⟨347396915665718107369656461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231597943777145404913104307 347396915665718107369656461)
            ·
              refine ⟨130273843374644290263621173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 347396915665718107369656461 130273843374644290263621173)
              ·
                refine ⟨12213172816372902212214485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 130273843374644290263621173 12213172816372902212214485)
                ·
                  refine ⟨286246237883739895598777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12213172816372902212214485 286246237883739895598777)
                  ·
                    rfl

theorem cell23_5017163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 7].length) (baseStart_5017163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017163 prefixEnd_5017163 := by exact prefixLift 5017163
  have htrace : WordTrace (prefixWord ++ tailWord_5017163) baseStart_5017163 baseEnd_5017163 := by
    simpa [prefixWord, tailWord_5017163, baseEnd_5017163] using wordTrace_append hprefix tailTrace_5017163
  have hstable : (prefixWord ++ tailWord_5017163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017163).length < 2 ^ (prefixWord ++ tailWord_5017163).sum := by decide
  have hdescent : baseEnd_5017163 < baseStart_5017163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017170 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_5017170 : Nat := 118140960795 + 5017170 * 2 ^ 59
def prefixEnd_5017170 : Nat := 4983230072969 + 3 ^ 40 * 5017170 * 2
def baseEnd_5017170 : Nat := 2576219735318240533001461

theorem tailTrace_5017170 : CollatzResearch.WordTrace tailWord_5017170 prefixEnd_5017170 2576219735318240533001461 := by
  unfold tailWord_5017170
  simp only [CollatzResearch.WordTrace]
  refine ⟨45747805808414357315662241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121994148822438286175099309 45747805808414357315662241)
  ·
    refine ⟨34310854356310767986746681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45747805808414357315662241 34310854356310767986746681)
    ·
      refine ⟨25733140767233075990060011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34310854356310767986746681 25733140767233075990060011)
      ·
        refine ⟨38599711150849613985090017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25733140767233075990060011 38599711150849613985090017)
        ·
          refine ⟨28949783363137210488817513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38599711150849613985090017 28949783363137210488817513)
          ·
            refine ⟨21712337522352907866613135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28949783363137210488817513 21712337522352907866613135)
            ·
              refine ⟨32568506283529361799919703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21712337522352907866613135 32568506283529361799919703)
              ·
                refine ⟨48852759425294042699879555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32568506283529361799919703 48852759425294042699879555)
                ·
                  refine ⟨73279139137941064049819333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48852759425294042699879555 73279139137941064049819333)
                  ·
                    refine ⟨13739838588363949509341125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73279139137941064049819333 13739838588363949509341125)
                    ·
                      refine ⟨2576219735318240533001461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13739838588363949509341125 2576219735318240533001461)
                      ·
                        rfl

theorem cell23_5017170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_5017170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017170 prefixEnd_5017170 := by exact prefixLift 5017170
  have htrace : WordTrace (prefixWord ++ tailWord_5017170) baseStart_5017170 baseEnd_5017170 := by
    simpa [prefixWord, tailWord_5017170, baseEnd_5017170] using wordTrace_append hprefix tailTrace_5017170
  have hstable : (prefixWord ++ tailWord_5017170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017170).length < 2 ^ (prefixWord ++ tailWord_5017170).sum := by decide
  have hdescent : baseEnd_5017170 < baseStart_5017170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017180 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 9]
def baseStart_5017180 : Nat := 118140960795 + 5017180 * 2 ^ 59
def prefixEnd_5017180 : Nat := 4983230072969 + 3 ^ 40 * 5017180 * 2
def baseEnd_5017180 : Nat := 286247207791642832652935

theorem tailTrace_5017180 : CollatzResearch.WordTrace tailWord_5017180 prefixEnd_5017180 286247207791642832652935 := by
  unfold tailWord_5017180
  simp only [CollatzResearch.WordTrace]
  refine ⟨91495793981810600485256497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121994391975747467313675329 91495793981810600485256497)
  ·
    refine ⟨68621845486357950363942373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91495793981810600485256497 68621845486357950363942373)
    ·
      refine ⟨12866596028692115693239195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68621845486357950363942373 12866596028692115693239195)
      ·
        refine ⟨19299894043038173539858793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12866596028692115693239195 19299894043038173539858793)
        ·
          refine ⟨14474920532278630154894095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19299894043038173539858793 14474920532278630154894095)
          ·
            refine ⟨21712380798417945232341143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14474920532278630154894095 21712380798417945232341143)
            ·
              refine ⟨32568571197626917848511715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21712380798417945232341143 32568571197626917848511715)
              ·
                refine ⟨48852856796440376772767573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32568571197626917848511715 48852856796440376772767573)
                ·
                  refine ⟨286247207791642832652935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48852856796440376772767573 286247207791642832652935)
                  ·
                    rfl

theorem cell23_5017180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 9].length) (baseStart_5017180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017180 prefixEnd_5017180 := by exact prefixLift 5017180
  have htrace : WordTrace (prefixWord ++ tailWord_5017180) baseStart_5017180 baseEnd_5017180 := by
    simpa [prefixWord, tailWord_5017180, baseEnd_5017180] using wordTrace_append hprefix tailTrace_5017180
  have hstable : (prefixWord ++ tailWord_5017180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017180).length < 2 ^ (prefixWord ++ tailWord_5017180).sum := by decide
  have hdescent : baseEnd_5017180 < baseStart_5017180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017267 : List Nat := [1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 3]
def baseStart_5017267 : Nat := 118140960795 + 5017267 * 2 ^ 59
def prefixEnd_5017267 : Nat := 4983230072969 + 3 ^ 40 * 5017267 * 2
def baseEnd_5017267 : Nat := 2576269542941726653488515

theorem tailTrace_5017267 : CollatzResearch.WordTrace tailWord_5017267 prefixEnd_5017267 2576269542941726653488515 := by
  unfold tailWord_5017267
  simp only [CollatzResearch.WordTrace]
  refine ⟨182994761114306014828930055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121996507409537343219286703 182994761114306014828930055)
  ·
    refine ⟨274492141671459022243395083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182994761114306014828930055 274492141671459022243395083)
    ·
      refine ⟨411738212507188533365092625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274492141671459022243395083 411738212507188533365092625)
      ·
        refine ⟨308803659380391400023819469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 411738212507188533365092625 308803659380391400023819469)
        ·
          refine ⟨115801372267646775008932301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308803659380391400023819469 115801372267646775008932301)
          ·
            refine ⟨43425514600367540628349613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115801372267646775008932301 43425514600367540628349613)
            ·
              refine ⟨16284567975137827735631105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43425514600367540628349613 16284567975137827735631105)
              ·
                refine ⟨12213425981353370801723329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16284567975137827735631105 12213425981353370801723329)
                ·
                  refine ⟨9160069486015028101292497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12213425981353370801723329 9160069486015028101292497)
                  ·
                    refine ⟨6870052114511271075969373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9160069486015028101292497 6870052114511271075969373)
                    ·
                      refine ⟨2576269542941726653488515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6870052114511271075969373 2576269542941726653488515)
                      ·
                        rfl

theorem cell23_5017267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 3].length) (baseStart_5017267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017267 prefixEnd_5017267 := by exact prefixLift 5017267
  have htrace : WordTrace (prefixWord ++ tailWord_5017267) baseStart_5017267 baseEnd_5017267 := by
    simpa [prefixWord, tailWord_5017267, baseEnd_5017267] using wordTrace_append hprefix tailTrace_5017267
  have hstable : (prefixWord ++ tailWord_5017267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017267).length < 2 ^ (prefixWord ++ tailWord_5017267).sum := by decide
  have hdescent : baseEnd_5017267 < baseStart_5017267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017274 : List Nat := [3, 1, 1, 1, 2, 6, 1, 1, 3, 4]
def baseStart_5017274 : Nat := 118140960795 + 5017274 * 2 ^ 59
def prefixEnd_5017274 : Nat := 4983230072969 + 3 ^ 40 * 5017274 * 2
def baseEnd_5017274 : Nat := 858757712435436042033661

theorem tailTrace_5017274 : CollatzResearch.WordTrace tailWord_5017274 prefixEnd_5017274 858757712435436042033661 := by
  unfold tailWord_5017274
  simp only [CollatzResearch.WordTrace]
  refine ⟨45748754106320163756108719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121996677616853770016289917 45748754106320163756108719)
  ·
    refine ⟨68623131159480245634163079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45748754106320163756108719 68623131159480245634163079)
    ·
      refine ⟨102934696739220368451244619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68623131159480245634163079 102934696739220368451244619)
      ·
        refine ⟨154402045108830552676866929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102934696739220368451244619 154402045108830552676866929)
        ·
          refine ⟨115801533831622914507650197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154402045108830552676866929 115801533831622914507650197)
          ·
            refine ⟨5428196898357324117546103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115801533831622914507650197 5428196898357324117546103)
            ·
              refine ⟨8142295347535986176319155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5428196898357324117546103 8142295347535986176319155)
              ·
                refine ⟨12213443021303979264478733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8142295347535986176319155 12213443021303979264478733)
                ·
                  refine ⟨4580041132988992224179525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12213443021303979264478733 4580041132988992224179525)
                  ·
                    refine ⟨858757712435436042033661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4580041132988992224179525 858757712435436042033661)
                    ·
                      rfl

theorem cell23_5017274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_5017274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017274 prefixEnd_5017274 := by exact prefixLift 5017274
  have htrace : WordTrace (prefixWord ++ tailWord_5017274) baseStart_5017274 baseEnd_5017274 := by
    simpa [prefixWord, tailWord_5017274, baseEnd_5017274] using wordTrace_append hprefix tailTrace_5017274
  have hstable : (prefixWord ++ tailWord_5017274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017274).length < 2 ^ (prefixWord ++ tailWord_5017274).sum := by decide
  have hdescent : baseEnd_5017274 < baseStart_5017274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017324 : List Nat := [2, 2, 1, 1, 2, 2, 4, 2, 2, 3, 2]
def baseStart_5017324 : Nat := 118140960795 + 5017324 * 2 ^ 59
def prefixEnd_5017324 : Nat := 4983230072969 + 3 ^ 40 * 5017324 * 2
def baseEnd_5017324 : Nat := 2576298811339032930475753

theorem tailTrace_5017324 : CollatzResearch.WordTrace tailWord_5017324 prefixEnd_5017324 2576298811339032930475753 := by
  unfold tailWord_5017324
  simp only [CollatzResearch.WordTrace]
  refine ⟨91498420037549756781877513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121997893383399675709170017 91498420037549756781877513)
  ·
    refine ⟨68623815028162317586408135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91498420037549756781877513 68623815028162317586408135)
    ·
      refine ⟨102935722542243476379612203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68623815028162317586408135 102935722542243476379612203)
      ·
        refine ⟨154403583813365214569418305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102935722542243476379612203 154403583813365214569418305)
        ·
          refine ⟨115802687860023910927063729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154403583813365214569418305 115802687860023910927063729)
          ·
            refine ⟨86852015895017933195297797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115802687860023910927063729 86852015895017933195297797)
            ·
              refine ⟨16284752980315862474118337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86852015895017933195297797 16284752980315862474118337)
              ·
                refine ⟨12213564735236896855588753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16284752980315862474118337 12213564735236896855588753)
                ·
                  refine ⟨9160173551427672641691565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12213564735236896855588753 9160173551427672641691565)
                  ·
                    refine ⟨3435065081785377240634337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9160173551427672641691565 3435065081785377240634337)
                    ·
                      refine ⟨2576298811339032930475753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3435065081785377240634337 2576298811339032930475753)
                      ·
                        rfl

theorem cell23_5017324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 3, 2].length) (baseStart_5017324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017324 prefixEnd_5017324 := by exact prefixLift 5017324
  have htrace : WordTrace (prefixWord ++ tailWord_5017324) baseStart_5017324 baseEnd_5017324 := by
    simpa [prefixWord, tailWord_5017324, baseEnd_5017324] using wordTrace_append hprefix tailTrace_5017324
  have hstable : (prefixWord ++ tailWord_5017324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017324).length < 2 ^ (prefixWord ++ tailWord_5017324).sum := by decide
  have hdescent : baseEnd_5017324 < baseStart_5017324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017337 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 4, 6, 2]
def baseStart_5017337 : Nat := 118140960795 + 5017337 * 2 ^ 59
def prefixEnd_5017337 : Nat := 4983230072969 + 3 ^ 40 * 5017337 * 2
def baseEnd_5017337 : Nat := 2576305486587541379613193

theorem tailTrace_5017337 : CollatzResearch.WordTrace tailWord_5017337 prefixEnd_5017337 2576305486587541379613193 := by
  unfold tailWord_5017337
  simp only [CollatzResearch.WordTrace]
  refine ⟨182997314224052416783978265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121998209482701611189318843 182997314224052416783978265)
  ·
    refine ⟨137247985668039312587983699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182997314224052416783978265 137247985668039312587983699)
    ·
      refine ⟨205871978502058968881975549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137247985668039312587983699 205871978502058968881975549)
      ·
        refine ⟨77201991938272113330740831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205871978502058968881975549 77201991938272113330740831)
        ·
          refine ⟨115802987907408169996111247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77201991938272113330740831 115802987907408169996111247)
          ·
            refine ⟨173704481861112254994166871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115802987907408169996111247 173704481861112254994166871)
            ·
              refine ⟨260556722791668382491250307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173704481861112254994166871 260556722791668382491250307)
              ·
                refine ⟨390835084187502573736875461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260556722791668382491250307 390835084187502573736875461)
                ·
                  refine ⟨73281578285156732575664149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 390835084187502573736875461 73281578285156732575664149)
                  ·
                    refine ⟨3435073982116721839484257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73281578285156732575664149 3435073982116721839484257)
                    ·
                      refine ⟨2576305486587541379613193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3435073982116721839484257 2576305486587541379613193)
                      ·
                        rfl

theorem cell23_5017337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_5017337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017337 prefixEnd_5017337 := by exact prefixLift 5017337
  have htrace : WordTrace (prefixWord ++ tailWord_5017337) baseStart_5017337 baseEnd_5017337 := by
    simpa [prefixWord, tailWord_5017337, baseEnd_5017337] using wordTrace_append hprefix tailTrace_5017337
  have hstable : (prefixWord ++ tailWord_5017337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017337).length < 2 ^ (prefixWord ++ tailWord_5017337).sum := by decide
  have hdescent : baseEnd_5017337 < baseStart_5017337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017381 : List Nat := [1, 3, 1, 2, 3, 4, 1, 2, 2, 4]
def baseStart_5017381 : Nat := 118140960795 + 5017381 * 2 ^ 59
def prefixEnd_5017381 : Nat := 4983230072969 + 3 ^ 40 * 5017381 * 2
def baseEnd_5017381 : Nat := 858776026578779735820997

theorem tailTrace_5017381 : CollatzResearch.WordTrace tailWord_5017381 prefixEnd_5017381 858776026578779735820997 := by
  unfold tailWord_5017381
  simp only [CollatzResearch.WordTrace]
  refine ⟨182998919035893012298579997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121999279357262008199053331 182998919035893012298579997)
  ·
    refine ⟨68624594638459879611967499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182998919035893012298579997 68624594638459879611967499)
    ·
      refine ⟨102936891957689819417951249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68624594638459879611967499 102936891957689819417951249)
      ·
        refine ⟨77202668968267364563463437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102936891957689819417951249 77202668968267364563463437)
        ·
          refine ⟨28951000863100261711298789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77202668968267364563463437 28951000863100261711298789)
          ·
            refine ⟨5428312661831299070868523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28951000863100261711298789 5428312661831299070868523)
            ·
              refine ⟨8142468992746948606302785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5428312661831299070868523 8142468992746948606302785)
              ·
                refine ⟨6106851744560211454727089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8142468992746948606302785 6106851744560211454727089)
                ·
                  refine ⟨4580138808420158591045317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6106851744560211454727089 4580138808420158591045317)
                  ·
                    refine ⟨858776026578779735820997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4580138808420158591045317 858776026578779735820997)
                    ·
                      rfl

theorem cell23_5017381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_5017381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017381 prefixEnd_5017381 := by exact prefixLift 5017381
  have htrace : WordTrace (prefixWord ++ tailWord_5017381) baseStart_5017381 baseEnd_5017381 := by
    simpa [prefixWord, tailWord_5017381, baseEnd_5017381] using wordTrace_append hprefix tailTrace_5017381
  have hstable : (prefixWord ++ tailWord_5017381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017381).length < 2 ^ (prefixWord ++ tailWord_5017381).sum := by decide
  have hdescent : baseEnd_5017381 < baseStart_5017381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017388 : List Nat := [2, 2, 1, 1, 1, 5, 2, 4, 1, 2, 2]
def baseStart_5017388 : Nat := 118140960795 + 5017388 * 2 ^ 59
def prefixEnd_5017388 : Nat := 4983230072969 + 3 ^ 40 * 5017388 * 2
def baseEnd_5017388 : Nat := 2576331674100920680075459

theorem tailTrace_5017388 : CollatzResearch.WordTrace tailWord_5017388 prefixEnd_5017388 2576331674100920680075459 := by
  unfold tailWord_5017388
  simp only [CollatzResearch.WordTrace]
  refine ⟨91499587173433826247042409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121999449564578434996056545 91499587173433826247042409)
  ·
    refine ⟨68624690380075369685281807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91499587173433826247042409 68624690380075369685281807)
    ·
      refine ⟨102937035570113054527922711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68624690380075369685281807 102937035570113054527922711)
      ·
        refine ⟨154405553355169581791884067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102937035570113054527922711 154405553355169581791884067)
        ·
          refine ⟨231608330032754372687826101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154405553355169581791884067 231608330032754372687826101)
          ·
            refine ⟨21713280940570722439483697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 231608330032754372687826101 21713280940570722439483697)
            ·
              refine ⟨16284960705428041829612773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21713280940570722439483697 16284960705428041829612773)
              ·
                refine ⟨3053430132267757843052395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16284960705428041829612773 3053430132267757843052395)
                ·
                  refine ⟨4580145198401636764578593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3053430132267757843052395 4580145198401636764578593)
                  ·
                    refine ⟨3435108898801227573433945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4580145198401636764578593 3435108898801227573433945)
                    ·
                      refine ⟨2576331674100920680075459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3435108898801227573433945 2576331674100920680075459)
                      ·
                        rfl

theorem cell23_5017388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 1, 2, 2].length) (baseStart_5017388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017388 prefixEnd_5017388 := by exact prefixLift 5017388
  have htrace : WordTrace (prefixWord ++ tailWord_5017388) baseStart_5017388 baseEnd_5017388 := by
    simpa [prefixWord, tailWord_5017388, baseEnd_5017388] using wordTrace_append hprefix tailTrace_5017388
  have hstable : (prefixWord ++ tailWord_5017388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017388).length < 2 ^ (prefixWord ++ tailWord_5017388).sum := by decide
  have hdescent : baseEnd_5017388 < baseStart_5017388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017404 : List Nat := [2, 2, 2, 2, 1, 1, 5, 1, 1, 3, 3]
def baseStart_5017404 : Nat := 118140960795 + 5017404 * 2 ^ 59
def prefixEnd_5017404 : Nat := 4983230072969 + 3 ^ 40 * 5017404 * 2
def baseEnd_5017404 : Nat := 2576339889791392617475385

theorem tailTrace_5017404 : CollatzResearch.WordTrace tailWord_5017404 prefixEnd_5017404 2576339889791392617475385 := by
  unfold tailWord_5017404
  simp only [CollatzResearch.WordTrace]
  refine ⟨91499878957404843613333633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121999838609873124817778177 91499878957404843613333633)
  ·
    refine ⟨68624909218053632710000225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91499878957404843613333633 68624909218053632710000225)
    ·
      refine ⟨51468681913540224532500169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68624909218053632710000225 51468681913540224532500169)
      ·
        refine ⟨38601511435155168399375127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51468681913540224532500169 38601511435155168399375127)
        ·
          refine ⟨57902267152732752599062691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38601511435155168399375127 57902267152732752599062691)
          ·
            refine ⟨86853400729099128898594037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57902267152732752599062691 86853400729099128898594037)
            ·
              refine ⟨8142506318353043334243191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86853400729099128898594037 8142506318353043334243191)
              ·
                refine ⟨12213759477529565001364787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8142506318353043334243191 12213759477529565001364787)
                ·
                  refine ⟨18320639216294347502047181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12213759477529565001364787 18320639216294347502047181)
                  ·
                    refine ⟨6870239706110380313267693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18320639216294347502047181 6870239706110380313267693)
                    ·
                      refine ⟨2576339889791392617475385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6870239706110380313267693 2576339889791392617475385)
                      ·
                        rfl

theorem cell23_5017404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_5017404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017404 prefixEnd_5017404 := by exact prefixLift 5017404
  have htrace : WordTrace (prefixWord ++ tailWord_5017404) baseStart_5017404 baseEnd_5017404 := by
    simpa [prefixWord, tailWord_5017404, baseEnd_5017404] using wordTrace_append hprefix tailTrace_5017404
  have hstable : (prefixWord ++ tailWord_5017404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017404).length < 2 ^ (prefixWord ++ tailWord_5017404).sum := by decide
  have hdescent : baseEnd_5017404 < baseStart_5017404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017447 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_5017447 : Nat := 118140960795 + 5017447 * 2 ^ 59
def prefixEnd_5017447 : Nat := 4983230072969 + 3 ^ 40 * 5017447 * 2
def baseEnd_5017447 : Nat := 2576361969459535949237687

theorem tailTrace_5017447 : CollatzResearch.WordTrace tailWord_5017447 prefixEnd_5017447 2576361969459535949237687 := by
  unfold tailWord_5017447
  simp only [CollatzResearch.WordTrace]
  refine ⟨183001326253653905570482595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122000884169102603713655063 183001326253653905570482595)
  ·
    refine ⟨274501989380480858355723893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183001326253653905570482595 274501989380480858355723893)
    ·
      refine ⟨25734561504420080470849115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 274501989380480858355723893 25734561504420080470849115)
      ·
        refine ⟨38601842256630120706273673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25734561504420080470849115 38601842256630120706273673)
        ·
          refine ⟨28951381692472590529705255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38601842256630120706273673 28951381692472590529705255)
          ·
            refine ⟨43427072538708885794557883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28951381692472590529705255 43427072538708885794557883)
            ·
              refine ⟨65140608808063328691836825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43427072538708885794557883 65140608808063328691836825)
              ·
                refine ⟨48855456606047496518877619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65140608808063328691836825 48855456606047496518877619)
                ·
                  refine ⟨73283184909071244778316429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48855456606047496518877619 73283184909071244778316429)
                  ·
                    refine ⟨27481194340901716791868661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73283184909071244778316429 27481194340901716791868661)
                    ·
                      refine ⟨2576361969459535949237687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27481194340901716791868661 2576361969459535949237687)
                      ·
                        rfl

theorem cell23_5017447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_5017447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017447 prefixEnd_5017447 := by exact prefixLift 5017447
  have htrace : WordTrace (prefixWord ++ tailWord_5017447) baseStart_5017447 baseEnd_5017447 := by
    simpa [prefixWord, tailWord_5017447, baseEnd_5017447] using wordTrace_append hprefix tailTrace_5017447
  have hstable : (prefixWord ++ tailWord_5017447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017447).length < 2 ^ (prefixWord ++ tailWord_5017447).sum := by decide
  have hdescent : baseEnd_5017447 < baseStart_5017447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017457 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 1, 4, 4]
def baseStart_5017457 : Nat := 118140960795 + 5017457 * 2 ^ 59
def prefixEnd_5017457 : Nat := 4983230072969 + 3 ^ 40 * 5017457 * 2
def baseEnd_5017457 : Nat := 2576367104266080910112641

theorem tailTrace_5017457 : CollatzResearch.WordTrace tailWord_5017457 prefixEnd_5017457 2576367104266080910112641 := by
  unfold tailWord_5017457
  simp only [CollatzResearch.WordTrace]
  refine ⟨183001690983617677278346625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122001127322411784852231083 183001690983617677278346625)
  ·
    refine ⟨137251268237713257958759969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183001690983617677278346625 137251268237713257958759969)
    ·
      refine ⟨102938451178284943469069977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137251268237713257958759969 102938451178284943469069977)
      ·
        refine ⟨77203838383713707601802483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102938451178284943469069977 77203838383713707601802483)
        ·
          refine ⟨115805757575570561402703725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77203838383713707601802483 115805757575570561402703725)
          ·
            refine ⟨43427159090838960526013897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115805757575570561402703725 43427159090838960526013897)
            ·
              refine ⟨32570369318129220394510423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43427159090838960526013897 32570369318129220394510423)
              ·
                refine ⟨48855553977193830591765635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32570369318129220394510423 48855553977193830591765635)
                ·
                  refine ⟨73283330965790745887648453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48855553977193830591765635 73283330965790745887648453)
                  ·
                    refine ⟨13740624556085764853934085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73283330965790745887648453 13740624556085764853934085)
                    ·
                      refine ⟨2576367104266080910112641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13740624556085764853934085 2576367104266080910112641)
                      ·
                        rfl

theorem cell23_5017457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_5017457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017457 prefixEnd_5017457 := by exact prefixLift 5017457
  have htrace : WordTrace (prefixWord ++ tailWord_5017457) baseStart_5017457 baseEnd_5017457 := by
    simpa [prefixWord, tailWord_5017457, baseEnd_5017457] using wordTrace_append hprefix tailTrace_5017457
  have hstable : (prefixWord ++ tailWord_5017457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017457).length < 2 ^ (prefixWord ++ tailWord_5017457).sum := by decide
  have hdescent : baseEnd_5017457 < baseStart_5017457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017461 : List Nat := [1, 3, 4, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_5017461 : Nat := 118140960795 + 5017461 * 2 ^ 59
def prefixEnd_5017461 : Nat := 4983230072969 + 3 ^ 40 * 5017461 * 2
def baseEnd_5017461 : Nat := 2576369158188698894462623

theorem tailTrace_5017461 : CollatzResearch.WordTrace tailWord_5017461 prefixEnd_5017461 2576369158188698894462623 := by
  unfold tailWord_5017461
  simp only [CollatzResearch.WordTrace]
  refine ⟨183001836875603185961492237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122001224583735457307661491 183001836875603185961492237)
  ·
    refine ⟨68625688828351194735559589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183001836875603185961492237 68625688828351194735559589)
    ·
      refine ⟨12867316655315849012917423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68625688828351194735559589 12867316655315849012917423)
      ·
        refine ⟨19300974982973773519376135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12867316655315849012917423 19300974982973773519376135)
        ·
          refine ⟨28951462474460660279064203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19300974982973773519376135 28951462474460660279064203)
          ·
            refine ⟨43427193711690990418596305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28951462474460660279064203 43427193711690990418596305)
            ·
              refine ⟨32570395283768242813947229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43427193711690990418596305 32570395283768242813947229)
              ·
                refine ⟨12213898231413091055230211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32570395283768242813947229 12213898231413091055230211)
                ·
                  refine ⟨18320847347119636582845317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12213898231413091055230211 18320847347119636582845317)
                  ·
                    refine ⟨3435158877584931859283497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18320847347119636582845317 3435158877584931859283497)
                    ·
                      refine ⟨2576369158188698894462623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3435158877584931859283497 2576369158188698894462623)
                      ·
                        rfl

theorem cell23_5017461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_5017461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017461 prefixEnd_5017461 := by exact prefixLift 5017461
  have htrace : WordTrace (prefixWord ++ tailWord_5017461) baseStart_5017461 baseEnd_5017461 := by
    simpa [prefixWord, tailWord_5017461, baseEnd_5017461] using wordTrace_append hprefix tailTrace_5017461
  have hstable : (prefixWord ++ tailWord_5017461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017461).length < 2 ^ (prefixWord ++ tailWord_5017461).sum := by decide
  have hdescent : baseEnd_5017461 < baseStart_5017461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017484 : List Nat := [2, 2, 1, 2, 1, 2, 1, 7, 5]
def baseStart_5017484 : Nat := 118140960795 + 5017484 * 2 ^ 59
def prefixEnd_5017484 : Nat := 4983230072969 + 3 ^ 40 * 5017484 * 2
def baseEnd_5017484 : Nat := 286264552027083589386113

theorem tailTrace_5017484 : CollatzResearch.WordTrace tailWord_5017484 prefixEnd_5017484 286264552027083589386113 := by
  unfold tailWord_5017484
  simp only [CollatzResearch.WordTrace]
  refine ⟨91501337877259930444789753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122001783836346573926386337 91501337877259930444789753)
  ·
    refine ⟨68626003407944947833592315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91501337877259930444789753 68626003407944947833592315)
    ·
      refine ⟨102939005111917421750388473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68626003407944947833592315 102939005111917421750388473)
      ·
        refine ⟨77204253833938066312791355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102939005111917421750388473 77204253833938066312791355)
        ·
          refine ⟨115806380750907099469187033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77204253833938066312791355 115806380750907099469187033)
          ·
            refine ⟨86854785563180324601890275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115806380750907099469187033 86854785563180324601890275)
            ·
              refine ⟨130282178344770486902835413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86854785563180324601890275 130282178344770486902835413)
              ·
                refine ⟨3053488554955558286785205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 130282178344770486902835413 3053488554955558286785205)
                ·
                  refine ⟨286264552027083589386113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3053488554955558286785205 286264552027083589386113)
                  ·
                    rfl

theorem cell23_5017484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 5].length) (baseStart_5017484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017484 prefixEnd_5017484 := by exact prefixLift 5017484
  have htrace : WordTrace (prefixWord ++ tailWord_5017484) baseStart_5017484 baseEnd_5017484 := by
    simpa [prefixWord, tailWord_5017484, baseEnd_5017484] using wordTrace_append hprefix tailTrace_5017484
  have hstable : (prefixWord ++ tailWord_5017484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017484).length < 2 ^ (prefixWord ++ tailWord_5017484).sum := by decide
  have hdescent : baseEnd_5017484 < baseStart_5017484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017501 : List Nat := [1, 4, 2, 1, 2, 3, 1, 4, 5]
def baseStart_5017501 : Nat := 118140960795 + 5017501 * 2 ^ 59
def prefixEnd_5017501 : Nat := 4983230072969 + 3 ^ 40 * 5017501 * 2
def baseEnd_5017501 : Nat := 286265521934986526440271

theorem tailTrace_5017501 : CollatzResearch.WordTrace tailWord_5017501 prefixEnd_5017501 286265521934986526440271 := by
  unfold tailWord_5017501
  simp only [CollatzResearch.WordTrace]
  refine ⟨183003295795458272792948357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122002197196972181861965571 183003295795458272792948357)
  ·
    refine ⟨34313117961648426148677817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183003295795458272792948357 34313117961648426148677817)
    ·
      refine ⟨25734838471236319611508363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34313117961648426148677817 25734838471236319611508363)
      ·
        refine ⟨38602257706854479417262545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25734838471236319611508363 38602257706854479417262545)
        ·
          refine ⟨28951693280140859562946909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38602257706854479417262545 28951693280140859562946909)
          ·
            refine ⟨10856884980052822336105091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28951693280140859562946909 10856884980052822336105091)
            ·
              refine ⟨16285327470079233504157637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10856884980052822336105091 16285327470079233504157637)
              ·
                refine ⟨3053498900639856282029557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16285327470079233504157637 3053498900639856282029557)
                ·
                  refine ⟨286265521934986526440271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3053498900639856282029557 286265521934986526440271)
                  ·
                    rfl

theorem cell23_5017501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_5017501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017501 prefixEnd_5017501 := by exact prefixLift 5017501
  have htrace : WordTrace (prefixWord ++ tailWord_5017501) baseStart_5017501 baseEnd_5017501 := by
    simpa [prefixWord, tailWord_5017501, baseEnd_5017501] using wordTrace_append hprefix tailTrace_5017501
  have hstable : (prefixWord ++ tailWord_5017501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017501).length < 2 ^ (prefixWord ++ tailWord_5017501).sum := by decide
  have hdescent : baseEnd_5017501 < baseStart_5017501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017511 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_5017511 : Nat := 118140960795 + 5017511 * 2 ^ 59
def prefixEnd_5017511 : Nat := 4983230072969 + 3 ^ 40 * 5017511 * 2
def baseEnd_5017511 : Nat := 2576394832221423698837393

theorem tailTrace_5017511 : CollatzResearch.WordTrace tailWord_5017511 prefixEnd_5017511 2576394832221423698837393 := by
  unfold tailWord_5017511
  simp only [CollatzResearch.WordTrace]
  refine ⟨183003660525422044500812387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122002440350281363000541591 183003660525422044500812387)
  ·
    refine ⟨274505490788133066751218581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183003660525422044500812387 274505490788133066751218581)
    ·
      refine ⟨12867444880693737503963371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 274505490788133066751218581 12867444880693737503963371)
      ·
        refine ⟨19301167321040606255945057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12867444880693737503963371 19301167321040606255945057)
        ·
          refine ⟨14475875490780454691958793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19301167321040606255945057 14475875490780454691958793)
          ·
            refine ⟨10856906618085341018969095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14475875490780454691958793 10856906618085341018969095)
            ·
              refine ⟨16285359927128011528453643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10856906618085341018969095 16285359927128011528453643)
              ·
                refine ⟨24428039890692017292680465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16285359927128011528453643 24428039890692017292680465)
                ·
                  refine ⟨18321029918019012969510349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24428039890692017292680465 18321029918019012969510349)
                  ·
                    refine ⟨6870386219257129863566381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18321029918019012969510349 6870386219257129863566381)
                    ·
                      refine ⟨2576394832221423698837393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6870386219257129863566381 2576394832221423698837393)
                      ·
                        rfl

theorem cell23_5017511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_5017511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017511 prefixEnd_5017511 := by exact prefixLift 5017511
  have htrace : WordTrace (prefixWord ++ tailWord_5017511) baseStart_5017511 baseEnd_5017511 := by
    simpa [prefixWord, tailWord_5017511, baseEnd_5017511] using wordTrace_append hprefix tailTrace_5017511
  have hstable : (prefixWord ++ tailWord_5017511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017511).length < 2 ^ (prefixWord ++ tailWord_5017511).sum := by decide
  have hdescent : baseEnd_5017511 < baseStart_5017511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017547 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 6]
def baseStart_5017547 : Nat := 118140960795 + 5017547 * 2 ^ 59
def prefixEnd_5017547 : Nat := 4983230072969 + 3 ^ 40 * 5017547 * 2
def baseEnd_5017547 : Nat := 2576413317524985557987227

theorem tailTrace_5017547 : CollatzResearch.WordTrace tailWord_5017547 prefixEnd_5017547 2576413317524985557987227 := by
  unfold tailWord_5017547
  simp only [CollatzResearch.WordTrace]
  refine ⟨183004973553291622649122895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122003315702194415099415263 183004973553291622649122895)
  ·
    refine ⟨274507460329937433973684343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183004973553291622649122895 274507460329937433973684343)
    ·
      refine ⟨411761190494906150960526515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274507460329937433973684343 411761190494906150960526515)
      ·
        refine ⟨617641785742359226440789773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411761190494906150960526515 617641785742359226440789773)
        ·
          refine ⟨231615669653384709915296165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 617641785742359226440789773 231615669653384709915296165)
          ·
            refine ⟨43427938060009633109118031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 231615669653384709915296165 43427938060009633109118031)
            ·
              refine ⟨65141907090014449663677047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43427938060009633109118031 65141907090014449663677047)
              ·
                refine ⟨97712860635021674495515571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65141907090014449663677047 97712860635021674495515571)
                ·
                  refine ⟨146569290952532511743273357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97712860635021674495515571 146569290952532511743273357)
                  ·
                    refine ⟨54963484107199691903727509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146569290952532511743273357 54963484107199691903727509)
                    ·
                      refine ⟨2576413317524985557987227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54963484107199691903727509 2576413317524985557987227)
                      ·
                        rfl

theorem cell23_5017547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 6].length) (baseStart_5017547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017547 prefixEnd_5017547 := by exact prefixLift 5017547
  have htrace : WordTrace (prefixWord ++ tailWord_5017547) baseStart_5017547 baseEnd_5017547 := by
    simpa [prefixWord, tailWord_5017547, baseEnd_5017547] using wordTrace_append hprefix tailTrace_5017547
  have hstable : (prefixWord ++ tailWord_5017547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017547).length < 2 ^ (prefixWord ++ tailWord_5017547).sum := by decide
  have hdescent : baseEnd_5017547 < baseStart_5017547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017587 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 2, 9]
def baseStart_5017587 : Nat := 118140960795 + 5017587 * 2 ^ 59
def prefixEnd_5017587 : Nat := 4983230072969 + 3 ^ 40 * 5017587 * 2
def baseEnd_5017587 : Nat := 858811285583721800495681

theorem tailTrace_5017587 : CollatzResearch.WordTrace tailWord_5017587 prefixEnd_5017587 858811285583721800495681 := by
  unfold tailWord_5017587
  simp only [CollatzResearch.WordTrace]
  refine ⟨183006432473146709480579015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122004288315431139653719343 183006432473146709480579015)
  ·
    refine ⟨274509648709720064220868523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183006432473146709480579015 274509648709720064220868523)
    ·
      refine ⟨411764473064580096331302785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274509648709720064220868523 411764473064580096331302785)
      ·
        refine ⟨308823354798435072248477089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 411764473064580096331302785 308823354798435072248477089)
        ·
          refine ⟨231617516098826304186357817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308823354798435072248477089 231617516098826304186357817)
          ·
            refine ⟨173713137074119728139768363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231617516098826304186357817 173713137074119728139768363)
            ·
              refine ⟨260569705611179592209652545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173713137074119728139768363 260569705611179592209652545)
              ·
                refine ⟨195427279208384694157239409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260569705611179592209652545 195427279208384694157239409)
                ·
                  refine ⟨146570459406288520617929557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195427279208384694157239409 146570459406288520617929557)
                  ·
                    refine ⟨858811285583721800495681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 146570459406288520617929557 858811285583721800495681)
                    ·
                      rfl

theorem cell23_5017587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 9].length) (baseStart_5017587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017587 prefixEnd_5017587 := by exact prefixLift 5017587
  have htrace : WordTrace (prefixWord ++ tailWord_5017587) baseStart_5017587 baseEnd_5017587 := by
    simpa [prefixWord, tailWord_5017587, baseEnd_5017587] using wordTrace_append hprefix tailTrace_5017587
  have hstable : (prefixWord ++ tailWord_5017587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017587).length < 2 ^ (prefixWord ++ tailWord_5017587).sum := by decide
  have hdescent : baseEnd_5017587 < baseStart_5017587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017675 : List Nat := [1, 1, 1, 1, 3, 1, 2, 8, 1, 2, 2]
def baseStart_5017675 : Nat := 118140960795 + 5017675 * 2 ^ 59
def prefixEnd_5017675 : Nat := 4983230072969 + 3 ^ 40 * 5017675 * 2
def baseEnd_5017675 : Nat := 2576479043048761057186639

theorem tailTrace_5017675 : CollatzResearch.WordTrace tailWord_5017675 prefixEnd_5017675 2576479043048761057186639 := by
  unfold tailWord_5017675
  simp only [CollatzResearch.WordTrace]
  refine ⟨183009642096827900509782479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122006428064551933673188319 183009642096827900509782479)
  ·
    refine ⟨274514463145241850764673719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183009642096827900509782479 274514463145241850764673719)
    ·
      refine ⟨411771694717862776147010579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274514463145241850764673719 411771694717862776147010579)
      ·
        refine ⟨617657542076794164220515869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411771694717862776147010579 617657542076794164220515869)
        ·
          refine ⟨231621578278797811582693451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 617657542076794164220515869 231621578278797811582693451)
          ·
            refine ⟨347432367418196717374040177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231621578278797811582693451 347432367418196717374040177)
            ·
              refine ⟨260574275563647538030530133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347432367418196717374040177 260574275563647538030530133)
              ·
                refine ⟨3053604791761494586295275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 260574275563647538030530133 3053604791761494586295275)
                ·
                  refine ⟨4580407187642241879442913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3053604791761494586295275 4580407187642241879442913)
                  ·
                    refine ⟨3435305390731681409582185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4580407187642241879442913 3435305390731681409582185)
                    ·
                      refine ⟨2576479043048761057186639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3435305390731681409582185 2576479043048761057186639)
                      ·
                        rfl

theorem cell23_5017675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 1, 2, 2].length) (baseStart_5017675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017675 prefixEnd_5017675 := by exact prefixLift 5017675
  have htrace : WordTrace (prefixWord ++ tailWord_5017675) baseStart_5017675 baseEnd_5017675 := by
    simpa [prefixWord, tailWord_5017675, baseEnd_5017675] using wordTrace_append hprefix tailTrace_5017675
  have hstable : (prefixWord ++ tailWord_5017675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017675).length < 2 ^ (prefixWord ++ tailWord_5017675).sum := by decide
  have hdescent : baseEnd_5017675 < baseStart_5017675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017725 : List Nat := [1, 4, 1, 1, 3, 2, 3, 2, 2, 1, 3]
def baseStart_5017725 : Nat := 118140960795 + 5017725 * 2 ^ 59
def prefixEnd_5017725 : Nat := 4983230072969 + 3 ^ 40 * 5017725 * 2
def baseEnd_5017725 : Nat := 2576504717081485861561409

theorem tailTrace_5017725 : CollatzResearch.WordTrace tailWord_5017725 prefixEnd_5017725 2576504717081485861561409 := by
  unfold tailWord_5017725
  simp only [CollatzResearch.WordTrace]
  refine ⟨183011465746646759049102629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122007643831097839366068419 183011465746646759049102629)
  ·
    refine ⟨34314649827496267321706743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183011465746646759049102629 34314649827496267321706743)
    ·
      refine ⟨51471974741244400982560115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34314649827496267321706743 51471974741244400982560115)
      ·
        refine ⟨77207962111866601473840173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51471974741244400982560115 77207962111866601473840173)
        ·
          refine ⟨28952985791949975552690065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77207962111866601473840173 28952985791949975552690065)
          ·
            refine ⟨21714739343962481664517549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28952985791949975552690065 21714739343962481664517549)
            ·
              refine ⟨8143027253985930624194081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21714739343962481664517549 8143027253985930624194081)
              ·
                refine ⟨6107270440489447968145561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8143027253985930624194081 6107270440489447968145561)
                ·
                  refine ⟨4580452830367085976109171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6107270440489447968145561 4580452830367085976109171)
                  ·
                    refine ⟨6870679245550628964163757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4580452830367085976109171 6870679245550628964163757)
                    ·
                      refine ⟨2576504717081485861561409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6870679245550628964163757 2576504717081485861561409)
                      ·
                        rfl

theorem cell23_5017725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_5017725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017725 prefixEnd_5017725 := by exact prefixLift 5017725
  have htrace : WordTrace (prefixWord ++ tailWord_5017725) baseStart_5017725 baseEnd_5017725 := by
    simpa [prefixWord, tailWord_5017725, baseEnd_5017725] using wordTrace_append hprefix tailTrace_5017725
  have hstable : (prefixWord ++ tailWord_5017725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017725).length < 2 ^ (prefixWord ++ tailWord_5017725).sum := by decide
  have hdescent : baseEnd_5017725 < baseStart_5017725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017742 : List Nat := [4, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3]
def baseStart_5017742 : Nat := 118140960795 + 5017742 * 2 ^ 59
def prefixEnd_5017742 : Nat := 4983230072969 + 3 ^ 40 * 5017742 * 2
def baseEnd_5017742 : Nat := 2576513446252612295048831

theorem tailTrace_5017742 : CollatzResearch.WordTrace tailWord_5017742 prefixEnd_5017742 2576513446252612295048831 := by
  unfold tailWord_5017742
  simp only [CollatzResearch.WordTrace]
  refine ⟨22876510723448146369058935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122008057191723447301647653 22876510723448146369058935)
  ·
    refine ⟨34314766085172219553588403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22876510723448146369058935 34314766085172219553588403)
    ·
      refine ⟨51472149127758329330382605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34314766085172219553588403 51472149127758329330382605)
      ·
        refine ⟨19302055922909373498893477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51472149127758329330382605 19302055922909373498893477)
        ·
          refine ⟨3619135485545507531042527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19302055922909373498893477 3619135485545507531042527)
          ·
            refine ⟨5428703228318261296563791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3619135485545507531042527 5428703228318261296563791)
            ·
              refine ⟨8143054842477391944845687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5428703228318261296563791 8143054842477391944845687)
              ·
                refine ⟨12214582263716087917268531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8143054842477391944845687 12214582263716087917268531)
                ·
                  refine ⟨18321873395574131875902797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12214582263716087917268531 18321873395574131875902797)
                  ·
                    refine ⟨6870702523340299453463549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18321873395574131875902797 6870702523340299453463549)
                    ·
                      refine ⟨2576513446252612295048831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6870702523340299453463549 2576513446252612295048831)
                      ·
                        rfl

theorem cell23_5017742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_5017742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017742 prefixEnd_5017742 := by exact prefixLift 5017742
  have htrace : WordTrace (prefixWord ++ tailWord_5017742) baseStart_5017742 baseEnd_5017742 := by
    simpa [prefixWord, tailWord_5017742, baseEnd_5017742] using wordTrace_append hprefix tailTrace_5017742
  have hstable : (prefixWord ++ tailWord_5017742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017742).length < 2 ^ (prefixWord ++ tailWord_5017742).sum := by decide
  have hdescent : baseEnd_5017742 < baseStart_5017742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017752 : List Nat := [2, 1, 2, 4, 3, 1, 2, 2, 1, 3, 2]
def baseStart_5017752 : Nat := 118140960795 + 5017752 * 2 ^ 59
def prefixEnd_5017752 : Nat := 4983230072969 + 3 ^ 40 * 5017752 * 2
def baseEnd_5017752 : Nat := 2576518581059157255923785

theorem tailTrace_5017752 : CollatzResearch.WordTrace tailWord_5017752 prefixEnd_5017752 2576518581059157255923785 := by
  unfold tailWord_5017752
  simp only [CollatzResearch.WordTrace]
  refine ⟨91506225258774471330167755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122008300345032628440223673 91506225258774471330167755)
  ·
    refine ⟨137259337888161706995251633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91506225258774471330167755 137259337888161706995251633)
    ·
      refine ⟨102944503416121280246438725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137259337888161706995251633 102944503416121280246438725)
      ·
        refine ⟨19302094390522740046207261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102944503416121280246438725 19302094390522740046207261)
        ·
          refine ⟨7238285396446027517327723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19302094390522740046207261 7238285396446027517327723)
          ·
            refine ⟨10857428094669041275991585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7238285396446027517327723 10857428094669041275991585)
            ·
              refine ⟨8143071071001780956993689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10857428094669041275991585 8143071071001780956993689)
              ·
                refine ⟨6107303303251335717745267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8143071071001780956993689 6107303303251335717745267)
                ·
                  refine ⟨9160954954877003576617901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6107303303251335717745267 9160954954877003576617901)
                  ·
                    refine ⟨3435358108078876341231713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9160954954877003576617901 3435358108078876341231713)
                    ·
                      refine ⟨2576518581059157255923785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3435358108078876341231713 2576518581059157255923785)
                      ·
                        rfl

theorem cell23_5017752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_5017752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017752 prefixEnd_5017752 := by exact prefixLift 5017752
  have htrace : WordTrace (prefixWord ++ tailWord_5017752) baseStart_5017752 baseEnd_5017752 := by
    simpa [prefixWord, tailWord_5017752, baseEnd_5017752] using wordTrace_append hprefix tailTrace_5017752
  have hstable : (prefixWord ++ tailWord_5017752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017752).length < 2 ^ (prefixWord ++ tailWord_5017752).sum := by decide
  have hdescent : baseEnd_5017752 < baseStart_5017752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017928 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_5017928 : Nat := 118140960795 + 5017928 * 2 ^ 59
def prefixEnd_5017928 : Nat := 4983230072969 + 3 ^ 40 * 5017928 * 2
def baseEnd_5017928 : Nat := 2576608953654348567322975

theorem tailTrace_5017928 : CollatzResearch.WordTrace tailWord_5017928 prefixEnd_5017928 2576608953654348567322975 := by
  unfold tailWord_5017928
  simp only [CollatzResearch.WordTrace]
  refine ⟨91509434882455662359371219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122012579843274216479161625 91509434882455662359371219)
  ·
    refine ⟨137264152323683493539056829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91509434882455662359371219 137264152323683493539056829)
    ·
      refine ⟨51474057121381310077146311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137264152323683493539056829 51474057121381310077146311)
      ·
        refine ⟨77211085682071965115719467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51474057121381310077146311 77211085682071965115719467)
        ·
          refine ⟨115816628523107947673579201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77211085682071965115719467 115816628523107947673579201)
          ·
            refine ⟨86862471392330960755184401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115816628523107947673579201 86862471392330960755184401)
            ·
              refine ⟨65146853544248220566388301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86862471392330960755184401 65146853544248220566388301)
              ·
                refine ⟨24430070079093082712395613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65146853544248220566388301 24430070079093082712395613)
                ·
                  refine ⟨9161276279659906017148355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24430070079093082712395613 9161276279659906017148355)
                  ·
                    refine ⟨13741914419489859025722533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9161276279659906017148355 13741914419489859025722533)
                    ·
                      refine ⟨2576608953654348567322975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13741914419489859025722533 2576608953654348567322975)
                      ·
                        rfl

theorem cell23_5017928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_5017928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017928 prefixEnd_5017928 := by exact prefixLift 5017928
  have htrace : WordTrace (prefixWord ++ tailWord_5017928) baseStart_5017928 baseEnd_5017928 := by
    simpa [prefixWord, tailWord_5017928, baseEnd_5017928] using wordTrace_append hprefix tailTrace_5017928
  have hstable : (prefixWord ++ tailWord_5017928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017928).length < 2 ^ (prefixWord ++ tailWord_5017928).sum := by decide
  have hdescent : baseEnd_5017928 < baseStart_5017928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017938 : List Nat := [3, 2, 2, 1, 1, 1, 2, 4, 1, 6]
def baseStart_5017938 : Nat := 118140960795 + 5017938 * 2 ^ 59
def prefixEnd_5017938 : Nat := 4983230072969 + 3 ^ 40 * 5017938 * 2
def baseEnd_5017938 : Nat := 858871362820297842732643

theorem tailTrace_5017938 : CollatzResearch.WordTrace tailWord_5017938 prefixEnd_5017938 858871362820297842732643 := by
  unfold tailWord_5017938
  simp only [CollatzResearch.WordTrace]
  refine ⟨45754808623718774106651617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122012822996583397617737645 45754808623718774106651617)
  ·
    refine ⟨34316106467789080579988713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45754808623718774106651617 34316106467789080579988713)
    ·
      refine ⟨25737079850841810434991535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34316106467789080579988713 25737079850841810434991535)
      ·
        refine ⟨38605619776262715652487303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25737079850841810434991535 38605619776262715652487303)
        ·
          refine ⟨57908429664394073478730955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38605619776262715652487303 57908429664394073478730955)
          ·
            refine ⟨86862644496591110218096433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57908429664394073478730955 86862644496591110218096433)
            ·
              refine ⟨65146983372443332663572325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86862644496591110218096433 65146983372443332663572325)
              ·
                refine ⟨12215059382333124874419811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65146983372443332663572325 12215059382333124874419811)
                ·
                  refine ⟨18322589073499687311629717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12215059382333124874419811 18322589073499687311629717)
                  ·
                    refine ⟨858871362820297842732643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18322589073499687311629717 858871362820297842732643)
                    ·
                      rfl

theorem cell23_5017938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_5017938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017938 prefixEnd_5017938 := by exact prefixLift 5017938
  have htrace : WordTrace (prefixWord ++ tailWord_5017938) baseStart_5017938 baseEnd_5017938 := by
    simpa [prefixWord, tailWord_5017938, baseEnd_5017938] using wordTrace_append hprefix tailTrace_5017938
  have hstable : (prefixWord ++ tailWord_5017938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017938).length < 2 ^ (prefixWord ++ tailWord_5017938).sum := by decide
  have hdescent : baseEnd_5017938 < baseStart_5017938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017950 : List Nat := [4, 4, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_5017950 : Nat := 118140960795 + 5017950 * 2 ^ 59
def prefixEnd_5017950 : Nat := 4983230072969 + 3 ^ 40 * 5017950 * 2
def baseEnd_5017950 : Nat := 858873416742915827082625

theorem tailTrace_5017950 : CollatzResearch.WordTrace tailWord_5017950 prefixEnd_5017950 858873416742915827082625 := by
  unfold tailWord_5017950
  simp only [CollatzResearch.WordTrace]
  refine ⟨22877459021353952809505413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122013114780554414984028869 22877459021353952809505413)
  ·
    refine ⟨4289523566503866151782265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22877459021353952809505413 4289523566503866151782265)
    ·
      refine ⟨3217142674877899613836699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4289523566503866151782265 3217142674877899613836699)
      ·
        refine ⟨4825714012316849420755049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3217142674877899613836699 4825714012316849420755049)
        ·
          refine ⟨3619285509237637065566287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4825714012316849420755049 3619285509237637065566287)
          ·
            refine ⟨5428928263856455598349431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3619285509237637065566287 5428928263856455598349431)
            ·
              refine ⟨8143392395784683397524147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5428928263856455598349431 8143392395784683397524147)
              ·
                refine ⟨12215088593677025096286221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8143392395784683397524147 12215088593677025096286221)
                ·
                  refine ⟨4580658222628884411107333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12215088593677025096286221 4580658222628884411107333)
                  ·
                    refine ⟨858873416742915827082625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4580658222628884411107333 858873416742915827082625)
                    ·
                      rfl

theorem cell23_5017950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_5017950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017950 prefixEnd_5017950 := by exact prefixLift 5017950
  have htrace : WordTrace (prefixWord ++ tailWord_5017950) baseStart_5017950 baseEnd_5017950 := by
    simpa [prefixWord, tailWord_5017950, baseEnd_5017950] using wordTrace_append hprefix tailTrace_5017950
  have hstable : (prefixWord ++ tailWord_5017950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017950).length < 2 ^ (prefixWord ++ tailWord_5017950).sum := by decide
  have hdescent : baseEnd_5017950 < baseStart_5017950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017951 : List Nat := [1, 1, 2, 3, 1, 2, 13]
def baseStart_5017951 : Nat := 118140960795 + 5017951 * 2 ^ 59
def prefixEnd_5017951 : Nat := 4983230072969 + 3 ^ 40 * 5017951 * 2
def baseEnd_5017951 : Nat := 31810132885301258979449

theorem tailTrace_5017951 : CollatzResearch.WordTrace tailWord_5017951 prefixEnd_5017951 31810132885301258979449 := by
  unfold tailWord_5017951
  simp only [CollatzResearch.WordTrace]
  refine ⟨183019708643827999646829707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122013139095885333097886471 183019708643827999646829707)
  ·
    refine ⟨274529562965741999470244561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183019708643827999646829707 274529562965741999470244561)
    ·
      refine ⟨205897172224306499602683421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274529562965741999470244561 205897172224306499602683421)
      ·
        refine ⟨77211439584114937351006283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205897172224306499602683421 77211439584114937351006283)
        ·
          refine ⟨115817159376172406026509425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77211439584114937351006283 115817159376172406026509425)
          ·
            refine ⟨86862869532129304519882069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115817159376172406026509425 86862869532129304519882069)
            ·
              refine ⟨31810132885301258979449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 86862869532129304519882069 31810132885301258979449)
              ·
                rfl

theorem cell23_5017951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 13].length) (baseStart_5017951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017951 prefixEnd_5017951 := by exact prefixLift 5017951
  have htrace : WordTrace (prefixWord ++ tailWord_5017951) baseStart_5017951 baseEnd_5017951 := by
    simpa [prefixWord, tailWord_5017951, baseEnd_5017951] using wordTrace_append hprefix tailTrace_5017951
  have hstable : (prefixWord ++ tailWord_5017951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017951).length < 2 ^ (prefixWord ++ tailWord_5017951).sum := by decide
  have hdescent : baseEnd_5017951 < baseStart_5017951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017955 : List Nat := [1, 1, 1, 5, 2, 1, 2, 4, 2, 4]
def baseStart_5017955 : Nat := 118140960795 + 5017955 * 2 ^ 59
def prefixEnd_5017955 : Nat := 4983230072969 + 3 ^ 40 * 5017955 * 2
def baseEnd_5017955 : Nat := 858874272544006653895117

theorem tailTrace_5017955 : CollatzResearch.WordTrace tailWord_5017955 prefixEnd_5017955 858874272544006653895117 := by
  unfold tailWord_5017955
  simp only [CollatzResearch.WordTrace]
  refine ⟨183019854535813508329975319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122013236357209005553316879 183019854535813508329975319)
  ·
    refine ⟨274529781803720262494962979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183019854535813508329975319 274529781803720262494962979)
    ·
      refine ⟨411794672705580393742444469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274529781803720262494962979 411794672705580393742444469)
      ·
        refine ⟨38605750566148161913354169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 411794672705580393742444469 38605750566148161913354169)
        ·
          refine ⟨28954312924611121435015627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38605750566148161913354169 28954312924611121435015627)
          ·
            refine ⟨43431469386916682152523441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28954312924611121435015627 43431469386916682152523441)
            ·
              refine ⟨32573602040187511614392581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43431469386916682152523441 32573602040187511614392581)
              ·
                refine ⟨6107550382535158427698609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32573602040187511614392581 6107550382535158427698609)
                ·
                  refine ⟨4580662786901368820773957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6107550382535158427698609 4580662786901368820773957)
                  ·
                    refine ⟨858874272544006653895117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4580662786901368820773957 858874272544006653895117)
                    ·
                      rfl

theorem cell23_5017955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 4].length) (baseStart_5017955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017955 prefixEnd_5017955 := by exact prefixLift 5017955
  have htrace : WordTrace (prefixWord ++ tailWord_5017955) baseStart_5017955 baseEnd_5017955 := by
    simpa [prefixWord, tailWord_5017955, baseEnd_5017955] using wordTrace_append hprefix tailTrace_5017955
  have hstable : (prefixWord ++ tailWord_5017955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017955).length < 2 ^ (prefixWord ++ tailWord_5017955).sum := by decide
  have hdescent : baseEnd_5017955 < baseStart_5017955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017965 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_5017965 : Nat := 118140960795 + 5017965 * 2 ^ 59
def prefixEnd_5017965 : Nat := 4983230072969 + 3 ^ 40 * 5017965 * 2
def baseEnd_5017965 : Nat := 2576627952438564922560305

theorem tailTrace_5017965 : CollatzResearch.WordTrace tailWord_5017965 prefixEnd_5017965 2576627952438564922560305 := by
  unfold tailWord_5017965
  simp only [CollatzResearch.WordTrace]
  refine ⟨183020219265777280037839349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122013479510518186691892899 183020219265777280037839349)
  ·
    refine ⟨17158145556166620003547439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183020219265777280037839349 17158145556166620003547439)
    ·
      refine ⟨25737218334249930005321159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17158145556166620003547439 25737218334249930005321159)
      ·
        refine ⟨38605827501374895007981739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25737218334249930005321159 38605827501374895007981739)
        ·
          refine ⟨57908741252062342511972609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38605827501374895007981739 57908741252062342511972609)
          ·
            refine ⟨43431555939046756883979457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57908741252062342511972609 43431555939046756883979457)
            ·
              refine ⟨32573666954285067662984593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43431555939046756883979457 32573666954285067662984593)
              ·
                refine ⟨24430250215713800747238445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32573666954285067662984593 24430250215713800747238445)
                ·
                  refine ⟨9161343830892675280214417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24430250215713800747238445 9161343830892675280214417)
                  ·
                    refine ⟨6871007873169506460160813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9161343830892675280214417 6871007873169506460160813)
                    ·
                      refine ⟨2576627952438564922560305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6871007873169506460160813 2576627952438564922560305)
                      ·
                        rfl

theorem cell23_5017965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_5017965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017965 prefixEnd_5017965 := by exact prefixLift 5017965
  have htrace : WordTrace (prefixWord ++ tailWord_5017965) baseStart_5017965 baseEnd_5017965 := by
    simpa [prefixWord, tailWord_5017965, baseEnd_5017965] using wordTrace_append hprefix tailTrace_5017965
  have hstable : (prefixWord ++ tailWord_5017965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017965).length < 2 ^ (prefixWord ++ tailWord_5017965).sum := by decide
  have hdescent : baseEnd_5017965 < baseStart_5017965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017968 : List Nat := [2, 1, 1, 1, 4, 4, 2, 8]
def baseStart_5017968 : Nat := 118140960795 + 5017968 * 2 ^ 59
def prefixEnd_5017968 : Nat := 4983230072969 + 3 ^ 40 * 5017968 * 2
def baseEnd_5017968 : Nat := 95430721958538089289733

theorem tailTrace_5017968 : CollatzResearch.WordTrace tailWord_5017968 prefixEnd_5017968 95430721958538089289733 := by
  unfold tailWord_5017968
  simp only [CollatzResearch.WordTrace]
  refine ⟨91510164342383205775099279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122013552456510941033465705 91510164342383205775099279)
  ·
    refine ⟨137265246513574808662648919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91510164342383205775099279 137265246513574808662648919)
    ·
      refine ⟨205897869770362212993973379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137265246513574808662648919 205897869770362212993973379)
      ·
        refine ⟨308846804655543319490960069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205897869770362212993973379 308846804655543319490960069)
        ·
          refine ⟨57908775872914372404555013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 308846804655543319490960069 57908775872914372404555013)
          ·
            refine ⟨10857895476171444825854065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57908775872914372404555013 10857895476171444825854065)
            ·
              refine ⟨8143421607128583619390549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10857895476171444825854065 8143421607128583619390549)
              ·
                refine ⟨95430721958538089289733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8143421607128583619390549 95430721958538089289733)
                ·
                  rfl

theorem cell23_5017968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 8].length) (baseStart_5017968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017968 prefixEnd_5017968 := by exact prefixLift 5017968
  have htrace : WordTrace (prefixWord ++ tailWord_5017968) baseStart_5017968 baseEnd_5017968 := by
    simpa [prefixWord, tailWord_5017968, baseEnd_5017968] using wordTrace_append hprefix tailTrace_5017968
  have hstable : (prefixWord ++ tailWord_5017968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017968).length < 2 ^ (prefixWord ++ tailWord_5017968).sum := by decide
  have hdescent : baseEnd_5017968 < baseStart_5017968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5017995 : List Nat := [1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 3]
def baseStart_5017995 : Nat := 118140960795 + 5017995 * 2 ^ 59
def prefixEnd_5017995 : Nat := 4983230072969 + 3 ^ 40 * 5017995 * 2
def baseEnd_5017995 : Nat := 2576643356858199805185167

theorem tailTrace_5017995 : CollatzResearch.WordTrace tailWord_5017995 prefixEnd_5017995 2576643356858199805185167 := by
  unfold tailWord_5017995
  simp only [CollatzResearch.WordTrace]
  refine ⟨183021313455668595161431439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122014208970445730107620959 183021313455668595161431439)
  ·
    refine ⟨274531970183502892742147159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183021313455668595161431439 274531970183502892742147159)
    ·
      refine ⟨411797955275254339113220739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274531970183502892742147159 411797955275254339113220739)
      ·
        refine ⟨617696932912881508669831109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411797955275254339113220739 617696932912881508669831109)
        ·
          refine ⟨115818174921165282875593333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 617696932912881508669831109 115818174921165282875593333)
          ·
            refine ⟨10857953898859245269586875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115818174921165282875593333 10857953898859245269586875)
            ·
              refine ⟨16286930848288867904380313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10857953898859245269586875 16286930848288867904380313)
              ·
                refine ⟨12215198136216650928285235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16286930848288867904380313 12215198136216650928285235)
                ·
                  refine ⟨18322797204324976392427853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12215198136216650928285235 18322797204324976392427853)
                  ·
                    refine ⟨6871048951621866147160445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18322797204324976392427853 6871048951621866147160445)
                    ·
                      refine ⟨2576643356858199805185167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6871048951621866147160445 2576643356858199805185167)
                      ·
                        rfl

theorem cell23_5017995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 3].length) (baseStart_5017995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5017995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5017995 prefixEnd_5017995 := by exact prefixLift 5017995
  have htrace : WordTrace (prefixWord ++ tailWord_5017995) baseStart_5017995 baseEnd_5017995 := by
    simpa [prefixWord, tailWord_5017995, baseEnd_5017995] using wordTrace_append hprefix tailTrace_5017995
  have hstable : (prefixWord ++ tailWord_5017995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5017995).length < 2 ^ (prefixWord ++ tailWord_5017995).sum := by decide
  have hdescent : baseEnd_5017995 < baseStart_5017995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5017995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018026 : List Nat := [3, 1, 6, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_5018026 : Nat := 118140960795 + 5018026 * 2 ^ 59
def prefixEnd_5018026 : Nat := 4983230072969 + 3 ^ 40 * 5018026 * 2
def baseEnd_5018026 : Nat := 2576659274758489183897525

theorem tailTrace_5018026 : CollatzResearch.WordTrace tailWord_5018026 prefixEnd_5018026 2576659274758489183897525 := by
  unfold tailWord_5018026
  simp only [CollatzResearch.WordTrace]
  refine ⟨45755611029639071863952483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122014962745704191637206621 45755611029639071863952483)
  ·
    refine ⟨68633416544458607795928725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45755611029639071863952483 68633416544458607795928725)
    ·
      refine ⟨3217191400521497240434159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68633416544458607795928725 3217191400521497240434159)
      ·
        refine ⟨4825787100782245860651239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3217191400521497240434159 4825787100782245860651239)
        ·
          refine ⟨7238680651173368790976859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4825787100782245860651239 7238680651173368790976859)
          ·
            refine ⟨10858020976760053186465289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7238680651173368790976859 10858020976760053186465289)
            ·
              refine ⟨8143515732570039889848967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10858020976760053186465289 8143515732570039889848967)
              ·
                refine ⟨12215273598855059834773451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8143515732570039889848967 12215273598855059834773451)
                ·
                  refine ⟨18322910398282589752160177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12215273598855059834773451 18322910398282589752160177)
                  ·
                    refine ⟨13742182798711942314120133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18322910398282589752160177 13742182798711942314120133)
                    ·
                      refine ⟨2576659274758489183897525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13742182798711942314120133 2576659274758489183897525)
                      ·
                        rfl

theorem cell23_5018026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_5018026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018026 prefixEnd_5018026 := by exact prefixLift 5018026
  have htrace : WordTrace (prefixWord ++ tailWord_5018026) baseStart_5018026 baseEnd_5018026 := by
    simpa [prefixWord, tailWord_5018026, baseEnd_5018026] using wordTrace_append hprefix tailTrace_5018026
  have hstable : (prefixWord ++ tailWord_5018026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018026).length < 2 ^ (prefixWord ++ tailWord_5018026).sum := by decide
  have hdescent : baseEnd_5018026 < baseStart_5018026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018029 : List Nat := [1, 5, 2, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_5018029 : Nat := 118140960795 + 5018029 * 2 ^ 59
def prefixEnd_5018029 : Nat := 4983230072969 + 3 ^ 40 * 5018029 * 2
def baseEnd_5018029 : Nat := 2576660815200452672160011

theorem tailTrace_5018029 : CollatzResearch.WordTrace tailWord_5018029 prefixEnd_5018029 2576660815200452672160011 := by
  unfold tailWord_5018029
  simp only [CollatzResearch.WordTrace]
  refine ⟨183022553537545418968169141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122015035691696945978779427 183022553537545418968169141)
  ·
    refine ⟨17158364394144883028265857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183022553537545418968169141 17158364394144883028265857)
    ·
      refine ⟨12868773295608662271199393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17158364394144883028265857 12868773295608662271199393)
      ·
        refine ⟨9651579971706496703399545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12868773295608662271199393 9651579971706496703399545)
        ·
          refine ⟨7238684978779872527549659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9651579971706496703399545 7238684978779872527549659)
          ·
            refine ⟨10858027468169808791324489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7238684978779872527549659 10858027468169808791324489)
            ·
              refine ⟨8143520601127356593493367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10858027468169808791324489 8143520601127356593493367)
              ·
                refine ⟨12215280901691034890240051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8143520601127356593493367 12215280901691034890240051)
                ·
                  refine ⟨18322921352536552335360077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12215280901691034890240051 18322921352536552335360077)
                  ·
                    refine ⟨6871095507201207125760029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18322921352536552335360077 6871095507201207125760029)
                    ·
                      refine ⟨2576660815200452672160011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6871095507201207125760029 2576660815200452672160011)
                      ·
                        rfl

theorem cell23_5018029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_5018029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018029 prefixEnd_5018029 := by exact prefixLift 5018029
  have htrace : WordTrace (prefixWord ++ tailWord_5018029) baseStart_5018029 baseEnd_5018029 := by
    simpa [prefixWord, tailWord_5018029, baseEnd_5018029] using wordTrace_append hprefix tailTrace_5018029
  have hstable : (prefixWord ++ tailWord_5018029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018029).length < 2 ^ (prefixWord ++ tailWord_5018029).sum := by decide
  have hdescent : baseEnd_5018029 < baseStart_5018029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018048 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 4]
def baseStart_5018048 : Nat := 118140960795 + 5018048 * 2 ^ 59
def prefixEnd_5018048 : Nat := 4983230072969 + 3 ^ 40 * 5018048 * 2
def baseEnd_5018048 : Nat := 2576670571332888097822423

theorem tailTrace_5018048 : CollatzResearch.WordTrace tailWord_5018048 prefixEnd_5018048 2576670571332888097822423 := by
  unfold tailWord_5018048
  simp only [CollatzResearch.WordTrace]
  refine ⟨91511623262238292606555399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122015497682984390142073865 91511623262238292606555399)
  ·
    refine ⟨137267434893357438909833099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91511623262238292606555399 137267434893357438909833099)
    ·
      refine ⟨205901152340036158364749649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137267434893357438909833099 205901152340036158364749649)
      ·
        refine ⟨154425864255027118773562237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205901152340036158364749649 154425864255027118773562237)
        ·
          refine ⟨57909699095635169540085839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154425864255027118773562237 57909699095635169540085839)
          ·
            refine ⟨86864548643452754310128759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57909699095635169540085839 86864548643452754310128759)
            ·
              refine ⟨130296822965179131465193139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86864548643452754310128759 130296822965179131465193139)
              ·
                refine ⟨195445234447768697197789709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130296822965179131465193139 195445234447768697197789709)
                ·
                  refine ⟨73291962917913261449171141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195445234447768697197789709 73291962917913261449171141)
                  ·
                    refine ⟨13742243047108736521719589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73291962917913261449171141 13742243047108736521719589)
                    ·
                      refine ⟨2576670571332888097822423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13742243047108736521719589 2576670571332888097822423)
                      ·
                        rfl

theorem cell23_5018048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_5018048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018048 prefixEnd_5018048 := by exact prefixLift 5018048
  have htrace : WordTrace (prefixWord ++ tailWord_5018048) baseStart_5018048 baseEnd_5018048 := by
    simpa [prefixWord, tailWord_5018048, baseEnd_5018048] using wordTrace_append hprefix tailTrace_5018048
  have hstable : (prefixWord ++ tailWord_5018048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018048).length < 2 ^ (prefixWord ++ tailWord_5018048).sum := by decide
  have hdescent : baseEnd_5018048 < baseStart_5018048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018056 : List Nat := [2, 1, 3, 1, 3, 4, 2, 1, 1, 3, 2]
def baseStart_5018056 : Nat := 118140960795 + 5018056 * 2 ^ 59
def prefixEnd_5018056 : Nat := 4983230072969 + 3 ^ 40 * 5018056 * 2
def baseEnd_5018056 : Nat := 2576674679178124066522387

theorem tailTrace_5018056 : CollatzResearch.WordTrace tailWord_5018056 prefixEnd_5018056 2576674679178124066522387 := by
  unfold tailWord_5018056
  simp only [CollatzResearch.WordTrace]
  refine ⟨91511769154223801289701011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122015692205631735052934681 91511769154223801289701011)
  ·
    refine ⟨137267653731335701934551517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91511769154223801289701011 137267653731335701934551517)
    ·
      refine ⟨51475370149250888225456819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137267653731335701934551517 51475370149250888225456819)
      ·
        refine ⟨77213055223876332338185229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51475370149250888225456819 77213055223876332338185229)
        ·
          refine ⟨28954895708953624626819461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77213055223876332338185229 28954895708953624626819461)
          ·
            refine ⟨5429042945428804617528649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28954895708953624626819461 5429042945428804617528649)
            ·
              refine ⟨4071782209071603463146487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5429042945428804617528649 4071782209071603463146487)
              ·
                refine ⟨6107673313607405194719731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4071782209071603463146487 6107673313607405194719731)
                ·
                  refine ⟨9161509970411107792079597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6107673313607405194719731 9161509970411107792079597)
                  ·
                    refine ⟨3435566238904165422029849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9161509970411107792079597 3435566238904165422029849)
                    ·
                      refine ⟨2576674679178124066522387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3435566238904165422029849 2576674679178124066522387)
                      ·
                        rfl

theorem cell23_5018056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_5018056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018056 prefixEnd_5018056 := by exact prefixLift 5018056
  have htrace : WordTrace (prefixWord ++ tailWord_5018056) baseStart_5018056 baseEnd_5018056 := by
    simpa [prefixWord, tailWord_5018056, baseEnd_5018056] using wordTrace_append hprefix tailTrace_5018056
  have hstable : (prefixWord ++ tailWord_5018056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018056).length < 2 ^ (prefixWord ++ tailWord_5018056).sum := by decide
  have hdescent : baseEnd_5018056 < baseStart_5018056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018058 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 9]
def baseStart_5018058 : Nat := 118140960795 + 5018058 * 2 ^ 59
def prefixEnd_5018058 : Nat := 4983230072969 + 3 ^ 40 * 5018058 * 2
def baseEnd_5018058 : Nat := 286297300682159228744153

theorem tailTrace_5018058 : CollatzResearch.WordTrace tailWord_5018058 prefixEnd_5018058 286297300682159228744153 := by
  unfold tailWord_5018058
  simp only [CollatzResearch.WordTrace]
  refine ⟨45755902813610089230243707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122015740836293571280649885 45755902813610089230243707)
  ·
    refine ⟨68633854220415133845365561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45755902813610089230243707 68633854220415133845365561)
    ·
      refine ⟨51475390665311350384024171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68633854220415133845365561 51475390665311350384024171)
      ·
        refine ⟨77213085997967025576036257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51475390665311350384024171 77213085997967025576036257)
        ·
          refine ⟨57909814498475269182027193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77213085997967025576036257 57909814498475269182027193)
          ·
            refine ⟨43432360873856451886520395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57909814498475269182027193 43432360873856451886520395)
            ·
              refine ⟨65148541310784677829780593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43432360873856451886520395 65148541310784677829780593)
              ·
                refine ⟨48861405983088508372335445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65148541310784677829780593 48861405983088508372335445)
                ·
                  refine ⟨286297300682159228744153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48861405983088508372335445 286297300682159228744153)
                  ·
                    rfl

theorem cell23_5018058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 9].length) (baseStart_5018058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018058 prefixEnd_5018058 := by exact prefixLift 5018058
  have htrace : WordTrace (prefixWord ++ tailWord_5018058) baseStart_5018058 baseEnd_5018058 := by
    simpa [prefixWord, tailWord_5018058, baseEnd_5018058] using wordTrace_append hprefix tailTrace_5018058
  have hstable : (prefixWord ++ tailWord_5018058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018058).length < 2 ^ (prefixWord ++ tailWord_5018058).sum := by decide
  have hdescent : baseEnd_5018058 < baseStart_5018058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018069 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 4, 2, 2]
def baseStart_5018069 : Nat := 118140960795 + 5018069 * 2 ^ 59
def prefixEnd_5018069 : Nat := 4983230072969 + 3 ^ 40 * 5018069 * 2
def baseEnd_5018069 : Nat := 2576681354426632515659827

theorem tailTrace_5018069 : CollatzResearch.WordTrace tailWord_5018069 prefixEnd_5018069 2576681354426632515659827 := by
  unfold tailWord_5018069
  simp only [CollatzResearch.WordTrace]
  refine ⟨183024012457400505799625261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122016008304933670533083507 183024012457400505799625261)
  ·
    refine ⟨68634004671525189674859473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183024012457400505799625261 68634004671525189674859473)
    ·
      refine ⟨51475503503643892256144605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68634004671525189674859473 51475503503643892256144605)
      ·
        refine ⟨19303313813866459596054227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51475503503643892256144605 19303313813866459596054227)
        ·
          refine ⟨28954970720799689394081341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19303313813866459596054227 28954970720799689394081341)
          ·
            refine ⟨10858114020299883522780503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28954970720799689394081341 10858114020299883522780503)
            ·
              refine ⟨16287171030449825284170755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10858114020299883522780503 16287171030449825284170755)
              ·
                refine ⟨24430756545674737926256133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16287171030449825284170755 24430756545674737926256133)
                ·
                  refine ⟨4580766852314013361173025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24430756545674737926256133 4580766852314013361173025)
                  ·
                    refine ⟨3435575139235510020879769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4580766852314013361173025 3435575139235510020879769)
                    ·
                      refine ⟨2576681354426632515659827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3435575139235510020879769 2576681354426632515659827)
                      ·
                        rfl

theorem cell23_5018069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_5018069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018069 prefixEnd_5018069 := by exact prefixLift 5018069
  have htrace : WordTrace (prefixWord ++ tailWord_5018069) baseStart_5018069 baseEnd_5018069 := by
    simpa [prefixWord, tailWord_5018069, baseEnd_5018069] using wordTrace_append hprefix tailTrace_5018069
  have hstable : (prefixWord ++ tailWord_5018069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018069).length < 2 ^ (prefixWord ++ tailWord_5018069).sum := by decide
  have hdescent : baseEnd_5018069 < baseStart_5018069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018132 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_5018132 : Nat := 118140960795 + 5018132 * 2 ^ 59
def prefixEnd_5018132 : Nat := 4983230072969 + 3 ^ 40 * 5018132 * 2
def baseEnd_5018132 : Nat := 2576713703707865769172037

theorem tailTrace_5018132 : CollatzResearch.WordTrace tailWord_5018132 prefixEnd_5018132 2576713703707865769172037 := by
  unfold tailWord_5018132
  simp only [CollatzResearch.WordTrace]
  refine ⟨91513155128086133779584325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122017540170781511706112433 91513155128086133779584325)
  ·
    refine ⟨17158716586516150083672061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91513155128086133779584325 17158716586516150083672061)
    ·
      refine ⟨6434518719943556281377023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17158716586516150083672061 6434518719943556281377023)
      ·
        refine ⟨9651778079915334422065535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6434518719943556281377023 9651778079915334422065535)
        ·
          refine ⟨14477667119873001633098303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9651778079915334422065535 14477667119873001633098303)
          ·
            refine ⟨21716500679809502449647455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14477667119873001633098303 21716500679809502449647455)
            ·
              refine ⟨32574751019714253674471183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21716500679809502449647455 32574751019714253674471183)
              ·
                refine ⟨48862126529571380511706775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32574751019714253674471183 48862126529571380511706775)
                ·
                  refine ⟨73293189794357070767560163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48862126529571380511706775 73293189794357070767560163)
                  ·
                    refine ⟨109939784691535606151340245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73293189794357070767560163 109939784691535606151340245)
                    ·
                      refine ⟨2576713703707865769172037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109939784691535606151340245 2576713703707865769172037)
                      ·
                        rfl

theorem cell23_5018132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_5018132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018132 prefixEnd_5018132 := by exact prefixLift 5018132
  have htrace : WordTrace (prefixWord ++ tailWord_5018132) baseStart_5018132 baseEnd_5018132 := by
    simpa [prefixWord, tailWord_5018132, baseEnd_5018132] using wordTrace_append hprefix tailTrace_5018132
  have hstable : (prefixWord ++ tailWord_5018132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018132).length < 2 ^ (prefixWord ++ tailWord_5018132).sum := by decide
  have hdescent : baseEnd_5018132 < baseStart_5018132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018162 : List Nat := [3, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3]
def baseStart_5018162 : Nat := 118140960795 + 5018162 * 2 ^ 59
def prefixEnd_5018162 : Nat := 4983230072969 + 3 ^ 40 * 5018162 * 2
def baseEnd_5018162 : Nat := 2576729108127500651796899

theorem tailTrace_5018162 : CollatzResearch.WordTrace tailWord_5018162 prefixEnd_5018162 2576729108127500651796899 := by
  unfold tailWord_5018162
  simp only [CollatzResearch.WordTrace]
  refine ⟨45756851111515895670690185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122018269630709055121840493 45756851111515895670690185)
  ·
    refine ⟨34317638333636921753017639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45756851111515895670690185 34317638333636921753017639)
    ·
      refine ⟨51476457500455382629526459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34317638333636921753017639 51476457500455382629526459)
      ·
        refine ⟨77214686250683073944289689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51476457500455382629526459 77214686250683073944289689)
        ·
          refine ⟨57911014688012305458217267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77214686250683073944289689 57911014688012305458217267)
          ·
            refine ⟨86866522032018458187325901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57911014688012305458217267 86866522032018458187325901)
            ·
              refine ⟨32574945762006921820247213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86866522032018458187325901 32574945762006921820247213)
              ·
                refine ⟨12215604660752595682592705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32574945762006921820247213 12215604660752595682592705)
                ·
                  refine ⟨9161703495564446761944529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12215604660752595682592705 9161703495564446761944529)
                  ·
                    refine ⟨6871277621673335071458397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9161703495564446761944529 6871277621673335071458397)
                    ·
                      refine ⟨2576729108127500651796899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6871277621673335071458397 2576729108127500651796899)
                      ·
                        rfl

theorem cell23_5018162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_5018162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018162 prefixEnd_5018162 := by exact prefixLift 5018162
  have htrace : WordTrace (prefixWord ++ tailWord_5018162) baseStart_5018162 baseEnd_5018162 := by
    simpa [prefixWord, tailWord_5018162, baseEnd_5018162] using wordTrace_append hprefix tailTrace_5018162
  have hstable : (prefixWord ++ tailWord_5018162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018162).length < 2 ^ (prefixWord ++ tailWord_5018162).sum := by decide
  have hdescent : baseEnd_5018162 < baseStart_5018162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018169 : List Nat := [1, 2, 1, 5, 1, 1, 2, 5, 1, 4]
def baseStart_5018169 : Nat := 118140960795 + 5018169 * 2 ^ 59
def prefixEnd_5018169 : Nat := 4983230072969 + 3 ^ 40 * 5018169 * 2
def baseEnd_5018169 : Nat := 858910900830694041469789

theorem tailTrace_5018169 : CollatzResearch.WordTrace tailWord_5018169 prefixEnd_5018169 858910900830694041469789 := by
  unfold tailWord_5018169
  simp only [CollatzResearch.WordTrace]
  refine ⟨183027659757038222878265561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122018439838025481918843707 183027659757038222878265561)
  ·
    refine ⟨137270744817778667158699171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183027659757038222878265561 137270744817778667158699171)
    ·
      refine ⟨205906117226668000738048757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137270744817778667158699171 205906117226668000738048757)
      ·
        refine ⟨19303698490000125069192071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 205906117226668000738048757 19303698490000125069192071)
        ·
          refine ⟨28955547735000187603788107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19303698490000125069192071 28955547735000187603788107)
          ·
            refine ⟨43433321602500281405682161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28955547735000187603788107 43433321602500281405682161)
            ·
              refine ⟨32574991201875211054261621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43433321602500281405682161 32574991201875211054261621)
              ·
                refine ⟨3053905425175801036337027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32574991201875211054261621 3053905425175801036337027)
                ·
                  refine ⟨4580858137763701554505541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3053905425175801036337027 4580858137763701554505541)
                  ·
                    refine ⟨858910900830694041469789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4580858137763701554505541 858910900830694041469789)
                    ·
                      rfl

theorem cell23_5018169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 1, 4].length) (baseStart_5018169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018169 prefixEnd_5018169 := by exact prefixLift 5018169
  have htrace : WordTrace (prefixWord ++ tailWord_5018169) baseStart_5018169 baseEnd_5018169 := by
    simpa [prefixWord, tailWord_5018169, baseEnd_5018169] using wordTrace_append hprefix tailTrace_5018169
  have hstable : (prefixWord ++ tailWord_5018169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018169).length < 2 ^ (prefixWord ++ tailWord_5018169).sum := by decide
  have hdescent : baseEnd_5018169 < baseStart_5018169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018186 : List Nat := [3, 1, 2, 1, 1, 4, 4, 2, 1, 4]
def baseStart_5018186 : Nat := 118140960795 + 5018186 * 2 ^ 59
def prefixEnd_5018186 : Nat := 4983230072969 + 3 ^ 40 * 5018186 * 2
def baseEnd_5018186 : Nat := 858913810554402852632263

theorem tailTrace_5018186 : CollatzResearch.WordTrace tailWord_5018186 prefixEnd_5018186 858913810554402852632263 := by
  unfold tailWord_5018186
  simp only [CollatzResearch.WordTrace]
  refine ⟨45757069949494158695408603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122018853198651089854422941 45757069949494158695408603)
  ·
    refine ⟨68635604924241238043112905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45757069949494158695408603 68635604924241238043112905)
    ·
      refine ⟨51476703693180928532334679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68635604924241238043112905 51476703693180928532334679)
      ·
        refine ⟨77215055539771392798502019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51476703693180928532334679 77215055539771392798502019)
        ·
          refine ⟨115822583309657089197753029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77215055539771392798502019 115822583309657089197753029)
          ·
            refine ⟨21716734370560704224578693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115822583309657089197753029 21716734370560704224578693)
            ·
              refine ⟨4071887694480132042108505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21716734370560704224578693 4071887694480132042108505)
              ·
                refine ⟨3053915770860099031581379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4071887694480132042108505 3053915770860099031581379)
                ·
                  refine ⟨4580873656290148547372069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3053915770860099031581379 4580873656290148547372069)
                  ·
                    refine ⟨858913810554402852632263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4580873656290148547372069 858913810554402852632263)
                    ·
                      rfl

theorem cell23_5018186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_5018186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018186 prefixEnd_5018186 := by exact prefixLift 5018186
  have htrace : WordTrace (prefixWord ++ tailWord_5018186) baseStart_5018186 baseEnd_5018186 := by
    simpa [prefixWord, tailWord_5018186, baseEnd_5018186] using wordTrace_append hprefix tailTrace_5018186
  have hstable : (prefixWord ++ tailWord_5018186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018186).length < 2 ^ (prefixWord ++ tailWord_5018186).sum := by decide
  have hdescent : baseEnd_5018186 < baseStart_5018186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018209 : List Nat := [1, 2, 3, 1, 1, 5, 1, 2, 3, 1, 3]
def baseStart_5018209 : Nat := 118140960795 + 5018209 * 2 ^ 59
def prefixEnd_5018209 : Nat := 4983230072969 + 3 ^ 40 * 5018209 * 2
def baseEnd_5018209 : Nat := 2576753241718261967909183

theorem tailTrace_5018209 : CollatzResearch.WordTrace tailWord_5018209 prefixEnd_5018209 2576753241718261967909183 := by
  unfold tailWord_5018209
  simp only [CollatzResearch.WordTrace]
  refine ⟨183029118676893309709721681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122019412451262206473147787 183029118676893309709721681)
  ·
    refine ⟨137271839007669982282291261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183029118676893309709721681 137271839007669982282291261)
    ·
      refine ⟨51476939627876243355859223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137271839007669982282291261 51476939627876243355859223)
      ·
        refine ⟨77215409441814365033788835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51476939627876243355859223 77215409441814365033788835)
        ·
          refine ⟨115823114162721547550683253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77215409441814365033788835 115823114162721547550683253)
          ·
            refine ⟨10858416952755145082876555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115823114162721547550683253 10858416952755145082876555)
            ·
              refine ⟨16287625429132717624314833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10858416952755145082876555 16287625429132717624314833)
              ·
                refine ⟨12215719071849538218236125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16287625429132717624314833 12215719071849538218236125)
                ·
                  refine ⟨4580894651943576831838547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12215719071849538218236125 4580894651943576831838547)
                  ·
                    refine ⟨6871341977915365247757821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4580894651943576831838547 6871341977915365247757821)
                    ·
                      refine ⟨2576753241718261967909183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6871341977915365247757821 2576753241718261967909183)
                      ·
                        rfl

theorem cell23_5018209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_5018209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018209 prefixEnd_5018209 := by exact prefixLift 5018209
  have htrace : WordTrace (prefixWord ++ tailWord_5018209) baseStart_5018209 baseEnd_5018209 := by
    simpa [prefixWord, tailWord_5018209, baseEnd_5018209] using wordTrace_append hprefix tailTrace_5018209
  have hstable : (prefixWord ++ tailWord_5018209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018209).length < 2 ^ (prefixWord ++ tailWord_5018209).sum := by decide
  have hdescent : baseEnd_5018209 < baseStart_5018209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018212 : List Nat := [2, 3, 1, 1, 2, 2, 2, 4, 1, 5]
def baseStart_5018212 : Nat := 118140960795 + 5018212 * 2 ^ 59
def prefixEnd_5018212 : Nat := 4983230072969 + 3 ^ 40 * 5018212 * 2
def baseEnd_5018212 : Nat := 858918260720075152057223

theorem tailTrace_5018212 : CollatzResearch.WordTrace tailWord_5018212 prefixEnd_5018212 858918260720075152057223 := by
  unfold tailWord_5018212
  simp only [CollatzResearch.WordTrace]
  refine ⟨91514614047941220611040445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122019485397254960814720593 91514614047941220611040445)
  ·
    refine ⟨34317980267977957729140167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91514614047941220611040445 34317980267977957729140167)
    ·
      refine ⟨51476970401966936593710251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34317980267977957729140167 51476970401966936593710251)
      ·
        refine ⟨77215455602950404890565377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51476970401966936593710251 77215455602950404890565377)
        ·
          refine ⟨57911591702212803667924033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77215455602950404890565377 57911591702212803667924033)
          ·
            refine ⟨43433693776659602750943025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57911591702212803667924033 43433693776659602750943025)
            ·
              refine ⟨32575270332494702063207269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43433693776659602750943025 32575270332494702063207269)
              ·
                refine ⟨6107863187342756636851363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32575270332494702063207269 6107863187342756636851363)
                ·
                  refine ⟨9161794781014134955277045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6107863187342756636851363 9161794781014134955277045)
                  ·
                    refine ⟨858918260720075152057223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9161794781014134955277045 858918260720075152057223)
                    ·
                      rfl

theorem cell23_5018212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_5018212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018212 prefixEnd_5018212 := by exact prefixLift 5018212
  have htrace : WordTrace (prefixWord ++ tailWord_5018212) baseStart_5018212 baseEnd_5018212 := by
    simpa [prefixWord, tailWord_5018212, baseEnd_5018212] using wordTrace_append hprefix tailTrace_5018212
  have hstable : (prefixWord ++ tailWord_5018212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018212).length < 2 ^ (prefixWord ++ tailWord_5018212).sum := by decide
  have hdescent : baseEnd_5018212 < baseStart_5018212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018232 : List Nat := [2, 1, 2, 1, 1, 1, 2, 7, 1, 1, 4]
def baseStart_5018232 : Nat := 118140960795 + 5018232 * 2 ^ 59
def prefixEnd_5018232 : Nat := 4983230072969 + 3 ^ 40 * 5018232 * 2
def baseEnd_5018232 : Nat := 2576765051773315377921577

theorem tailTrace_5018232 : CollatzResearch.WordTrace tailWord_5018232 prefixEnd_5018232 2576765051773315377921577 := by
  unfold tailWord_5018232
  simp only [CollatzResearch.WordTrace]
  refine ⟨91514978777904992318904475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122019971703873323091872633 91514978777904992318904475)
  ·
    refine ⟨137272468166857488478356713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91514978777904992318904475 137272468166857488478356713)
    ·
      refine ⟨102954351125143116358767535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137272468166857488478356713 102954351125143116358767535)
      ·
        refine ⟨154431526687714674538151303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102954351125143116358767535 154431526687714674538151303)
        ·
          refine ⟨231647290031572011807226955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154431526687714674538151303 231647290031572011807226955)
          ·
            refine ⟨347470935047358017710840433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231647290031572011807226955 347470935047358017710840433)
            ·
              refine ⟨260603201285518513283130325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347470935047358017710840433 260603201285518513283130325)
              ·
                refine ⟨6107887530129340155073367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 260603201285518513283130325 6107887530129340155073367)
                ·
                  refine ⟨9161831295194010232610051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6107887530129340155073367 9161831295194010232610051)
                  ·
                    refine ⟨13742746942791015348915077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9161831295194010232610051 13742746942791015348915077)
                    ·
                      refine ⟨2576765051773315377921577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13742746942791015348915077 2576765051773315377921577)
                      ·
                        rfl

theorem cell23_5018232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 1, 1, 4].length) (baseStart_5018232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018232 prefixEnd_5018232 := by exact prefixLift 5018232
  have htrace : WordTrace (prefixWord ++ tailWord_5018232) baseStart_5018232 baseEnd_5018232 := by
    simpa [prefixWord, tailWord_5018232, baseEnd_5018232] using wordTrace_append hprefix tailTrace_5018232
  have hstable : (prefixWord ++ tailWord_5018232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018232).length < 2 ^ (prefixWord ++ tailWord_5018232).sum := by decide
  have hdescent : baseEnd_5018232 < baseStart_5018232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018252 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 3, 2, 3]
def baseStart_5018252 : Nat := 118140960795 + 5018252 * 2 ^ 59
def prefixEnd_5018252 : Nat := 4983230072969 + 3 ^ 40 * 5018252 * 2
def baseEnd_5018252 : Nat := 2576775321386405299671485

theorem tailTrace_5018252 : CollatzResearch.WordTrace tailWord_5018252 prefixEnd_5018252 2576775321386405299671485 := by
  unfold tailWord_5018252
  simp only [CollatzResearch.WordTrace]
  refine ⟨91515343507868764026768505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122020458010491685369024673 91515343507868764026768505)
  ·
    refine ⟨68636507630901573020076379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91515343507868764026768505 68636507630901573020076379)
    ·
      refine ⟨102954761446352359530114569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68636507630901573020076379 102954761446352359530114569)
      ·
        refine ⟨77216071084764269647585927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102954761446352359530114569 77216071084764269647585927)
        ·
          refine ⟨115824106627146404471378891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77216071084764269647585927 115824106627146404471378891)
          ·
            refine ⟨173736159940719606707068337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115824106627146404471378891 173736159940719606707068337)
            ·
              refine ⟨130302119955539705030301253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173736159940719606707068337 130302119955539705030301253)
              ·
                refine ⟨24431647491663694693181485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130302119955539705030301253 24431647491663694693181485)
                ·
                  refine ⟨9161867809373885509943057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24431647491663694693181485 9161867809373885509943057)
                  ·
                    refine ⟨6871400857030414132457293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9161867809373885509943057 6871400857030414132457293)
                    ·
                      refine ⟨2576775321386405299671485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6871400857030414132457293 2576775321386405299671485)
                      ·
                        rfl

theorem cell23_5018252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_5018252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018252 prefixEnd_5018252 := by exact prefixLift 5018252
  have htrace : WordTrace (prefixWord ++ tailWord_5018252) baseStart_5018252 baseEnd_5018252 := by
    simpa [prefixWord, tailWord_5018252, baseEnd_5018252] using wordTrace_append hprefix tailTrace_5018252
  have hstable : (prefixWord ++ tailWord_5018252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018252).length < 2 ^ (prefixWord ++ tailWord_5018252).sum := by decide
  have hdescent : baseEnd_5018252 < baseStart_5018252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018269 : List Nat := [1, 4, 2, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_5018269 : Nat := 118140960795 + 5018269 * 2 ^ 59
def prefixEnd_5018269 : Nat := 4983230072969 + 3 ^ 40 * 5018269 * 2
def baseEnd_5018269 : Nat := 2576784050557531733158907

theorem tailTrace_5018269 : CollatzResearch.WordTrace tailWord_5018269 prefixEnd_5018269 2576784050557531733158907 := by
  unfold tailWord_5018269
  simp only [CollatzResearch.WordTrace]
  refine ⟨183031307056675939956905861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122020871371117293304603907 183031307056675939956905861)
  ·
    refine ⟨34318370073126738741919849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183031307056675939956905861 34318370073126738741919849)
    ·
      refine ⟨25738777554845054056439887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34318370073126738741919849 25738777554845054056439887)
      ·
        refine ⟨38608166332267581084659831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25738777554845054056439887 38608166332267581084659831)
        ·
          refine ⟨57912249498401371626989747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38608166332267581084659831 57912249498401371626989747)
          ·
            refine ⟨86868374247602057440484621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57912249498401371626989747 86868374247602057440484621)
            ·
              refine ⟨32575640342850771540181733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86868374247602057440484621 32575640342850771540181733)
              ·
                refine ⟨6107932564284519663784075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32575640342850771540181733 6107932564284519663784075)
                ·
                  refine ⟨9161898846426779495676113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6107932564284519663784075 9161898846426779495676113)
                  ·
                    refine ⟨6871424134820084621757085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9161898846426779495676113 6871424134820084621757085)
                    ·
                      refine ⟨2576784050557531733158907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6871424134820084621757085 2576784050557531733158907)
                      ·
                        rfl

theorem cell23_5018269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_5018269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018269 prefixEnd_5018269 := by exact prefixLift 5018269
  have htrace : WordTrace (prefixWord ++ tailWord_5018269) baseStart_5018269 baseEnd_5018269 := by
    simpa [prefixWord, tailWord_5018269, baseEnd_5018269] using wordTrace_append hprefix tailTrace_5018269
  have hstable : (prefixWord ++ tailWord_5018269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018269).length < 2 ^ (prefixWord ++ tailWord_5018269).sum := by decide
  have hdescent : baseEnd_5018269 < baseStart_5018269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018272 : List Nat := [2, 1, 1, 4, 4, 1, 1, 9]
def baseStart_5018272 : Nat := 118140960795 + 5018272 * 2 ^ 59
def prefixEnd_5018272 : Nat := 4983230072969 + 3 ^ 40 * 5018272 * 2
def baseEnd_5018272 : Nat := 95436503370351674867459

theorem tailTrace_5018272 : CollatzResearch.WordTrace tailWord_5018272 prefixEnd_5018272 95436503370351674867459 := by
  unfold tailWord_5018272
  simp only [CollatzResearch.WordTrace]
  refine ⟨91515708237832535734632535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122020944317110047646176713 91515708237832535734632535)
  ·
    refine ⟨137273562356748803601948803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91515708237832535734632535 137273562356748803601948803)
    ·
      refine ⟨205910343535123205402923205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137273562356748803601948803 205910343535123205402923205)
      ·
        refine ⟨38608189412835601013048101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205910343535123205402923205 38608189412835601013048101)
        ·
          refine ⟨7239035514906675189946519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38608189412835601013048101 7239035514906675189946519)
          ·
            refine ⟨10858553272360012784919779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7239035514906675189946519 10858553272360012784919779)
            ·
              refine ⟨16287829908540019177379669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10858553272360012784919779 16287829908540019177379669)
              ·
                refine ⟨95436503370351674867459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16287829908540019177379669 95436503370351674867459)
                ·
                  rfl

theorem cell23_5018272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 9].length) (baseStart_5018272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018272 prefixEnd_5018272 := by exact prefixLift 5018272
  have htrace : WordTrace (prefixWord ++ tailWord_5018272) baseStart_5018272 baseEnd_5018272 := by
    simpa [prefixWord, tailWord_5018272, baseEnd_5018272] using wordTrace_append hprefix tailTrace_5018272
  have hstable : (prefixWord ++ tailWord_5018272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018272).length < 2 ^ (prefixWord ++ tailWord_5018272).sum := by decide
  have hdescent : baseEnd_5018272 < baseStart_5018272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018286 : List Nat := [4, 1, 4, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_5018286 : Nat := 118140960795 + 5018286 * 2 ^ 59
def prefixEnd_5018286 : Nat := 4983230072969 + 3 ^ 40 * 5018286 * 2
def baseEnd_5018286 : Nat := 2576792779728658166646329

theorem tailTrace_5018286 : CollatzResearch.WordTrace tailWord_5018286 prefixEnd_5018286 2576792779728658166646329 := by
  unfold tailWord_5018286
  simp only [CollatzResearch.WordTrace]
  refine ⟨22878990887201793982534339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122021284731742901240183141 22878990887201793982534339)
  ·
    refine ⟨34318486330802690973801509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22878990887201793982534339 34318486330802690973801509)
    ·
      refine ⟨6434716187025504557587783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34318486330802690973801509 6434716187025504557587783)
      ·
        refine ⟨9652074280538256836381675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6434716187025504557587783 9652074280538256836381675)
        ·
          refine ⟨14478111420807385254572513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9652074280538256836381675 14478111420807385254572513)
          ·
            refine ⟨10858583565605538940929385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14478111420807385254572513 10858583565605538940929385)
            ·
              refine ⟨8143937674204154205697039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10858583565605538940929385 8143937674204154205697039)
              ·
                refine ⟨12215906511306231308545559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8143937674204154205697039 12215906511306231308545559)
                ·
                  refine ⟨18323859766959346962818339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12215906511306231308545559 18323859766959346962818339)
                  ·
                    refine ⟨27485789650439020444227509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18323859766959346962818339 27485789650439020444227509)
                    ·
                      refine ⟨2576792779728658166646329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27485789650439020444227509 2576792779728658166646329)
                      ·
                        rfl

theorem cell23_5018286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_5018286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018286 prefixEnd_5018286 := by exact prefixLift 5018286
  have htrace : WordTrace (prefixWord ++ tailWord_5018286) baseStart_5018286 baseEnd_5018286 := by
    simpa [prefixWord, tailWord_5018286, baseEnd_5018286] using wordTrace_append hprefix tailTrace_5018286
  have hstable : (prefixWord ++ tailWord_5018286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018286).length < 2 ^ (prefixWord ++ tailWord_5018286).sum := by decide
  have hdescent : baseEnd_5018286 < baseStart_5018286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018289 : List Nat := [1, 2, 2, 6, 1, 2, 9]
def baseStart_5018289 : Nat := 118140960795 + 5018289 * 2 ^ 59
def prefixEnd_5018289 : Nat := 4983230072969 + 3 ^ 40 * 5018289 * 2
def baseEnd_5018289 : Nat := 31812275557661995739615

theorem tailTrace_5018289 : CollatzResearch.WordTrace tailWord_5018289 prefixEnd_5018289 31812275557661995739615 := by
  unfold tailWord_5018289
  simp only [CollatzResearch.WordTrace]
  refine ⟨183032036516603483372633921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122021357677735655581755947 183032036516603483372633921)
  ·
    refine ⟨137274027387452612529475441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183032036516603483372633921 137274027387452612529475441)
    ·
      refine ⟨102955520540589459397106581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137274027387452612529475441 102955520540589459397106581)
      ·
        refine ⟨4826040025340130909239371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 102955520540589459397106581 4826040025340130909239371)
        ·
          refine ⟨7239060038010196363859057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4826040025340130909239371 7239060038010196363859057)
          ·
            refine ⟨5429295028507647272894293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7239060038010196363859057 5429295028507647272894293)
            ·
              refine ⟨31812275557661995739615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5429295028507647272894293 31812275557661995739615)
              ·
                rfl

theorem cell23_5018289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 9].length) (baseStart_5018289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018289 prefixEnd_5018289 := by exact prefixLift 5018289
  have htrace : WordTrace (prefixWord ++ tailWord_5018289) baseStart_5018289 baseEnd_5018289 := by
    simpa [prefixWord, tailWord_5018289, baseEnd_5018289] using wordTrace_append hprefix tailTrace_5018289
  have hstable : (prefixWord ++ tailWord_5018289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018289).length < 2 ^ (prefixWord ++ tailWord_5018289).sum := by decide
  have hdescent : baseEnd_5018289 < baseStart_5018289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018300 : List Nat := [2, 2, 2, 3, 1, 1, 5, 2, 1, 2, 2]
def baseStart_5018300 : Nat := 118140960795 + 5018300 * 2 ^ 59
def prefixEnd_5018300 : Nat := 4983230072969 + 3 ^ 40 * 5018300 * 2
def baseEnd_5018300 : Nat := 2576799968457821111871265

theorem tailTrace_5018300 : CollatzResearch.WordTrace tailWord_5018300 prefixEnd_5018300 2576799968457821111871265 := by
  unfold tailWord_5018300
  simp only [CollatzResearch.WordTrace]
  refine ⟨91516218859781816125642177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122021625146375754834189569 91516218859781816125642177)
  ·
    refine ⟨68637164144836362094231633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91516218859781816125642177 68637164144836362094231633)
    ·
      refine ⟨51477873108627271570673725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68637164144836362094231633 51477873108627271570673725)
      ·
        refine ⟨19304202415735226839002647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51477873108627271570673725 19304202415735226839002647)
        ·
          refine ⟨28956303623602840258503971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19304202415735226839002647 28956303623602840258503971)
          ·
            refine ⟨43434455435404260387755957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28956303623602840258503971 43434455435404260387755957)
            ·
              refine ⟨4071980197069149411352121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43434455435404260387755957 4071980197069149411352121)
              ·
                refine ⟨3053985147801862058514091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4071980197069149411352121 3053985147801862058514091)
                ·
                  refine ⟨4580977721702793087771137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3053985147801862058514091 4580977721702793087771137)
                  ·
                    refine ⟨3435733291277094815828353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4580977721702793087771137 3435733291277094815828353)
                    ·
                      refine ⟨2576799968457821111871265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3435733291277094815828353 2576799968457821111871265)
                      ·
                        rfl

theorem cell23_5018300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_5018300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018300 prefixEnd_5018300 := by exact prefixLift 5018300
  have htrace : WordTrace (prefixWord ++ tailWord_5018300) baseStart_5018300 baseEnd_5018300 := by
    simpa [prefixWord, tailWord_5018300, baseEnd_5018300] using wordTrace_append hprefix tailTrace_5018300
  have hstable : (prefixWord ++ tailWord_5018300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018300).length < 2 ^ (prefixWord ++ tailWord_5018300).sum := by decide
  have hdescent : baseEnd_5018300 < baseStart_5018300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018302 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_5018302 : Nat := 118140960795 + 5018302 * 2 ^ 59
def prefixEnd_5018302 : Nat := 4983230072969 + 3 ^ 40 * 5018302 * 2
def baseEnd_5018302 : Nat := 858933665139710034682085

theorem tailTrace_5018302 : CollatzResearch.WordTrace tailWord_5018302 prefixEnd_5018302 858933665139710034682085 := by
  unfold tailWord_5018302
  simp only [CollatzResearch.WordTrace]
  refine ⟨22879063833194548324107145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122021673777037591061904773 22879063833194548324107145)
  ·
    refine ⟨17159297874895911243080359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22879063833194548324107145 17159297874895911243080359)
    ·
      refine ⟨25738946812343866864620539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17159297874895911243080359 25738946812343866864620539)
      ·
        refine ⟨38608420218515800296930809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25738946812343866864620539 38608420218515800296930809)
        ·
          refine ⟨28956315163886850222698107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38608420218515800296930809 28956315163886850222698107)
          ·
            refine ⟨43434472745830275334047161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28956315163886850222698107 43434472745830275334047161)
            ·
              refine ⟨32575854559372706500535371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43434472745830275334047161 32575854559372706500535371)
              ·
                refine ⟨48863781839059059750803057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32575854559372706500535371 48863781839059059750803057)
                ·
                  refine ⟨36647836379294294813102293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48863781839059059750803057 36647836379294294813102293)
                  ·
                    refine ⟨858933665139710034682085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36647836379294294813102293 858933665139710034682085)
                    ·
                      rfl

theorem cell23_5018302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_5018302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018302 prefixEnd_5018302 := by exact prefixLift 5018302
  have htrace : WordTrace (prefixWord ++ tailWord_5018302) baseStart_5018302 baseEnd_5018302 := by
    simpa [prefixWord, tailWord_5018302, baseEnd_5018302] using wordTrace_append hprefix tailTrace_5018302
  have hstable : (prefixWord ++ tailWord_5018302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018302).length < 2 ^ (prefixWord ++ tailWord_5018302).sum := by decide
  have hdescent : baseEnd_5018302 < baseStart_5018302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018310 : List Nat := [6, 1, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_5018310 : Nat := 118140960795 + 5018310 * 2 ^ 59
def prefixEnd_5018310 : Nat := 4983230072969 + 3 ^ 40 * 5018310 * 2
def baseEnd_5018310 : Nat := 858935034421455357582073

theorem tailTrace_5018310 : CollatzResearch.WordTrace tailWord_5018310 prefixEnd_5018310 858935034421455357582073 := by
  unfold tailWord_5018310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5719775076547731373723387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 122021868299684935972765589 5719775076547731373723387)
  ·
    refine ⟨8579662614821597060585081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5719775076547731373723387 8579662614821597060585081)
    ·
      refine ⟨6434746961116197795438811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8579662614821597060585081 6434746961116197795438811)
      ·
        refine ⟨9652120441674296693158217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6434746961116197795438811 9652120441674296693158217)
        ·
          refine ⟨7239090331255722519868663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9652120441674296693158217 7239090331255722519868663)
          ·
            refine ⟨10858635496883583779802995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7239090331255722519868663 10858635496883583779802995)
            ·
              refine ⟨16287953245325375669704493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10858635496883583779802995 16287953245325375669704493)
              ·
                refine ⟨6107982466997015876139185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16287953245325375669704493 6107982466997015876139185)
                ·
                  refine ⟨4580986850247761907104389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6107982466997015876139185 4580986850247761907104389)
                  ·
                    refine ⟨858935034421455357582073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4580986850247761907104389 858935034421455357582073)
                    ·
                      rfl

theorem cell23_5018310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_5018310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018310 prefixEnd_5018310 := by exact prefixLift 5018310
  have htrace : WordTrace (prefixWord ++ tailWord_5018310) baseStart_5018310 baseEnd_5018310 := by
    simpa [prefixWord, tailWord_5018310, baseEnd_5018310] using wordTrace_append hprefix tailTrace_5018310
  have hstable : (prefixWord ++ tailWord_5018310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018310).length < 2 ^ (prefixWord ++ tailWord_5018310).sum := by decide
  have hdescent : baseEnd_5018310 < baseStart_5018310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018352 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 4]
def baseStart_5018352 : Nat := 118140960795 + 5018352 * 2 ^ 59
def prefixEnd_5018352 : Nat := 4983230072969 + 3 ^ 40 * 5018352 * 2
def baseEnd_5018352 : Nat := 2576826669451854908421025

theorem tailTrace_5018352 : CollatzResearch.WordTrace tailWord_5018352 prefixEnd_5018352 2576826669451854908421025 := by
  unfold tailWord_5018352
  simp only [CollatzResearch.WordTrace]
  refine ⟨91517167157687622566088655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122022889543583496754784873 91517167157687622566088655)
  ·
    refine ⟨137275750736531433849132983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91517167157687622566088655 137275750736531433849132983)
    ·
      refine ⟨205913626104797150773699475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137275750736531433849132983 205913626104797150773699475)
      ·
        refine ⟨308870439157195726160549213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205913626104797150773699475 308870439157195726160549213)
        ·
          refine ⟨115826414683948397310205955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308870439157195726160549213 115826414683948397310205955)
          ·
            refine ⟨173739622025922595965308933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115826414683948397310205955 173739622025922595965308933)
            ·
              refine ⟨32576179129860486743495425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173739622025922595965308933 32576179129860486743495425)
              ·
                refine ⟨24432134347395365057621569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32576179129860486743495425 24432134347395365057621569)
                ·
                  refine ⟨18324100760546523793216177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24432134347395365057621569 18324100760546523793216177)
                  ·
                    refine ⟨13743075570409892844912133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18324100760546523793216177 13743075570409892844912133)
                    ·
                      refine ⟨2576826669451854908421025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13743075570409892844912133 2576826669451854908421025)
                      ·
                        rfl

theorem cell23_5018352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_5018352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018352 prefixEnd_5018352 := by exact prefixLift 5018352
  have htrace : WordTrace (prefixWord ++ tailWord_5018352) baseStart_5018352 baseEnd_5018352 := by
    simpa [prefixWord, tailWord_5018352, baseEnd_5018352] using wordTrace_append hprefix tailTrace_5018352
  have hstable : (prefixWord ++ tailWord_5018352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018352).length < 2 ^ (prefixWord ++ tailWord_5018352).sum := by decide
  have hdescent : baseEnd_5018352 < baseStart_5018352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018396 : List Nat := [2, 2, 3, 1, 1, 4, 2, 3, 5]
def baseStart_5018396 : Nat := 118140960795 + 5018396 * 2 ^ 59
def prefixEnd_5018396 : Nat := 4983230072969 + 3 ^ 40 * 5018396 * 2
def baseEnd_5018396 : Nat := 286316584733405859585647

theorem tailTrace_5018396 : CollatzResearch.WordTrace tailWord_5018396 prefixEnd_5018396 286316584733405859585647 := by
  unfold tailWord_5018396
  simp only [CollatzResearch.WordTrace]
  refine ⟨91517969563607920323389521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122023959418143893764519361 91517969563607920323389521)
  ·
    refine ⟨68638477172705940242542141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91517969563607920323389521 68638477172705940242542141)
    ·
      refine ⟨25739428939764727590953303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68638477172705940242542141 25739428939764727590953303)
      ·
        refine ⟨38609143409647091386429955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25739428939764727590953303 38609143409647091386429955)
        ·
          refine ⟨57913715114470637079644933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38609143409647091386429955 57913715114470637079644933)
          ·
            refine ⟨10858821583963244452433425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57913715114470637079644933 10858821583963244452433425)
            ·
              refine ⟨8144116187972433339325069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10858821583963244452433425 8144116187972433339325069)
              ·
                refine ⟨3054043570489662502246901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8144116187972433339325069 3054043570489662502246901)
                ·
                  refine ⟨286316584733405859585647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3054043570489662502246901 286316584733405859585647)
                  ·
                    rfl

theorem cell23_5018396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 5].length) (baseStart_5018396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018396 prefixEnd_5018396 := by exact prefixLift 5018396
  have htrace : WordTrace (prefixWord ++ tailWord_5018396) baseStart_5018396 baseEnd_5018396 := by
    simpa [prefixWord, tailWord_5018396, baseEnd_5018396] using wordTrace_append hprefix tailTrace_5018396
  have hstable : (prefixWord ++ tailWord_5018396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018396).length < 2 ^ (prefixWord ++ tailWord_5018396).sum := by decide
  have hdescent : baseEnd_5018396 < baseStart_5018396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018413 : List Nat := [1, 5, 3, 2, 1, 1, 2, 1, 7]
def baseStart_5018413 : Nat := 118140960795 + 5018413 * 2 ^ 59
def prefixEnd_5018413 : Nat := 4983230072969 + 3 ^ 40 * 5018413 * 2
def baseEnd_5018413 : Nat := 286317554641308796639805

theorem tailTrace_5018413 : CollatzResearch.WordTrace tailWord_5018413 prefixEnd_5018413 286317554641308796639805 := by
  unfold tailWord_5018413
  simp only [CollatzResearch.WordTrace]
  refine ⟨183036559168154252550147893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122024372778769501700098595 183036559168154252550147893)
  ·
    refine ⟨17159677422014461176576365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183036559168154252550147893 17159677422014461176576365)
    ·
      refine ⟨6434879033255422941216137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17159677422014461176576365 6434879033255422941216137)
      ·
        refine ⟨4826159274941567205912103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6434879033255422941216137 4826159274941567205912103)
        ·
          refine ⟨7239238912412350808868155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4826159274941567205912103 7239238912412350808868155)
          ·
            refine ⟨10858858368618526213302233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7239238912412350808868155 10858858368618526213302233)
            ·
              refine ⟨8144143776463894659976675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10858858368618526213302233 8144143776463894659976675)
              ·
                refine ⟨12216215664695841989965013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8144143776463894659976675 12216215664695841989965013)
                ·
                  refine ⟨286317554641308796639805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12216215664695841989965013 286317554641308796639805)
                  ·
                    rfl

theorem cell23_5018413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_5018413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018413 prefixEnd_5018413 := by exact prefixLift 5018413
  have htrace : WordTrace (prefixWord ++ tailWord_5018413) baseStart_5018413 baseEnd_5018413 := by
    simpa [prefixWord, tailWord_5018413, baseEnd_5018413] using wordTrace_append hprefix tailTrace_5018413
  have hstable : (prefixWord ++ tailWord_5018413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018413).length < 2 ^ (prefixWord ++ tailWord_5018413).sum := by decide
  have hdescent : baseEnd_5018413 < baseStart_5018413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018442 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_5018442 : Nat := 118140960795 + 5018442 * 2 ^ 59
def prefixEnd_5018442 : Nat := 4983230072969 + 3 ^ 40 * 5018442 * 2
def baseEnd_5018442 : Nat := 2576872882710759556295611

theorem tailTrace_5018442 : CollatzResearch.WordTrace tailWord_5018442 prefixEnd_5018442 2576872882710759556295611 := by
  unfold tailWord_5018442
  simp only [CollatzResearch.WordTrace]
  refine ⟨45759404221262297625738395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122025077923366127001969053 45759404221262297625738395)
  ·
    refine ⟨68639106331893446438607593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45759404221262297625738395 68639106331893446438607593)
    ·
      refine ⟨51479329748920084828955695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68639106331893446438607593 51479329748920084828955695)
      ·
        refine ⟨77218994623380127243433543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51479329748920084828955695 77218994623380127243433543)
        ·
          refine ⟨115828491935070190865150315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77218994623380127243433543 115828491935070190865150315)
          ·
            refine ⟨173742737902605286297725473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115828491935070190865150315 173742737902605286297725473)
            ·
              refine ⟨130307053426953964723294105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173742737902605286297725473 130307053426953964723294105)
              ·
                refine ⟨97730290070215473542470579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130307053426953964723294105 97730290070215473542470579)
                ·
                  refine ⟨146595435105323210313705869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97730290070215473542470579 146595435105323210313705869)
                  ·
                    refine ⟨54973288164496203867639701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146595435105323210313705869 54973288164496203867639701)
                    ·
                      refine ⟨2576872882710759556295611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54973288164496203867639701 2576872882710759556295611)
                      ·
                        rfl

theorem cell23_5018442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_5018442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018442 prefixEnd_5018442 := by exact prefixLift 5018442
  have htrace : WordTrace (prefixWord ++ tailWord_5018442) baseStart_5018442 baseEnd_5018442 := by
    simpa [prefixWord, tailWord_5018442, baseEnd_5018442] using wordTrace_append hprefix tailTrace_5018442
  have hstable : (prefixWord ++ tailWord_5018442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018442).length < 2 ^ (prefixWord ++ tailWord_5018442).sum := by decide
  have hdescent : baseEnd_5018442 < baseStart_5018442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018499 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 3, 5]
def baseStart_5018499 : Nat := 118140960795 + 5018499 * 2 ^ 59
def prefixEnd_5018499 : Nat := 4983230072969 + 3 ^ 40 * 5018499 * 2
def baseEnd_5018499 : Nat := 858967383702688611094283

theorem tailTrace_5018499 : CollatzResearch.WordTrace tailWord_5018499 prefixEnd_5018499 858967383702688611094283 := by
  unfold tailWord_5018499
  simp only [CollatzResearch.WordTrace]
  refine ⟨183039695845842689237778551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122026463897228459491852367 183039695845842689237778551)
  ·
    refine ⟨274559543768764033856667827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183039695845842689237778551 274559543768764033856667827)
    ·
      refine ⟨411839315653146050785001741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274559543768764033856667827 411839315653146050785001741)
      ·
        refine ⟨154439743369929769044375653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 411839315653146050785001741 154439743369929769044375653)
        ·
          refine ⟨28957451881861831695820435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154439743369929769044375653 28957451881861831695820435)
          ·
            refine ⟨43436177822792747543730653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28957451881861831695820435 43436177822792747543730653)
            ·
              refine ⟨16288566683547280328898995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43436177822792747543730653 16288566683547280328898995)
              ·
                refine ⟨24432850025320920493348493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16288566683547280328898995 24432850025320920493348493)
                ·
                  refine ⟨9162318759495345185005685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24432850025320920493348493 9162318759495345185005685)
                  ·
                    refine ⟨858967383702688611094283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9162318759495345185005685 858967383702688611094283)
                    ·
                      rfl

theorem cell23_5018499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 5].length) (baseStart_5018499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018499 prefixEnd_5018499 := by exact prefixLift 5018499
  have htrace : WordTrace (prefixWord ++ tailWord_5018499) baseStart_5018499 baseEnd_5018499 := by
    simpa [prefixWord, tailWord_5018499, baseEnd_5018499] using wordTrace_append hprefix tailTrace_5018499
  have hstable : (prefixWord ++ tailWord_5018499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018499).length < 2 ^ (prefixWord ++ tailWord_5018499).sum := by decide
  have hdescent : baseEnd_5018499 < baseStart_5018499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018512 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 2, 10]
def baseStart_5018512 : Nat := 118140960795 + 5018512 * 2 ^ 59
def prefixEnd_5018512 : Nat := 4983230072969 + 3 ^ 40 * 5018512 * 2
def baseEnd_5018512 : Nat := 858969608785524760806763

theorem tailTrace_5018512 : CollatzResearch.WordTrace tailWord_5018512 prefixEnd_5018512 858969608785524760806763 := by
  unfold tailWord_5018512
  simp only [CollatzResearch.WordTrace]
  refine ⟨91520084997397796229000895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122026779996530394972001193 91520084997397796229000895)
  ·
    refine ⟨137280127496096694343501343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91520084997397796229000895 137280127496096694343501343)
    ·
      refine ⟨205920191244145041515252015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137280127496096694343501343 205920191244145041515252015)
      ·
        refine ⟨308880286866217562272878023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205920191244145041515252015 308880286866217562272878023)
        ·
          refine ⟨463320430299326343409317035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308880286866217562272878023 463320430299326343409317035)
          ·
            refine ⟨694980645448989515113975553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463320430299326343409317035 694980645448989515113975553)
            ·
              refine ⟨521235484086742136335481665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 694980645448989515113975553 521235484086742136335481665)
              ·
                refine ⟨390926613065056602251611249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521235484086742136335481665 390926613065056602251611249)
                ·
                  refine ⟨293194959798792451688708437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390926613065056602251611249 293194959798792451688708437)
                  ·
                    refine ⟨858969608785524760806763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 293194959798792451688708437 858969608785524760806763)
                    ·
                      rfl

theorem cell23_5018512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 10].length) (baseStart_5018512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018512 prefixEnd_5018512 := by exact prefixLift 5018512
  have htrace : WordTrace (prefixWord ++ tailWord_5018512) baseStart_5018512 baseEnd_5018512 := by
    simpa [prefixWord, tailWord_5018512, baseEnd_5018512] using wordTrace_append hprefix tailTrace_5018512
  have hstable : (prefixWord ++ tailWord_5018512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018512).length < 2 ^ (prefixWord ++ tailWord_5018512).sum := by decide
  have hdescent : baseEnd_5018512 < baseStart_5018512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018513 : List Nat := [1, 2, 2, 1, 1, 1, 3, 7, 1, 1, 3]
def baseStart_5018513 : Nat := 118140960795 + 5018513 * 2 ^ 59
def prefixEnd_5018513 : Nat := 4983230072969 + 3 ^ 40 * 5018513 * 2
def baseEnd_5018513 : Nat := 2576909339837228778507785

theorem tailTrace_5018513 : CollatzResearch.WordTrace tailWord_5018513 prefixEnd_5018513 2576909339837228778507785 := by
  unfold tailWord_5018513
  simp only [CollatzResearch.WordTrace]
  refine ⟨183040206467791969628788193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122026804311861313085858795 183040206467791969628788193)
  ·
    refine ⟨137280154850843977221591145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183040206467791969628788193 137280154850843977221591145)
    ·
      refine ⟨102960116138132982916193359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137280154850843977221591145 102960116138132982916193359)
      ·
        refine ⟨154440174207199474374290039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102960116138132982916193359 154440174207199474374290039)
        ·
          refine ⟨231660261310799211561435059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154440174207199474374290039 231660261310799211561435059)
          ·
            refine ⟨347490391966198817342152589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231660261310799211561435059 347490391966198817342152589)
            ·
              refine ⟨130308896987324556503307221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 347490391966198817342152589 130308896987324556503307221)
              ·
                refine ⟨3054114773140419293046263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 130308896987324556503307221 3054114773140419293046263)
                ·
                  refine ⟨4581172159710628939569395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3054114773140419293046263 4581172159710628939569395)
                  ·
                    refine ⟨6871758239565943409354093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4581172159710628939569395 6871758239565943409354093)
                    ·
                      refine ⟨2576909339837228778507785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6871758239565943409354093 2576909339837228778507785)
                      ·
                        rfl

theorem cell23_5018513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 1, 1, 3].length) (baseStart_5018513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018513 prefixEnd_5018513 := by exact prefixLift 5018513
  have htrace : WordTrace (prefixWord ++ tailWord_5018513) baseStart_5018513 baseEnd_5018513 := by
    simpa [prefixWord, tailWord_5018513, baseEnd_5018513] using wordTrace_append hprefix tailTrace_5018513
  have hstable : (prefixWord ++ tailWord_5018513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018513).length < 2 ^ (prefixWord ++ tailWord_5018513).sum := by decide
  have hdescent : baseEnd_5018513 < baseStart_5018513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018524 : List Nat := [2, 2, 3, 3, 3, 1, 2, 2, 1, 4]
def baseStart_5018524 : Nat := 118140960795 + 5018524 * 2 ^ 59
def prefixEnd_5018524 : Nat := 4983230072969 + 3 ^ 40 * 5018524 * 2
def baseEnd_5018524 : Nat := 858971662708142745156745

theorem tailTrace_5018524 : CollatzResearch.WordTrace tailWord_5018524 prefixEnd_5018524 858971662708142745156745 := by
  unfold tailWord_5018524
  simp only [CollatzResearch.WordTrace]
  refine ⟨91520303835376059253719313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122027071780501412338292417 91520303835376059253719313)
  ·
    refine ⟨68640227876532044440289485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91520303835376059253719313 68640227876532044440289485)
    ·
      refine ⟨25740085453699516665108557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68640227876532044440289485 25740085453699516665108557)
      ·
        refine ⟨9652532045137318749415709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25740085453699516665108557 9652532045137318749415709)
        ·
          refine ⟨3619699516926494531030891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9652532045137318749415709 3619699516926494531030891)
          ·
            refine ⟨5429549275389741796546337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3619699516926494531030891 5429549275389741796546337)
            ·
              refine ⟨4072161956542306347409753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5429549275389741796546337 4072161956542306347409753)
              ·
                refine ⟨3054121467406729760557315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4072161956542306347409753 3054121467406729760557315)
                ·
                  refine ⟨4581182201110094640835973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3054121467406729760557315 4581182201110094640835973)
                  ·
                    refine ⟨858971662708142745156745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4581182201110094640835973 858971662708142745156745)
                    ·
                      rfl

theorem cell23_5018524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_5018524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018524 prefixEnd_5018524 := by exact prefixLift 5018524
  have htrace : WordTrace (prefixWord ++ tailWord_5018524) baseStart_5018524 baseEnd_5018524 := by
    simpa [prefixWord, tailWord_5018524, baseEnd_5018524] using wordTrace_append hprefix tailTrace_5018524
  have hstable : (prefixWord ++ tailWord_5018524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018524).length < 2 ^ (prefixWord ++ tailWord_5018524).sum := by decide
  have hdescent : baseEnd_5018524 < baseStart_5018524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018553 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 5, 2, 2]
def baseStart_5018553 : Nat := 118140960795 + 5018553 * 2 ^ 59
def prefixEnd_5018553 : Nat := 4983230072969 + 3 ^ 40 * 5018553 * 2
def baseEnd_5018553 : Nat := 2576929879063408622007601

theorem tailTrace_5018553 : CollatzResearch.WordTrace tailWord_5018553 prefixEnd_5018553 2576929879063408622007601 := by
  unfold tailWord_5018553
  simp only [CollatzResearch.WordTrace]
  refine ⟨183041665387647056460244313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122027776925098037640162875 183041665387647056460244313)
  ·
    refine ⟨137281249040735292345183235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183041665387647056460244313 137281249040735292345183235)
    ·
      refine ⟨205921873561102938517774853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137281249040735292345183235 205921873561102938517774853)
      ·
        refine ⟨38610351292706800972082785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205921873561102938517774853 38610351292706800972082785)
        ·
          refine ⟨28957763469530100729062089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38610351292706800972082785 28957763469530100729062089)
          ·
            refine ⟨21718322602147575546796567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28957763469530100729062089 21718322602147575546796567)
            ·
              refine ⟨32577483903221363320194851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21718322602147575546796567 32577483903221363320194851)
              ·
                refine ⟨48866225854832044980292277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32577483903221363320194851 48866225854832044980292277)
                ·
                  refine ⟨4581208673890504216902401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48866225854832044980292277 4581208673890504216902401)
                  ·
                    refine ⟨3435906505417878162676801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4581208673890504216902401 3435906505417878162676801)
                    ·
                      refine ⟨2576929879063408622007601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3435906505417878162676801 2576929879063408622007601)
                      ·
                        rfl

theorem cell23_5018553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_5018553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018553 prefixEnd_5018553 := by exact prefixLift 5018553
  have htrace : WordTrace (prefixWord ++ tailWord_5018553) baseStart_5018553 baseEnd_5018553 := by
    simpa [prefixWord, tailWord_5018553, baseEnd_5018553] using wordTrace_append hprefix tailTrace_5018553
  have hstable : (prefixWord ++ tailWord_5018553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018553).length < 2 ^ (prefixWord ++ tailWord_5018553).sum := by decide
  have hdescent : baseEnd_5018553 < baseStart_5018553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018557 : List Nat := [1, 4, 1, 2, 5, 1, 1, 1, 2, 3, 2]
def baseStart_5018557 : Nat := 118140960795 + 5018557 * 2 ^ 59
def prefixEnd_5018557 : Nat := 4983230072969 + 3 ^ 40 * 5018557 * 2
def baseEnd_5018557 : Nat := 2576931932986026606357583

theorem tailTrace_5018557 : CollatzResearch.WordTrace tailWord_5018557 prefixEnd_5018557 2576931932986026606357583 := by
  unfold tailWord_5018557
  simp only [CollatzResearch.WordTrace]
  refine ⟨183041811279632565143389925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122027874186421710095593283 183041811279632565143389925)
  ·
    refine ⟨34320339614931105964385611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183041811279632565143389925 34320339614931105964385611)
    ·
      refine ⟨51480509422396658946578417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34320339614931105964385611 51480509422396658946578417)
      ·
        refine ⟨38610382066797494209933813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51480509422396658946578417 38610382066797494209933813)
        ·
          refine ⟨3619723318762265082181295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38610382066797494209933813 3619723318762265082181295)
          ·
            refine ⟨5429584978143397623271943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3619723318762265082181295 5429584978143397623271943)
            ·
              refine ⟨8144377467215096434907915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5429584978143397623271943 8144377467215096434907915)
              ·
                refine ⟨12216566200822644652361873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8144377467215096434907915 12216566200822644652361873)
                ·
                  refine ⟨9162424650616983489271405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12216566200822644652361873 9162424650616983489271405)
                  ·
                    refine ⟨3435909243981368808476777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9162424650616983489271405 3435909243981368808476777)
                    ·
                      refine ⟨2576931932986026606357583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3435909243981368808476777 2576931932986026606357583)
                      ·
                        rfl

theorem cell23_5018557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_5018557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018557 prefixEnd_5018557 := by exact prefixLift 5018557
  have htrace : WordTrace (prefixWord ++ tailWord_5018557) baseStart_5018557 baseEnd_5018557 := by
    simpa [prefixWord, tailWord_5018557, baseEnd_5018557] using wordTrace_append hprefix tailTrace_5018557
  have hstable : (prefixWord ++ tailWord_5018557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018557).length < 2 ^ (prefixWord ++ tailWord_5018557).sum := by decide
  have hdescent : baseEnd_5018557 < baseStart_5018557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018564 : List Nat := [2, 3, 3, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_5018564 : Nat := 118140960795 + 5018564 * 2 ^ 59
def prefixEnd_5018564 : Nat := 4983230072969 + 3 ^ 40 * 5018564 * 2
def baseEnd_5018564 : Nat := 2576935527350608078970051

theorem tailTrace_5018564 : CollatzResearch.WordTrace tailWord_5018564 prefixEnd_5018564 2576935527350608078970051 := by
  unfold tailWord_5018564
  simp only [CollatzResearch.WordTrace]
  refine ⟨91521033295303602669447373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122028044393738136892596497 91521033295303602669447373)
  ·
    refine ⟨34320387485738851001042765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91521033295303602669447373 34320387485738851001042765)
    ·
      refine ⟨12870145307152069125391037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34320387485738851001042765 12870145307152069125391037)
      ·
        refine ⟨4826304490182025922021639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12870145307152069125391037 4826304490182025922021639)
        ·
          refine ⟨7239456735273038883032459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4826304490182025922021639 7239456735273038883032459)
          ·
            refine ⟨10859185102909558324548689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7239456735273038883032459 10859185102909558324548689)
            ·
              refine ⟨8144388827182168743411517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10859185102909558324548689 8144388827182168743411517)
              ·
                refine ⟨3054145810193313278779319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8144388827182168743411517 3054145810193313278779319)
                ·
                  refine ⟨4581218715289969918168979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3054145810193313278779319 4581218715289969918168979)
                  ·
                    refine ⟨6871828072934954877253469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4581218715289969918168979 6871828072934954877253469)
                    ·
                      refine ⟨2576935527350608078970051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6871828072934954877253469 2576935527350608078970051)
                      ·
                        rfl

theorem cell23_5018564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_5018564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018564 prefixEnd_5018564 := by exact prefixLift 5018564
  have htrace : WordTrace (prefixWord ++ tailWord_5018564) baseStart_5018564 baseEnd_5018564 := by
    simpa [prefixWord, tailWord_5018564, baseEnd_5018564] using wordTrace_append hprefix tailTrace_5018564
  have hstable : (prefixWord ++ tailWord_5018564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018564).length < 2 ^ (prefixWord ++ tailWord_5018564).sum := by decide
  have hdescent : baseEnd_5018564 < baseStart_5018564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
