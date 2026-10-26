import V185TrunkScan23Chunk0176

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1047614 : List Nat := [4, 2, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_1047614 : Nat := 118140960795 + 1047614 * 2 ^ 59
def prefixEnd_1047614 : Nat := 4983230072969 + 3 ^ 40 * 1047614 * 2
def baseEnd_1047614 : Nat := 179309840793123146369039

theorem tailTrace_1047614 : CollatzResearch.WordTrace tailWord_1047614 prefixEnd_1047614 179309840793123146369039 := by
  unfold tailWord_1047614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4776202703335108883987737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25473081084453914047934597 4776202703335108883987737)
  ·
    refine ⟨3582152027501331662990803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4776202703335108883987737 3582152027501331662990803)
    ·
      refine ⟨5373228041251997494486205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3582152027501331662990803 5373228041251997494486205)
      ·
        refine ⟨2014960515469499060432327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5373228041251997494486205 2014960515469499060432327)
        ·
          refine ⟨3022440773204248590648491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2014960515469499060432327 3022440773204248590648491)
          ·
            refine ⟨4533661159806372885972737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022440773204248590648491 4533661159806372885972737)
            ·
              refine ⟨3400245869854779664479553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4533661159806372885972737 3400245869854779664479553)
              ·
                refine ⟨2550184402391084748359665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3400245869854779664479553 2550184402391084748359665)
                ·
                  refine ⟨1912638301793313561269749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2550184402391084748359665 1912638301793313561269749)
                  ·
                    refine ⟨179309840793123146369039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1912638301793313561269749 179309840793123146369039)
                    ·
                      rfl

theorem cell23_1047614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_1047614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047614 prefixEnd_1047614 := by exact prefixLift 1047614
  have htrace : WordTrace (prefixWord ++ tailWord_1047614) baseStart_1047614 baseEnd_1047614 := by
    simpa [prefixWord, tailWord_1047614, baseEnd_1047614] using wordTrace_append hprefix tailTrace_1047614
  have hstable : (prefixWord ++ tailWord_1047614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047614).length < 2 ^ (prefixWord ++ tailWord_1047614).sum := by decide
  have hdescent : baseEnd_1047614 < baseStart_1047614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047634 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 1, 6, 2]
def baseStart_1047634 : Nat := 118140960795 + 1047634 * 2 ^ 59
def prefixEnd_1047634 : Nat := 4983230072969 + 3 ^ 40 * 1047634 * 2
def baseEnd_1047634 : Nat := 537939791992459360857025

theorem tailTrace_1047634 : CollatzResearch.WordTrace tailWord_1047634 prefixEnd_1047634 537939791992459360857025 := by
  unfold tailWord_1047634
  simp only [CollatzResearch.WordTrace]
  refine ⟨9552587771652103621907489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25473567391072276325086637 9552587771652103621907489)
  ·
    refine ⟨7164440828739077716430617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9552587771652103621907489 7164440828739077716430617)
    ·
      refine ⟨5373330621554308287322963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7164440828739077716430617 5373330621554308287322963)
      ·
        refine ⟨8059995932331462430984445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5373330621554308287322963 8059995932331462430984445)
        ·
          refine ⟨3022498474624298411619167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8059995932331462430984445 3022498474624298411619167)
          ·
            refine ⟨4533747711936447617428751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022498474624298411619167 4533747711936447617428751)
            ·
              refine ⟨6800621567904671426143127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4533747711936447617428751 6800621567904671426143127)
              ·
                refine ⟨10200932351857007139214691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6800621567904671426143127 10200932351857007139214691)
                ·
                  refine ⟨15301398527785510708822037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10200932351857007139214691 15301398527785510708822037)
                  ·
                    refine ⟨717253055989945814476033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15301398527785510708822037 717253055989945814476033)
                    ·
                      refine ⟨537939791992459360857025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 717253055989945814476033 537939791992459360857025)
                      ·
                        rfl

theorem cell23_1047634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_1047634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047634 prefixEnd_1047634 := by exact prefixLift 1047634
  have htrace : WordTrace (prefixWord ++ tailWord_1047634) baseStart_1047634 baseEnd_1047634 := by
    simpa [prefixWord, tailWord_1047634, baseEnd_1047634] using wordTrace_append hprefix tailTrace_1047634
  have hstable : (prefixWord ++ tailWord_1047634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047634).length < 2 ^ (prefixWord ++ tailWord_1047634).sum := by decide
  have hdescent : baseEnd_1047634 < baseStart_1047634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047637 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 1, 4, 3]
def baseStart_1047637 : Nat := 118140960795 + 1047637 * 2 ^ 59
def prefixEnd_1047637 : Nat := 4983230072969 + 3 ^ 40 * 1047637 * 2
def baseEnd_1047637 : Nat := 537941332434422849119511

theorem tailTrace_1047637 : CollatzResearch.WordTrace tailWord_1047637 prefixEnd_1047637 537941332434422849119511 := by
  unfold tailWord_1047637
  simp only [CollatzResearch.WordTrace]
  refine ⟨38210460505597545999989165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25473640337065030666659443 38210460505597545999989165)
  ·
    refine ⟨14328922689599079749995937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38210460505597545999989165 14328922689599079749995937)
    ·
      refine ⟨10746692017199309812496953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14328922689599079749995937 10746692017199309812496953)
      ·
        refine ⟨8060019012899482359372715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10746692017199309812496953 8060019012899482359372715)
        ·
          refine ⟨12090028519349223539059073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8060019012899482359372715 12090028519349223539059073)
          ·
            refine ⟨9067521389511917654294305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12090028519349223539059073 9067521389511917654294305)
            ·
              refine ⟨6800641042133938240720729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9067521389511917654294305 6800641042133938240720729)
              ·
                refine ⟨5100480781600453680540547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6800641042133938240720729 5100480781600453680540547)
                ·
                  refine ⟨7650721172400680520810821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5100480781600453680540547 7650721172400680520810821)
                  ·
                    refine ⟨1434510219825127597652029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7650721172400680520810821 1434510219825127597652029)
                    ·
                      refine ⟨537941332434422849119511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1434510219825127597652029 537941332434422849119511)
                      ·
                        rfl

theorem cell23_1047637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_1047637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047637 prefixEnd_1047637 := by exact prefixLift 1047637
  have htrace : WordTrace (prefixWord ++ tailWord_1047637) baseStart_1047637 baseEnd_1047637 := by
    simpa [prefixWord, tailWord_1047637, baseEnd_1047637] using wordTrace_append hprefix tailTrace_1047637
  have hstable : (prefixWord ++ tailWord_1047637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047637).length < 2 ^ (prefixWord ++ tailWord_1047637).sum := by decide
  have hdescent : baseEnd_1047637 < baseStart_1047637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047644 : List Nat := [2, 2, 4, 1, 1, 1, 3, 2, 3, 4]
def baseStart_1047644 : Nat := 118140960795 + 1047644 * 2 ^ 59
def prefixEnd_1047644 : Nat := 4983230072969 + 3 ^ 40 * 1047644 * 2
def baseEnd_1047644 : Nat := 179314975599668107243993

theorem tailTrace_1047644 : CollatzResearch.WordTrace tailWord_1047644 prefixEnd_1047644 179314975599668107243993 := by
  unfold tailWord_1047644
  simp only [CollatzResearch.WordTrace]
  refine ⟨19105357908286093097746993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25473810544381457463662657 19105357908286093097746993)
  ·
    refine ⟨14329018431214569823310245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19105357908286093097746993 14329018431214569823310245)
    ·
      refine ⟨2686690955852731841870671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14329018431214569823310245 2686690955852731841870671)
      ·
        refine ⟨4030036433779097762806007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2686690955852731841870671 4030036433779097762806007)
        ·
          refine ⟨6045054650668646644209011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4030036433779097762806007 6045054650668646644209011)
          ·
            refine ⟨9067581976002969966313517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6045054650668646644209011 9067581976002969966313517)
            ·
              refine ⟨3400343241001113737367569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9067581976002969966313517 3400343241001113737367569)
              ·
                refine ⟨2550257430750835303025677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3400343241001113737367569 2550257430750835303025677)
                ·
                  refine ⟨956346536531563238634629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2550257430750835303025677 956346536531563238634629)
                  ·
                    refine ⟨179314975599668107243993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 956346536531563238634629 179314975599668107243993)
                    ·
                      rfl

theorem cell23_1047644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_1047644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047644 prefixEnd_1047644 := by exact prefixLift 1047644
  have htrace : WordTrace (prefixWord ++ tailWord_1047644) baseStart_1047644 baseEnd_1047644 := by
    simpa [prefixWord, tailWord_1047644, baseEnd_1047644] using wordTrace_append hprefix tailTrace_1047644
  have hstable : (prefixWord ++ tailWord_1047644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047644).length < 2 ^ (prefixWord ++ tailWord_1047644).sum := by decide
  have hdescent : baseEnd_1047644 < baseStart_1047644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047661 : List Nat := [1, 5, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_1047661 : Nat := 118140960795 + 1047661 * 2 ^ 59
def prefixEnd_1047661 : Nat := 4983230072969 + 3 ^ 40 * 1047661 * 2
def baseEnd_1047661 : Nat := 179317885323376918406467

theorem tailTrace_1047661 : CollatzResearch.WordTrace tailWord_1047661 prefixEnd_1047661 179317885323376918406467 := by
  unfold tailWord_1047661
  simp only [CollatzResearch.WordTrace]
  refine ⟨38211335857510598098862837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25474223905007065399241891 38211335857510598098862837)
  ·
    refine ⟨3582312736641618571768391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38211335857510598098862837 3582312736641618571768391)
    ·
      refine ⟨5373469104962427857652587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3582312736641618571768391 5373469104962427857652587)
      ·
        refine ⟨8060203657443641786478881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5373469104962427857652587 8060203657443641786478881)
        ·
          refine ⟨6045152743082731339859161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8060203657443641786478881 6045152743082731339859161)
          ·
            refine ⟨4533864557312048504894371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6045152743082731339859161 4533864557312048504894371)
            ·
              refine ⟨6800796835968072757341557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4533864557312048504894371 6800796835968072757341557)
              ·
                refine ⟨637574703372006821000771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6800796835968072757341557 637574703372006821000771)
                ·
                  refine ⟨956362055058010231501157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637574703372006821000771 956362055058010231501157)
                  ·
                    refine ⟨179317885323376918406467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 956362055058010231501157 179317885323376918406467)
                    ·
                      rfl

theorem cell23_1047661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_1047661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047661 prefixEnd_1047661 := by exact prefixLift 1047661
  have htrace : WordTrace (prefixWord ++ tailWord_1047661) baseStart_1047661 baseEnd_1047661 := by
    simpa [prefixWord, tailWord_1047661, baseEnd_1047661] using wordTrace_append hprefix tailTrace_1047661
  have hstable : (prefixWord ++ tailWord_1047661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047661).length < 2 ^ (prefixWord ++ tailWord_1047661).sum := by decide
  have hdescent : baseEnd_1047661 < baseStart_1047661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047704 : List Nat := [2, 1, 2, 4, 2, 1, 1, 4, 1, 5]
def baseStart_1047704 : Nat := 118140960795 + 1047704 * 2 ^ 59
def prefixEnd_1047704 : Nat := 4983230072969 + 3 ^ 40 * 1047704 * 2
def baseEnd_1047704 : Nat := 179325245212758028993901

theorem tailTrace_1047704 : CollatzResearch.WordTrace tailWord_1047704 prefixEnd_1047704 179325245212758028993901 := by
  unfold tailWord_1047704
  simp only [CollatzResearch.WordTrace]
  refine ⟨19106452098177408221339083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25475269464236544295118777 19106452098177408221339083)
  ·
    refine ⟨28659678147266112332008625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19106452098177408221339083 28659678147266112332008625)
    ·
      refine ⟨21494758610449584249006469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28659678147266112332008625 21494758610449584249006469)
      ·
        refine ⟨4030267239459297046688713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21494758610449584249006469 4030267239459297046688713)
        ·
          refine ⟨3022700429594472785016535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4030267239459297046688713 3022700429594472785016535)
          ·
            refine ⟨4534050644391709177524803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022700429594472785016535 4534050644391709177524803)
            ·
              refine ⟨6801075966587563766287205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4534050644391709177524803 6801075966587563766287205)
              ·
                refine ⟨1275201743735168206178851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6801075966587563766287205 1275201743735168206178851)
                ·
                  refine ⟨1912802615602752309268277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1275201743735168206178851 1912802615602752309268277)
                  ·
                    refine ⟨179325245212758028993901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1912802615602752309268277 179325245212758028993901)
                    ·
                      rfl

theorem cell23_1047704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_1047704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047704 prefixEnd_1047704 := by exact prefixLift 1047704
  have htrace : WordTrace (prefixWord ++ tailWord_1047704) baseStart_1047704 baseEnd_1047704 := by
    simpa [prefixWord, tailWord_1047704, baseEnd_1047704] using wordTrace_append hprefix tailTrace_1047704
  have hstable : (prefixWord ++ tailWord_1047704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047704).length < 2 ^ (prefixWord ++ tailWord_1047704).sum := by decide
  have hdescent : baseEnd_1047704 < baseStart_1047704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047727 : List Nat := [1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 5]
def baseStart_1047727 : Nat := 118140960795 + 1047727 * 2 ^ 59
def prefixEnd_1047727 : Nat := 4983230072969 + 3 ^ 40 * 1047727 * 2
def baseEnd_1047727 : Nat := 537987545693327496994097

theorem tailTrace_1047727 : CollatzResearch.WordTrace tailWord_1047727 prefixEnd_1047727 537987545693327496994097 := by
  unfold tailWord_1047727
  simp only [CollatzResearch.WordTrace]
  refine ⟨38213743075271491370765435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25475828716847660913843623 38213743075271491370765435)
  ·
    refine ⟨57320614612907237056148153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38213743075271491370765435 57320614612907237056148153)
    ·
      refine ⟨42990460959680427792111115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57320614612907237056148153 42990460959680427792111115)
      ·
        refine ⟨64485691439520641688166673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42990460959680427792111115 64485691439520641688166673)
        ·
          refine ⟨48364268579640481266125005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64485691439520641688166673 48364268579640481266125005)
          ·
            refine ⟨18136600717365180474796877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48364268579640481266125005 18136600717365180474796877)
            ·
              refine ⟨6801225269011942678048829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18136600717365180474796877 6801225269011942678048829)
              ·
                refine ⟨2550459475879478504268311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6801225269011942678048829 2550459475879478504268311)
                ·
                  refine ⟨3825689213819217756402467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550459475879478504268311 3825689213819217756402467)
                  ·
                    refine ⟨5738533820728826634603701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3825689213819217756402467 5738533820728826634603701)
                    ·
                      refine ⟨537987545693327496994097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5738533820728826634603701 537987545693327496994097)
                      ·
                        rfl

theorem cell23_1047727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 5].length) (baseStart_1047727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047727 prefixEnd_1047727 := by exact prefixLift 1047727
  have htrace : WordTrace (prefixWord ++ tailWord_1047727) baseStart_1047727 baseEnd_1047727 := by
    simpa [prefixWord, tailWord_1047727, baseEnd_1047727] using wordTrace_append hprefix tailTrace_1047727
  have hstable : (prefixWord ++ tailWord_1047727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047727).length < 2 ^ (prefixWord ++ tailWord_1047727).sum := by decide
  have hdescent : baseEnd_1047727 < baseStart_1047727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047737 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 1, 1, 6]
def baseStart_1047737 : Nat := 118140960795 + 1047737 * 2 ^ 59
def prefixEnd_1047737 : Nat := 4983230072969 + 3 ^ 40 * 1047737 * 2
def baseEnd_1047737 : Nat := 537992680499872457869051

theorem tailTrace_1047737 : CollatzResearch.WordTrace tailWord_1047737 prefixEnd_1047737 537992680499872457869051 := by
  unfold tailWord_1047737
  simp only [CollatzResearch.WordTrace]
  refine ⟨38214107805235263078629465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25476071870156842052419643 38214107805235263078629465)
  ·
    refine ⟨28660580853926447308972099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38214107805235263078629465 28660580853926447308972099)
    ·
      refine ⟨42990871280889670963458149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28660580853926447308972099 42990871280889670963458149)
      ·
        refine ⟨8060788365166813305648403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42990871280889670963458149 8060788365166813305648403)
        ·
          refine ⟨12091182547750219958472605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8060788365166813305648403 12091182547750219958472605)
          ·
            refine ⟨4534193455406332484427227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12091182547750219958472605 4534193455406332484427227)
            ·
              refine ⟨6801290183109498726640841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4534193455406332484427227 6801290183109498726640841)
              ·
                refine ⟨5100967637332124044980631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6801290183109498726640841 5100967637332124044980631)
                ·
                  refine ⟨7651451455998186067470947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5100967637332124044980631 7651451455998186067470947)
                  ·
                    refine ⟨11477177183997279101206421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7651451455998186067470947 11477177183997279101206421)
                    ·
                      refine ⟨537992680499872457869051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11477177183997279101206421 537992680499872457869051)
                      ·
                        rfl

theorem cell23_1047737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_1047737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047737 prefixEnd_1047737 := by exact prefixLift 1047737
  have htrace : WordTrace (prefixWord ++ tailWord_1047737) baseStart_1047737 baseEnd_1047737 := by
    simpa [prefixWord, tailWord_1047737, baseEnd_1047737] using wordTrace_append hprefix tailTrace_1047737
  have hstable : (prefixWord ++ tailWord_1047737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047737).length < 2 ^ (prefixWord ++ tailWord_1047737).sum := by decide
  have hdescent : baseEnd_1047737 < baseStart_1047737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047758 : List Nat := [4, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4]
def baseStart_1047758 : Nat := 118140960795 + 1047758 * 2 ^ 59
def prefixEnd_1047758 : Nat := 4983230072969 + 3 ^ 40 * 1047758 * 2
def baseEnd_1047758 : Nat := 538003463593616875706455

theorem tailTrace_1047758 : CollatzResearch.WordTrace tailWord_1047758 prefixEnd_1047758 538003463593616875706455 := by
  unfold tailWord_1047758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4776859217269897958142991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25476582492106122443429285 4776859217269897958142991)
  ·
    refine ⟨7165288825904846937214487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4776859217269897958142991 7165288825904846937214487)
    ·
      refine ⟨10747933238857270405821731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7165288825904846937214487 10747933238857270405821731)
      ·
        refine ⟨16121899858285905608732597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10747933238857270405821731 16121899858285905608732597)
        ·
          refine ⟨1511428111714303650818681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16121899858285905608732597 1511428111714303650818681)
          ·
            refine ⟨1133571083785727738114011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1511428111714303650818681 1133571083785727738114011)
            ·
              refine ⟨1700356625678591607171017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133571083785727738114011 1700356625678591607171017)
              ·
                refine ⟨1275267469258943705378263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1700356625678591607171017 1275267469258943705378263)
                ·
                  refine ⟨1912901203888415558067395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1275267469258943705378263 1912901203888415558067395)
                  ·
                    refine ⟨2869351805832623337101093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1912901203888415558067395 2869351805832623337101093)
                    ·
                      refine ⟨538003463593616875706455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2869351805832623337101093 538003463593616875706455)
                      ·
                        rfl

theorem cell23_1047758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_1047758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047758 prefixEnd_1047758 := by exact prefixLift 1047758
  have htrace : WordTrace (prefixWord ++ tailWord_1047758) baseStart_1047758 baseEnd_1047758 := by
    simpa [prefixWord, tailWord_1047758, baseEnd_1047758] using wordTrace_append hprefix tailTrace_1047758
  have hstable : (prefixWord ++ tailWord_1047758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047758).length < 2 ^ (prefixWord ++ tailWord_1047758).sum := by decide
  have hdescent : baseEnd_1047758 < baseStart_1047758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047807 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 1, 8]
def baseStart_1047807 : Nat := 118140960795 + 1047807 * 2 ^ 59
def prefixEnd_1047807 : Nat := 4983230072969 + 3 ^ 40 * 1047807 * 2
def baseEnd_1047807 : Nat := 179342874715229061331243

theorem tailTrace_1047807 : CollatzResearch.WordTrace tailWord_1047807 prefixEnd_1047807 179342874715229061331243 := by
  unfold tailWord_1047807
  simp only [CollatzResearch.WordTrace]
  refine ⟨38216660914981665033677675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25477773943321110022451783 38216660914981665033677675)
  ·
    refine ⟨57324991372472497550516513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38216660914981665033677675 57324991372472497550516513)
    ·
      refine ⟨42993743529354373162887385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57324991372472497550516513 42993743529354373162887385)
      ·
        refine ⟨32245307647015779872165539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42993743529354373162887385 32245307647015779872165539)
        ·
          refine ⟨48367961470523669808248309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32245307647015779872165539 48367961470523669808248309)
          ·
            refine ⟨4534496387861594044523279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48367961470523669808248309 4534496387861594044523279)
            ·
              refine ⟨6801744581792391066784919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4534496387861594044523279 6801744581792391066784919)
              ·
                refine ⟨10202616872688586600177379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6801744581792391066784919 10202616872688586600177379)
                ·
                  refine ⟨15303925309032879900266069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10202616872688586600177379 15303925309032879900266069)
                  ·
                    refine ⟨179342874715229061331243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15303925309032879900266069 179342874715229061331243)
                    ·
                      rfl

theorem cell23_1047807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 8].length) (baseStart_1047807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047807 prefixEnd_1047807 := by exact prefixLift 1047807
  have htrace : WordTrace (prefixWord ++ tailWord_1047807) baseStart_1047807 baseEnd_1047807 := by
    simpa [prefixWord, tailWord_1047807, baseEnd_1047807] using wordTrace_append hprefix tailTrace_1047807
  have hstable : (prefixWord ++ tailWord_1047807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047807).length < 2 ^ (prefixWord ++ tailWord_1047807).sum := by decide
  have hdescent : baseEnd_1047807 < baseStart_1047807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047831 : List Nat := [1, 1, 3, 4, 1, 1, 1, 4, 1, 4, 2]
def baseStart_1047831 : Nat := 118140960795 + 1047831 * 2 ^ 59
def prefixEnd_1047831 : Nat := 4983230072969 + 3 ^ 40 * 1047831 * 2
def baseEnd_1047831 : Nat := 538040947681395090093619

theorem tailTrace_1047831 : CollatzResearch.WordTrace tailWord_1047831 prefixEnd_1047831 538040947681395090093619 := by
  unfold tailWord_1047831
  simp only [CollatzResearch.WordTrace]
  refine ⟨38217536266894717132551347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25478357511263144755034231 38217536266894717132551347)
  ·
    refine ⟨57326304400342075698827021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38217536266894717132551347 57326304400342075698827021)
    ·
      refine ⟨21497364150128278387060133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57326304400342075698827021 21497364150128278387060133)
      ·
        refine ⟨4030755778149052197573775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21497364150128278387060133 4030755778149052197573775)
        ·
          refine ⟨6046133667223578296360663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4030755778149052197573775 6046133667223578296360663)
          ·
            refine ⟨9069200500835367444540995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6046133667223578296360663 9069200500835367444540995)
            ·
              refine ⟨13603800751253051166811493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9069200500835367444540995 13603800751253051166811493)
              ·
                refine ⟨2550712640859947093777155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13603800751253051166811493 2550712640859947093777155)
                ·
                  refine ⟨3826068961289920640665733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550712640859947093777155 3826068961289920640665733)
                  ·
                    refine ⟨717387930241860120124825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3826068961289920640665733 717387930241860120124825)
                    ·
                      refine ⟨538040947681395090093619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 717387930241860120124825 538040947681395090093619)
                      ·
                        rfl

theorem cell23_1047831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_1047831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047831 prefixEnd_1047831 := by exact prefixLift 1047831
  have htrace : WordTrace (prefixWord ++ tailWord_1047831) baseStart_1047831 baseEnd_1047831 := by
    simpa [prefixWord, tailWord_1047831, baseEnd_1047831] using wordTrace_append hprefix tailTrace_1047831
  have hstable : (prefixWord ++ tailWord_1047831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047831).length < 2 ^ (prefixWord ++ tailWord_1047831).sum := by decide
  have hdescent : baseEnd_1047831 < baseStart_1047831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047842 : List Nat := [3, 3, 1, 1, 5, 1, 1, 2, 2, 1, 3]
def baseStart_1047842 : Nat := 118140960795 + 1047842 * 2 ^ 59
def prefixEnd_1047842 : Nat := 4983230072969 + 3 ^ 40 * 1047842 * 2
def baseEnd_1047842 : Nat := 538046595968594547056069

theorem tailTrace_1047842 : CollatzResearch.WordTrace tailWord_1047842 prefixEnd_1047842 538046595968594547056069 := by
  unfold tailWord_1047842
  simp only [CollatzResearch.WordTrace]
  refine ⟨9554484367463716502800445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25478624979903244007467853 9554484367463716502800445)
  ·
    refine ⟨3582931637798893688550167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9554484367463716502800445 3582931637798893688550167)
    ·
      refine ⟨5374397456698340532825251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3582931637798893688550167 5374397456698340532825251)
      ·
        refine ⟨8061596185047510799237877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5374397456698340532825251 8061596185047510799237877)
        ·
          refine ⟨755774642348204137428551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8061596185047510799237877 755774642348204137428551)
          ·
            refine ⟨1133661963522306206142827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755774642348204137428551 1133661963522306206142827)
            ·
              refine ⟨1700492945283459309214241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133661963522306206142827 1700492945283459309214241)
              ·
                refine ⟨1275369708962594481910681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1700492945283459309214241 1275369708962594481910681)
                ·
                  refine ⟨956527281721945861433011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1275369708962594481910681 956527281721945861433011)
                  ·
                    refine ⟨1434790922582918792149517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 956527281721945861433011 1434790922582918792149517)
                    ·
                      refine ⟨538046595968594547056069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1434790922582918792149517 538046595968594547056069)
                      ·
                        rfl

theorem cell23_1047842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_1047842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047842 prefixEnd_1047842 := by exact prefixLift 1047842
  have htrace : WordTrace (prefixWord ++ tailWord_1047842) baseStart_1047842 baseEnd_1047842 := by
    simpa [prefixWord, tailWord_1047842, baseEnd_1047842] using wordTrace_append hprefix tailTrace_1047842
  have hstable : (prefixWord ++ tailWord_1047842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047842).length < 2 ^ (prefixWord ++ tailWord_1047842).sum := by decide
  have hdescent : baseEnd_1047842 < baseStart_1047842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047844 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_1047844 : Nat := 118140960795 + 1047844 * 2 ^ 59
def prefixEnd_1047844 : Nat := 4983230072969 + 3 ^ 40 * 1047844 * 2
def baseEnd_1047844 : Nat := 538047622929903539231059

theorem tailTrace_1047844 : CollatzResearch.WordTrace tailWord_1047844 prefixEnd_1047844 538047622929903539231059 := by
  unfold tailWord_1047844
  simp only [CollatzResearch.WordTrace]
  refine ⟨19109005207923810176387293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25478673610565080235183057 19109005207923810176387293)
  ·
    refine ⟨7165876952971428816145235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19109005207923810176387293 7165876952971428816145235)
    ·
      refine ⟨10748815429457143224217853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7165876952971428816145235 10748815429457143224217853)
      ·
        refine ⟨4030805786046428709081695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10748815429457143224217853 4030805786046428709081695)
        ·
          refine ⟨6046208679069643063622543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4030805786046428709081695 6046208679069643063622543)
          ·
            refine ⟨9069313018604464595433815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6046208679069643063622543 9069313018604464595433815)
            ·
              refine ⟨13603969527906696893150723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9069313018604464595433815 13603969527906696893150723)
              ·
                refine ⟨20405954291860045339726085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13603969527906696893150723 20405954291860045339726085)
                ·
                  refine ⟨3826116429723758501198641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20405954291860045339726085 3826116429723758501198641)
                  ·
                    refine ⟨2869587322292818875898981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3826116429723758501198641 2869587322292818875898981)
                    ·
                      refine ⟨538047622929903539231059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2869587322292818875898981 538047622929903539231059)
                      ·
                        rfl

theorem cell23_1047844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_1047844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047844 prefixEnd_1047844 := by exact prefixLift 1047844
  have htrace : WordTrace (prefixWord ++ tailWord_1047844) baseStart_1047844 baseEnd_1047844 := by
    simpa [prefixWord, tailWord_1047844, baseEnd_1047844] using wordTrace_append hprefix tailTrace_1047844
  have hstable : (prefixWord ++ tailWord_1047844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047844).length < 2 ^ (prefixWord ++ tailWord_1047844).sum := by decide
  have hdescent : baseEnd_1047844 < baseStart_1047844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047865 : List Nat := [1, 2, 1, 6, 2, 2, 1, 1, 1, 4, 2]
def baseStart_1047865 : Nat := 118140960795 + 1047865 * 2 ^ 59
def prefixEnd_1047865 : Nat := 4983230072969 + 3 ^ 40 * 1047865 * 2
def baseEnd_1047865 : Nat := 538058406023647957068463

theorem tailTrace_1047865 : CollatzResearch.WordTrace tailWord_1047865 prefixEnd_1047865 538058406023647957068463 := by
  unfold tailWord_1047865
  simp only [CollatzResearch.WordTrace]
  refine ⟨38218776348771540939289049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25479184232514360626192699 38218776348771540939289049)
  ·
    refine ⟨28664082261578655704466787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38218776348771540939289049 28664082261578655704466787)
    ·
      refine ⟨42996123392367983556700181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28664082261578655704466787 42996123392367983556700181)
      ·
        refine ⟨2015443284017249229220321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42996123392367983556700181 2015443284017249229220321)
        ·
          refine ⟨1511582463012936921915241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2015443284017249229220321 1511582463012936921915241)
          ·
            refine ⟨1133686847259702691436431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1511582463012936921915241 1133686847259702691436431)
            ·
              refine ⟨1700530270889554037154647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133686847259702691436431 1700530270889554037154647)
              ·
                refine ⟨2550795406334331055731971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700530270889554037154647 2550795406334331055731971)
                ·
                  refine ⟨3826193109501496583597957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550795406334331055731971 3826193109501496583597957)
                  ·
                    refine ⟨717411208031530609424617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3826193109501496583597957 717411208031530609424617)
                    ·
                      refine ⟨538058406023647957068463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 717411208031530609424617 538058406023647957068463)
                      ·
                        rfl

theorem cell23_1047865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_1047865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047865 prefixEnd_1047865 := by exact prefixLift 1047865
  have htrace : WordTrace (prefixWord ++ tailWord_1047865) baseStart_1047865 baseEnd_1047865 := by
    simpa [prefixWord, tailWord_1047865, baseEnd_1047865] using wordTrace_append hprefix tailTrace_1047865
  have hstable : (prefixWord ++ tailWord_1047865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047865).length < 2 ^ (prefixWord ++ tailWord_1047865).sum := by decide
  have hdescent : baseEnd_1047865 < baseStart_1047865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047884 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 1, 7]
def baseStart_1047884 : Nat := 118140960795 + 1047884 * 2 ^ 59
def prefixEnd_1047884 : Nat := 4983230072969 + 3 ^ 40 * 1047884 * 2
def baseEnd_1047884 : Nat := 179356054052027794243625

theorem tailTrace_1047884 : CollatzResearch.WordTrace tailWord_1047884 prefixEnd_1047884 179356054052027794243625 := by
  unfold tailWord_1047884
  simp only [CollatzResearch.WordTrace]
  refine ⟨19109734667851353592115353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25479646223801804789487137 19109734667851353592115353)
  ·
    refine ⟨14332301000888515194086515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19109734667851353592115353 14332301000888515194086515)
    ·
      refine ⟨21498451501332772791129773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14332301000888515194086515 21498451501332772791129773)
      ·
        refine ⟨8061919312999789796673665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21498451501332772791129773 8061919312999789796673665)
        ·
          refine ⟨6046439484749842347505249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8061919312999789796673665 6046439484749842347505249)
          ·
            refine ⟨4534829613562381760628937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6046439484749842347505249 4534829613562381760628937)
            ·
              refine ⟨3401122210171786320471703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4534829613562381760628937 3401122210171786320471703)
              ·
                refine ⟨5101683315257679480707555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3401122210171786320471703 5101683315257679480707555)
                ·
                  refine ⟨7652524972886519221061333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5101683315257679480707555 7652524972886519221061333)
                  ·
                    refine ⟨179356054052027794243625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7652524972886519221061333 179356054052027794243625)
                    ·
                      rfl

theorem cell23_1047884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_1047884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047884 prefixEnd_1047884 := by exact prefixLift 1047884
  have htrace : WordTrace (prefixWord ++ tailWord_1047884) baseStart_1047884 baseEnd_1047884 := by
    simpa [prefixWord, tailWord_1047884, baseEnd_1047884] using wordTrace_append hprefix tailTrace_1047884
  have hstable : (prefixWord ++ tailWord_1047884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047884).length < 2 ^ (prefixWord ++ tailWord_1047884).sum := by decide
  have hdescent : baseEnd_1047884 < baseStart_1047884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047887 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 8]
def baseStart_1047887 : Nat := 118140960795 + 1047887 * 2 ^ 59
def prefixEnd_1047887 : Nat := 4983230072969 + 3 ^ 40 * 1047887 * 2
def baseEnd_1047887 : Nat := 538069702598046870993361

theorem tailTrace_1047887 : CollatzResearch.WordTrace tailWord_1047887 prefixEnd_1047887 538069702598046870993361 := by
  unfold tailWord_1047887
  simp only [CollatzResearch.WordTrace]
  refine ⟨38219578754691838696589915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25479719169794559131059943 38219578754691838696589915)
  ·
    refine ⟨57329368132037758044884873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38219578754691838696589915 57329368132037758044884873)
    ·
      refine ⟨42997026099028318533663655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57329368132037758044884873 42997026099028318533663655)
      ·
        refine ⟨64495539148542477800495483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42997026099028318533663655 64495539148542477800495483)
        ·
          refine ⟨96743308722813716700743225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64495539148542477800495483 96743308722813716700743225)
          ·
            refine ⟨72557481542110287525557419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96743308722813716700743225 72557481542110287525557419)
            ·
              refine ⟨108836222313165431288336129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72557481542110287525557419 108836222313165431288336129)
              ·
                refine ⟨81627166734874073466252097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108836222313165431288336129 81627166734874073466252097)
                ·
                  refine ⟨61220375051155555099689073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81627166734874073466252097 61220375051155555099689073)
                  ·
                    refine ⟨45915281288366666324766805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61220375051155555099689073 45915281288366666324766805)
                    ·
                      refine ⟨538069702598046870993361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 45915281288366666324766805 538069702598046870993361)
                      ·
                        rfl

theorem cell23_1047887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_1047887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047887 prefixEnd_1047887 := by exact prefixLift 1047887
  have htrace : WordTrace (prefixWord ++ tailWord_1047887) baseStart_1047887 baseEnd_1047887 := by
    simpa [prefixWord, tailWord_1047887, baseEnd_1047887] using wordTrace_append hprefix tailTrace_1047887
  have hstable : (prefixWord ++ tailWord_1047887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047887).length < 2 ^ (prefixWord ++ tailWord_1047887).sum := by decide
  have hdescent : baseEnd_1047887 < baseStart_1047887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047911 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_1047911 : Nat := 118140960795 + 1047911 * 2 ^ 59
def prefixEnd_1047911 : Nat := 4983230072969 + 3 ^ 40 * 1047911 * 2
def baseEnd_1047911 : Nat := 538082026133754777093251

theorem tailTrace_1047911 : CollatzResearch.WordTrace tailWord_1047911 prefixEnd_1047911 538082026133754777093251 := by
  unfold tailWord_1047911
  simp only [CollatzResearch.WordTrace]
  refine ⟨38220454106604890795463587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25480302737736593863642391 38220454106604890795463587)
  ·
    refine ⟨57330681159907336193195381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38220454106604890795463587 57330681159907336193195381)
    ·
      refine ⟨5374751358741312768112067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57330681159907336193195381 5374751358741312768112067)
      ·
        refine ⟨8062127038111969152168101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5374751358741312768112067 8062127038111969152168101)
        ·
          refine ⟨1511648819645994216031519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8062127038111969152168101 1511648819645994216031519)
          ·
            refine ⟨2267473229468991324047279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511648819645994216031519 2267473229468991324047279)
            ·
              refine ⟨3401209844203486986070919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2267473229468991324047279 3401209844203486986070919)
              ·
                refine ⟨5101814766305230479106379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3401209844203486986070919 5101814766305230479106379)
                ·
                  refine ⟨7652722149457845718659569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5101814766305230479106379 7652722149457845718659569)
                  ·
                    refine ⟨5739541612093384288994677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7652722149457845718659569 5739541612093384288994677)
                    ·
                      refine ⟨538082026133754777093251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5739541612093384288994677 538082026133754777093251)
                      ·
                        rfl

theorem cell23_1047911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_1047911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047911 prefixEnd_1047911 := by exact prefixLift 1047911
  have htrace : WordTrace (prefixWord ++ tailWord_1047911) baseStart_1047911 baseEnd_1047911 := by
    simpa [prefixWord, tailWord_1047911, baseEnd_1047911] using wordTrace_append hprefix tailTrace_1047911
  have hstable : (prefixWord ++ tailWord_1047911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047911).length < 2 ^ (prefixWord ++ tailWord_1047911).sum := by decide
  have hdescent : baseEnd_1047911 < baseStart_1047911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047921 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 2, 4, 2]
def baseStart_1047921 : Nat := 118140960795 + 1047921 * 2 ^ 59
def prefixEnd_1047921 : Nat := 4983230072969 + 3 ^ 40 * 1047921 * 2
def baseEnd_1047921 : Nat := 538087160940299737968205

theorem tailTrace_1047921 : CollatzResearch.WordTrace tailWord_1047921 prefixEnd_1047921 538087160940299737968205 := by
  unfold tailWord_1047921
  simp only [CollatzResearch.WordTrace]
  refine ⟨38220818836568662503327617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25480545891045775002218411 38220818836568662503327617)
  ·
    refine ⟨28665614127426496877495713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38220818836568662503327617 28665614127426496877495713)
    ·
      refine ⟨21499210595569872658121785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28665614127426496877495713 21499210595569872658121785)
      ·
        refine ⟨16124407946677404493591339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21499210595569872658121785 16124407946677404493591339)
        ·
          refine ⟨24186611920016106740387009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16124407946677404493591339 24186611920016106740387009)
          ·
            refine ⟨18139958940012080055290257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24186611920016106740387009 18139958940012080055290257)
            ·
              refine ⟨13604969205009060041467693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18139958940012080055290257 13604969205009060041467693)
              ·
                refine ⟨5101863451878397515550385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13604969205009060041467693 5101863451878397515550385)
                ·
                  refine ⟨3826397588908798136662789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5101863451878397515550385 3826397588908798136662789)
                  ·
                    refine ⟨717449547920399650624273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3826397588908798136662789 717449547920399650624273)
                    ·
                      refine ⟨538087160940299737968205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 717449547920399650624273 538087160940299737968205)
                      ·
                        rfl

theorem cell23_1047921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_1047921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047921 prefixEnd_1047921 := by exact prefixLift 1047921
  have htrace : WordTrace (prefixWord ++ tailWord_1047921) baseStart_1047921 baseEnd_1047921 := by
    simpa [prefixWord, tailWord_1047921, baseEnd_1047921] using wordTrace_append hprefix tailTrace_1047921
  have hstable : (prefixWord ++ tailWord_1047921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047921).length < 2 ^ (prefixWord ++ tailWord_1047921).sum := by decide
  have hdescent : baseEnd_1047921 < baseStart_1047921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047941 : List Nat := [1, 3, 1, 1, 3, 1, 3, 3, 2, 2, 3]
def baseStart_1047941 : Nat := 118140960795 + 1047941 * 2 ^ 59
def prefixEnd_1047941 : Nat := 4983230072969 + 3 ^ 40 * 1047941 * 2
def baseEnd_1047941 : Nat := 538097430553389659718113

theorem tailTrace_1047941 : CollatzResearch.WordTrace tailWord_1047941 prefixEnd_1047941 538097430553389659718113 := by
  unfold tailWord_1047941
  simp only [CollatzResearch.WordTrace]
  refine ⟨38221548296496205919055677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25481032197664137279370451 38221548296496205919055677)
  ·
    refine ⟨14333080611186077219645879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38221548296496205919055677 14333080611186077219645879)
    ·
      refine ⟨21499620916779115829468819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14333080611186077219645879 21499620916779115829468819)
      ·
        refine ⟨32249431375168673744203229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21499620916779115829468819 32249431375168673744203229)
        ·
          refine ⟨12093536765688252654076211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32249431375168673744203229 12093536765688252654076211)
          ·
            refine ⟨18140305148532378981114317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12093536765688252654076211 18140305148532378981114317)
            ·
              refine ⟨6802614430699642117917869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18140305148532378981114317 6802614430699642117917869)
              ·
                refine ⟨2550980411512365794219201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6802614430699642117917869 2550980411512365794219201)
                ·
                  refine ⟨1913235308634274345664401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2550980411512365794219201 1913235308634274345664401)
                  ·
                    refine ⟨1434926481475705759248301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1913235308634274345664401 1434926481475705759248301)
                    ·
                      refine ⟨538097430553389659718113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1434926481475705759248301 538097430553389659718113)
                      ·
                        rfl

theorem cell23_1047941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_1047941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047941 prefixEnd_1047941 := by exact prefixLift 1047941
  have htrace : WordTrace (prefixWord ++ tailWord_1047941) baseStart_1047941 baseEnd_1047941 := by
    simpa [prefixWord, tailWord_1047941, baseEnd_1047941] using wordTrace_append hprefix tailTrace_1047941
  have hstable : (prefixWord ++ tailWord_1047941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047941).length < 2 ^ (prefixWord ++ tailWord_1047941).sum := by decide
  have hdescent : baseEnd_1047941 < baseStart_1047941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047948 : List Nat := [2, 2, 1, 2, 1, 3, 2, 5, 1, 4]
def baseStart_1047948 : Nat := 118140960795 + 1047948 * 2 ^ 59
def prefixEnd_1047948 : Nat := 4983230072969 + 3 ^ 40 * 1047948 * 2
def baseEnd_1047948 : Nat := 179367008305990377443527

theorem tailTrace_1047948 : CollatzResearch.WordTrace tailWord_1047948 prefixEnd_1047948 179367008305990377443527 := by
  unfold tailWord_1047948
  simp only [CollatzResearch.WordTrace]
  refine ⟨19110901803735423057280249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25481202404980564076373665 19110901803735423057280249)
  ·
    refine ⟨14333176352801567292960187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19110901803735423057280249 14333176352801567292960187)
    ·
      refine ⟨21499764529202350939440281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14333176352801567292960187 21499764529202350939440281)
      ·
        refine ⟨16124823396901763204580211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21499764529202350939440281 16124823396901763204580211)
        ·
          refine ⟨24187235095352644806870317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16124823396901763204580211 24187235095352644806870317)
          ·
            refine ⟨9070213160757241802576369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24187235095352644806870317 9070213160757241802576369)
            ·
              refine ⟨6802659870567931351932277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9070213160757241802576369 6802659870567931351932277)
              ·
                refine ⟨637749362865743564243651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6802659870567931351932277 637749362865743564243651)
                ·
                  refine ⟨956624044298615346365477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637749362865743564243651 956624044298615346365477)
                  ·
                    refine ⟨179367008305990377443527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 956624044298615346365477 179367008305990377443527)
                    ·
                      rfl

theorem cell23_1047948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 1, 4].length) (baseStart_1047948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047948 prefixEnd_1047948 := by exact prefixLift 1047948
  have htrace : WordTrace (prefixWord ++ tailWord_1047948) baseStart_1047948 baseEnd_1047948 := by
    simpa [prefixWord, tailWord_1047948, baseEnd_1047948] using wordTrace_append hprefix tailTrace_1047948
  have hstable : (prefixWord ++ tailWord_1047948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047948).length < 2 ^ (prefixWord ++ tailWord_1047948).sum := by decide
  have hdescent : baseEnd_1047948 < baseStart_1047948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047961 : List Nat := [1, 2, 1, 2, 1, 6, 2, 2, 6]
def baseStart_1047961 : Nat := 118140960795 + 1047961 * 2 ^ 59
def prefixEnd_1047961 : Nat := 4983230072969 + 3 ^ 40 * 1047961 * 2
def baseEnd_1047961 : Nat := 59789744462942175718669

theorem tailTrace_1047961 : CollatzResearch.WordTrace tailWord_1047961 prefixEnd_1047961 59789744462942175718669 := by
  unfold tailWord_1047961
  simp only [CollatzResearch.WordTrace]
  refine ⟨38222277756423749334783737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25481518504282499556522491 38222277756423749334783737)
  ·
    refine ⟨28666708317317812001087803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38222277756423749334783737 28666708317317812001087803)
    ·
      refine ⟨43000062475976718001631705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28666708317317812001087803 43000062475976718001631705)
      ·
        refine ⟨32250046856982538501223779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43000062475976718001631705 32250046856982538501223779)
        ·
          refine ⟨48375070285473807751835669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32250046856982538501223779 48375070285473807751835669)
          ·
            refine ⟨2267581419631584738367297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48375070285473807751835669 2267581419631584738367297)
            ·
              refine ⟨1700686064723688553775473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2267581419631584738367297 1700686064723688553775473)
              ·
                refine ⟨1275514548542766415331605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1700686064723688553775473 1275514548542766415331605)
                ·
                  refine ⟨59789744462942175718669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1275514548542766415331605 59789744462942175718669)
                  ·
                    rfl

theorem cell23_1047961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 6].length) (baseStart_1047961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047961 prefixEnd_1047961 := by exact prefixLift 1047961
  have htrace : WordTrace (prefixWord ++ tailWord_1047961) baseStart_1047961 baseEnd_1047961 := by
    simpa [prefixWord, tailWord_1047961, baseEnd_1047961] using wordTrace_append hprefix tailTrace_1047961
  have hstable : (prefixWord ++ tailWord_1047961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047961).length < 2 ^ (prefixWord ++ tailWord_1047961).sum := by decide
  have hdescent : baseEnd_1047961 < baseStart_1047961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047965 : List Nat := [1, 4, 2, 1, 3, 2, 1, 4, 1, 4]
def baseStart_1047965 : Nat := 118140960795 + 1047965 * 2 ^ 59
def prefixEnd_1047965 : Nat := 4983230072969 + 3 ^ 40 * 1047965 * 2
def baseEnd_1047965 : Nat := 179369918029699188606001

theorem tailTrace_1047965 : CollatzResearch.WordTrace tailWord_1047965 prefixEnd_1047965 179369918029699188606001 := by
  unfold tailWord_1047965
  simp only [CollatzResearch.WordTrace]
  refine ⟨38222423648409258017929349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25481615765606172011952899 38222423648409258017929349)
  ·
    refine ⟨7166704434076735878361753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38222423648409258017929349 7166704434076735878361753)
    ·
      refine ⟨5375028325557551908771315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7166704434076735878361753 5375028325557551908771315)
      ·
        refine ⟨8062542488336327863156973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5375028325557551908771315 8062542488336327863156973)
        ·
          refine ⟨3023453433126122948683865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8062542488336327863156973 3023453433126122948683865)
          ·
            refine ⟨2267590074844592211512899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3023453433126122948683865 2267590074844592211512899)
            ·
              refine ⟨3401385112266888317269349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2267590074844592211512899 3401385112266888317269349)
              ·
                refine ⟨637759708550041559488003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3401385112266888317269349 637759708550041559488003)
                ·
                  refine ⟨956639562825062339232005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637759708550041559488003 956639562825062339232005)
                  ·
                    refine ⟨179369918029699188606001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 956639562825062339232005 179369918029699188606001)
                    ·
                      rfl

theorem cell23_1047965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_1047965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047965 prefixEnd_1047965 := by exact prefixLift 1047965
  have htrace : WordTrace (prefixWord ++ tailWord_1047965) baseStart_1047965 baseEnd_1047965 := by
    simpa [prefixWord, tailWord_1047965, baseEnd_1047965] using wordTrace_append hprefix tailTrace_1047965
  have hstable : (prefixWord ++ tailWord_1047965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047965).length < 2 ^ (prefixWord ++ tailWord_1047965).sum := by decide
  have hdescent : baseEnd_1047965 < baseStart_1047965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047991 : List Nat := [1, 1, 3, 1, 3, 2, 2, 4, 1, 5]
def baseStart_1047991 : Nat := 118140960795 + 1047991 * 2 ^ 59
def prefixEnd_1047991 : Nat := 4983230072969 + 3 ^ 40 * 1047991 * 2
def baseEnd_1047991 : Nat := 179374368195371488030961

theorem tailTrace_1047991 : CollatzResearch.WordTrace tailWord_1047991 prefixEnd_1047991 179374368195371488030961 := by
  unfold tailWord_1047991
  simp only [CollatzResearch.WordTrace]
  refine ⟨38223371946315064458375827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25482247964210042972250551 38223371946315064458375827)
  ·
    refine ⟨57335057919472596687563741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38223371946315064458375827 57335057919472596687563741)
    ·
      refine ⟨21500646719802223757836403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57335057919472596687563741 21500646719802223757836403)
      ·
        refine ⟨32250970079703335636754605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21500646719802223757836403 32250970079703335636754605)
        ·
          refine ⟨12094113779888750863782977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32250970079703335636754605 12094113779888750863782977)
          ·
            refine ⟨9070585334916563147837233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12094113779888750863782977 9070585334916563147837233)
            ·
              refine ⟨6802939001187422360877925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9070585334916563147837233 6802939001187422360877925)
              ·
                refine ⟨1275551062722641692664611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6802939001187422360877925 1275551062722641692664611)
                ·
                  refine ⟨1913326594083962538996917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1275551062722641692664611 1913326594083962538996917)
                  ·
                    refine ⟨179374368195371488030961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1913326594083962538996917 179374368195371488030961)
                    ·
                      rfl

theorem cell23_1047991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_1047991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047991 prefixEnd_1047991 := by exact prefixLift 1047991
  have htrace : WordTrace (prefixWord ++ tailWord_1047991) baseStart_1047991 baseEnd_1047991 := by
    simpa [prefixWord, tailWord_1047991, baseEnd_1047991] using wordTrace_append hprefix tailTrace_1047991
  have hstable : (prefixWord ++ tailWord_1047991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047991).length < 2 ^ (prefixWord ++ tailWord_1047991).sum := by decide
  have hdescent : baseEnd_1047991 < baseStart_1047991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048022 : List Nat := [5, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_1048022 : Nat := 118140960795 + 1048022 * 2 ^ 59
def prefixEnd_1048022 : Nat := 4983230072969 + 3 ^ 40 * 1048022 * 2
def baseEnd_1048022 : Nat := 538139022486403842805241

theorem tailTrace_1048022 : CollatzResearch.WordTrace tailWord_1048022 prefixEnd_1048022 538139022486403842805241 := by
  unfold tailWord_1048022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2389031413075172297047145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25483001739468504501836213 2389031413075172297047145)
  ·
    refine ⟨1791773559806379222785359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2389031413075172297047145 1791773559806379222785359)
    ·
      refine ⟨2687660339709568834178039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1791773559806379222785359 2687660339709568834178039)
      ·
        refine ⟨4031490509564353251267059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2687660339709568834178039 4031490509564353251267059)
        ·
          refine ⟨6047235764346529876900589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4031490509564353251267059 6047235764346529876900589)
          ·
            refine ⟨2267713411629948703837721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6047235764346529876900589 2267713411629948703837721)
            ·
              refine ⟨1700785058722461527878291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2267713411629948703837721 1700785058722461527878291)
              ·
                refine ⟨2551177588083692291817437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700785058722461527878291 2551177588083692291817437)
                ·
                  refine ⟨956691595531384609431539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2551177588083692291817437 956691595531384609431539)
                  ·
                    refine ⟨1435037393297076914147309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 956691595531384609431539 1435037393297076914147309)
                    ·
                      refine ⟨538139022486403842805241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1435037393297076914147309 538139022486403842805241)
                      ·
                        rfl

theorem cell23_1048022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_1048022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048022 prefixEnd_1048022 := by exact prefixLift 1048022
  have htrace : WordTrace (prefixWord ++ tailWord_1048022) baseStart_1048022 baseEnd_1048022 := by
    simpa [prefixWord, tailWord_1048022, baseEnd_1048022] using wordTrace_append hprefix tailTrace_1048022
  have hstable : (prefixWord ++ tailWord_1048022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048022).length < 2 ^ (prefixWord ++ tailWord_1048022).sum := by decide
  have hdescent : baseEnd_1048022 < baseStart_1048022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048031 : List Nat := [1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 5]
def baseStart_1048031 : Nat := 118140960795 + 1048031 * 2 ^ 59
def prefixEnd_1048031 : Nat := 4983230072969 + 3 ^ 40 * 1048031 * 2
def baseEnd_1048031 : Nat := 538143643812294307592699

theorem tailTrace_1048031 : CollatzResearch.WordTrace tailWord_1048031 prefixEnd_1048031 538143643812294307592699 := by
  unfold tailWord_1048031
  simp only [CollatzResearch.WordTrace]
  refine ⟨38224830866170151289831947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25483220577446767526554631 38224830866170151289831947)
  ·
    refine ⟨57337246299255226934747921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38224830866170151289831947 57337246299255226934747921)
    ·
      refine ⟨43002934724441420201060941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57337246299255226934747921 43002934724441420201060941)
      ·
        refine ⟨16126100521665532575397853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43002934724441420201060941 16126100521665532575397853)
        ·
          refine ⟨6047287695624574715774195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16126100521665532575397853 6047287695624574715774195)
          ·
            refine ⟨9070931543436862073661293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6047287695624574715774195 9070931543436862073661293)
            ·
              refine ⟨3401599328788823277622985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9070931543436862073661293 3401599328788823277622985)
              ·
                refine ⟨2551199496591617458217239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3401599328788823277622985 2551199496591617458217239)
                ·
                  refine ⟨3826799244887426187325859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2551199496591617458217239 3826799244887426187325859)
                  ·
                    refine ⟨5740198867331139280988789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3826799244887426187325859 5740198867331139280988789)
                    ·
                      refine ⟨538143643812294307592699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5740198867331139280988789 538143643812294307592699)
                      ·
                        rfl

theorem cell23_1048031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_1048031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048031 prefixEnd_1048031 := by exact prefixLift 1048031
  have htrace : WordTrace (prefixWord ++ tailWord_1048031) baseStart_1048031 baseEnd_1048031 := by
    simpa [prefixWord, tailWord_1048031, baseEnd_1048031] using wordTrace_append hprefix tailTrace_1048031
  have hstable : (prefixWord ++ tailWord_1048031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048031).length < 2 ^ (prefixWord ++ tailWord_1048031).sum := by decide
  have hdescent : baseEnd_1048031 < baseStart_1048031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048048 : List Nat := [2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 3]
def baseStart_1048048 : Nat := 118140960795 + 1048048 * 2 ^ 59
def prefixEnd_1048048 : Nat := 4983230072969 + 3 ^ 40 * 1048048 * 2
def baseEnd_1048048 : Nat := 538152372983420741080121

theorem tailTrace_1048048 : CollatzResearch.WordTrace tailWord_1048048 prefixEnd_1048048 538152372983420741080121 := by
  unfold tailWord_1048048
  simp only [CollatzResearch.WordTrace]
  refine ⟨19112725453554281596600399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25483633938072375462133865 19112725453554281596600399)
  ·
    refine ⟨28669088180331422394900599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19112725453554281596600399 28669088180331422394900599)
    ·
      refine ⟨43003632270497133592350899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28669088180331422394900599 43003632270497133592350899)
      ·
        refine ⟨64505448405745700388526349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43003632270497133592350899 64505448405745700388526349)
        ·
          refine ⟨24189543152154637645697381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64505448405745700388526349 24189543152154637645697381)
          ·
            refine ⟨4535539341028994558568259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24189543152154637645697381 4535539341028994558568259)
            ·
              refine ⟨6803309011543491837852389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4535539341028994558568259 6803309011543491837852389)
              ·
                refine ⟨1275620439664404719597323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6803309011543491837852389 1275620439664404719597323)
                ·
                  refine ⟨1913430659496607079395985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1275620439664404719597323 1913430659496607079395985)
                  ·
                    refine ⟨1435072994622455309546989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1913430659496607079395985 1435072994622455309546989)
                    ·
                      refine ⟨538152372983420741080121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1435072994622455309546989 538152372983420741080121)
                      ·
                        rfl

theorem cell23_1048048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 3].length) (baseStart_1048048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048048 prefixEnd_1048048 := by exact prefixLift 1048048
  have htrace : WordTrace (prefixWord ++ tailWord_1048048) baseStart_1048048 baseEnd_1048048 := by
    simpa [prefixWord, tailWord_1048048, baseEnd_1048048] using wordTrace_append hprefix tailTrace_1048048
  have hstable : (prefixWord ++ tailWord_1048048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048048).length < 2 ^ (prefixWord ++ tailWord_1048048).sum := by decide
  have hdescent : baseEnd_1048048 < baseStart_1048048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048068 : List Nat := [2, 3, 2, 3, 2, 2, 9]
def baseStart_1048068 : Nat := 118140960795 + 1048068 * 2 ^ 59
def prefixEnd_1048068 : Nat := 4983230072969 + 3 ^ 40 * 1048068 * 2
def baseEnd_1048068 : Nat := 6643983241932230405309

theorem tailTrace_1048068 : CollatzResearch.WordTrace tailWord_1048068 prefixEnd_1048068 6643983241932230405309 := by
  unfold tailWord_1048068
  simp only [CollatzResearch.WordTrace]
  refine ⟨19113090183518053304464429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25484120244690737739285905 19113090183518053304464429)
  ·
    refine ⟨7167408818819269989174161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19113090183518053304464429 7167408818819269989174161)
    ·
      refine ⟨5375556614114452491880621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7167408818819269989174161 5375556614114452491880621)
      ·
        refine ⟨2015833730292919684455233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5375556614114452491880621 2015833730292919684455233)
        ·
          refine ⟨1511875297719689763341425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2015833730292919684455233 1511875297719689763341425)
          ·
            refine ⟨1133906473289767322506069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1511875297719689763341425 1133906473289767322506069)
            ·
              refine ⟨6643983241932230405309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1133906473289767322506069 6643983241932230405309)
              ·
                rfl

theorem cell23_1048068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 9].length) (baseStart_1048068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048068 prefixEnd_1048068 := by exact prefixLift 1048068
  have htrace : WordTrace (prefixWord ++ tailWord_1048068) baseStart_1048068 baseEnd_1048068 := by
    simpa [prefixWord, tailWord_1048068, baseEnd_1048068] using wordTrace_append hprefix tailTrace_1048068
  have hstable : (prefixWord ++ tailWord_1048068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048068).length < 2 ^ (prefixWord ++ tailWord_1048068).sum := by decide
  have hdescent : baseEnd_1048068 < baseStart_1048068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048122 : List Nat := [3, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2]
def baseStart_1048122 : Nat := 118140960795 + 1048122 * 2 ^ 59
def prefixEnd_1048122 : Nat := 4983230072969 + 3 ^ 40 * 1048122 * 2
def baseEnd_1048122 : Nat := 538190370551853451554781

theorem tailTrace_1048122 : CollatzResearch.WordTrace tailWord_1048122 prefixEnd_1048122 538190370551853451554781 := by
  unfold tailWord_1048122
  simp only [CollatzResearch.WordTrace]
  refine ⟨9557037477210118457848655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25485433272560315887596413 9557037477210118457848655)
  ·
    refine ⟨14335556215815177686772983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9557037477210118457848655 14335556215815177686772983)
    ·
      refine ⟨21503334323722766530159475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14335556215815177686772983 21503334323722766530159475)
      ·
        refine ⟨32255001485584149795239213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21503334323722766530159475 32255001485584149795239213)
        ·
          refine ⟨12095625557094056173214705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32255001485584149795239213 12095625557094056173214705)
          ·
            refine ⟨9071719167820542129911029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12095625557094056173214705 9071719167820542129911029)
            ·
              refine ⟨850473671983175824679159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9071719167820542129911029 850473671983175824679159)
              ·
                refine ⟨1275710507974763737018739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850473671983175824679159 1275710507974763737018739)
                ·
                  refine ⟨1913565761962145605528109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1275710507974763737018739 1913565761962145605528109)
                  ·
                    refine ⟨717587160735804602073041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1913565761962145605528109 717587160735804602073041)
                    ·
                      refine ⟨538190370551853451554781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 717587160735804602073041 538190370551853451554781)
                      ·
                        rfl

theorem cell23_1048122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2].length) (baseStart_1048122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048122 prefixEnd_1048122 := by exact prefixLift 1048122
  have htrace : WordTrace (prefixWord ++ tailWord_1048122) baseStart_1048122 baseEnd_1048122 := by
    simpa [prefixWord, tailWord_1048122, baseEnd_1048122] using wordTrace_append hprefix tailTrace_1048122
  have hstable : (prefixWord ++ tailWord_1048122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048122).length < 2 ^ (prefixWord ++ tailWord_1048122).sum := by decide
  have hdescent : baseEnd_1048122 < baseStart_1048122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048148 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_1048148 : Nat := 118140960795 + 1048148 * 2 ^ 59
def prefixEnd_1048148 : Nat := 4983230072969 + 3 ^ 40 * 1048148 * 2
def baseEnd_1048148 : Nat := 538203721048870349829661

theorem tailTrace_1048148 : CollatzResearch.WordTrace tailWord_1048148 prefixEnd_1048148 538203721048870349829661 := by
  unfold tailWord_1048148
  simp only [CollatzResearch.WordTrace]
  refine ⟨19114549103373140135920549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25486065471164186847894065 19114549103373140135920549)
  ·
    refine ⟨3583977956882463775485103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19114549103373140135920549 3583977956882463775485103)
    ·
      refine ⟨5375966935323695663227655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3583977956882463775485103 5375966935323695663227655)
      ·
        refine ⟨8063950402985543494841483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5375966935323695663227655 8063950402985543494841483)
        ·
          refine ⟨12095925604478315242262225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8063950402985543494841483 12095925604478315242262225)
          ·
            refine ⟨9071944203358736431696669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12095925604478315242262225 9071944203358736431696669)
            ·
              refine ⟨3401979076259526161886251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9071944203358736431696669 3401979076259526161886251)
              ·
                refine ⟨5102968614389289242829377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3401979076259526161886251 5102968614389289242829377)
                ·
                  refine ⟨3827226460791966932122033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5102968614389289242829377 3827226460791966932122033)
                  ·
                    refine ⟨2870419845593975199091525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3827226460791966932122033 2870419845593975199091525)
                    ·
                      refine ⟨538203721048870349829661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2870419845593975199091525 538203721048870349829661)
                      ·
                        rfl

theorem cell23_1048148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_1048148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048148 prefixEnd_1048148 := by exact prefixLift 1048148
  have htrace : WordTrace (prefixWord ++ tailWord_1048148) baseStart_1048148 baseEnd_1048148 := by
    simpa [prefixWord, tailWord_1048148, baseEnd_1048148] using wordTrace_append hprefix tailTrace_1048148
  have hstable : (prefixWord ++ tailWord_1048148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048148).length < 2 ^ (prefixWord ++ tailWord_1048148).sum := by decide
  have hdescent : baseEnd_1048148 < baseStart_1048148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048226 : List Nat := [3, 3, 1, 4, 2, 1, 1, 3, 5]
def baseStart_1048226 : Nat := 118140960795 + 1048226 * 2 ^ 59
def prefixEnd_1048226 : Nat := 4983230072969 + 3 ^ 40 * 1048226 * 2
def baseEnd_1048226 : Nat := 59804863615546782739367

theorem tailTrace_1048226 : CollatzResearch.WordTrace tailWord_1048226 prefixEnd_1048226 59804863615546782739367 := by
  unfold tailWord_1048226
  simp only [CollatzResearch.WordTrace]
  refine ⟨9557985775115924898295133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25487962066975799728787021 9557985775115924898295133)
  ·
    refine ⟨3584244665668471836860675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9557985775115924898295133 3584244665668471836860675)
    ·
      refine ⟨5376366998502707755291013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3584244665668471836860675 5376366998502707755291013)
      ·
        refine ⟨1008068812219257704117065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5376366998502707755291013 1008068812219257704117065)
        ·
          refine ⟨756051609164443278087799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1008068812219257704117065 756051609164443278087799)
          ·
            refine ⟨1134077413746664917131699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756051609164443278087799 1134077413746664917131699)
            ·
              refine ⟨1701116120619997375697549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1134077413746664917131699 1701116120619997375697549)
              ·
                refine ⟨637918545232499015886581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1701116120619997375697549 637918545232499015886581)
                ·
                  refine ⟨59804863615546782739367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 637918545232499015886581 59804863615546782739367)
                  ·
                    rfl

theorem cell23_1048226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_1048226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048226 prefixEnd_1048226 := by exact prefixLift 1048226
  have htrace : WordTrace (prefixWord ++ tailWord_1048226) baseStart_1048226 baseEnd_1048226 := by
    simpa [prefixWord, tailWord_1048226, baseEnd_1048226] using wordTrace_append hprefix tailTrace_1048226
  have hstable : (prefixWord ++ tailWord_1048226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048226).length < 2 ^ (prefixWord ++ tailWord_1048226).sum := by decide
  have hdescent : baseEnd_1048226 < baseStart_1048226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048251 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 8]
def baseStart_1048251 : Nat := 118140960795 + 1048251 * 2 ^ 59
def prefixEnd_1048251 : Nat := 4983230072969 + 3 ^ 40 * 1048251 * 2
def baseEnd_1048251 : Nat := 538256609556283446841687

theorem tailTrace_1048251 : CollatzResearch.WordTrace tailWord_1048251 prefixEnd_1048251 538256609556283446841687 := by
  unfold tailWord_1048251
  simp only [CollatzResearch.WordTrace]
  refine ⟨38232854925373128862840607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25488569950248752575227071 38232854925373128862840607)
  ·
    refine ⟨57349282388059693294260911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38232854925373128862840607 57349282388059693294260911)
    ·
      refine ⟨86023923582089539941391367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57349282388059693294260911 86023923582089539941391367)
      ·
        refine ⟨129035885373134309912087051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86023923582089539941391367 129035885373134309912087051)
        ·
          refine ⟨193553828059701464868130577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129035885373134309912087051 193553828059701464868130577)
          ·
            refine ⟨145165371044776098651097933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193553828059701464868130577 145165371044776098651097933)
            ·
              refine ⟨54437014141791036994161725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145165371044776098651097933 54437014141791036994161725)
              ·
                refine ⟨20413880303171638872810647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54437014141791036994161725 20413880303171638872810647)
                ·
                  refine ⟨30620820454757458309215971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20413880303171638872810647 30620820454757458309215971)
                  ·
                    refine ⟨45931230682136187463823957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30620820454757458309215971 45931230682136187463823957)
                    ·
                      refine ⟨538256609556283446841687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 45931230682136187463823957 538256609556283446841687)
                      ·
                        rfl

theorem cell23_1048251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 8].length) (baseStart_1048251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048251 prefixEnd_1048251 := by exact prefixLift 1048251
  have htrace : WordTrace (prefixWord ++ tailWord_1048251) baseStart_1048251 baseEnd_1048251 := by
    simpa [prefixWord, tailWord_1048251, baseEnd_1048251] using wordTrace_append hprefix tailTrace_1048251
  have hstable : (prefixWord ++ tailWord_1048251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048251).length < 2 ^ (prefixWord ++ tailWord_1048251).sum := by decide
  have hdescent : baseEnd_1048251 < baseStart_1048251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048252 : List Nat := [2, 2, 2, 3, 1, 4, 1, 1, 3, 4]
def baseStart_1048252 : Nat := 118140960795 + 1048252 * 2 ^ 59
def prefixEnd_1048252 : Nat := 4983230072969 + 3 ^ 40 * 1048252 * 2
def baseEnd_1048252 : Nat := 179419041012312647643061

theorem tailTrace_1048252 : CollatzResearch.WordTrace tailWord_1048252 prefixEnd_1048252 179419041012312647643061 := by
  unfold tailWord_1048252
  simp only [CollatzResearch.WordTrace]
  refine ⟨19116445699184753016813505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25488594265579670689084673 19116445699184753016813505)
  ·
    refine ⟨14337334274388564762610129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19116445699184753016813505 14337334274388564762610129)
    ·
      refine ⟨10753000705791423571957597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14337334274388564762610129 10753000705791423571957597)
      ·
        refine ⟨4032375264671783839484099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10753000705791423571957597 4032375264671783839484099)
        ·
          refine ⟨6048562897007675759226149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4032375264671783839484099 6048562897007675759226149)
          ·
            refine ⟨1134105543188939204854903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6048562897007675759226149 1134105543188939204854903)
            ·
              refine ⟨1701158314783408807282355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1134105543188939204854903 1701158314783408807282355)
              ·
                refine ⟨2551737472175113210923533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1701158314783408807282355 2551737472175113210923533)
                ·
                  refine ⟨956901552065667454096325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2551737472175113210923533 956901552065667454096325)
                  ·
                    refine ⟨179419041012312647643061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 956901552065667454096325 179419041012312647643061)
                    ·
                      rfl

theorem cell23_1048252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_1048252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048252 prefixEnd_1048252 := by exact prefixLift 1048252
  have htrace : WordTrace (prefixWord ++ tailWord_1048252) baseStart_1048252 baseEnd_1048252 := by
    simpa [prefixWord, tailWord_1048252, baseEnd_1048252] using wordTrace_append hprefix tailTrace_1048252
  have hstable : (prefixWord ++ tailWord_1048252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048252).length < 2 ^ (prefixWord ++ tailWord_1048252).sum := by decide
  have hdescent : baseEnd_1048252 < baseStart_1048252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048302 : List Nat := [4, 1, 2, 1, 1, 2, 1, 4, 2, 3, 2]
def baseStart_1048302 : Nat := 118140960795 + 1048302 * 2 ^ 59
def prefixEnd_1048302 : Nat := 4983230072969 + 3 ^ 40 * 1048302 * 2
def baseEnd_1048302 : Nat := 538282797069662747303953

theorem tailTrace_1048302 : CollatzResearch.WordTrace tailWord_1048302 prefixEnd_1048302 538282797069662747303953 := by
  unfold tailWord_1048302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4779339381023545571618395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25489810032125576381964773 4779339381023545571618395)
  ·
    refine ⟨7169009071535318357427593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4779339381023545571618395 7169009071535318357427593)
    ·
      refine ⟨5376756803651488768070695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7169009071535318357427593 5376756803651488768070695)
      ·
        refine ⟨8065135205477233152106043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5376756803651488768070695 8065135205477233152106043)
        ·
          refine ⟨12097702808215849728159065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8065135205477233152106043 12097702808215849728159065)
          ·
            refine ⟨9073277106161887296119299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12097702808215849728159065 9073277106161887296119299)
            ·
              refine ⟨13609915659242830944178949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9073277106161887296119299 13609915659242830944178949)
              ·
                refine ⟨2551859186108030802033553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13609915659242830944178949 2551859186108030802033553)
                ·
                  refine ⟨1913894389581023101525165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2551859186108030802033553 1913894389581023101525165)
                  ·
                    refine ⟨717710396092883663071937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1913894389581023101525165 717710396092883663071937)
                    ·
                      refine ⟨538282797069662747303953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 717710396092883663071937 538282797069662747303953)
                      ·
                        rfl

theorem cell23_1048302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_1048302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048302 prefixEnd_1048302 := by exact prefixLift 1048302
  have htrace : WordTrace (prefixWord ++ tailWord_1048302) baseStart_1048302 baseEnd_1048302 := by
    simpa [prefixWord, tailWord_1048302, baseEnd_1048302] using wordTrace_append hprefix tailTrace_1048302
  have hstable : (prefixWord ++ tailWord_1048302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048302).length < 2 ^ (prefixWord ++ tailWord_1048302).sum := by decide
  have hdescent : baseEnd_1048302 < baseStart_1048302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048332 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 5, 2, 2]
def baseStart_1048332 : Nat := 118140960795 + 1048332 * 2 ^ 59
def prefixEnd_1048332 : Nat := 4983230072969 + 3 ^ 40 * 1048332 * 2
def baseEnd_1048332 : Nat := 538298201489297629928815

theorem tailTrace_1048332 : CollatzResearch.WordTrace tailWord_1048332 prefixEnd_1048332 538298201489297629928815 := by
  unfold tailWord_1048332
  simp only [CollatzResearch.WordTrace]
  refine ⟨19117904619039839848269625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25490539492053119797692833 19117904619039839848269625)
  ·
    refine ⟨14338428464279879886202219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19117904619039839848269625 14338428464279879886202219)
    ·
      refine ⟨21507642696419819829303329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14338428464279879886202219 21507642696419819829303329)
      ·
        refine ⟨16130732022314864871977497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21507642696419819829303329 16130732022314864871977497)
        ·
          refine ⟨12098049016736148653983123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16130732022314864871977497 12098049016736148653983123)
          ·
            refine ⟨18147073525104222980974685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12098049016736148653983123 18147073525104222980974685)
            ·
              refine ⟨6805152571914083617865507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18147073525104222980974685 6805152571914083617865507)
              ·
                refine ⟨10207728857871125426798261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6805152571914083617865507 10207728857871125426798261)
                ·
                  refine ⟨956974580425418008762337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10207728857871125426798261 956974580425418008762337)
                  ·
                    refine ⟨717730935319063506571753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 956974580425418008762337 717730935319063506571753)
                    ·
                      refine ⟨538298201489297629928815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 717730935319063506571753 538298201489297629928815)
                      ·
                        rfl

theorem cell23_1048332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_1048332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048332 prefixEnd_1048332 := by exact prefixLift 1048332
  have htrace : WordTrace (prefixWord ++ tailWord_1048332) baseStart_1048332 baseEnd_1048332 := by
    simpa [prefixWord, tailWord_1048332, baseEnd_1048332] using wordTrace_append hprefix tailTrace_1048332
  have hstable : (prefixWord ++ tailWord_1048332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048332).length < 2 ^ (prefixWord ++ tailWord_1048332).sum := by decide
  have hdescent : baseEnd_1048332 < baseStart_1048332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048352 : List Nat := [2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 3]
def baseStart_1048352 : Nat := 118140960795 + 1048352 * 2 ^ 59
def prefixEnd_1048352 : Nat := 4983230072969 + 3 ^ 40 * 1048352 * 2
def baseEnd_1048352 : Nat := 538308471102387551678723

theorem tailTrace_1048352 : CollatzResearch.WordTrace tailWord_1048352 prefixEnd_1048352 538308471102387551678723 := by
  unfold tailWord_1048352
  simp only [CollatzResearch.WordTrace]
  refine ⟨19118269349003611556133655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25491025798671482074844873 19118269349003611556133655)
  ·
    refine ⟨28677404023505417334200483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19118269349003611556133655 28677404023505417334200483)
    ·
      refine ⟨43016106035258126001300725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28677404023505417334200483 43016106035258126001300725)
      ·
        refine ⟨4032759940805449312621943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43016106035258126001300725 4032759940805449312621943)
        ·
          refine ⟨6049139911208173968932915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4032759940805449312621943 6049139911208173968932915)
          ·
            refine ⟨9073709866812260953399373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6049139911208173968932915 9073709866812260953399373)
            ·
              refine ⟨3402641200054597857524765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9073709866812260953399373 3402641200054597857524765)
              ·
                refine ⟨1275990450020474196571787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3402641200054597857524765 1275990450020474196571787)
                ·
                  refine ⟨1913985675030711294857681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1275990450020474196571787 1913985675030711294857681)
                  ·
                    refine ⟨1435489256273033471143261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1913985675030711294857681 1435489256273033471143261)
                    ·
                      refine ⟨538308471102387551678723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1435489256273033471143261 538308471102387551678723)
                      ·
                        rfl

theorem cell23_1048352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_1048352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048352 prefixEnd_1048352 := by exact prefixLift 1048352
  have htrace : WordTrace (prefixWord ++ tailWord_1048352) baseStart_1048352 baseEnd_1048352 := by
    simpa [prefixWord, tailWord_1048352, baseEnd_1048352] using wordTrace_append hprefix tailTrace_1048352
  have hstable : (prefixWord ++ tailWord_1048352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048352).length < 2 ^ (prefixWord ++ tailWord_1048352).sum := by decide
  have hdescent : baseEnd_1048352 < baseStart_1048352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048375 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 2, 7, 2]
def baseStart_1048375 : Nat := 118140960795 + 1048375 * 2 ^ 59
def prefixEnd_1048375 : Nat := 4983230072969 + 3 ^ 40 * 1048375 * 2
def baseEnd_1048375 : Nat := 538320281157440961691117

theorem tailTrace_1048375 : CollatzResearch.WordTrace tailWord_1048375 prefixEnd_1048375 538320281157440961691117 := by
  unfold tailWord_1048375
  simp only [CollatzResearch.WordTrace]
  refine ⟨38237377576923898040354579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25491585051282598693569719 38237377576923898040354579)
  ·
    refine ⟨57356066365385847060531869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38237377576923898040354579 57356066365385847060531869)
    ·
      refine ⟨21508524887019692647699451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57356066365385847060531869 21508524887019692647699451)
      ·
        refine ⟨32262787330529538971549177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21508524887019692647699451 32262787330529538971549177)
        ·
          refine ⟨24197090497897154228661883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32262787330529538971549177 24197090497897154228661883)
          ·
            refine ⟨36295635746845731342992825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24197090497897154228661883 36295635746845731342992825)
            ·
              refine ⟨27221726810134298507244619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36295635746845731342992825 27221726810134298507244619)
              ·
                refine ⟨40832590215201447760866929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27221726810134298507244619 40832590215201447760866929)
                ·
                  refine ⟨30624442661401085820650197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40832590215201447760866929 30624442661401085820650197)
                  ·
                    refine ⟨717760374876587948921489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30624442661401085820650197 717760374876587948921489)
                    ·
                      refine ⟨538320281157440961691117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 717760374876587948921489 538320281157440961691117)
                      ·
                        rfl

theorem cell23_1048375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 7, 2].length) (baseStart_1048375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048375 prefixEnd_1048375 := by exact prefixLift 1048375
  have htrace : WordTrace (prefixWord ++ tailWord_1048375) baseStart_1048375 baseEnd_1048375 := by
    simpa [prefixWord, tailWord_1048375, baseEnd_1048375] using wordTrace_append hprefix tailTrace_1048375
  have hstable : (prefixWord ++ tailWord_1048375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048375).length < 2 ^ (prefixWord ++ tailWord_1048375).sum := by decide
  have hdescent : baseEnd_1048375 < baseStart_1048375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048479 : List Nat := [1, 1, 2, 5, 3, 1, 1, 4, 5]
def baseStart_1048479 : Nat := 118140960795 + 1048479 * 2 ^ 59
def prefixEnd_1048479 : Nat := 4983230072969 + 3 ^ 40 * 1048479 * 2
def baseEnd_1048479 : Nat := 59819298127278728310071

theorem tailTrace_1048479 : CollatzResearch.WordTrace tailWord_1048479 prefixEnd_1048479 59819298127278728310071 := by
  unfold tailWord_1048479
  simp only [CollatzResearch.WordTrace]
  refine ⟨38241170768547123802140491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25494113845698082534760327 38241170768547123802140491)
  ·
    refine ⟨57361756152820685703210737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38241170768547123802140491 57361756152820685703210737)
    ·
      refine ⟨43021317114615514277408053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57361756152820685703210737 43021317114615514277408053)
      ·
        refine ⟨4033248479495204463507005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43021317114615514277408053 4033248479495204463507005)
        ·
          refine ⟨1512468179810701673815127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4033248479495204463507005 1512468179810701673815127)
          ·
            refine ⟨2268702269716052510722691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1512468179810701673815127 2268702269716052510722691)
            ·
              refine ⟨3403053404574078766084037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2268702269716052510722691 3403053404574078766084037)
              ·
                refine ⟨638072513357639768640757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3403053404574078766084037 638072513357639768640757)
                ·
                  refine ⟨59819298127278728310071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 638072513357639768640757 59819298127278728310071)
                  ·
                    rfl

theorem cell23_1048479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 5].length) (baseStart_1048479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048479 prefixEnd_1048479 := by exact prefixLift 1048479
  have htrace : WordTrace (prefixWord ++ tailWord_1048479) baseStart_1048479 baseEnd_1048479 := by
    simpa [prefixWord, tailWord_1048479, baseEnd_1048479] using wordTrace_append hprefix tailTrace_1048479
  have hstable : (prefixWord ++ tailWord_1048479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048479).length < 2 ^ (prefixWord ++ tailWord_1048479).sum := by decide
  have hdescent : baseEnd_1048479 < baseStart_1048479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048495 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 4]
def baseStart_1048495 : Nat := 118140960795 + 1048495 * 2 ^ 59
def prefixEnd_1048495 : Nat := 4983230072969 + 3 ^ 40 * 1048495 * 2
def baseEnd_1048495 : Nat := 538381898835980492190565

theorem tailTrace_1048495 : CollatzResearch.WordTrace tailWord_1048495 prefixEnd_1048495 538381898835980492190565 := by
  unfold tailWord_1048495
  simp only [CollatzResearch.WordTrace]
  refine ⟨38241754336489158534722939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25494502890992772356481959 38241754336489158534722939)
  ·
    refine ⟨57362631504733737802084409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38241754336489158534722939 57362631504733737802084409)
    ·
      refine ⟨43021973628550303351563307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57362631504733737802084409 43021973628550303351563307)
      ·
        refine ⟨64532960442825455027344961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43021973628550303351563307 64532960442825455027344961)
        ·
          refine ⟨48399720332119091270508721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64532960442825455027344961 48399720332119091270508721)
          ·
            refine ⟨36299790249089318452881541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48399720332119091270508721 36299790249089318452881541)
            ·
              refine ⟨6806210671704247209915289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36299790249089318452881541 6806210671704247209915289)
              ·
                refine ⟨5104658003778185407436467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6806210671704247209915289 5104658003778185407436467)
                ·
                  refine ⟨7656987005667278111154701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5104658003778185407436467 7656987005667278111154701)
                  ·
                    refine ⟨2871370127125229291683013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7656987005667278111154701 2871370127125229291683013)
                    ·
                      refine ⟨538381898835980492190565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2871370127125229291683013 538381898835980492190565)
                      ·
                        rfl

theorem cell23_1048495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_1048495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048495 prefixEnd_1048495 := by exact prefixLift 1048495
  have htrace : WordTrace (prefixWord ++ tailWord_1048495) baseStart_1048495 baseEnd_1048495 := by
    simpa [prefixWord, tailWord_1048495, baseEnd_1048495] using wordTrace_append hprefix tailTrace_1048495
  have hstable : (prefixWord ++ tailWord_1048495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048495).length < 2 ^ (prefixWord ++ tailWord_1048495).sum := by decide
  have hdescent : baseEnd_1048495 < baseStart_1048495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048509 : List Nat := [1, 4, 1, 2, 3, 3, 1, 1, 2, 5]
def baseStart_1048509 : Nat := 118140960795 + 1048509 * 2 ^ 59
def prefixEnd_1048509 : Nat := 4983230072969 + 3 ^ 40 * 1048509 * 2
def baseEnd_1048509 : Nat := 179463029188381145805167

theorem tailTrace_1048509 : CollatzResearch.WordTrace tailWord_1048509 prefixEnd_1048509 179463029188381145805167 := by
  unfold tailWord_1048509
  simp only [CollatzResearch.WordTrace]
  refine ⟨38242264958438438925732581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25494843305625625950488387 38242264958438438925732581)
  ·
    refine ⟨7170424679707207298574859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38242264958438438925732581 7170424679707207298574859)
    ·
      refine ⟨10755637019560810947862289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7170424679707207298574859 10755637019560810947862289)
      ·
        refine ⟨8066727764670608210896717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10755637019560810947862289 8066727764670608210896717)
        ·
          refine ⟨3025022911751478079086269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8066727764670608210896717 3025022911751478079086269)
          ·
            refine ⟨1134383591906804279657351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3025022911751478079086269 1134383591906804279657351)
            ·
              refine ⟨1701575387860206419486027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1134383591906804279657351 1701575387860206419486027)
              ·
                refine ⟨2552363081790309629229041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1701575387860206419486027 2552363081790309629229041)
                ·
                  refine ⟨1914272311342732221921781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2552363081790309629229041 1914272311342732221921781)
                  ·
                    refine ⟨179463029188381145805167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1914272311342732221921781 179463029188381145805167)
                    ·
                      rfl

theorem cell23_1048509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_1048509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048509 prefixEnd_1048509 := by exact prefixLift 1048509
  have htrace : WordTrace (prefixWord ++ tailWord_1048509) baseStart_1048509 baseEnd_1048509 := by
    simpa [prefixWord, tailWord_1048509, baseEnd_1048509] using wordTrace_append hprefix tailTrace_1048509
  have hstable : (prefixWord ++ tailWord_1048509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048509).length < 2 ^ (prefixWord ++ tailWord_1048509).sum := by decide
  have hdescent : baseEnd_1048509 < baseStart_1048509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048512 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 1, 6, 2]
def baseStart_1048512 : Nat := 118140960795 + 1048512 * 2 ^ 59
def prefixEnd_1048512 : Nat := 4983230072969 + 3 ^ 40 * 1048512 * 2
def baseEnd_1048512 : Nat := 538390628007106925677987

theorem tailTrace_1048512 : CollatzResearch.WordTrace tailWord_1048512 prefixEnd_1048512 538390628007106925677987 := by
  unfold tailWord_1048512
  simp only [CollatzResearch.WordTrace]
  refine ⟨19121187188713785219045895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25494916251618380292061193 19121187188713785219045895)
  ·
    refine ⟨28681780783070677828568843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19121187188713785219045895 28681780783070677828568843)
    ·
      refine ⟨43022671174606016742853265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28681780783070677828568843 43022671174606016742853265)
      ·
        refine ⟨32267003380954512557139949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43022671174606016742853265 32267003380954512557139949)
        ·
          refine ⟨12100126267857942208927481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32267003380954512557139949 12100126267857942208927481)
          ·
            refine ⟨9075094700893456656695611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12100126267857942208927481 9075094700893456656695611)
            ·
              refine ⟨13612642051340184985043417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9075094700893456656695611 13612642051340184985043417)
              ·
                refine ⟨10209481538505138738782563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13612642051340184985043417 10209481538505138738782563)
                ·
                  refine ⟨15314222307757708108173845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10209481538505138738782563 15314222307757708108173845)
                  ·
                    refine ⟨717854170676142567570649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15314222307757708108173845 717854170676142567570649)
                    ·
                      refine ⟨538390628007106925677987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 717854170676142567570649 538390628007106925677987)
                      ·
                        rfl

theorem cell23_1048512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 6, 2].length) (baseStart_1048512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048512 prefixEnd_1048512 := by exact prefixLift 1048512
  have htrace : WordTrace (prefixWord ++ tailWord_1048512) baseStart_1048512 baseEnd_1048512 := by
    simpa [prefixWord, tailWord_1048512, baseEnd_1048512] using wordTrace_append hprefix tailTrace_1048512
  have hstable : (prefixWord ++ tailWord_1048512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048512).length < 2 ^ (prefixWord ++ tailWord_1048512).sum := by decide
  have hdescent : baseEnd_1048512 < baseStart_1048512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048535 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 8]
def baseStart_1048535 : Nat := 118140960795 + 1048535 * 2 ^ 59
def prefixEnd_1048535 : Nat := 4983230072969 + 3 ^ 40 * 1048535 * 2
def baseEnd_1048535 : Nat := 59822493118017815076709

theorem tailTrace_1048535 : CollatzResearch.WordTrace tailWord_1048535 prefixEnd_1048535 59822493118017815076709 := by
  unfold tailWord_1048535
  simp only [CollatzResearch.WordTrace]
  refine ⟨38243213256344245366179059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25495475504229496910786039 38243213256344245366179059)
  ·
    refine ⟨57364819884516368049268589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38243213256344245366179059 57364819884516368049268589)
    ·
      refine ⟨21511807456693638018475721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57364819884516368049268589 21511807456693638018475721)
      ·
        refine ⟨16133855592520228513856791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21511807456693638018475721 16133855592520228513856791)
        ·
          refine ⟨24200783388780342770785187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16133855592520228513856791 24200783388780342770785187)
          ·
            refine ⟨36301175083170514156177781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24200783388780342770785187 36301175083170514156177781)
            ·
              refine ⟨3403235164047235702141667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36301175083170514156177781 3403235164047235702141667)
              ·
                refine ⟨5104852746070853553212501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3403235164047235702141667 5104852746070853553212501)
                ·
                  refine ⟨59822493118017815076709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5104852746070853553212501 59822493118017815076709)
                  ·
                    rfl

theorem cell23_1048535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 8].length) (baseStart_1048535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048535 prefixEnd_1048535 := by exact prefixLift 1048535
  have htrace : WordTrace (prefixWord ++ tailWord_1048535) baseStart_1048535 baseEnd_1048535 := by
    simpa [prefixWord, tailWord_1048535, baseEnd_1048535] using wordTrace_append hprefix tailTrace_1048535
  have hstable : (prefixWord ++ tailWord_1048535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048535).length < 2 ^ (prefixWord ++ tailWord_1048535).sum := by decide
  have hdescent : baseEnd_1048535 < baseStart_1048535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048616 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 3, 5]
def baseStart_1048616 : Nat := 118140960795 + 1048616 * 2 ^ 59
def prefixEnd_1048616 : Nat := 4983230072969 + 3 ^ 40 * 1048616 * 2
def baseEnd_1048616 : Nat := 179481343331724839592503

theorem tailTrace_1048616 : CollatzResearch.WordTrace tailWord_1048616 prefixEnd_1048616 179481343331724839592503 := by
  unfold tailWord_1048616
  simp only [CollatzResearch.WordTrace]
  refine ⟨19123083784525398099938851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25497445046033864133251801 19123083784525398099938851)
  ·
    refine ⟨28684625676788097149908277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19123083784525398099938851 28684625676788097149908277)
    ·
      refine ⟨2689183657198884107803901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28684625676788097149908277 2689183657198884107803901)
      ·
        refine ⟨1008443871449581540426463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2689183657198884107803901 1008443871449581540426463)
        ·
          refine ⟨1512665807174372310639695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008443871449581540426463 1512665807174372310639695)
          ·
            refine ⟨2268998710761558465959543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1512665807174372310639695 2268998710761558465959543)
            ·
              refine ⟨3403498066142337698939315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2268998710761558465959543 3403498066142337698939315)
              ·
                refine ⟨5105247099213506548408973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3403498066142337698939315 5105247099213506548408973)
                ·
                  refine ⟨1914467662205064955653365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5105247099213506548408973 1914467662205064955653365)
                  ·
                    refine ⟨179481343331724839592503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1914467662205064955653365 179481343331724839592503)
                    ·
                      rfl

theorem cell23_1048616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_1048616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048616 prefixEnd_1048616 := by exact prefixLift 1048616
  have htrace : WordTrace (prefixWord ++ tailWord_1048616) baseStart_1048616 baseEnd_1048616 := by
    simpa [prefixWord, tailWord_1048616, baseEnd_1048616] using wordTrace_append hprefix tailTrace_1048616
  have hstable : (prefixWord ++ tailWord_1048616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048616).length < 2 ^ (prefixWord ++ tailWord_1048616).sum := by decide
  have hdescent : baseEnd_1048616 < baseStart_1048616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048636 : List Nat := [2, 2, 2, 2, 2, 1, 5, 1, 1, 1, 4]
def baseStart_1048636 : Nat := 118140960795 + 1048636 * 2 ^ 59
def prefixEnd_1048636 : Nat := 4983230072969 + 3 ^ 40 * 1048636 * 2
def baseEnd_1048636 : Nat := 538454299608264440527417

theorem tailTrace_1048636 : CollatzResearch.WordTrace tailWord_1048636 prefixEnd_1048636 538454299608264440527417 := by
  unfold tailWord_1048636
  simp only [CollatzResearch.WordTrace]
  refine ⟨19123448514489169807802881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25497931352652226410403841 19123448514489169807802881)
  ·
    refine ⟨14342586385866877355852161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19123448514489169807802881 14342586385866877355852161)
    ·
      refine ⟨10756939789400158016889121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14342586385866877355852161 10756939789400158016889121)
      ·
        refine ⟨8067704842050118512666841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10756939789400158016889121 8067704842050118512666841)
        ·
          refine ⟨6050778631537588884500131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8067704842050118512666841 6050778631537588884500131)
          ·
            refine ⟨9076167947306383326750197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6050778631537588884500131 9076167947306383326750197)
            ·
              refine ⟨850890745059973436882831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9076167947306383326750197 850890745059973436882831)
              ·
                refine ⟨1276336117589960155324247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850890745059973436882831 1276336117589960155324247)
                ·
                  refine ⟨1914504176384940232986371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1276336117589960155324247 1914504176384940232986371)
                  ·
                    refine ⟨2871756264577410349479557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1914504176384940232986371 2871756264577410349479557)
                    ·
                      refine ⟨538454299608264440527417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2871756264577410349479557 538454299608264440527417)
                      ·
                        rfl

theorem cell23_1048636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_1048636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048636 prefixEnd_1048636 := by exact prefixLift 1048636
  have htrace : WordTrace (prefixWord ++ tailWord_1048636) baseStart_1048636 baseEnd_1048636 := by
    simpa [prefixWord, tailWord_1048636, baseEnd_1048636] using wordTrace_append hprefix tailTrace_1048636
  have hstable : (prefixWord ++ tailWord_1048636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048636).length < 2 ^ (prefixWord ++ tailWord_1048636).sum := by decide
  have hdescent : baseEnd_1048636 < baseStart_1048636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048639 : List Nat := [1, 1, 2, 2, 3, 1, 2, 5, 1, 2, 3]
def baseStart_1048639 : Nat := 118140960795 + 1048639 * 2 ^ 59
def prefixEnd_1048639 : Nat := 4983230072969 + 3 ^ 40 * 1048639 * 2
def baseEnd_1048639 : Nat := 538455840050227928789903

theorem tailTrace_1048639 : CollatzResearch.WordTrace tailWord_1048639 prefixEnd_1048639 538455840050227928789903 := by
  unfold tailWord_1048639
  simp only [CollatzResearch.WordTrace]
  refine ⟨38247006447967471127964971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25498004298644980751976647 38247006447967471127964971)
  ·
    refine ⟨57370509671951206691947457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38247006447967471127964971 57370509671951206691947457)
    ·
      refine ⟨43027882253963405018960593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57370509671951206691947457 43027882253963405018960593)
      ·
        refine ⟨32270911690472553764220445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43027882253963405018960593 32270911690472553764220445)
        ·
          refine ⟨12101591883927207661582667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32270911690472553764220445 12101591883927207661582667)
          ·
            refine ⟨18152387825890811492374001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12101591883927207661582667 18152387825890811492374001)
            ·
              refine ⟨13614290869418108619280501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18152387825890811492374001 13614290869418108619280501)
              ·
                refine ⟨1276339769007947683057547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13614290869418108619280501 1276339769007947683057547)
                ·
                  refine ⟨1914509653511921524586321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1276339769007947683057547 1914509653511921524586321)
                  ·
                    refine ⟨1435882240133941143439741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1914509653511921524586321 1435882240133941143439741)
                    ·
                      refine ⟨538455840050227928789903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1435882240133941143439741 538455840050227928789903)
                      ·
                        rfl

theorem cell23_1048639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 2, 3].length) (baseStart_1048639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048639 prefixEnd_1048639 := by exact prefixLift 1048639
  have htrace : WordTrace (prefixWord ++ tailWord_1048639) baseStart_1048639 baseEnd_1048639 := by
    simpa [prefixWord, tailWord_1048639, baseEnd_1048639] using wordTrace_append hprefix tailTrace_1048639
  have hstable : (prefixWord ++ tailWord_1048639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048639).length < 2 ^ (prefixWord ++ tailWord_1048639).sum := by decide
  have hdescent : baseEnd_1048639 < baseStart_1048639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048653 : List Nat := [1, 6, 1, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_1048653 : Nat := 118140960795 + 1048653 * 2 ^ 59
def prefixEnd_1048653 : Nat := 4983230072969 + 3 ^ 40 * 1048653 * 2
def baseEnd_1048653 : Nat := 538463028779390874014839

theorem tailTrace_1048653 : CollatzResearch.WordTrace tailWord_1048653 prefixEnd_1048653 538463028779390874014839 := by
  unfold tailWord_1048653
  simp only [CollatzResearch.WordTrace]
  refine ⟨38247517069916751518974613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25498344713277834345983075 38247517069916751518974613)
  ·
    refine ⟨1792852362652347727451935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38247517069916751518974613 1792852362652347727451935)
    ·
      refine ⟨2689278543978521591177903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1792852362652347727451935 2689278543978521591177903)
      ·
        refine ⟨4033917815967782386766855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2689278543978521591177903 4033917815967782386766855)
        ·
          refine ⟨6050876723951673580150283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4033917815967782386766855 6050876723951673580150283)
          ·
            refine ⟨9076315085927510370225425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6050876723951673580150283 9076315085927510370225425)
            ·
              refine ⟨6807236314445632777669069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9076315085927510370225425 6807236314445632777669069)
              ·
                refine ⟨2552713617917112291625901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6807236314445632777669069 2552713617917112291625901)
                ·
                  refine ⟨957267606718917109359713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2552713617917112291625901 957267606718917109359713)
                  ·
                    refine ⟨717950705039187832019785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 957267606718917109359713 717950705039187832019785)
                    ·
                      refine ⟨538463028779390874014839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 717950705039187832019785 538463028779390874014839)
                      ·
                        rfl

theorem cell23_1048653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_1048653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048653 prefixEnd_1048653 := by exact prefixLift 1048653
  have htrace : WordTrace (prefixWord ++ tailWord_1048653) baseStart_1048653 baseEnd_1048653 := by
    simpa [prefixWord, tailWord_1048653, baseEnd_1048653] using wordTrace_append hprefix tailTrace_1048653
  have hstable : (prefixWord ++ tailWord_1048653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048653).length < 2 ^ (prefixWord ++ tailWord_1048653).sum := by decide
  have hdescent : baseEnd_1048653 < baseStart_1048653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048686 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_1048686 : Nat := 118140960795 + 1048686 * 2 ^ 59
def prefixEnd_1048686 : Nat := 4983230072969 + 3 ^ 40 * 1048686 * 2
def baseEnd_1048686 : Nat := 538479973640989244902187

theorem tailTrace_1048686 : CollatzResearch.WordTrace tailWord_1048686 prefixEnd_1048686 538479973640989244902187 := by
  unfold tailWord_1048686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4781090084849649769365739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25499147119198132103283941 4781090084849649769365739)
  ·
    refine ⟨7171635127274474654048609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4781090084849649769365739 7171635127274474654048609)
    ·
      refine ⟨5378726345455855990536457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7171635127274474654048609 5378726345455855990536457)
      ·
        refine ⟨4034044759091891992902343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5378726345455855990536457 4034044759091891992902343)
        ·
          refine ⟨6051067138637837989353515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4034044759091891992902343 6051067138637837989353515)
          ·
            refine ⟨9076600707956756984030273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6051067138637837989353515 9076600707956756984030273)
            ·
              refine ⟨6807450530967567738022705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9076600707956756984030273 6807450530967567738022705)
              ·
                refine ⟨5105587898225675803517029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6807450530967567738022705 5105587898225675803517029)
                ·
                  refine ⟨957297730917314213159443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5105587898225675803517029 957297730917314213159443)
                  ·
                    refine ⟨1435946596375971319739165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 957297730917314213159443 1435946596375971319739165)
                    ·
                      refine ⟨538479973640989244902187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1435946596375971319739165 538479973640989244902187)
                      ·
                        rfl

theorem cell23_1048686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_1048686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048686 prefixEnd_1048686 := by exact prefixLift 1048686
  have htrace : WordTrace (prefixWord ++ tailWord_1048686) baseStart_1048686 baseEnd_1048686 := by
    simpa [prefixWord, tailWord_1048686, baseEnd_1048686] using wordTrace_append hprefix tailTrace_1048686
  have hstable : (prefixWord ++ tailWord_1048686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048686).length < 2 ^ (prefixWord ++ tailWord_1048686).sum := by decide
  have hdescent : baseEnd_1048686 < baseStart_1048686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048730 : List Nat := [3, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2]
def baseStart_1048730 : Nat := 118140960795 + 1048730 * 2 ^ 59
def prefixEnd_1048730 : Nat := 4983230072969 + 3 ^ 40 * 1048730 * 2
def baseEnd_1048730 : Nat := 538502566789787072751985

theorem tailTrace_1048730 : CollatzResearch.WordTrace tailWord_1048730 prefixEnd_1048730 538502566789787072751985 := by
  unfold tailWord_1048730
  simp only [CollatzResearch.WordTrace]
  refine ⟨9562581372659448417381911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25500216993758529113018429 9562581372659448417381911)
  ·
    refine ⟨14343872058989172626072867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9562581372659448417381911 14343872058989172626072867)
    ·
      refine ⟨21515808088483758939109301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14343872058989172626072867 21515808088483758939109301)
      ·
        refine ⟨2017107008295352400541497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21515808088483758939109301 2017107008295352400541497)
        ·
          refine ⟨1512830256221514300406123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2017107008295352400541497 1512830256221514300406123)
          ·
            refine ⟨2269245384332271450609185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1512830256221514300406123 2269245384332271450609185)
            ·
              refine ⟨1701934038249203587956889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2269245384332271450609185 1701934038249203587956889)
              ·
                refine ⟨1276450528686902690967667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1701934038249203587956889 1276450528686902690967667)
                ·
                  refine ⟨1914675793030354036451501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1276450528686902690967667 1914675793030354036451501)
                  ·
                    refine ⟨718003422386382763669313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1914675793030354036451501 718003422386382763669313)
                    ·
                      refine ⟨538502566789787072751985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 718003422386382763669313 538502566789787072751985)
                      ·
                        rfl

theorem cell23_1048730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_1048730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048730 prefixEnd_1048730 := by exact prefixLift 1048730
  have htrace : WordTrace (prefixWord ++ tailWord_1048730) baseStart_1048730 baseEnd_1048730 := by
    simpa [prefixWord, tailWord_1048730, baseEnd_1048730] using wordTrace_append hprefix tailTrace_1048730
  have hstable : (prefixWord ++ tailWord_1048730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048730).length < 2 ^ (prefixWord ++ tailWord_1048730).sum := by decide
  have hdescent : baseEnd_1048730 < baseStart_1048730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048809 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 5, 4]
def baseStart_1048809 : Nat := 118140960795 + 1048809 * 2 ^ 59
def prefixEnd_1048809 : Nat := 4983230072969 + 3 ^ 40 * 1048809 * 2
def baseEnd_1048809 : Nat := 179514377253830754554707

theorem tailTrace_1048809 : CollatzResearch.WordTrace tailWord_1048809 prefixEnd_1048809 179514377253830754554707 := by
  unfold tailWord_1048809
  simp only [CollatzResearch.WordTrace]
  refine ⟨38253206857351590161653481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25502137904901060107768987 38253206857351590161653481)
  ·
    refine ⟨28689905143013692621240111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38253206857351590161653481 28689905143013692621240111)
    ·
      refine ⟨43034857714520538931860167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28689905143013692621240111 43034857714520538931860167)
      ·
        refine ⟨64552286571780808397790251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43034857714520538931860167 64552286571780808397790251)
        ·
          refine ⟨96828429857671212596685377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64552286571780808397790251 96828429857671212596685377)
          ·
            refine ⟨72621322393253409447514033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96828429857671212596685377 72621322393253409447514033)
            ·
              refine ⟨54465991794940057085635525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72621322393253409447514033 54465991794940057085635525)
              ·
                refine ⟨10212373461551260703556661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54465991794940057085635525 10212373461551260703556661)
                ·
                  refine ⟨957410012020430690958437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10212373461551260703556661 957410012020430690958437)
                  ·
                    refine ⟨179514377253830754554707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 957410012020430690958437 179514377253830754554707)
                    ·
                      rfl

theorem cell23_1048809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 4].length) (baseStart_1048809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048809 prefixEnd_1048809 := by exact prefixLift 1048809
  have htrace : WordTrace (prefixWord ++ tailWord_1048809) baseStart_1048809 baseEnd_1048809 := by
    simpa [prefixWord, tailWord_1048809, baseEnd_1048809] using wordTrace_append hprefix tailTrace_1048809
  have hstable : (prefixWord ++ tailWord_1048809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048809).length < 2 ^ (prefixWord ++ tailWord_1048809).sum := by decide
  have hdescent : baseEnd_1048809 < baseStart_1048809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048883 : List Nat := [1, 1, 1, 2, 5, 1, 4, 1, 3, 1, 3]
def baseStart_1048883 : Nat := 118140960795 + 1048883 * 2 ^ 59
def prefixEnd_1048883 : Nat := 4983230072969 + 3 ^ 40 * 1048883 * 2
def baseEnd_1048883 : Nat := 538581129329924974138781

theorem tailTrace_1048883 : CollatzResearch.WordTrace tailWord_1048883 prefixEnd_1048883 538581129329924974138781 := by
  unfold tailWord_1048883
  simp only [CollatzResearch.WordTrace]
  refine ⟨38255905859083500799847303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25503937239389000533231535 38255905859083500799847303)
  ·
    refine ⟨57383858788625251199770955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38255905859083500799847303 57383858788625251199770955)
    ·
      refine ⟨86075788182937876799656433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57383858788625251199770955 86075788182937876799656433)
      ·
        refine ⟨64556841137203407599742325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86075788182937876799656433 64556841137203407599742325)
        ·
          refine ⟨6052203856612819462475843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64556841137203407599742325 6052203856612819462475843)
          ·
            refine ⟨9078305784919229193713765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6052203856612819462475843 9078305784919229193713765)
            ·
              refine ⟨1702182334672355473821331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9078305784919229193713765 1702182334672355473821331)
              ·
                refine ⟨2553273502008533210731997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1702182334672355473821331 2553273502008533210731997)
                ·
                  refine ⟨957477563253199954024499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2553273502008533210731997 957477563253199954024499)
                  ·
                    refine ⟨1436216344879799931036749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 957477563253199954024499 1436216344879799931036749)
                    ·
                      refine ⟨538581129329924974138781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1436216344879799931036749 538581129329924974138781)
                      ·
                        rfl

theorem cell23_1048883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 1, 3].length) (baseStart_1048883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048883 prefixEnd_1048883 := by exact prefixLift 1048883
  have htrace : WordTrace (prefixWord ++ tailWord_1048883) baseStart_1048883 baseEnd_1048883 := by
    simpa [prefixWord, tailWord_1048883, baseEnd_1048883] using wordTrace_append hprefix tailTrace_1048883
  have hstable : (prefixWord ++ tailWord_1048883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048883).length < 2 ^ (prefixWord ++ tailWord_1048883).sum := by decide
  have hdescent : baseEnd_1048883 < baseStart_1048883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048936 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1048936 : Nat := 118140960795 + 1048936 * 2 ^ 59
def prefixEnd_1048936 : Nat := 4983230072969 + 3 ^ 40 * 1048936 * 2
def baseEnd_1048936 : Nat := 538608343804613266776037

theorem tailTrace_1048936 : CollatzResearch.WordTrace tailWord_1048936 prefixEnd_1048936 538608343804613266776037 := by
  unfold tailWord_1048936
  simp only [CollatzResearch.WordTrace]
  refine ⟨19128919463945745425763331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25505225951927660567684441 19128919463945745425763331)
  ·
    refine ⟨28693379195918618138644997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19128919463945745425763331 28693379195918618138644997)
    ·
      refine ⟨5380008599234740900995937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28693379195918618138644997 5380008599234740900995937)
      ·
        refine ⟨4035006449426055675746953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5380008599234740900995937 4035006449426055675746953)
        ·
          refine ⟨3026254837069541756810215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4035006449426055675746953 3026254837069541756810215)
          ·
            refine ⟨4539382255604312635215323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3026254837069541756810215 4539382255604312635215323)
            ·
              refine ⟨6809073383406468952822985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4539382255604312635215323 6809073383406468952822985)
              ·
                refine ⟨5106805037554851714617239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6809073383406468952822985 5106805037554851714617239)
                ·
                  refine ⟨7660207556332277571925859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5106805037554851714617239 7660207556332277571925859)
                  ·
                    refine ⟨11490311334498416357888789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7660207556332277571925859 11490311334498416357888789)
                    ·
                      refine ⟨538608343804613266776037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11490311334498416357888789 538608343804613266776037)
                      ·
                        rfl

theorem cell23_1048936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1048936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048936 prefixEnd_1048936 := by exact prefixLift 1048936
  have htrace : WordTrace (prefixWord ++ tailWord_1048936) baseStart_1048936 baseEnd_1048936 := by
    simpa [prefixWord, tailWord_1048936, baseEnd_1048936] using wordTrace_append hprefix tailTrace_1048936
  have hstable : (prefixWord ++ tailWord_1048936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048936).length < 2 ^ (prefixWord ++ tailWord_1048936).sum := by decide
  have hdescent : baseEnd_1048936 < baseStart_1048936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048946 : List Nat := [3, 2, 1, 2, 1, 4, 2, 8]
def baseStart_1048946 : Nat := 118140960795 + 1048946 * 2 ^ 59
def prefixEnd_1048946 : Nat := 4983230072969 + 3 ^ 40 * 1048946 * 2
def baseEnd_1048946 : Nat := 19948647355968823246333

theorem tailTrace_1048946 : CollatzResearch.WordTrace tailWord_1048946 prefixEnd_1048946 19948647355968823246333 := by
  unfold tailWord_1048946
  simp only [CollatzResearch.WordTrace]
  refine ⟨9564550914463815639847673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25505469105236841706260461 9564550914463815639847673)
  ·
    refine ⟨7173413185847861729885755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9564550914463815639847673 7173413185847861729885755)
    ·
      refine ⟨10760119778771792594828633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7173413185847861729885755 10760119778771792594828633)
      ·
        refine ⟨8070089834078844446121475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10760119778771792594828633 8070089834078844446121475)
        ·
          refine ⟨12105134751118266669182213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8070089834078844446121475 12105134751118266669182213)
          ·
            refine ⟨2269712765834675000471665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12105134751118266669182213 2269712765834675000471665)
            ·
              refine ⟨1702284574376006250353749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2269712765834675000471665 1702284574376006250353749)
              ·
                refine ⟨19948647355968823246333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1702284574376006250353749 19948647355968823246333)
                ·
                  rfl

theorem cell23_1048946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 8].length) (baseStart_1048946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048946 prefixEnd_1048946 := by exact prefixLift 1048946
  have htrace : WordTrace (prefixWord ++ tailWord_1048946) baseStart_1048946 baseEnd_1048946 := by
    simpa [prefixWord, tailWord_1048946, baseEnd_1048946] using wordTrace_append hprefix tailTrace_1048946
  have hstable : (prefixWord ++ tailWord_1048946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048946).length < 2 ^ (prefixWord ++ tailWord_1048946).sum := by decide
  have hdescent : baseEnd_1048946 < baseStart_1048946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048959 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 2, 7]
def baseStart_1048959 : Nat := 118140960795 + 1048959 * 2 ^ 59
def prefixEnd_1048959 : Nat := 4983230072969 + 3 ^ 40 * 1048959 * 2
def baseEnd_1048959 : Nat := 179540051286555558929477

theorem tailTrace_1048959 : CollatzResearch.WordTrace tailWord_1048959 prefixEnd_1048959 179540051286555558929477 := by
  unfold tailWord_1048959
  simp only [CollatzResearch.WordTrace]
  refine ⟨38258677806808165779613931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25505785204538777186409287 38258677806808165779613931)
  ·
    refine ⟨57388016710212248669420897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38258677806808165779613931 57388016710212248669420897)
    ·
      refine ⟨43041012532659186502065673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57388016710212248669420897 43041012532659186502065673)
      ·
        refine ⟨32280759399494389876549255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43041012532659186502065673 32280759399494389876549255)
        ·
          refine ⟨48421139099241584814823883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32280759399494389876549255 48421139099241584814823883)
          ·
            refine ⟨72631708648862377222235825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48421139099241584814823883 72631708648862377222235825)
            ·
              refine ⟨54473781486646782916676869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72631708648862377222235825 54473781486646782916676869)
              ·
                refine ⟨10213834028746271796876913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54473781486646782916676869 10213834028746271796876913)
                ·
                  refine ⟨7660375521559703847657685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10213834028746271796876913 7660375521559703847657685)
                  ·
                    refine ⟨179540051286555558929477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7660375521559703847657685 179540051286555558929477)
                    ·
                      rfl

theorem cell23_1048959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 7].length) (baseStart_1048959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048959 prefixEnd_1048959 := by exact prefixLift 1048959
  have htrace : WordTrace (prefixWord ++ tailWord_1048959) baseStart_1048959 baseEnd_1048959 := by
    simpa [prefixWord, tailWord_1048959, baseEnd_1048959] using wordTrace_append hprefix tailTrace_1048959
  have hstable : (prefixWord ++ tailWord_1048959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048959).length < 2 ^ (prefixWord ++ tailWord_1048959).sum := by decide
  have hdescent : baseEnd_1048959 < baseStart_1048959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048970 : List Nat := [3, 1, 2, 5, 1, 1, 1, 2, 1, 2, 4]
def baseStart_1048970 : Nat := 118140960795 + 1048970 * 2 ^ 59
def prefixEnd_1048970 : Nat := 4983230072969 + 3 ^ 40 * 1048970 * 2
def baseEnd_1048970 : Nat := 538625802146866133750881

theorem tailTrace_1048970 : CollatzResearch.WordTrace tailWord_1048970 prefixEnd_1048970 538625802146866133750881 := by
  unfold tailWord_1048970
  simp only [CollatzResearch.WordTrace]
  refine ⟨9564769752442078664566091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25506052673178876438842909 9564769752442078664566091)
  ·
    refine ⟨14347154628663117996849137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9564769752442078664566091 14347154628663117996849137)
    ·
      refine ⟨10760365971497338497636853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14347154628663117996849137 10760365971497338497636853)
      ·
        refine ⟨1008784309827875484153455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10760365971497338497636853 1008784309827875484153455)
        ·
          refine ⟨1513176464741813226230183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008784309827875484153455 1513176464741813226230183)
          ·
            refine ⟨2269764697112719839345275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513176464741813226230183 2269764697112719839345275)
            ·
              refine ⟨3404647045669079759017913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2269764697112719839345275 3404647045669079759017913)
              ·
                refine ⟨2553485284251809819263435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3404647045669079759017913 2553485284251809819263435)
                ·
                  refine ⟨3830227926377714728895153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2553485284251809819263435 3830227926377714728895153)
                  ·
                    refine ⟨2872670944783286046671365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3830227926377714728895153 2872670944783286046671365)
                    ·
                      refine ⟨538625802146866133750881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2872670944783286046671365 538625802146866133750881)
                      ·
                        rfl

theorem cell23_1048970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_1048970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048970 prefixEnd_1048970 := by exact prefixLift 1048970
  have htrace : WordTrace (prefixWord ++ tailWord_1048970) baseStart_1048970 baseEnd_1048970 := by
    simpa [prefixWord, tailWord_1048970, baseEnd_1048970] using wordTrace_append hprefix tailTrace_1048970
  have hstable : (prefixWord ++ tailWord_1048970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048970).length < 2 ^ (prefixWord ++ tailWord_1048970).sum := by decide
  have hdescent : baseEnd_1048970 < baseStart_1048970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048996 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_1048996 : Nat := 118140960795 + 1048996 * 2 ^ 59
def prefixEnd_1048996 : Nat := 4983230072969 + 3 ^ 40 * 1048996 * 2
def baseEnd_1048996 : Nat := 538639152643883032025761

theorem tailTrace_1048996 : CollatzResearch.WordTrace tailWord_1048996 prefixEnd_1048996 538639152643883032025761 := by
  unfold tailWord_1048996
  simp only [CollatzResearch.WordTrace]
  refine ⟨19130013653837060549355421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25506684871782747399140561 19130013653837060549355421)
  ·
    refine ⟨7173755120188897706008283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19130013653837060549355421 7173755120188897706008283)
    ·
      refine ⟨10760632680283346559012425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7173755120188897706008283 10760632680283346559012425)
      ·
        refine ⟨8070474510212509919259319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10760632680283346559012425 8070474510212509919259319)
        ·
          refine ⟨12105711765318764878888979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8070474510212509919259319 12105711765318764878888979)
          ·
            refine ⟨18158567647978147318333469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12105711765318764878888979 18158567647978147318333469)
            ·
              refine ⟨6809462867991805244375051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18158567647978147318333469 6809462867991805244375051)
              ·
                refine ⟨10214194301987707866562577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6809462867991805244375051 10214194301987707866562577)
                ·
                  refine ⟨7660645726490780899921933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10214194301987707866562577 7660645726490780899921933)
                  ·
                    refine ⟨2872742147434042837470725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7660645726490780899921933 2872742147434042837470725)
                    ·
                      refine ⟨538639152643883032025761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2872742147434042837470725 538639152643883032025761)
                      ·
                        rfl

theorem cell23_1048996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_1048996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1048996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1048996 prefixEnd_1048996 := by exact prefixLift 1048996
  have htrace : WordTrace (prefixWord ++ tailWord_1048996) baseStart_1048996 baseEnd_1048996 := by
    simpa [prefixWord, tailWord_1048996, baseEnd_1048996] using wordTrace_append hprefix tailTrace_1048996
  have hstable : (prefixWord ++ tailWord_1048996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048996).length < 2 ^ (prefixWord ++ tailWord_1048996).sum := by decide
  have hdescent : baseEnd_1048996 < baseStart_1048996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049016 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 4, 4, 3]
def baseStart_1049016 : Nat := 118140960795 + 1049016 * 2 ^ 59
def prefixEnd_1049016 : Nat := 4983230072969 + 3 ^ 40 * 1049016 * 2
def baseEnd_1049016 : Nat := 538649422256972953775669

theorem tailTrace_1049016 : CollatzResearch.WordTrace tailWord_1049016 prefixEnd_1049016 538649422256972953775669 := by
  unfold tailWord_1049016
  simp only [CollatzResearch.WordTrace]
  refine ⟨19130378383800832257219451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25507171178401109676292601 19130378383800832257219451)
  ·
    refine ⟨28695567575701248385829177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19130378383800832257219451 28695567575701248385829177)
    ·
      refine ⟨21521675681775936289371883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28695567575701248385829177 21521675681775936289371883)
      ·
        refine ⟨32282513522663904434057825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21521675681775936289371883 32282513522663904434057825)
        ·
          refine ⟨24211885141997928325543369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32282513522663904434057825 24211885141997928325543369)
          ·
            refine ⟨18158913856498446244157527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24211885141997928325543369 18158913856498446244157527)
            ·
              refine ⟨27238370784747669366236291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18158913856498446244157527 27238370784747669366236291)
              ·
                refine ⟨40857556177121504049354437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27238370784747669366236291 40857556177121504049354437)
                ·
                  refine ⟨7660791783210282009253957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40857556177121504049354437 7660791783210282009253957)
                  ·
                    refine ⟨1436398459351927876735117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7660791783210282009253957 1436398459351927876735117)
                    ·
                      refine ⟨538649422256972953775669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1436398459351927876735117 538649422256972953775669)
                      ·
                        rfl

theorem cell23_1049016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_1049016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049016 prefixEnd_1049016 := by exact prefixLift 1049016
  have htrace : WordTrace (prefixWord ++ tailWord_1049016) baseStart_1049016 baseEnd_1049016 := by
    simpa [prefixWord, tailWord_1049016, baseEnd_1049016] using wordTrace_append hprefix tailTrace_1049016
  have hstable : (prefixWord ++ tailWord_1049016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049016).length < 2 ^ (prefixWord ++ tailWord_1049016).sum := by decide
  have hdescent : baseEnd_1049016 < baseStart_1049016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049053 : List Nat := [1, 4, 3, 1, 1, 1, 4, 1, 7]
def baseStart_1049053 : Nat := 118140960795 + 1049053 * 2 ^ 59
def prefixEnd_1049053 : Nat := 4983230072969 + 3 ^ 40 * 1049053 * 2
def baseEnd_1049053 : Nat := 59852046782354367668111

theorem tailTrace_1049053 : CollatzResearch.WordTrace tailWord_1049053 prefixEnd_1049053 59852046782354367668111 := by
  unfold tailWord_1049053
  simp only [CollatzResearch.WordTrace]
  refine ⟨38262106268467619833535813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25508070845645079889023875 38262106268467619833535813)
  ·
    refine ⟨7174144925337678718787965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38262106268467619833535813 7174144925337678718787965)
    ·
      refine ⟨2690304347001629519545487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7174144925337678718787965 2690304347001629519545487)
      ·
        refine ⟨4035456520502444279318231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2690304347001629519545487 4035456520502444279318231)
        ·
          refine ⟨6053184780753666418977347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4035456520502444279318231 6053184780753666418977347)
          ·
            refine ⟨9079777171130499628466021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6053184780753666418977347 9079777171130499628466021)
            ·
              refine ⟨1702458219586968680337379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9079777171130499628466021 1702458219586968680337379)
              ·
                refine ⟨2553687329380453020506069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1702458219586968680337379 2553687329380453020506069)
                ·
                  refine ⟨59852046782354367668111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2553687329380453020506069 59852046782354367668111)
                  ·
                    rfl

theorem cell23_1049053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_1049053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049053 prefixEnd_1049053 := by exact prefixLift 1049053
  have htrace : WordTrace (prefixWord ++ tailWord_1049053) baseStart_1049053 baseEnd_1049053 := by
    simpa [prefixWord, tailWord_1049053, baseEnd_1049053] using wordTrace_append hprefix tailTrace_1049053
  have hstable : (prefixWord ++ tailWord_1049053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049053).length < 2 ^ (prefixWord ++ tailWord_1049053).sum := by decide
  have hdescent : baseEnd_1049053 < baseStart_1049053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049063 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_1049063 : Nat := 118140960795 + 1049063 * 2 ^ 59
def prefixEnd_1049063 : Nat := 4983230072969 + 3 ^ 40 * 1049063 * 2
def baseEnd_1049063 : Nat := 538673555847734269887953

theorem tailTrace_1049063 : CollatzResearch.WordTrace tailWord_1049063 prefixEnd_1049063 538673555847734269887953 := by
  unfold tailWord_1049063
  simp only [CollatzResearch.WordTrace]
  refine ⟨38262470998431391541399843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25508313998954261027599895 38262470998431391541399843)
  ·
    refine ⟨57393706497647087312099765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38262470998431391541399843 57393706497647087312099765)
    ·
      refine ⟨5380659984154414435509353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57393706497647087312099765 5380659984154414435509353)
      ·
        refine ⟨4035494988115810826632015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5380659984154414435509353 4035494988115810826632015)
        ·
          refine ⟨6053242482173716239948023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4035494988115810826632015 6053242482173716239948023)
          ·
            refine ⟨9079863723260574359922035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6053242482173716239948023 9079863723260574359922035)
            ·
              refine ⟨13619795584890861539883053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9079863723260574359922035 13619795584890861539883053)
              ·
                refine ⟨5107423344334073077456145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13619795584890861539883053 5107423344334073077456145)
                ·
                  refine ⟨3830567508250554808092109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5107423344334073077456145 3830567508250554808092109)
                  ·
                    refine ⟨1436462815593958053034541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3830567508250554808092109 1436462815593958053034541)
                    ·
                      refine ⟨538673555847734269887953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1436462815593958053034541 538673555847734269887953)
                      ·
                        rfl

theorem cell23_1049063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_1049063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049063 prefixEnd_1049063 := by exact prefixLift 1049063
  have htrace : WordTrace (prefixWord ++ tailWord_1049063) baseStart_1049063 baseEnd_1049063 := by
    simpa [prefixWord, tailWord_1049063, baseEnd_1049063] using wordTrace_append hprefix tailTrace_1049063
  have hstable : (prefixWord ++ tailWord_1049063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049063).length < 2 ^ (prefixWord ++ tailWord_1049063).sum := by decide
  have hdescent : baseEnd_1049063 < baseStart_1049063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049064 : List Nat := [2, 1, 4, 1, 1, 4, 3, 1, 2, 2, 2]
def baseStart_1049064 : Nat := 118140960795 + 1049064 * 2 ^ 59
def prefixEnd_1049064 : Nat := 4983230072969 + 3 ^ 40 * 1049064 * 2
def baseEnd_1049064 : Nat := 538674069328388765975449

theorem tailTrace_1049064 : CollatzResearch.WordTrace tailWord_1049064 prefixEnd_1049064 538674069328388765975449 := by
  unfold tailWord_1049064
  simp only [CollatzResearch.WordTrace]
  refine ⟨19131253735713884356093123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25508338314285179141457497 19131253735713884356093123)
  ·
    refine ⟨28696880603570826534139685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19131253735713884356093123 28696880603570826534139685)
    ·
      refine ⟨5380665113169529975151191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28696880603570826534139685 5380665113169529975151191)
      ·
        refine ⟨8070997669754294962726787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5380665113169529975151191 8070997669754294962726787)
        ·
          refine ⟨12106496504631442444090181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8070997669754294962726787 12106496504631442444090181)
          ·
            refine ⟨2269968094618395458266909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12106496504631442444090181 2269968094618395458266909)
            ·
              refine ⟨851238035481898296850091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2269968094618395458266909 851238035481898296850091)
              ·
                refine ⟨1276857053222847445275137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851238035481898296850091 1276857053222847445275137)
                ·
                  refine ⟨957642789917135583956353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1276857053222847445275137 957642789917135583956353)
                  ·
                    refine ⟨718232092437851687967265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 957642789917135583956353 718232092437851687967265)
                    ·
                      refine ⟨538674069328388765975449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 718232092437851687967265 538674069328388765975449)
                      ·
                        rfl

theorem cell23_1049064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_1049064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049064 prefixEnd_1049064 := by exact prefixLift 1049064
  have htrace : WordTrace (prefixWord ++ tailWord_1049064) baseStart_1049064 baseEnd_1049064 := by
    simpa [prefixWord, tailWord_1049064, baseEnd_1049064] using wordTrace_append hprefix tailTrace_1049064
  have hstable : (prefixWord ++ tailWord_1049064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049064).length < 2 ^ (prefixWord ++ tailWord_1049064).sum := by decide
  have hdescent : baseEnd_1049064 < baseStart_1049064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049173 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 3, 5]
def baseStart_1049173 : Nat := 118140960795 + 1049173 * 2 ^ 59
def prefixEnd_1049173 : Nat := 4983230072969 + 3 ^ 40 * 1049173 * 2
def baseEnd_1049173 : Nat := 179576679573242946504149

theorem tailTrace_1049173 : CollatzResearch.WordTrace tailWord_1049173 prefixEnd_1049173 179576679573242946504149 := by
  unfold tailWord_1049173
  simp only [CollatzResearch.WordTrace]
  refine ⟨38266483028032880327904173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25510988685355253551936115 38266483028032880327904173)
  ·
    refine ⟨14349931135512330122964065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38266483028032880327904173 14349931135512330122964065)
    ·
      refine ⟨10762448351634247592223049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14349931135512330122964065 10762448351634247592223049)
      ·
        refine ⟨8071836263725685694167287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10762448351634247592223049 8071836263725685694167287)
        ·
          refine ⟨12107754395588528541250931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8071836263725685694167287 12107754395588528541250931)
          ·
            refine ⟨18161631593382792811876397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12107754395588528541250931 18161631593382792811876397)
            ·
              refine ⟨6810611847518547304453649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18161631593382792811876397 6810611847518547304453649)
              ·
                refine ⟨5107958885638910478340237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6810611847518547304453649 5107958885638910478340237)
                ·
                  refine ⟨1915484582114591429377589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5107958885638910478340237 1915484582114591429377589)
                  ·
                    refine ⟨179576679573242946504149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1915484582114591429377589 179576679573242946504149)
                    ·
                      rfl

theorem cell23_1049173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_1049173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049173 prefixEnd_1049173 := by exact prefixLift 1049173
  have htrace : WordTrace (prefixWord ++ tailWord_1049173) baseStart_1049173 baseEnd_1049173 := by
    simpa [prefixWord, tailWord_1049173, baseEnd_1049173] using wordTrace_append hprefix tailTrace_1049173
  have hstable : (prefixWord ++ tailWord_1049173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049173).length < 2 ^ (prefixWord ++ tailWord_1049173).sum := by decide
  have hdescent : baseEnd_1049173 < baseStart_1049173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049197 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 1, 5, 2]
def baseStart_1049197 : Nat := 118140960795 + 1049197 * 2 ^ 59
def prefixEnd_1049197 : Nat := 4983230072969 + 3 ^ 40 * 1049197 * 2
def baseEnd_1049197 : Nat := 538742362255436745612337

theorem tailTrace_1049197 : CollatzResearch.WordTrace tailWord_1049197 prefixEnd_1049197 538742362255436745612337 := by
  unfold tailWord_1049197
  simp only [CollatzResearch.WordTrace]
  refine ⟨38267358379945932426777845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25511572253297288284518563 38267358379945932426777845)
  ·
    refine ⟨3587564848119931165010423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38267358379945932426777845 3587564848119931165010423)
    ·
      refine ⟨5381347272179896747515635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3587564848119931165010423 5381347272179896747515635)
      ·
        refine ⟨8072020908269845121273453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5381347272179896747515635 8072020908269845121273453)
        ·
          refine ⟨3027007840601191920477545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8072020908269845121273453 3027007840601191920477545)
          ·
            refine ⟨2270255880450893940358159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3027007840601191920477545 2270255880450893940358159)
            ·
              refine ⟨3405383820676340910537239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2270255880450893940358159 3405383820676340910537239)
              ·
                refine ⟨5108075731014511365805859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3405383820676340910537239 5108075731014511365805859)
                ·
                  refine ⟨7662113596521767048708789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5108075731014511365805859 7662113596521767048708789)
                  ·
                    refine ⟨718323149673915660816449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7662113596521767048708789 718323149673915660816449)
                    ·
                      refine ⟨538742362255436745612337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 718323149673915660816449 538742362255436745612337)
                      ·
                        rfl

theorem cell23_1049197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_1049197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049197 prefixEnd_1049197 := by exact prefixLift 1049197
  have htrace : WordTrace (prefixWord ++ tailWord_1049197) baseStart_1049197 baseEnd_1049197 := by
    simpa [prefixWord, tailWord_1049197, baseEnd_1049197] using wordTrace_append hprefix tailTrace_1049197
  have hstable : (prefixWord ++ tailWord_1049197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049197).length < 2 ^ (prefixWord ++ tailWord_1049197).sum := by decide
  have hdescent : baseEnd_1049197 < baseStart_1049197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049223 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_1049223 : Nat := 118140960795 + 1049223 * 2 ^ 59
def prefixEnd_1049223 : Nat := 4983230072969 + 3 ^ 40 * 1049223 * 2
def baseEnd_1049223 : Nat := 538755712752453643887217

theorem tailTrace_1049223 : CollatzResearch.WordTrace tailWord_1049223 prefixEnd_1049223 538755712752453643887217 := by
  unfold tailWord_1049223
  simp only [CollatzResearch.WordTrace]
  refine ⟨38268306677851738867224323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25512204451901159244816215 38268306677851738867224323)
  ·
    refine ⟨57402460016777608300836485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38268306677851738867224323 57402460016777608300836485)
    ·
      refine ⟨10762961253145801556406841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57402460016777608300836485 10762961253145801556406841)
      ·
        refine ⟨8072220939859351167305131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10762961253145801556406841 8072220939859351167305131)
        ·
          refine ⟨12108331409789026750957697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8072220939859351167305131 12108331409789026750957697)
          ·
            refine ⟨9081248557341770063218273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12108331409789026750957697 9081248557341770063218273)
            ·
              refine ⟨6810936418006327547413705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9081248557341770063218273 6810936418006327547413705)
              ·
                refine ⟨5108202313504745660560279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6810936418006327547413705 5108202313504745660560279)
                ·
                  refine ⟨7662303470257118490840419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5108202313504745660560279 7662303470257118490840419)
                  ·
                    refine ⟨11493455205385677736260629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7662303470257118490840419 11493455205385677736260629)
                    ·
                      refine ⟨538755712752453643887217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11493455205385677736260629 538755712752453643887217)
                      ·
                        rfl

theorem cell23_1049223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_1049223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049223 prefixEnd_1049223 := by exact prefixLift 1049223
  have htrace : WordTrace (prefixWord ++ tailWord_1049223) baseStart_1049223 baseEnd_1049223 := by
    simpa [prefixWord, tailWord_1049223, baseEnd_1049223] using wordTrace_append hprefix tailTrace_1049223
  have hstable : (prefixWord ++ tailWord_1049223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049223).length < 2 ^ (prefixWord ++ tailWord_1049223).sum := by decide
  have hdescent : baseEnd_1049223 < baseStart_1049223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049230 : List Nat := [4, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_1049230 : Nat := 118140960795 + 1049230 * 2 ^ 59
def prefixEnd_1049230 : Nat := 4983230072969 + 3 ^ 40 * 1049230 * 2
def baseEnd_1049230 : Nat := 538759307117035116499685

theorem tailTrace_1049230 : CollatzResearch.WordTrace tailWord_1049230 prefixEnd_1049230 538759307117035116499685 := by
  unfold tailWord_1049230
  simp only [CollatzResearch.WordTrace]
  refine ⟨4783570248603297382841143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25512374659217586041819429 4783570248603297382841143)
  ·
    refine ⟨7175355372904946074261715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4783570248603297382841143 7175355372904946074261715)
    ·
      refine ⟨10763033059357419111392573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7175355372904946074261715 10763033059357419111392573)
      ·
        refine ⟨4036137397259032166772215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10763033059357419111392573 4036137397259032166772215)
        ·
          refine ⟨6054206095888548250158323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4036137397259032166772215 6054206095888548250158323)
          ·
            refine ⟨9081309143832822375237485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6054206095888548250158323 9081309143832822375237485)
            ·
              refine ⟨3405490928937308390714057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9081309143832822375237485 3405490928937308390714057)
              ·
                refine ⟨2554118196702981293035543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3405490928937308390714057 2554118196702981293035543)
                ·
                  refine ⟨3831177295054471939553315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2554118196702981293035543 3831177295054471939553315)
                  ·
                    refine ⟨5746765942581707909329973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3831177295054471939553315 5746765942581707909329973)
                    ·
                      refine ⟨538759307117035116499685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5746765942581707909329973 538759307117035116499685)
                      ·
                        rfl

theorem cell23_1049230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_1049230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049230 prefixEnd_1049230 := by exact prefixLift 1049230
  have htrace : WordTrace (prefixWord ++ tailWord_1049230) baseStart_1049230 baseEnd_1049230 := by
    simpa [prefixWord, tailWord_1049230, baseEnd_1049230] using wordTrace_append hprefix tailTrace_1049230
  have hstable : (prefixWord ++ tailWord_1049230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049230).length < 2 ^ (prefixWord ++ tailWord_1049230).sum := by decide
  have hdescent : baseEnd_1049230 < baseStart_1049230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049244 : List Nat := [2, 2, 3, 2, 2, 1, 2, 2, 3, 2, 2]
def baseStart_1049244 : Nat := 118140960795 + 1049244 * 2 ^ 59
def prefixEnd_1049244 : Nat := 4983230072969 + 3 ^ 40 * 1049244 * 2
def baseEnd_1049244 : Nat := 538766495846198061724621

theorem tailTrace_1049244 : CollatzResearch.WordTrace tailWord_1049244 prefixEnd_1049244 538766495846198061724621 := by
  unfold tailWord_1049244
  simp only [CollatzResearch.WordTrace]
  refine ⟨19134536305387829726869393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25512715073850439635825857 19134536305387829726869393)
  ·
    refine ⟨14350902229040872295152045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19134536305387829726869393 14350902229040872295152045)
    ·
      refine ⟨5381588335890327110682017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14350902229040872295152045 5381588335890327110682017)
      ·
        refine ⟨4036191251917745333011513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5381588335890327110682017 4036191251917745333011513)
        ·
          refine ⟨3027143438938308999758635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4036191251917745333011513 3027143438938308999758635)
          ·
            refine ⟨4540715158407463499637953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3027143438938308999758635 4540715158407463499637953)
            ·
              refine ⟨3405536368805597624728465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4540715158407463499637953 3405536368805597624728465)
              ·
                refine ⟨2554152276604198218546349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3405536368805597624728465 2554152276604198218546349)
                ·
                  refine ⟨957807103726574331954881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2554152276604198218546349 957807103726574331954881)
                  ·
                    refine ⟨718355327794930748966161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 957807103726574331954881 718355327794930748966161)
                    ·
                      refine ⟨538766495846198061724621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 718355327794930748966161 538766495846198061724621)
                      ·
                        rfl

theorem cell23_1049244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_1049244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049244 prefixEnd_1049244 := by exact prefixLift 1049244
  have htrace : WordTrace (prefixWord ++ tailWord_1049244) baseStart_1049244 baseEnd_1049244 := by
    simpa [prefixWord, tailWord_1049244, baseEnd_1049244] using wordTrace_append hprefix tailTrace_1049244
  have hstable : (prefixWord ++ tailWord_1049244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049244).length < 2 ^ (prefixWord ++ tailWord_1049244).sum := by decide
  have hdescent : baseEnd_1049244 < baseStart_1049244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049255 : List Nat := [1, 1, 6, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_1049255 : Nat := 118140960795 + 1049255 * 2 ^ 59
def prefixEnd_1049255 : Nat := 4983230072969 + 3 ^ 40 * 1049255 * 2
def baseEnd_1049255 : Nat := 538772144133397518687071

theorem tailTrace_1049255 : CollatzResearch.WordTrace tailWord_1049255 prefixEnd_1049255 538772144133397518687071 := by
  unfold tailWord_1049255
  simp only [CollatzResearch.WordTrace]
  refine ⟨38269473813735808332389219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25512982542490538888259479 38269473813735808332389219)
  ·
    refine ⟨57404210720603712498583829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38269473813735808332389219 57404210720603712498583829)
    ·
      refine ⟨2690822377528299023371117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57404210720603712498583829 2690822377528299023371117)
      ·
        refine ⟨1009058391573112133764169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2690822377528299023371117 1009058391573112133764169)
        ·
          refine ⟨756793793679834100323127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1009058391573112133764169 756793793679834100323127)
          ·
            refine ⟨1135190690519751150484691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756793793679834100323127 1135190690519751150484691)
            ·
              refine ⟨1702786035779626725727037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1135190690519751150484691 1702786035779626725727037)
              ·
                refine ⟨638544763417360022147639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1702786035779626725727037 638544763417360022147639)
                ·
                  refine ⟨957817145126040033221459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 638544763417360022147639 957817145126040033221459)
                  ·
                    refine ⟨1436725717689060049832189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 957817145126040033221459 1436725717689060049832189)
                    ·
                      refine ⟨538772144133397518687071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1436725717689060049832189 538772144133397518687071)
                      ·
                        rfl

theorem cell23_1049255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_1049255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049255 prefixEnd_1049255 := by exact prefixLift 1049255
  have htrace : WordTrace (prefixWord ++ tailWord_1049255) baseStart_1049255 baseEnd_1049255 := by
    simpa [prefixWord, tailWord_1049255, baseEnd_1049255] using wordTrace_append hprefix tailTrace_1049255
  have hstable : (prefixWord ++ tailWord_1049255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049255).length < 2 ^ (prefixWord ++ tailWord_1049255).sum := by decide
  have hdescent : baseEnd_1049255 < baseStart_1049255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049273 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 4, 2, 5]
def baseStart_1049273 : Nat := 118140960795 + 1049273 * 2 ^ 59
def prefixEnd_1049273 : Nat := 4983230072969 + 3 ^ 40 * 1049273 * 2
def baseEnd_1049273 : Nat := 538781386785178448261987

theorem tailTrace_1049273 : CollatzResearch.WordTrace tailWord_1049273 prefixEnd_1049273 538781386785178448261987 := by
  unfold tailWord_1049273
  simp only [CollatzResearch.WordTrace]
  refine ⟨38270130327670597406544473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25513420218447064937696315 38270130327670597406544473)
  ·
    refine ⟨28702597745752948054908355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38270130327670597406544473 28702597745752948054908355)
    ·
      refine ⟨43053896618629422082362533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28702597745752948054908355 43053896618629422082362533)
      ·
        refine ⟨8072605615993016640442975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43053896618629422082362533 8072605615993016640442975)
        ·
          refine ⟨12108908423989524960664463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8072605615993016640442975 12108908423989524960664463)
          ·
            refine ⟨18163362635984287440996695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12108908423989524960664463 18163362635984287440996695)
            ·
              refine ⟨27245043953976431161495043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18163362635984287440996695 27245043953976431161495043)
              ·
                refine ⟨40867565930964646742242565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27245043953976431161495043 40867565930964646742242565)
                ·
                  refine ⟨7662668612055871264170481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40867565930964646742242565 7662668612055871264170481)
                  ·
                    refine ⟨5747001459041903448127861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7662668612055871264170481 5747001459041903448127861)
                    ·
                      refine ⟨538781386785178448261987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5747001459041903448127861 538781386785178448261987)
                      ·
                        rfl

theorem cell23_1049273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_1049273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049273 prefixEnd_1049273 := by exact prefixLift 1049273
  have htrace : WordTrace (prefixWord ++ tailWord_1049273) baseStart_1049273 baseEnd_1049273 := by
    simpa [prefixWord, tailWord_1049273, baseEnd_1049273] using wordTrace_append hprefix tailTrace_1049273
  have hstable : (prefixWord ++ tailWord_1049273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049273).length < 2 ^ (prefixWord ++ tailWord_1049273).sum := by decide
  have hdescent : baseEnd_1049273 < baseStart_1049273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049277 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 4, 1, 3]
def baseStart_1049277 : Nat := 118140960795 + 1049277 * 2 ^ 59
def prefixEnd_1049277 : Nat := 4983230072969 + 3 ^ 40 * 1049277 * 2
def baseEnd_1049277 : Nat := 538783440707796432611969

theorem tailTrace_1049277 : CollatzResearch.WordTrace tailWord_1049277 prefixEnd_1049277 538783440707796432611969 := by
  unfold tailWord_1049277
  simp only [CollatzResearch.WordTrace]
  refine ⟨38270276219656106089690085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25513517479770737393126723 38270276219656106089690085)
  ·
    refine ⟨7175676791185519891816891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38270276219656106089690085 7175676791185519891816891)
    ·
      refine ⟨10763515186778279837725337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7175676791185519891816891 10763515186778279837725337)
      ·
        refine ⟨8072636390083709878294003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10763515186778279837725337 8072636390083709878294003)
        ·
          refine ⟨12108954585125564817441005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8072636390083709878294003 12108954585125564817441005)
          ·
            refine ⟨4540857969422086806540377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12108954585125564817441005 4540857969422086806540377)
            ·
              refine ⟨3405643477066565104905283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4540857969422086806540377 3405643477066565104905283)
              ·
                refine ⟨5108465215599847657357925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3405643477066565104905283 5108465215599847657357925)
                ·
                  refine ⟨957837227924971435754611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5108465215599847657357925 957837227924971435754611)
                  ·
                    refine ⟨1436755841887457153631917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 957837227924971435754611 1436755841887457153631917)
                    ·
                      refine ⟨538783440707796432611969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1436755841887457153631917 538783440707796432611969)
                      ·
                        rfl

theorem cell23_1049277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_1049277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049277 prefixEnd_1049277 := by exact prefixLift 1049277
  have htrace : WordTrace (prefixWord ++ tailWord_1049277) baseStart_1049277 baseEnd_1049277 := by
    simpa [prefixWord, tailWord_1049277, baseEnd_1049277] using wordTrace_append hprefix tailTrace_1049277
  have hstable : (prefixWord ++ tailWord_1049277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049277).length < 2 ^ (prefixWord ++ tailWord_1049277).sum := by decide
  have hdescent : baseEnd_1049277 < baseStart_1049277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049278 : List Nat := [4, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2]
def baseStart_1049278 : Nat := 118140960795 + 1049278 * 2 ^ 59
def prefixEnd_1049278 : Nat := 4983230072969 + 3 ^ 40 * 1049278 * 2
def baseEnd_1049278 : Nat := 538783954188450928699465

theorem tailTrace_1049278 : CollatzResearch.WordTrace tailWord_1049278 prefixEnd_1049278 538783954188450928699465 := by
  unfold tailWord_1049278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4783789086581560407559561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25513541795101655506984325 4783789086581560407559561)
  ·
    refine ⟨3587841814936170305669671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4783789086581560407559561 3587841814936170305669671)
    ·
      refine ⟨5381762722404255458504507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3587841814936170305669671 5381762722404255458504507)
      ·
        refine ⟨8072644083606383187756761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5381762722404255458504507 8072644083606383187756761)
        ·
          refine ⟨6054483062704787390817571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8072644083606383187756761 6054483062704787390817571)
          ·
            refine ⟨9081724594057181086226357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6054483062704787390817571 9081724594057181086226357)
            ·
              refine ⟨851411680692860726833721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9081724594057181086226357 851411680692860726833721)
              ·
                refine ⟨638558760519645545125291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 851411680692860726833721 638558760519645545125291)
                ·
                  refine ⟨957838140779468317687937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 638558760519645545125291 957838140779468317687937)
                  ·
                    refine ⟨718378605584601238265953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 957838140779468317687937 718378605584601238265953)
                    ·
                      refine ⟨538783954188450928699465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 718378605584601238265953 538783954188450928699465)
                      ·
                        rfl

theorem cell23_1049278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_1049278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049278 prefixEnd_1049278 := by exact prefixLift 1049278
  have htrace : WordTrace (prefixWord ++ tailWord_1049278) baseStart_1049278 baseEnd_1049278 := by
    simpa [prefixWord, tailWord_1049278, baseEnd_1049278] using wordTrace_append hprefix tailTrace_1049278
  have hstable : (prefixWord ++ tailWord_1049278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049278).length < 2 ^ (prefixWord ++ tailWord_1049278).sum := by decide
  have hdescent : baseEnd_1049278 < baseStart_1049278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049294 : List Nat := [4, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3]
def baseStart_1049294 : Nat := 118140960795 + 1049294 * 2 ^ 59
def prefixEnd_1049294 : Nat := 4983230072969 + 3 ^ 40 * 1049294 * 2
def baseEnd_1049294 : Nat := 538792169878922866099391

theorem tailTrace_1049294 : CollatzResearch.WordTrace tailWord_1049294 prefixEnd_1049294 538792169878922866099391 := by
  unfold tailWord_1049294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4783862032574314749132367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25513930840396345328705957 4783862032574314749132367)
  ·
    refine ⟨7175793048861472123698551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4783862032574314749132367 7175793048861472123698551)
    ·
      refine ⟨10763689573292208185547827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7175793048861472123698551 10763689573292208185547827)
      ·
        refine ⟨16145534359938312278321741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10763689573292208185547827 16145534359938312278321741)
        ·
          refine ⟨6054575384976867104370653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16145534359938312278321741 6054575384976867104370653)
          ·
            refine ⟨2270465769366325164138995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6054575384976867104370653 2270465769366325164138995)
            ·
              refine ⟨3405698654049487746208493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2270465769366325164138995 3405698654049487746208493)
              ·
                refine ⟨1277136995268557904828185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3405698654049487746208493 1277136995268557904828185)
                ·
                  refine ⟨957852746451418428621139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1277136995268557904828185 957852746451418428621139)
                  ·
                    refine ⟨1436779119677127642931709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 957852746451418428621139 1436779119677127642931709)
                    ·
                      refine ⟨538792169878922866099391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1436779119677127642931709 538792169878922866099391)
                      ·
                        rfl

theorem cell23_1049294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_1049294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049294 prefixEnd_1049294 := by exact prefixLift 1049294
  have htrace : WordTrace (prefixWord ++ tailWord_1049294) baseStart_1049294 baseEnd_1049294 := by
    simpa [prefixWord, tailWord_1049294, baseEnd_1049294] using wordTrace_append hprefix tailTrace_1049294
  have hstable : (prefixWord ++ tailWord_1049294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049294).length < 2 ^ (prefixWord ++ tailWord_1049294).sum := by decide
  have hdescent : baseEnd_1049294 < baseStart_1049294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049304 : List Nat := [2, 1, 2, 2, 3, 2, 3, 2, 1, 3, 2]
def baseStart_1049304 : Nat := 118140960795 + 1049304 * 2 ^ 59
def prefixEnd_1049304 : Nat := 4983230072969 + 3 ^ 40 * 1049304 * 2
def baseEnd_1049304 : Nat := 538797304685467826974345

theorem tailTrace_1049304 : CollatzResearch.WordTrace tailWord_1049304 prefixEnd_1049304 538797304685467826974345 := by
  unfold tailWord_1049304
  simp only [CollatzResearch.WordTrace]
  refine ⟨19135630495279144850461483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25514173993705526467281977 19135630495279144850461483)
  ·
    refine ⟨28703445742918717275692225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19135630495279144850461483 28703445742918717275692225)
    ·
      refine ⟨21527584307189037956769169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28703445742918717275692225 21527584307189037956769169)
      ·
        refine ⟨16145688230391778467576877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21527584307189037956769169 16145688230391778467576877)
        ·
          refine ⟨6054633086396916925341329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16145688230391778467576877 6054633086396916925341329)
          ·
            refine ⟨4540974814797687694005997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6054633086396916925341329 4540974814797687694005997)
            ·
              refine ⟨1702865555549132885252249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4540974814797687694005997 1702865555549132885252249)
              ·
                refine ⟨1277149166661849663939187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1702865555549132885252249 1277149166661849663939187)
                ·
                  refine ⟨1915723749992774495908781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1277149166661849663939187 1915723749992774495908781)
                  ·
                    refine ⟨718396406247290435965793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1915723749992774495908781 718396406247290435965793)
                    ·
                      refine ⟨538797304685467826974345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 718396406247290435965793 538797304685467826974345)
                      ·
                        rfl

theorem cell23_1049304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_1049304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049304 prefixEnd_1049304 := by exact prefixLift 1049304
  have htrace : WordTrace (prefixWord ++ tailWord_1049304) baseStart_1049304 baseEnd_1049304 := by
    simpa [prefixWord, tailWord_1049304, baseEnd_1049304] using wordTrace_append hprefix tailTrace_1049304
  have hstable : (prefixWord ++ tailWord_1049304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049304).length < 2 ^ (prefixWord ++ tailWord_1049304).sum := by decide
  have hdescent : baseEnd_1049304 < baseStart_1049304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049317 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 3, 4, 2]
def baseStart_1049317 : Nat := 118140960795 + 1049317 * 2 ^ 59
def prefixEnd_1049317 : Nat := 4983230072969 + 3 ^ 40 * 1049317 * 2
def baseEnd_1049317 : Nat := 538803979933976276111785

theorem tailTrace_1049317 : CollatzResearch.WordTrace tailWord_1049317 prefixEnd_1049317 538803979933976276111785 := by
  unfold tailWord_1049317
  simp only [CollatzResearch.WordTrace]
  refine ⟨38271735139511192921146205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25514490093007461947430803 38271735139511192921146205)
  ·
    refine ⟨14351900677316697345429827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38271735139511192921146205 14351900677316697345429827)
    ·
      refine ⟨21527851015975046018144741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14351900677316697345429827 21527851015975046018144741)
      ·
        refine ⟨4036472065495321128402139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21527851015975046018144741 4036472065495321128402139)
        ·
          refine ⟨6054708098242981692603209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4036472065495321128402139 6054708098242981692603209)
          ·
            refine ⟨4541031073682236269452407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6054708098242981692603209 4541031073682236269452407)
            ·
              refine ⟨6811546610523354404178611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4541031073682236269452407 6811546610523354404178611)
              ·
                refine ⟨10217319915785031606267917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6811546610523354404178611 10217319915785031606267917)
                ·
                  refine ⟨3831494968419386852350469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10217319915785031606267917 3831494968419386852350469)
                  ·
                    refine ⟨718405306578635034815713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3831494968419386852350469 718405306578635034815713)
                    ·
                      refine ⟨538803979933976276111785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 718405306578635034815713 538803979933976276111785)
                      ·
                        rfl

theorem cell23_1049317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_1049317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049317 prefixEnd_1049317 := by exact prefixLift 1049317
  have htrace : WordTrace (prefixWord ++ tailWord_1049317) baseStart_1049317 baseEnd_1049317 := by
    simpa [prefixWord, tailWord_1049317, baseEnd_1049317] using wordTrace_append hprefix tailTrace_1049317
  have hstable : (prefixWord ++ tailWord_1049317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049317).length < 2 ^ (prefixWord ++ tailWord_1049317).sum := by decide
  have hdescent : baseEnd_1049317 < baseStart_1049317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049343 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 8]
def baseStart_1049343 : Nat := 118140960795 + 1049343 * 2 ^ 59
def prefixEnd_1049343 : Nat := 4983230072969 + 3 ^ 40 * 1049343 * 2
def baseEnd_1049343 : Nat := 538817330430993174386665

theorem tailTrace_1049343 : CollatzResearch.WordTrace tailWord_1049343 prefixEnd_1049343 538817330430993174386665 := by
  unfold tailWord_1049343
  simp only [CollatzResearch.WordTrace]
  refine ⟨38272683437416999361592683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25515122291611332907728455 38272683437416999361592683)
  ·
    refine ⟨57409025156125499042389025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38272683437416999361592683 57409025156125499042389025)
    ·
      refine ⟨43056768867094124281791769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57409025156125499042389025 43056768867094124281791769)
      ·
        refine ⟨32292576650320593211343827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43056768867094124281791769 32292576650320593211343827)
        ·
          refine ⟨48438864975480889817015741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32292576650320593211343827 48438864975480889817015741)
          ·
            refine ⟨18164574365805333681380903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48438864975480889817015741 18164574365805333681380903)
            ·
              refine ⟨27246861548708000522071355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18164574365805333681380903 27246861548708000522071355)
              ·
                refine ⟨40870292323062000783107033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27246861548708000522071355 40870292323062000783107033)
                ·
                  refine ⟨30652719242296500587330275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40870292323062000783107033 30652719242296500587330275)
                  ·
                    refine ⟨45979078863444750880995413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30652719242296500587330275 45979078863444750880995413)
                    ·
                      refine ⟨538817330430993174386665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 45979078863444750880995413 538817330430993174386665)
                      ·
                        rfl

theorem cell23_1049343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_1049343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049343 prefixEnd_1049343 := by exact prefixLift 1049343
  have htrace : WordTrace (prefixWord ++ tailWord_1049343) baseStart_1049343 baseEnd_1049343 := by
    simpa [prefixWord, tailWord_1049343, baseEnd_1049343] using wordTrace_append hprefix tailTrace_1049343
  have hstable : (prefixWord ++ tailWord_1049343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049343).length < 2 ^ (prefixWord ++ tailWord_1049343).sum := by decide
  have hdescent : baseEnd_1049343 < baseStart_1049343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049351 : List Nat := [1, 1, 4, 4, 1, 1, 2, 3, 2, 2, 2]
def baseStart_1049351 : Nat := 118140960795 + 1049351 * 2 ^ 59
def prefixEnd_1049351 : Nat := 4983230072969 + 3 ^ 40 * 1049351 * 2
def baseEnd_1049351 : Nat := 538821438276229143086629

theorem tailTrace_1049351 : CollatzResearch.WordTrace tailWord_1049351 prefixEnd_1049351 538821438276229143086629 := by
  unfold tailWord_1049351
  simp only [CollatzResearch.WordTrace]
  refine ⟨38272975221388016727883907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25515316814258677818589271 38272975221388016727883907)
  ·
    refine ⟨57409462832082025091825861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38272975221388016727883907 57409462832082025091825861)
    ·
      refine ⟨10764274281015379704717349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57409462832082025091825861 10764274281015379704717349)
      ·
        refine ⟨2018301427690383694634503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10764274281015379704717349 2018301427690383694634503)
        ·
          refine ⟨3027452141535575541951755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2018301427690383694634503 3027452141535575541951755)
          ·
            refine ⟨4541178212303363312927633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3027452141535575541951755 4541178212303363312927633)
            ·
              refine ⟨3405883659227522484695725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4541178212303363312927633 3405883659227522484695725)
              ·
                refine ⟨1277206372210320931760897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3405883659227522484695725 1277206372210320931760897)
                ·
                  refine ⟨957904779157740698820673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1277206372210320931760897 957904779157740698820673)
                  ·
                    refine ⟨718428584368305524115505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 957904779157740698820673 718428584368305524115505)
                    ·
                      refine ⟨538821438276229143086629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 718428584368305524115505 538821438276229143086629)
                      ·
                        rfl

theorem cell23_1049351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_1049351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049351 prefixEnd_1049351 := by exact prefixLift 1049351
  have htrace : WordTrace (prefixWord ++ tailWord_1049351) baseStart_1049351 baseEnd_1049351 := by
    simpa [prefixWord, tailWord_1049351, baseEnd_1049351] using wordTrace_append hprefix tailTrace_1049351
  have hstable : (prefixWord ++ tailWord_1049351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049351).length < 2 ^ (prefixWord ++ tailWord_1049351).sum := by decide
  have hdescent : baseEnd_1049351 < baseStart_1049351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049370 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 1, 7]
def baseStart_1049370 : Nat := 118140960795 + 1049370 * 2 ^ 59
def prefixEnd_1049370 : Nat := 4983230072969 + 3 ^ 40 * 1049370 * 2
def baseEnd_1049370 : Nat := 179610398136221522916347

theorem tailTrace_1049370 : CollatzResearch.WordTrace tailWord_1049370 prefixEnd_1049370 179610398136221522916347 := by
  unfold tailWord_1049370
  simp only [CollatzResearch.WordTrace]
  refine ⟨9568417052079795743206391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25515778805546121981883709 9568417052079795743206391)
  ·
    refine ⟨14352625578119693614809587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9568417052079795743206391 14352625578119693614809587)
    ·
      refine ⟨21528938367179540422214381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14352625578119693614809587 21528938367179540422214381)
      ·
        refine ⟨8073351887692327658330393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21528938367179540422214381 8073351887692327658330393)
        ·
          refine ⟨6055013915769245743747795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8073351887692327658330393 6055013915769245743747795)
          ·
            refine ⟨9082520873653868615621693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6055013915769245743747795 9082520873653868615621693)
            ·
              refine ⟨3405945327620200730858135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9082520873653868615621693 3405945327620200730858135)
              ·
                refine ⟨5108917991430301096287203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3405945327620200730858135 5108917991430301096287203)
                ·
                  refine ⟨7663376987145451644430805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5108917991430301096287203 7663376987145451644430805)
                  ·
                    refine ⟨179610398136221522916347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7663376987145451644430805 179610398136221522916347)
                    ·
                      rfl

theorem cell23_1049370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_1049370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049370 prefixEnd_1049370 := by exact prefixLift 1049370
  have htrace : WordTrace (prefixWord ++ tailWord_1049370) baseStart_1049370 baseEnd_1049370 := by
    simpa [prefixWord, tailWord_1049370, baseEnd_1049370] using wordTrace_append hprefix tailTrace_1049370
  have hstable : (prefixWord ++ tailWord_1049370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049370).length < 2 ^ (prefixWord ++ tailWord_1049370).sum := by decide
  have hdescent : baseEnd_1049370 < baseStart_1049370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049417 : List Nat := [1, 2, 1, 1, 2, 5, 2, 2, 3, 4]
def baseStart_1049417 : Nat := 118140960795 + 1049417 * 2 ^ 59
def prefixEnd_1049417 : Nat := 4983230072969 + 3 ^ 40 * 1049417 * 2
def baseEnd_1049417 : Nat := 179618442666475294953775

theorem tailTrace_1049417 : CollatzResearch.WordTrace tailWord_1049417 prefixEnd_1049417 179618442666475294953775 := by
  unfold tailWord_1049417
  simp only [CollatzResearch.WordTrace]
  refine ⟨38275382439148909999786505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25516921626099273333191003 38275382439148909999786505)
  ·
    refine ⟨28706536829361682499839879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38275382439148909999786505 28706536829361682499839879)
    ·
      refine ⟨43059805244042523749759819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28706536829361682499839879 43059805244042523749759819)
      ·
        refine ⟨64589707866063785624639729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43059805244042523749759819 64589707866063785624639729)
        ·
          refine ⟨48442280899547839218479797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64589707866063785624639729 48442280899547839218479797)
          ·
            refine ⟨4541463834332609926732481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48442280899547839218479797 4541463834332609926732481)
            ·
              refine ⟨3406097875749457445049361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4541463834332609926732481 3406097875749457445049361)
              ·
                refine ⟨2554573406812093083787021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3406097875749457445049361 2554573406812093083787021)
                ·
                  refine ⟨957965027554534906420133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2554573406812093083787021 957965027554534906420133)
                  ·
                    refine ⟨179618442666475294953775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 957965027554534906420133 179618442666475294953775)
                    ·
                      rfl

theorem cell23_1049417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 4].length) (baseStart_1049417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049417 prefixEnd_1049417 := by exact prefixLift 1049417
  have htrace : WordTrace (prefixWord ++ tailWord_1049417) baseStart_1049417 baseEnd_1049417 := by
    simpa [prefixWord, tailWord_1049417, baseEnd_1049417] using wordTrace_append hprefix tailTrace_1049417
  have hstable : (prefixWord ++ tailWord_1049417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049417).length < 2 ^ (prefixWord ++ tailWord_1049417).sum := by decide
  have hdescent : baseEnd_1049417 < baseStart_1049417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049444 : List Nat := [2, 3, 1, 1, 4, 2, 1, 2, 2, 2, 3]
def baseStart_1049444 : Nat := 118140960795 + 1049444 * 2 ^ 59
def prefixEnd_1049444 : Nat := 4983230072969 + 3 ^ 40 * 1049444 * 2
def baseEnd_1049444 : Nat := 538869191977097279223701

theorem tailTrace_1049444 : CollatzResearch.WordTrace tailWord_1049444 prefixEnd_1049444 538869191977097279223701 := by
  unfold tailWord_1049444
  simp only [CollatzResearch.WordTrace]
  refine ⟨19138183605025546805509693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25517578140034062407346257 19138183605025546805509693)
  ·
    refine ⟨7176818851884580052066135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19138183605025546805509693 7176818851884580052066135)
    ·
      refine ⟨10765228277826870078099203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7176818851884580052066135 10765228277826870078099203)
      ·
        refine ⟨16147842416740305117148805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10765228277826870078099203 16147842416740305117148805)
        ·
          refine ⟨3027720453138807209465401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16147842416740305117148805 3027720453138807209465401)
          ·
            refine ⟨2270790339854105407099051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3027720453138807209465401 2270790339854105407099051)
            ·
              refine ⟨3406185509781158110648577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2270790339854105407099051 3406185509781158110648577)
              ·
                refine ⟨2554639132335868582986433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3406185509781158110648577 2554639132335868582986433)
                ·
                  refine ⟨1915979349251901437239825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2554639132335868582986433 1915979349251901437239825)
                  ·
                    refine ⟨1436984511938926077929869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1915979349251901437239825 1436984511938926077929869)
                    ·
                      refine ⟨538869191977097279223701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1436984511938926077929869 538869191977097279223701)
                      ·
                        rfl

theorem cell23_1049444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_1049444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049444 prefixEnd_1049444 := by exact prefixLift 1049444
  have htrace : WordTrace (prefixWord ++ tailWord_1049444) baseStart_1049444 baseEnd_1049444 := by
    simpa [prefixWord, tailWord_1049444, baseEnd_1049444] using wordTrace_append hprefix tailTrace_1049444
  have hstable : (prefixWord ++ tailWord_1049444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049444).length < 2 ^ (prefixWord ++ tailWord_1049444).sum := by decide
  have hdescent : baseEnd_1049444 < baseStart_1049444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049467 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 3, 5, 2]
def baseStart_1049467 : Nat := 118140960795 + 1049467 * 2 ^ 59
def prefixEnd_1049467 : Nat := 4983230072969 + 3 ^ 40 * 1049467 * 2
def baseEnd_1049467 : Nat := 538881002032150689236095

theorem tailTrace_1049467 : CollatzResearch.WordTrace tailWord_1049467 prefixEnd_1049467 538881002032150689236095 := by
  unfold tailWord_1049467
  simp only [CollatzResearch.WordTrace]
  refine ⟨38277206088967768539106655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25518137392645179026071103 38277206088967768539106655)
  ·
    refine ⟨57415809133451652808659983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38277206088967768539106655 57415809133451652808659983)
    ·
      refine ⟨86123713700177479212989975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57415809133451652808659983 86123713700177479212989975)
      ·
        refine ⟨129185570550266218819484963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86123713700177479212989975 129185570550266218819484963)
        ·
          refine ⟨193778355825399328229227445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129185570550266218819484963 193778355825399328229227445)
          ·
            refine ⟨18166720858631187021490073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193778355825399328229227445 18166720858631187021490073)
            ·
              refine ⟨13625040643973390266117555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18166720858631187021490073 13625040643973390266117555)
              ·
                refine ⟨20437560965960085399176333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13625040643973390266117555 20437560965960085399176333)
                ·
                  refine ⟨7664085362235032024691125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20437560965960085399176333 7664085362235032024691125)
                  ·
                    refine ⟨718508002709534252314793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7664085362235032024691125 718508002709534252314793)
                    ·
                      refine ⟨538881002032150689236095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 718508002709534252314793 538881002032150689236095)
                      ·
                        rfl

theorem cell23_1049467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 5, 2].length) (baseStart_1049467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049467 prefixEnd_1049467 := by exact prefixLift 1049467
  have htrace : WordTrace (prefixWord ++ tailWord_1049467) baseStart_1049467 baseEnd_1049467 := by
    simpa [prefixWord, tailWord_1049467, baseEnd_1049467] using wordTrace_append hprefix tailTrace_1049467
  have hstable : (prefixWord ++ tailWord_1049467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049467).length < 2 ^ (prefixWord ++ tailWord_1049467).sum := by decide
  have hdescent : baseEnd_1049467 < baseStart_1049467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049477 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 3, 5]
def baseStart_1049477 : Nat := 118140960795 + 1049477 * 2 ^ 59
def prefixEnd_1049477 : Nat := 4983230072969 + 3 ^ 40 * 1049477 * 2
def baseEnd_1049477 : Nat := 179628712279565216703683

theorem tailTrace_1049477 : CollatzResearch.WordTrace tailWord_1049477 prefixEnd_1049477 179628712279565216703683 := by
  unfold tailWord_1049477
  simp only [CollatzResearch.WordTrace]
  refine ⟨38277570818931540246970685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25518380545954360164647123 38277570818931540246970685)
  ·
    refine ⟨14354089057099327592614007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38277570818931540246970685 14354089057099327592614007)
    ·
      refine ⟨21531133585648991388921011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14354089057099327592614007 21531133585648991388921011)
      ·
        refine ⟨32296700378473487083381517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21531133585648991388921011 32296700378473487083381517)
        ·
          refine ⟨12111262641927557656268069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32296700378473487083381517 12111262641927557656268069)
          ·
            refine ⟨2270861745361417060550263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12111262641927557656268069 2270861745361417060550263)
            ·
              refine ⟨3406292618042125590825395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2270861745361417060550263 3406292618042125590825395)
              ·
                refine ⟨5109438927063188386238093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406292618042125590825395 5109438927063188386238093)
                ·
                  refine ⟨1916039597648695644839285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5109438927063188386238093 1916039597648695644839285)
                  ·
                    refine ⟨179628712279565216703683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1916039597648695644839285 179628712279565216703683)
                    ·
                      rfl

theorem cell23_1049477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_1049477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049477 prefixEnd_1049477 := by exact prefixLift 1049477
  have htrace : WordTrace (prefixWord ++ tailWord_1049477) baseStart_1049477 baseEnd_1049477 := by
    simpa [prefixWord, tailWord_1049477, baseEnd_1049477] using wordTrace_append hprefix tailTrace_1049477
  have hstable : (prefixWord ++ tailWord_1049477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049477).length < 2 ^ (prefixWord ++ tailWord_1049477).sum := by decide
  have hdescent : baseEnd_1049477 < baseStart_1049477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049484 : List Nat := [2, 2, 1, 2, 1, 2, 3, 3, 2, 3, 2]
def baseStart_1049484 : Nat := 118140960795 + 1049484 * 2 ^ 59
def prefixEnd_1049484 : Nat := 4983230072969 + 3 ^ 40 * 1049484 * 2
def baseEnd_1049484 : Nat := 538889731203277122723517

theorem tailTrace_1049484 : CollatzResearch.WordTrace tailWord_1049484 prefixEnd_1049484 538889731203277122723517 := by
  unfold tailWord_1049484
  simp only [CollatzResearch.WordTrace]
  refine ⟨19138913064953090221237753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25518550753270786961650337 19138913064953090221237753)
  ·
    refine ⟨14354184798714817665928315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19138913064953090221237753 14354184798714817665928315)
    ·
      refine ⟨21531277198072226498892473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14354184798714817665928315 21531277198072226498892473)
      ·
        refine ⟨16148457898554169874169355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21531277198072226498892473 16148457898554169874169355)
        ·
          refine ⟨24222686847831254811254033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16148457898554169874169355 24222686847831254811254033)
          ·
            refine ⟨18167015135873441108440525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24222686847831254811254033 18167015135873441108440525)
            ·
              refine ⟨6812630675952540415665197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18167015135873441108440525 6812630675952540415665197)
              ·
                refine ⟨2554736503482202655874449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6812630675952540415665197 2554736503482202655874449)
                ·
                  refine ⟨1916052377611651991905837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2554736503482202655874449 1916052377611651991905837)
                  ·
                    refine ⟨718519641604369496964689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1916052377611651991905837 718519641604369496964689)
                    ·
                      refine ⟨538889731203277122723517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 718519641604369496964689 538889731203277122723517)
                      ·
                        rfl

theorem cell23_1049484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_1049484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049484 prefixEnd_1049484 := by exact prefixLift 1049484
  have htrace : WordTrace (prefixWord ++ tailWord_1049484) baseStart_1049484 baseEnd_1049484 := by
    simpa [prefixWord, tailWord_1049484, baseEnd_1049484] using wordTrace_append hprefix tailTrace_1049484
  have hstable : (prefixWord ++ tailWord_1049484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049484).length < 2 ^ (prefixWord ++ tailWord_1049484).sum := by decide
  have hdescent : baseEnd_1049484 < baseStart_1049484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049507 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 4, 4]
def baseStart_1049507 : Nat := 118140960795 + 1049507 * 2 ^ 59
def prefixEnd_1049507 : Nat := 4983230072969 + 3 ^ 40 * 1049507 * 2
def baseEnd_1049507 : Nat := 179633847086110177578637

theorem tailTrace_1049507 : CollatzResearch.WordTrace tailWord_1049507 prefixEnd_1049507 179633847086110177578637 := by
  unfold tailWord_1049507
  simp only [CollatzResearch.WordTrace]
  refine ⟨38278665008822855370562775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25519110005881903580375183 38278665008822855370562775)
  ·
    refine ⟨57417997513234283055844163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38278665008822855370562775 57417997513234283055844163)
    ·
      refine ⟨86126996269851424583766245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57417997513234283055844163 86126996269851424583766245)
      ·
        refine ⟨16148811800597142109456171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86126996269851424583766245 16148811800597142109456171)
        ·
          refine ⟨24223217700895713164184257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16148811800597142109456171 24223217700895713164184257)
          ·
            refine ⟨18167413275671784873138193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24223217700895713164184257 18167413275671784873138193)
            ·
              refine ⟨13625559956753838654853645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18167413275671784873138193 13625559956753838654853645)
              ·
                refine ⟨5109584983782689495570117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13625559956753838654853645 5109584983782689495570117)
                ·
                  refine ⟨958047184459254280419397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5109584983782689495570117 958047184459254280419397)
                  ·
                    refine ⟨179633847086110177578637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 958047184459254280419397 179633847086110177578637)
                    ·
                      rfl

theorem cell23_1049507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 4].length) (baseStart_1049507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049507 prefixEnd_1049507 := by exact prefixLift 1049507
  have htrace : WordTrace (prefixWord ++ tailWord_1049507) baseStart_1049507 baseEnd_1049507 := by
    simpa [prefixWord, tailWord_1049507, baseEnd_1049507] using wordTrace_append hprefix tailTrace_1049507
  have hstable : (prefixWord ++ tailWord_1049507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049507).length < 2 ^ (prefixWord ++ tailWord_1049507).sum := by decide
  have hdescent : baseEnd_1049507 < baseStart_1049507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049527 : List Nat := [1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 4]
def baseStart_1049527 : Nat := 118140960795 + 1049527 * 2 ^ 59
def prefixEnd_1049527 : Nat := 4983230072969 + 3 ^ 40 * 1049527 * 2
def baseEnd_1049527 : Nat := 538911810871420454485819

theorem tailTrace_1049527 : CollatzResearch.WordTrace tailWord_1049527 prefixEnd_1049527 538911810871420454485819 := by
  unfold tailWord_1049527
  simp only [CollatzResearch.WordTrace]
  refine ⟨38279394468750398786290835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25519596312500265857527223 38279394468750398786290835)
  ·
    refine ⟨57419091703125598179436253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38279394468750398786290835 57419091703125598179436253)
    ·
      refine ⟨21532159388672099317288595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57419091703125598179436253 21532159388672099317288595)
      ·
        refine ⟨32298239083008148975932893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21532159388672099317288595 32298239083008148975932893)
        ·
          refine ⟨12111839656128055865974835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32298239083008148975932893 12111839656128055865974835)
          ·
            refine ⟨18167759484192083798962253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12111839656128055865974835 18167759484192083798962253)
            ·
              refine ⟨6812909806572031424610845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18167759484192083798962253 6812909806572031424610845)
              ·
                refine ⟨2554841177464511784229067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6812909806572031424610845 2554841177464511784229067)
                ·
                  refine ⟨3832261766196767676343601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2554841177464511784229067 3832261766196767676343601)
                  ·
                    refine ⟨2874196324647575757257701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3832261766196767676343601 2874196324647575757257701)
                    ·
                      refine ⟨538911810871420454485819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2874196324647575757257701 538911810871420454485819)
                      ·
                        rfl

theorem cell23_1049527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_1049527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049527 prefixEnd_1049527 := by exact prefixLift 1049527
  have htrace : WordTrace (prefixWord ++ tailWord_1049527) baseStart_1049527 baseEnd_1049527 := by
    simpa [prefixWord, tailWord_1049527, baseEnd_1049527] using wordTrace_append hprefix tailTrace_1049527
  have hstable : (prefixWord ++ tailWord_1049527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049527).length < 2 ^ (prefixWord ++ tailWord_1049527).sum := by decide
  have hdescent : baseEnd_1049527 < baseStart_1049527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049534 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_1049534 : Nat := 118140960795 + 1049534 * 2 ^ 59
def prefixEnd_1049534 : Nat := 4983230072969 + 3 ^ 40 * 1049534 * 2
def baseEnd_1049534 : Nat := 538915405236001927098287

theorem tailTrace_1049534 : CollatzResearch.WordTrace tailWord_1049534 prefixEnd_1049534 538915405236001927098287 := by
  unfold tailWord_1049534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4784956222465629872724457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25519766519816692654530437 4784956222465629872724457)
  ·
    refine ⟨3588717166849222404543343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4784956222465629872724457 3588717166849222404543343)
    ·
      refine ⟨5383075750273833606815015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3588717166849222404543343 5383075750273833606815015)
      ·
        refine ⟨8074613625410750410222523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5383075750273833606815015 8074613625410750410222523)
        ·
          refine ⟨12111920438116125615333785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8074613625410750410222523 12111920438116125615333785)
          ·
            refine ⟨9083940328587094211500339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12111920438116125615333785 9083940328587094211500339)
            ·
              refine ⟨13625910492880641317250509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9083940328587094211500339 13625910492880641317250509)
              ·
                refine ⟨5109716434830240493968941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13625910492880641317250509 5109716434830240493968941)
                ·
                  refine ⟨1916143663061340185238353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5109716434830240493968941 1916143663061340185238353)
                  ·
                    refine ⟨1437107747296005138928765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1916143663061340185238353 1437107747296005138928765)
                    ·
                      refine ⟨538915405236001927098287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1437107747296005138928765 538915405236001927098287)
                      ·
                        rfl

theorem cell23_1049534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_1049534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049534 prefixEnd_1049534 := by exact prefixLift 1049534
  have htrace : WordTrace (prefixWord ++ tailWord_1049534) baseStart_1049534 baseEnd_1049534 := by
    simpa [prefixWord, tailWord_1049534, baseEnd_1049534] using wordTrace_append hprefix tailTrace_1049534
  have hstable : (prefixWord ++ tailWord_1049534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049534).length < 2 ^ (prefixWord ++ tailWord_1049534).sum := by decide
  have hdescent : baseEnd_1049534 < baseStart_1049534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049551 : List Nat := [1, 1, 2, 1, 1, 6, 4, 1, 1, 2, 3]
def baseStart_1049551 : Nat := 118140960795 + 1049551 * 2 ^ 59
def prefixEnd_1049551 : Nat := 4983230072969 + 3 ^ 40 * 1049551 * 2
def baseEnd_1049551 : Nat := 538924134407128360585709

theorem tailTrace_1049551 : CollatzResearch.WordTrace tailWord_1049551 prefixEnd_1049551 538924134407128360585709 := by
  unfold tailWord_1049551
  simp only [CollatzResearch.WordTrace]
  refine ⟨38280269820663450885164507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25520179880442300590109671 38280269820663450885164507)
  ·
    refine ⟨57420404730995176327746761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38280269820663450885164507 57420404730995176327746761)
    ·
      refine ⟨43065303548246382245810071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57420404730995176327746761 43065303548246382245810071)
      ·
        refine ⟨64597955322369573368715107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43065303548246382245810071 64597955322369573368715107)
        ·
          refine ⟨96896932983554360053072661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64597955322369573368715107 96896932983554360053072661)
          ·
            refine ⟨4542043733604110627487781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96896932983554360053072661 4542043733604110627487781)
            ·
              refine ⟨851633200050770742653959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4542043733604110627487781 851633200050770742653959)
              ·
                refine ⟨1277449800076156113980939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851633200050770742653959 1277449800076156113980939)
                ·
                  refine ⟨1916174700114234170971409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1277449800076156113980939 1916174700114234170971409)
                  ·
                    refine ⟨1437131025085675628228557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1916174700114234170971409 1437131025085675628228557)
                    ·
                      refine ⟨538924134407128360585709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1437131025085675628228557 538924134407128360585709)
                      ·
                        rfl

theorem cell23_1049551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 1, 2, 3].length) (baseStart_1049551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049551 prefixEnd_1049551 := by exact prefixLift 1049551
  have htrace : WordTrace (prefixWord ++ tailWord_1049551) baseStart_1049551 baseEnd_1049551 := by
    simpa [prefixWord, tailWord_1049551, baseEnd_1049551] using wordTrace_append hprefix tailTrace_1049551
  have hstable : (prefixWord ++ tailWord_1049551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049551).length < 2 ^ (prefixWord ++ tailWord_1049551).sum := by decide
  have hdescent : baseEnd_1049551 < baseStart_1049551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049558 : List Nat := [5, 2, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_1049558 : Nat := 118140960795 + 1049558 * 2 ^ 59
def prefixEnd_1049558 : Nat := 4983230072969 + 3 ^ 40 * 1049558 * 2
def baseEnd_1049558 : Nat := 179642576257236611066059

theorem tailTrace_1049558 : CollatzResearch.WordTrace tailWord_1049558 prefixEnd_1049558 179642576257236611066059 := by
  unfold tailWord_1049558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2392532820727380692541833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25520350087758727387112885 2392532820727380692541833)
  ·
    refine ⟨1794399615545535519406375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2392532820727380692541833 1794399615545535519406375)
    ·
      refine ⟨2691599423318303279109563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1794399615545535519406375 2691599423318303279109563)
      ·
        refine ⟨4037399134977454918664345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2691599423318303279109563 4037399134977454918664345)
        ·
          refine ⟨3028049351233091188998259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4037399134977454918664345 3028049351233091188998259)
          ·
            refine ⟨4542074026849636783497389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3028049351233091188998259 4542074026849636783497389)
            ·
              refine ⟨1703277760068613793811521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4542074026849636783497389 1703277760068613793811521)
              ·
                refine ⟨1277458320051460345358641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1703277760068613793811521 1277458320051460345358641)
                ·
                  refine ⟨958093740038595259018981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1277458320051460345358641 958093740038595259018981)
                  ·
                    refine ⟨179642576257236611066059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 958093740038595259018981 179642576257236611066059)
                    ·
                      rfl

theorem cell23_1049558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_1049558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049558 prefixEnd_1049558 := by exact prefixLift 1049558
  have htrace : WordTrace (prefixWord ++ tailWord_1049558) baseStart_1049558 baseEnd_1049558 := by
    simpa [prefixWord, tailWord_1049558, baseEnd_1049558] using wordTrace_append hprefix tailTrace_1049558
  have hstable : (prefixWord ++ tailWord_1049558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049558).length < 2 ^ (prefixWord ++ tailWord_1049558).sum := by decide
  have hdescent : baseEnd_1049558 < baseStart_1049558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049565 : List Nat := [1, 4, 3, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_1049565 : Nat := 118140960795 + 1049565 * 2 ^ 59
def prefixEnd_1049565 : Nat := 4983230072969 + 3 ^ 40 * 1049565 * 2
def baseEnd_1049565 : Nat := 538931323136291305810645

theorem tailTrace_1049565 : CollatzResearch.WordTrace tailWord_1049565 prefixEnd_1049565 538931323136291305810645 := by
  unfold tailWord_1049565
  simp only [CollatzResearch.WordTrace]
  refine ⟨38280780442612731276174149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25520520295075154184116099 38280780442612731276174149)
  ·
    refine ⟨7177646332989887114282653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38280780442612731276174149 7177646332989887114282653)
    ·
      refine ⟨2691617374871207667855995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7177646332989887114282653 2691617374871207667855995)
      ·
        refine ⟨4037426062306811501783993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2691617374871207667855995 4037426062306811501783993)
        ·
          refine ⟨3028069546730108626337995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4037426062306811501783993 3028069546730108626337995)
          ·
            refine ⟨4542104320095162939506993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3028069546730108626337995 4542104320095162939506993)
            ·
              refine ⟨3406578240071372204630245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4542104320095162939506993 3406578240071372204630245)
              ·
                refine ⟨638733420013382288368171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3406578240071372204630245 638733420013382288368171)
                ·
                  refine ⟨958100130020073432552257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 638733420013382288368171 958100130020073432552257)
                  ·
                    refine ⟨718575097515055074414193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 958100130020073432552257 718575097515055074414193)
                    ·
                      refine ⟨538931323136291305810645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 718575097515055074414193 538931323136291305810645)
                      ·
                        rfl

theorem cell23_1049565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_1049565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049565 prefixEnd_1049565 := by exact prefixLift 1049565
  have htrace : WordTrace (prefixWord ++ tailWord_1049565) baseStart_1049565 baseEnd_1049565 := by
    simpa [prefixWord, tailWord_1049565, baseEnd_1049565] using wordTrace_append hprefix tailTrace_1049565
  have hstable : (prefixWord ++ tailWord_1049565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049565).length < 2 ^ (prefixWord ++ tailWord_1049565).sum := by decide
  have hdescent : baseEnd_1049565 < baseStart_1049565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049617 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 4]
def baseStart_1049617 : Nat := 118140960795 + 1049617 * 2 ^ 59
def prefixEnd_1049617 : Nat := 4983230072969 + 3 ^ 40 * 1049617 * 2
def baseEnd_1049617 : Nat := 538958024130325102360405

theorem tailTrace_1049617 : CollatzResearch.WordTrace tailWord_1049617 prefixEnd_1049617 538958024130325102360405 := by
  unfold tailWord_1049617
  simp only [CollatzResearch.WordTrace]
  refine ⟨38282677038424344157067105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25521784692282896104711403 38282677038424344157067105)
  ·
    refine ⟨28712007778818258117800329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38282677038424344157067105 28712007778818258117800329)
    ·
      refine ⟨21534005834113693588350247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28712007778818258117800329 21534005834113693588350247)
      ·
        refine ⟨32301008751170540382525371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21534005834113693588350247 32301008751170540382525371)
        ·
          refine ⟨48451513126755810573788057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32301008751170540382525371 48451513126755810573788057)
          ·
            refine ⟨36338634845066857930341043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48451513126755810573788057 36338634845066857930341043)
            ·
              refine ⟨54507952267600286895511565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36338634845066857930341043 54507952267600286895511565)
              ·
                refine ⟨20440482100350107585816837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54507952267600286895511565 20440482100350107585816837)
                ·
                  refine ⟨3832590393815645172340657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20440482100350107585816837 3832590393815645172340657)
                  ·
                    refine ⟨2874442795361733879255493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3832590393815645172340657 2874442795361733879255493)
                    ·
                      refine ⟨538958024130325102360405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2874442795361733879255493 538958024130325102360405)
                      ·
                        rfl

theorem cell23_1049617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_1049617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049617 prefixEnd_1049617 := by exact prefixLift 1049617
  have htrace : WordTrace (prefixWord ++ tailWord_1049617) baseStart_1049617 baseEnd_1049617 := by
    simpa [prefixWord, tailWord_1049617, baseEnd_1049617] using wordTrace_append hprefix tailTrace_1049617
  have hstable : (prefixWord ++ tailWord_1049617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049617).length < 2 ^ (prefixWord ++ tailWord_1049617).sum := by decide
  have hdescent : baseEnd_1049617 < baseStart_1049617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049632 : List Nat := [2, 1, 1, 7, 1, 2, 2, 1, 2, 1, 3]
def baseStart_1049632 : Nat := 118140960795 + 1049632 * 2 ^ 59
def prefixEnd_1049632 : Nat := 4983230072969 + 3 ^ 40 * 1049632 * 2
def baseEnd_1049632 : Nat := 538965726340142543672837

theorem tailTrace_1049632 : CollatzResearch.WordTrace tailWord_1049632 prefixEnd_1049632 538965726340142543672837 := by
  unfold tailWord_1049632
  simp only [CollatzResearch.WordTrace]
  refine ⟨19141612066685000859431575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25522149422246667812575433 19141612066685000859431575)
  ·
    refine ⟨28712418100027501289147363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19141612066685000859431575 28712418100027501289147363)
    ·
      refine ⟨43068627150041251933721045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28712418100027501289147363 43068627150041251933721045)
      ·
        refine ⟨1009420948829091842196587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 43068627150041251933721045 1009420948829091842196587)
        ·
          refine ⟨1514131423243637763294881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009420948829091842196587 1514131423243637763294881)
          ·
            refine ⟨1135598567432728322471161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1514131423243637763294881 1135598567432728322471161)
            ·
              refine ⟨851698925574546241853371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1135598567432728322471161 851698925574546241853371)
              ·
                refine ⟨1277548388361819362780057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851698925574546241853371 1277548388361819362780057)
                ·
                  refine ⟨958161291271364522085043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1277548388361819362780057 958161291271364522085043)
                  ·
                    refine ⟨1437241936907046783127565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 958161291271364522085043 1437241936907046783127565)
                    ·
                      refine ⟨538965726340142543672837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1437241936907046783127565 538965726340142543672837)
                      ·
                        rfl

theorem cell23_1049632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_1049632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049632 prefixEnd_1049632 := by exact prefixLift 1049632
  have htrace : WordTrace (prefixWord ++ tailWord_1049632) baseStart_1049632 baseEnd_1049632 := by
    simpa [prefixWord, tailWord_1049632, baseEnd_1049632] using wordTrace_append hprefix tailTrace_1049632
  have hstable : (prefixWord ++ tailWord_1049632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049632).length < 2 ^ (prefixWord ++ tailWord_1049632).sum := by decide
  have hdescent : baseEnd_1049632 < baseStart_1049632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049642 : List Nat := [3, 1, 4, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_1049642 : Nat := 118140960795 + 1049642 * 2 ^ 59
def prefixEnd_1049642 : Nat := 4983230072969 + 3 ^ 40 * 1049642 * 2
def baseEnd_1049642 : Nat := 538970861146687504547791

theorem tailTrace_1049642 : CollatzResearch.WordTrace tailWord_1049642 prefixEnd_1049642 538970861146687504547791 := by
  unfold tailWord_1049642
  simp only [CollatzResearch.WordTrace]
  refine ⟨9570897215833443356681795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25522392575555848951151453 9570897215833443356681795)
  ·
    refine ⟨14356345823750165035022693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9570897215833443356681795 14356345823750165035022693)
    ·
      refine ⟨2691814841953155944066755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14356345823750165035022693 2691814841953155944066755)
      ·
        refine ⟨4037722262929733916100133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2691814841953155944066755 4037722262929733916100133)
        ·
          refine ⟨757072924299325109268775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4037722262929733916100133 757072924299325109268775)
          ·
            refine ⟨1135609386448987663903163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757072924299325109268775 1135609386448987663903163)
            ·
              refine ⟨1703414079673481495854745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1135609386448987663903163 1703414079673481495854745)
              ·
                refine ⟨1277560559755111121891059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1703414079673481495854745 1277560559755111121891059)
                ·
                  refine ⟨1916340839632666682836589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1277560559755111121891059 1916340839632666682836589)
                  ·
                    refine ⟨718627814862250006063721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1916340839632666682836589 718627814862250006063721)
                    ·
                      refine ⟨538970861146687504547791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 718627814862250006063721 538970861146687504547791)
                      ·
                        rfl

theorem cell23_1049642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_1049642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049642 prefixEnd_1049642 := by exact prefixLift 1049642
  have htrace : WordTrace (prefixWord ++ tailWord_1049642) baseStart_1049642 baseEnd_1049642 := by
    simpa [prefixWord, tailWord_1049642, baseEnd_1049642] using wordTrace_append hprefix tailTrace_1049642
  have hstable : (prefixWord ++ tailWord_1049642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049642).length < 2 ^ (prefixWord ++ tailWord_1049642).sum := by decide
  have hdescent : baseEnd_1049642 < baseStart_1049642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049667 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 5]
def baseStart_1049667 : Nat := 118140960795 + 1049667 * 2 ^ 59
def prefixEnd_1049667 : Nat := 4983230072969 + 3 ^ 40 * 1049667 * 2
def baseEnd_1049667 : Nat := 538983698163049906735175

theorem tailTrace_1049667 : CollatzResearch.WordTrace tailWord_1049667 prefixEnd_1049667 538983698163049906735175 := by
  unfold tailWord_1049667
  simp only [CollatzResearch.WordTrace]
  refine ⟨38284500688243202696387255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25523000458828801797591503 38284500688243202696387255)
  ·
    refine ⟨57426751032364804044580883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38284500688243202696387255 57426751032364804044580883)
    ·
      refine ⟨86140126548547206066871325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57426751032364804044580883 86140126548547206066871325)
      ·
        refine ⟨32302547455705202275076747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86140126548547206066871325 32302547455705202275076747)
        ·
          refine ⟨48453821183557803412615121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32302547455705202275076747 48453821183557803412615121)
          ·
            refine ⟨36340365887668352559461341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48453821183557803412615121 36340365887668352559461341)
            ·
              refine ⟨13627637207875632209798003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36340365887668352559461341 13627637207875632209798003)
              ·
                refine ⟨20441455811813448314697005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13627637207875632209798003 20441455811813448314697005)
                ·
                  refine ⟨7665545929430043118011377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20441455811813448314697005 7665545929430043118011377)
                  ·
                    refine ⟨5749159447072532338508533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7665545929430043118011377 5749159447072532338508533)
                    ·
                      refine ⟨538983698163049906735175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5749159447072532338508533 538983698163049906735175)
                      ·
                        rfl

theorem cell23_1049667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_1049667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049667 prefixEnd_1049667 := by exact prefixLift 1049667
  have htrace : WordTrace (prefixWord ++ tailWord_1049667) baseStart_1049667 baseEnd_1049667 := by
    simpa [prefixWord, tailWord_1049667, baseEnd_1049667] using wordTrace_append hprefix tailTrace_1049667
  have hstable : (prefixWord ++ tailWord_1049667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049667).length < 2 ^ (prefixWord ++ tailWord_1049667).sum := by decide
  have hdescent : baseEnd_1049667 < baseStart_1049667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049674 : List Nat := [3, 1, 2, 1, 1, 2, 4, 2, 2, 5]
def baseStart_1049674 : Nat := 118140960795 + 1049674 * 2 ^ 59
def prefixEnd_1049674 : Nat := 4983230072969 + 3 ^ 40 * 1049674 * 2
def baseEnd_1049674 : Nat := 179662430842543793115881

theorem tailTrace_1049674 : CollatzResearch.WordTrace tailWord_1049674 prefixEnd_1049674 179662430842543793115881 := by
  unfold tailWord_1049674
  simp only [CollatzResearch.WordTrace]
  refine ⟨9571188999804460722973019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25523170666145228594594717 9571188999804460722973019)
  ·
    refine ⟨14356783499706691084459529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9571188999804460722973019 14356783499706691084459529)
    ·
      refine ⟨10767587624780018313344647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14356783499706691084459529 10767587624780018313344647)
      ·
        refine ⟨16151381437170027470016971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10767587624780018313344647 16151381437170027470016971)
        ·
          refine ⟨24227072155755041205025457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16151381437170027470016971 24227072155755041205025457)
          ·
            refine ⟨18170304116816280903769093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24227072155755041205025457 18170304116816280903769093)
            ·
              refine ⟨3406932021903052669456705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18170304116816280903769093 3406932021903052669456705)
              ·
                refine ⟨2555199016427289502092529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3406932021903052669456705 2555199016427289502092529)
                ·
                  refine ⟨1916399262320467126569397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2555199016427289502092529 1916399262320467126569397)
                  ·
                    refine ⟨179662430842543793115881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1916399262320467126569397 179662430842543793115881)
                    ·
                      rfl

theorem cell23_1049674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_1049674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049674 prefixEnd_1049674 := by exact prefixLift 1049674
  have htrace : WordTrace (prefixWord ++ tailWord_1049674) baseStart_1049674 baseEnd_1049674 := by
    simpa [prefixWord, tailWord_1049674, baseEnd_1049674] using wordTrace_append hprefix tailTrace_1049674
  have hstable : (prefixWord ++ tailWord_1049674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049674).length < 2 ^ (prefixWord ++ tailWord_1049674).sum := by decide
  have hdescent : baseEnd_1049674 < baseStart_1049674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049684 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_1049684 : Nat := 118140960795 + 1049684 * 2 ^ 59
def prefixEnd_1049684 : Nat := 4983230072969 + 3 ^ 40 * 1049684 * 2
def baseEnd_1049684 : Nat := 538992427334176340222597

theorem tailTrace_1049684 : CollatzResearch.WordTrace tailWord_1049684 prefixEnd_1049684 538992427334176340222597 := by
  unfold tailWord_1049684
  simp only [CollatzResearch.WordTrace]
  refine ⟨19142560364590807299878053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25523413819454409733170737 19142560364590807299878053)
  ·
    refine ⟨3589230068360776368727135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19142560364590807299878053 3589230068360776368727135)
    ·
      refine ⟨5383845102541164553090703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3589230068360776368727135 5383845102541164553090703)
      ·
        refine ⟨8075767653811746829636055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5383845102541164553090703 8075767653811746829636055)
        ·
          refine ⟨12113651480717620244454083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8075767653811746829636055 12113651480717620244454083)
          ·
            refine ⟨18170477221076430366681125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12113651480717620244454083 18170477221076430366681125)
            ·
              refine ⟨3406964478951830693752711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18170477221076430366681125 3406964478951830693752711)
              ·
                refine ⟨5110446718427746040629067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406964478951830693752711 5110446718427746040629067)
                ·
                  refine ⟨7665670077641619060943601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5110446718427746040629067 7665670077641619060943601)
                  ·
                    refine ⟨5749252558231214295707701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7665670077641619060943601 5749252558231214295707701)
                    ·
                      refine ⟨538992427334176340222597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5749252558231214295707701 538992427334176340222597)
                      ·
                        rfl

theorem cell23_1049684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_1049684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049684 prefixEnd_1049684 := by exact prefixLift 1049684
  have htrace : WordTrace (prefixWord ++ tailWord_1049684) baseStart_1049684 baseEnd_1049684 := by
    simpa [prefixWord, tailWord_1049684, baseEnd_1049684] using wordTrace_append hprefix tailTrace_1049684
  have hstable : (prefixWord ++ tailWord_1049684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049684).length < 2 ^ (prefixWord ++ tailWord_1049684).sum := by decide
  have hdescent : baseEnd_1049684 < baseStart_1049684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049687 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 2, 8]
def baseStart_1049687 : Nat := 118140960795 + 1049687 * 2 ^ 59
def prefixEnd_1049687 : Nat := 4983230072969 + 3 ^ 40 * 1049687 * 2
def baseEnd_1049687 : Nat := 179664655925379942828361

theorem tailTrace_1049687 : CollatzResearch.WordTrace tailWord_1049687 prefixEnd_1049687 179664655925379942828361 := by
  unfold tailWord_1049687
  simp only [CollatzResearch.WordTrace]
  refine ⟨38285230148170746112115315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25523486765447164074743543 38285230148170746112115315)
  ·
    refine ⟨57427845222256119168172973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38285230148170746112115315 57427845222256119168172973)
    ·
      refine ⟨21535441958346044688064865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57427845222256119168172973 21535441958346044688064865)
      ·
        refine ⟨16151581468759533516048649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21535441958346044688064865 16151581468759533516048649)
        ·
          refine ⟨12113686101569650137036487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16151581468759533516048649 12113686101569650137036487)
          ·
            refine ⟨18170529152354475205554731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12113686101569650137036487 18170529152354475205554731)
            ·
              refine ⟨27255793728531712808332097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18170529152354475205554731 27255793728531712808332097)
              ·
                refine ⟨20441845296398784606249073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27255793728531712808332097 20441845296398784606249073)
                ·
                  refine ⟨15331383972299088454686805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20441845296398784606249073 15331383972299088454686805)
                  ·
                    refine ⟨179664655925379942828361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15331383972299088454686805 179664655925379942828361)
                    ·
                      rfl

theorem cell23_1049687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_1049687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049687 prefixEnd_1049687 := by exact prefixLift 1049687
  have htrace : WordTrace (prefixWord ++ tailWord_1049687) baseStart_1049687 baseEnd_1049687 := by
    simpa [prefixWord, tailWord_1049687, baseEnd_1049687] using wordTrace_append hprefix tailTrace_1049687
  have hstable : (prefixWord ++ tailWord_1049687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049687).length < 2 ^ (prefixWord ++ tailWord_1049687).sum := by decide
  have hdescent : baseEnd_1049687 < baseStart_1049687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049707 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 6]
def baseStart_1049707 : Nat := 118140960795 + 1049707 * 2 ^ 59
def prefixEnd_1049707 : Nat := 4983230072969 + 3 ^ 40 * 1049707 * 2
def baseEnd_1049707 : Nat := 539004237389229750234991

theorem tailTrace_1049707 : CollatzResearch.WordTrace tailWord_1049707 prefixEnd_1049707 539004237389229750234991 := by
  unfold tailWord_1049707
  simp only [CollatzResearch.WordTrace]
  refine ⟨38285959608098289527843375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25523973072065526351895583 38285959608098289527843375)
  ·
    refine ⟨57428939412147434291765063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38285959608098289527843375 57428939412147434291765063)
    ·
      refine ⟨86143409118221151437647595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57428939412147434291765063 86143409118221151437647595)
      ·
        refine ⟨129215113677331727156471393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86143409118221151437647595 129215113677331727156471393)
        ·
          refine ⟨96911335257998795367353545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129215113677331727156471393 96911335257998795367353545)
          ·
            refine ⟨72683501443499096525515159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96911335257998795367353545 72683501443499096525515159)
            ·
              refine ⟨109025252165248644788272739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72683501443499096525515159 109025252165248644788272739)
              ·
                refine ⟨163537878247872967182409109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109025252165248644788272739 163537878247872967182409109)
                ·
                  refine ⟨7665838042869045336675427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 163537878247872967182409109 7665838042869045336675427)
                  ·
                    refine ⟨11498757064303568005013141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7665838042869045336675427 11498757064303568005013141)
                    ·
                      refine ⟨539004237389229750234991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11498757064303568005013141 539004237389229750234991)
                      ·
                        rfl

theorem cell23_1049707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 6].length) (baseStart_1049707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049707 prefixEnd_1049707 := by exact prefixLift 1049707
  have htrace : WordTrace (prefixWord ++ tailWord_1049707) baseStart_1049707 baseEnd_1049707 := by
    simpa [prefixWord, tailWord_1049707, baseEnd_1049707] using wordTrace_append hprefix tailTrace_1049707
  have hstable : (prefixWord ++ tailWord_1049707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049707).length < 2 ^ (prefixWord ++ tailWord_1049707).sum := by decide
  have hdescent : baseEnd_1049707 < baseStart_1049707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049727 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 7]
def baseStart_1049727 : Nat := 118140960795 + 1049727 * 2 ^ 59
def prefixEnd_1049727 : Nat := 4983230072969 + 3 ^ 40 * 1049727 * 2
def baseEnd_1049727 : Nat := 539014507002319671984899

theorem tailTrace_1049727 : CollatzResearch.WordTrace tailWord_1049727 prefixEnd_1049727 539014507002319671984899 := by
  unfold tailWord_1049727
  simp only [CollatzResearch.WordTrace]
  refine ⟨38286689068025832943571435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25524459378683888629047623 38286689068025832943571435)
  ·
    refine ⟨57430033602038749415357153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38286689068025832943571435 57430033602038749415357153)
    ·
      refine ⟨43072525201529062061517865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57430033602038749415357153 43072525201529062061517865)
      ·
        refine ⟨32304393901146796546138399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43072525201529062061517865 32304393901146796546138399)
        ·
          refine ⟨48456590851720194819207599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32304393901146796546138399 48456590851720194819207599)
          ·
            refine ⟨72684886277580292228811399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48456590851720194819207599 72684886277580292228811399)
            ·
              refine ⟨109027329416370438343217099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72684886277580292228811399 109027329416370438343217099)
              ·
                refine ⟨163540994124555657514825649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109027329416370438343217099 163540994124555657514825649)
                ·
                  refine ⟨122655745593416743136119237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163540994124555657514825649 122655745593416743136119237)
                  ·
                    refine ⟨22997952298765639338022357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122655745593416743136119237 22997952298765639338022357)
                    ·
                      refine ⟨539014507002319671984899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22997952298765639338022357 539014507002319671984899)
                      ·
                        rfl

theorem cell23_1049727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_1049727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049727 prefixEnd_1049727 := by exact prefixLift 1049727
  have htrace : WordTrace (prefixWord ++ tailWord_1049727) baseStart_1049727 baseEnd_1049727 := by
    simpa [prefixWord, tailWord_1049727, baseEnd_1049727] using wordTrace_append hprefix tailTrace_1049727
  have hstable : (prefixWord ++ tailWord_1049727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049727).length < 2 ^ (prefixWord ++ tailWord_1049727).sum := by decide
  have hdescent : baseEnd_1049727 < baseStart_1049727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049738 : List Nat := [3, 1, 2, 3, 1, 1, 1, 6, 1, 4]
def baseStart_1049738 : Nat := 118140960795 + 1049738 * 2 ^ 59
def prefixEnd_1049738 : Nat := 4983230072969 + 3 ^ 40 * 1049738 * 2
def baseEnd_1049738 : Nat := 179673385096506376315783

theorem tailTrace_1049738 : CollatzResearch.WordTrace tailWord_1049738 prefixEnd_1049738 179673385096506376315783 := by
  unfold tailWord_1049738
  simp only [CollatzResearch.WordTrace]
  refine ⟨9571772567746495455555467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25524726847323987881481245 9571772567746495455555467)
  ·
    refine ⟨14357658851619743183333201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9571772567746495455555467 14357658851619743183333201)
    ·
      refine ⟨10768244138714807387499901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14357658851619743183333201 10768244138714807387499901)
      ·
        refine ⟨4038091552018052770312463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10768244138714807387499901 4038091552018052770312463)
        ·
          refine ⟨6057137328027079155468695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4038091552018052770312463 6057137328027079155468695)
          ·
            refine ⟨9085705992040618733203043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6057137328027079155468695 9085705992040618733203043)
            ·
              refine ⟨13628558988060928099804565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9085705992040618733203043 13628558988060928099804565)
              ·
                refine ⟨638838702565356004678339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13628558988060928099804565 638838702565356004678339)
                ·
                  refine ⟨958258053848034007017509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 638838702565356004678339 958258053848034007017509)
                  ·
                    refine ⟨179673385096506376315783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 958258053848034007017509 179673385096506376315783)
                    ·
                      rfl

theorem cell23_1049738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_1049738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049738 prefixEnd_1049738 := by exact prefixLift 1049738
  have htrace : WordTrace (prefixWord ++ tailWord_1049738) baseStart_1049738 baseEnd_1049738 := by
    simpa [prefixWord, tailWord_1049738, baseEnd_1049738] using wordTrace_append hprefix tailTrace_1049738
  have hstable : (prefixWord ++ tailWord_1049738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049738).length < 2 ^ (prefixWord ++ tailWord_1049738).sum := by decide
  have hdescent : baseEnd_1049738 < baseStart_1049738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049782 : List Nat := [5, 1, 3, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1049782 : Nat := 118140960795 + 1049782 * 2 ^ 59
def prefixEnd_1049782 : Nat := 4983230072969 + 3 ^ 40 * 1049782 * 2
def baseEnd_1049782 : Nat := 539042748438316956797147

theorem tailTrace_1049782 : CollatzResearch.WordTrace tailWord_1049782 prefixEnd_1049782 539042748438316956797147 := by
  unfold tailWord_1049782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2393043442676661083551475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25525796721884384891215733 2393043442676661083551475)
  ·
    refine ⟨3589565164014991625327213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2393043442676661083551475 3589565164014991625327213)
    ·
      refine ⟨1346086936505621859497705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3589565164014991625327213 1346086936505621859497705)
      ·
        refine ⟨1009565202379216394623279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1346086936505621859497705 1009565202379216394623279)
        ·
          refine ⟨1514347803568824591934919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009565202379216394623279 1514347803568824591934919)
          ·
            refine ⟨2271521705353236887902379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514347803568824591934919 2271521705353236887902379)
            ·
              refine ⟨3407282558029855331853569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2271521705353236887902379 3407282558029855331853569)
              ·
                refine ⟨2555461918522391498890177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3407282558029855331853569 2555461918522391498890177)
                ·
                  refine ⟨1916596438891793624167633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2555461918522391498890177 1916596438891793624167633)
                  ·
                    refine ⟨1437447329168845218125725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1916596438891793624167633 1437447329168845218125725)
                    ·
                      refine ⟨539042748438316956797147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1437447329168845218125725 539042748438316956797147)
                      ·
                        rfl

theorem cell23_1049782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1049782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049782 prefixEnd_1049782 := by exact prefixLift 1049782
  have htrace : WordTrace (prefixWord ++ tailWord_1049782) baseStart_1049782 baseEnd_1049782 := by
    simpa [prefixWord, tailWord_1049782, baseEnd_1049782] using wordTrace_append hprefix tailTrace_1049782
  have hstable : (prefixWord ++ tailWord_1049782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049782).length < 2 ^ (prefixWord ++ tailWord_1049782).sum := by decide
  have hdescent : baseEnd_1049782 < baseStart_1049782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049788 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 4, 3, 2]
def baseStart_1049788 : Nat := 118140960795 + 1049788 * 2 ^ 59
def prefixEnd_1049788 : Nat := 4983230072969 + 3 ^ 40 * 1049788 * 2
def baseEnd_1049788 : Nat := 539045829322243933322119

theorem tailTrace_1049788 : CollatzResearch.WordTrace tailWord_1049788 prefixEnd_1049788 539045829322243933322119 := by
  unfold tailWord_1049788
  simp only [CollatzResearch.WordTrace]
  refine ⟨19144456960402420180771009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25525942613869893574361345 19144456960402420180771009)
  ·
    refine ⟨14358342720301815135578257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19144456960402420180771009 14358342720301815135578257)
    ·
      refine ⟨10768757040226361351683693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14358342720301815135578257 10768757040226361351683693)
      ·
        refine ⟨4038283890084885506881385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10768757040226361351683693 4038283890084885506881385)
        ·
          refine ⟨3028712917563664130161039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4038283890084885506881385 3028712917563664130161039)
          ·
            refine ⟨4543069376345496195241559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3028712917563664130161039 4543069376345496195241559)
            ·
              refine ⟨6814604064518244292862339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4543069376345496195241559 6814604064518244292862339)
              ·
                refine ⟨10221906096777366439293509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6814604064518244292862339 10221906096777366439293509)
                ·
                  refine ⟨1916607393145756207367533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10221906096777366439293509 1916607393145756207367533)
                  ·
                    refine ⟨718727772429658577762825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1916607393145756207367533 718727772429658577762825)
                    ·
                      refine ⟨539045829322243933322119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 718727772429658577762825 539045829322243933322119)
                      ·
                        rfl

theorem cell23_1049788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_1049788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049788 prefixEnd_1049788 := by exact prefixLift 1049788
  have htrace : WordTrace (prefixWord ++ tailWord_1049788) baseStart_1049788 baseEnd_1049788 := by
    simpa [prefixWord, tailWord_1049788, baseEnd_1049788] using wordTrace_append hprefix tailTrace_1049788
  have hstable : (prefixWord ++ tailWord_1049788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049788).length < 2 ^ (prefixWord ++ tailWord_1049788).sum := by decide
  have hdescent : baseEnd_1049788 < baseStart_1049788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049811 : List Nat := [1, 1, 1, 2, 1, 1, 1, 9, 2, 4]
def baseStart_1049811 : Nat := 118140960795 + 1049811 * 2 ^ 59
def prefixEnd_1049811 : Nat := 4983230072969 + 3 ^ 40 * 1049811 * 2
def baseEnd_1049811 : Nat := 179685879792432447778171

theorem tailTrace_1049811 : CollatzResearch.WordTrace tailWord_1049811 prefixEnd_1049811 179685879792432447778171 := by
  unfold tailWord_1049811
  simp only [CollatzResearch.WordTrace]
  refine ⟨38289752799721515289629287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25526501866481010193086191 38289752799721515289629287)
  ·
    refine ⟨57434629199582272934443931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38289752799721515289629287 57434629199582272934443931)
    ·
      refine ⟨86151943799373409401665897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57434629199582272934443931 86151943799373409401665897)
      ·
        refine ⟨64613957849530057051249423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86151943799373409401665897 64613957849530057051249423)
        ·
          refine ⟨96920936774295085576874135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64613957849530057051249423 96920936774295085576874135)
          ·
            refine ⟨145381405161442628365311203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96920936774295085576874135 145381405161442628365311203)
            ·
              refine ⟨218072107742163942547966805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145381405161442628365311203 218072107742163942547966805)
              ·
                refine ⟨1277766256301741850866993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 218072107742163942547966805 1277766256301741850866993)
                ·
                  refine ⟨958324692226306388150245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1277766256301741850866993 958324692226306388150245)
                  ·
                    refine ⟨179685879792432447778171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 958324692226306388150245 179685879792432447778171)
                    ·
                      rfl

theorem cell23_1049811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 4].length) (baseStart_1049811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049811 prefixEnd_1049811 := by exact prefixLift 1049811
  have htrace : WordTrace (prefixWord ++ tailWord_1049811) baseStart_1049811 baseEnd_1049811 := by
    simpa [prefixWord, tailWord_1049811, baseEnd_1049811] using wordTrace_append hprefix tailTrace_1049811
  have hstable : (prefixWord ++ tailWord_1049811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049811).length < 2 ^ (prefixWord ++ tailWord_1049811).sum := by decide
  have hdescent : baseEnd_1049811 < baseStart_1049811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049818 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2]
def baseStart_1049818 : Nat := 118140960795 + 1049818 * 2 ^ 59
def prefixEnd_1049818 : Nat := 4983230072969 + 3 ^ 40 * 1049818 * 2
def baseEnd_1049818 : Nat := 539061233741878815946981

theorem tailTrace_1049818 : CollatzResearch.WordTrace tailWord_1049818 prefixEnd_1049818 539061233741878815946981 := by
  unfold tailWord_1049818
  simp only [CollatzResearch.WordTrace]
  refine ⟨9572502027674038871283527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25526672073797436990089405 9572502027674038871283527)
  ·
    refine ⟨14358753041511058306925291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9572502027674038871283527 14358753041511058306925291)
    ·
      refine ⟨21538129562266587460387937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14358753041511058306925291 21538129562266587460387937)
      ·
        refine ⟨16153597171699940595290953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21538129562266587460387937 16153597171699940595290953)
        ·
          refine ⟨12115197878774955446468215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16153597171699940595290953 12115197878774955446468215)
          ·
            refine ⟨18172796818162433169702323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12115197878774955446468215 18172796818162433169702323)
            ·
              refine ⟨27259195227243649754553485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18172796818162433169702323 27259195227243649754553485)
              ·
                refine ⟨10222198210216368657957557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27259195227243649754553485 10222198210216368657957557)
                ·
                  refine ⟨958331082207784561683521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10222198210216368657957557 958331082207784561683521)
                  ·
                    refine ⟨718748311655838421262641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 958331082207784561683521 718748311655838421262641)
                    ·
                      refine ⟨539061233741878815946981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 718748311655838421262641 539061233741878815946981)
                      ·
                        rfl

theorem cell23_1049818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_1049818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049818 prefixEnd_1049818 := by exact prefixLift 1049818
  have htrace : WordTrace (prefixWord ++ tailWord_1049818) baseStart_1049818 baseEnd_1049818 := by
    simpa [prefixWord, tailWord_1049818, baseEnd_1049818] using wordTrace_append hprefix tailTrace_1049818
  have hstable : (prefixWord ++ tailWord_1049818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049818).length < 2 ^ (prefixWord ++ tailWord_1049818).sum := by decide
  have hdescent : baseEnd_1049818 < baseStart_1049818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049824 : List Nat := [2, 1, 1, 3, 1, 4, 2, 9]
def baseStart_1049824 : Nat := 118140960795 + 1049824 * 2 ^ 59
def prefixEnd_1049824 : Nat := 4983230072969 + 3 ^ 40 * 1049824 * 2
def baseEnd_1049824 : Nat := 19965344986140955276739

theorem tailTrace_1049824 : CollatzResearch.WordTrace tailWord_1049824 prefixEnd_1049824 19965344986140955276739 := by
  unfold tailWord_1049824
  simp only [CollatzResearch.WordTrace]
  refine ⟨19145113474337209254926263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25526817965782945673235017 19145113474337209254926263)
  ·
    refine ⟨28717670211505813882389395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19145113474337209254926263 28717670211505813882389395)
    ·
      refine ⟨43076505317258720823584093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28717670211505813882389395 43076505317258720823584093)
      ·
        refine ⟨16153689493972020308844035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43076505317258720823584093 16153689493972020308844035)
        ·
          refine ⟨24230534240958030463266053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16153689493972020308844035 24230534240958030463266053)
          ·
            refine ⟨4543225170179630711862385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24230534240958030463266053 4543225170179630711862385)
            ·
              refine ⟨3407418877634723033896789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4543225170179630711862385 3407418877634723033896789)
              ·
                refine ⟨19965344986140955276739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3407418877634723033896789 19965344986140955276739)
                ·
                  rfl

theorem cell23_1049824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 9].length) (baseStart_1049824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049824 prefixEnd_1049824 := by exact prefixLift 1049824
  have htrace : WordTrace (prefixWord ++ tailWord_1049824) baseStart_1049824 baseEnd_1049824 := by
    simpa [prefixWord, tailWord_1049824, baseEnd_1049824] using wordTrace_append hprefix tailTrace_1049824
  have hstable : (prefixWord ++ tailWord_1049824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049824).length < 2 ^ (prefixWord ++ tailWord_1049824).sum := by decide
  have hdescent : baseEnd_1049824 < baseStart_1049824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049838 : List Nat := [4, 1, 2, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_1049838 : Nat := 118140960795 + 1049838 * 2 ^ 59
def prefixEnd_1049838 : Nat := 4983230072969 + 3 ^ 40 * 1049838 * 2
def baseEnd_1049838 : Nat := 539071503354968737696889

theorem tailTrace_1049838 : CollatzResearch.WordTrace tailWord_1049838 prefixEnd_1049838 539071503354968737696889 := by
  unfold tailWord_1049838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4786342196327962362607771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25527158380415799267241445 4786342196327962362607771)
  ·
    refine ⟨7179513294491943543911657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4786342196327962362607771 7179513294491943543911657)
    ·
      refine ⟨5384634970868957657933743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7179513294491943543911657 5384634970868957657933743)
      ·
        refine ⟨8076952456303436486900615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5384634970868957657933743 8076952456303436486900615)
        ·
          refine ⟨12115428684455154730350923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8076952456303436486900615 12115428684455154730350923)
          ·
            refine ⟨18173143026682732095526385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12115428684455154730350923 18173143026682732095526385)
            ·
              refine ⟨13629857270012049071644789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18173143026682732095526385 13629857270012049071644789)
              ·
                refine ⟨1277799119063629600466699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13629857270012049071644789 1277799119063629600466699)
                ·
                  refine ⟨1916698678595444400700049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1277799119063629600466699 1916698678595444400700049)
                  ·
                    refine ⟨1437524008946583300525037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1916698678595444400700049 1437524008946583300525037)
                    ·
                      refine ⟨539071503354968737696889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1437524008946583300525037 539071503354968737696889)
                      ·
                        rfl

theorem cell23_1049838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_1049838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049838 prefixEnd_1049838 := by exact prefixLift 1049838
  have htrace : WordTrace (prefixWord ++ tailWord_1049838) baseStart_1049838 baseEnd_1049838 := by
    simpa [prefixWord, tailWord_1049838, baseEnd_1049838] using wordTrace_append hprefix tailTrace_1049838
  have hstable : (prefixWord ++ tailWord_1049838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049838).length < 2 ^ (prefixWord ++ tailWord_1049838).sum := by decide
  have hdescent : baseEnd_1049838 < baseStart_1049838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049868 : List Nat := [2, 2, 1, 2, 2, 4, 2, 1, 1, 3, 3]
def baseStart_1049868 : Nat := 118140960795 + 1049868 * 2 ^ 59
def prefixEnd_1049868 : Nat := 4983230072969 + 3 ^ 40 * 1049868 * 2
def baseEnd_1049868 : Nat := 539086907774603620321751

theorem tailTrace_1049868 : CollatzResearch.WordTrace tailWord_1049868 prefixEnd_1049868 539086907774603620321751 := by
  unfold tailWord_1049868
  simp only [CollatzResearch.WordTrace]
  refine ⟨19145915880257507012227129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25527887840343342682969505 19145915880257507012227129)
  ·
    refine ⟨14359436910193130259170347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19145915880257507012227129 14359436910193130259170347)
    ·
      refine ⟨21539155365289695388755521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14359436910193130259170347 21539155365289695388755521)
      ·
        refine ⟨16154366523967271541566641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21539155365289695388755521 16154366523967271541566641)
        ·
          refine ⟨12115774892975453656174981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16154366523967271541566641 12115774892975453656174981)
          ·
            refine ⟨2271707792432897560532809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12115774892975453656174981 2271707792432897560532809)
            ·
              refine ⟨1703780844324673170399607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2271707792432897560532809 1703780844324673170399607)
              ·
                refine ⟨2555671266487009755599411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1703780844324673170399607 2555671266487009755599411)
                ·
                  refine ⟨3833506899730514633399117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2555671266487009755599411 3833506899730514633399117)
                  ·
                    refine ⟨1437565087398942987524669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3833506899730514633399117 1437565087398942987524669)
                    ·
                      refine ⟨539086907774603620321751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1437565087398942987524669 539086907774603620321751)
                      ·
                        rfl

theorem cell23_1049868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_1049868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049868 prefixEnd_1049868 := by exact prefixLift 1049868
  have htrace : WordTrace (prefixWord ++ tailWord_1049868) baseStart_1049868 baseEnd_1049868 := by
    simpa [prefixWord, tailWord_1049868, baseEnd_1049868] using wordTrace_append hprefix tailTrace_1049868
  have hstable : (prefixWord ++ tailWord_1049868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049868).length < 2 ^ (prefixWord ++ tailWord_1049868).sum := by decide
  have hdescent : baseEnd_1049868 < baseStart_1049868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049886 : List Nat := [4, 3, 2, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_1049886 : Nat := 118140960795 + 1049886 * 2 ^ 59
def prefixEnd_1049886 : Nat := 4983230072969 + 3 ^ 40 * 1049886 * 2
def baseEnd_1049886 : Nat := 539096150426384549896669

theorem tailTrace_1049886 : CollatzResearch.WordTrace tailWord_1049886 prefixEnd_1049886 539096150426384549896669 := by
  unfold tailWord_1049886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4786561034306225387326189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25528325516299868732406341 4786561034306225387326189)
  ·
    refine ⟨1794960387864834520247321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4786561034306225387326189 1794960387864834520247321)
    ·
      refine ⟨1346220290898625890185491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1794960387864834520247321 1346220290898625890185491)
      ·
        refine ⟨2019330436347938835278237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1346220290898625890185491 2019330436347938835278237)
        ·
          refine ⟨757248913630477063229339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2019330436347938835278237 757248913630477063229339)
          ·
            refine ⟨1135873370445715594844009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757248913630477063229339 1135873370445715594844009)
            ·
              refine ⟨851905027834286696133007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1135873370445715594844009 851905027834286696133007)
              ·
                refine ⟨1277857541751430044199511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851905027834286696133007 1277857541751430044199511)
                ·
                  refine ⟨1916786312627145066299267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1277857541751430044199511 1916786312627145066299267)
                  ·
                    refine ⟨2875179468940717599448901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1916786312627145066299267 2875179468940717599448901)
                    ·
                      refine ⟨539096150426384549896669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2875179468940717599448901 539096150426384549896669)
                      ·
                        rfl

theorem cell23_1049886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_1049886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049886 prefixEnd_1049886 := by exact prefixLift 1049886
  have htrace : WordTrace (prefixWord ++ tailWord_1049886) baseStart_1049886 baseEnd_1049886 := by
    simpa [prefixWord, tailWord_1049886, baseEnd_1049886] using wordTrace_append hprefix tailTrace_1049886
  have hstable : (prefixWord ++ tailWord_1049886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049886).length < 2 ^ (prefixWord ++ tailWord_1049886).sum := by decide
  have hdescent : baseEnd_1049886 < baseStart_1049886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049925 : List Nat := [1, 3, 1, 1, 1, 2, 1, 7, 2, 2, 2]
def baseStart_1049925 : Nat := 118140960795 + 1049925 * 2 ^ 59
def prefixEnd_1049925 : Nat := 4983230072969 + 3 ^ 40 * 1049925 * 2
def baseEnd_1049925 : Nat := 539116176171909897308989

theorem tailTrace_1049925 : CollatzResearch.WordTrace tailWord_1049925 prefixEnd_1049925 539116176171909897308989 := by
  unfold tailWord_1049925
  simp only [CollatzResearch.WordTrace]
  refine ⟨38293910721308512759279229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25529273814205675172852819 38293910721308512759279229)
  ·
    refine ⟨14360216520490692284729711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38293910721308512759279229 14360216520490692284729711)
    ·
      refine ⟨21540324780736038427094567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14360216520490692284729711 21540324780736038427094567)
      ·
        refine ⟨32310487171104057640641851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21540324780736038427094567 32310487171104057640641851)
        ·
          refine ⟨48465730756656086460962777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32310487171104057640641851 48465730756656086460962777)
          ·
            refine ⟨36349298067492064845722083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48465730756656086460962777 36349298067492064845722083)
            ·
              refine ⟨54523947101238097268583125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36349298067492064845722083 54523947101238097268583125)
              ·
                refine ⟨1277905010185267904732417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 54523947101238097268583125 1277905010185267904732417)
                ·
                  refine ⟨958428757638950928549313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1277905010185267904732417 958428757638950928549313)
                  ·
                    refine ⟨718821568229213196411985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 958428757638950928549313 718821568229213196411985)
                    ·
                      refine ⟨539116176171909897308989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 718821568229213196411985 539116176171909897308989)
                      ·
                        rfl

theorem cell23_1049925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 2, 2].length) (baseStart_1049925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049925 prefixEnd_1049925 := by exact prefixLift 1049925
  have htrace : WordTrace (prefixWord ++ tailWord_1049925) baseStart_1049925 baseEnd_1049925 := by
    simpa [prefixWord, tailWord_1049925, baseEnd_1049925] using wordTrace_append hprefix tailTrace_1049925
  have hstable : (prefixWord ++ tailWord_1049925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049925).length < 2 ^ (prefixWord ++ tailWord_1049925).sum := by decide
  have hdescent : baseEnd_1049925 < baseStart_1049925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049968 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 2, 5, 2]
def baseStart_1049968 : Nat := 118140960795 + 1049968 * 2 ^ 59
def prefixEnd_1049968 : Nat := 4983230072969 + 3 ^ 40 * 1049968 * 2
def baseEnd_1049968 : Nat := 539138255840053229071291

theorem tailTrace_1049968 : CollatzResearch.WordTrace tailWord_1049968 prefixEnd_1049968 539138255840053229071291 := by
  unfold tailWord_1049968
  simp only [CollatzResearch.WordTrace]
  refine ⟨19147739530076365551547279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25530319373435154068729705 19147739530076365551547279)
  ·
    refine ⟨28721609295114548327320919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19147739530076365551547279 28721609295114548327320919)
    ·
      refine ⟨43082413942671822490981379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28721609295114548327320919 43082413942671822490981379)
      ·
        refine ⟨64623620914007733736472069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43082413942671822490981379 64623620914007733736472069)
        ·
          refine ⟨12116928921376450075588513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64623620914007733736472069 12116928921376450075588513)
          ·
            refine ⟨9087696691032337556691385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12116928921376450075588513 9087696691032337556691385)
            ·
              refine ⟨6815772518274253167518539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9087696691032337556691385 6815772518274253167518539)
              ·
                refine ⟨10223658777411379751277809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6815772518274253167518539 10223658777411379751277809)
                ·
                  refine ⟨7667744083058534813458357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10223658777411379751277809 7667744083058534813458357)
                  ·
                    refine ⟨718851007786737638761721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7667744083058534813458357 718851007786737638761721)
                    ·
                      refine ⟨539138255840053229071291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 718851007786737638761721 539138255840053229071291)
                      ·
                        rfl

theorem cell23_1049968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 2, 5, 2].length) (baseStart_1049968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1049968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1049968 prefixEnd_1049968 := by exact prefixLift 1049968
  have htrace : WordTrace (prefixWord ++ tailWord_1049968) baseStart_1049968 baseEnd_1049968 := by
    simpa [prefixWord, tailWord_1049968, baseEnd_1049968] using wordTrace_append hprefix tailTrace_1049968
  have hstable : (prefixWord ++ tailWord_1049968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049968).length < 2 ^ (prefixWord ++ tailWord_1049968).sum := by decide
  have hdescent : baseEnd_1049968 < baseStart_1049968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050052 : List Nat := [2, 3, 3, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1050052 : Nat := 118140960795 + 1050052 * 2 ^ 59
def prefixEnd_1050052 : Nat := 4983230072969 + 3 ^ 40 * 1050052 * 2
def baseEnd_1050052 : Nat := 539181388215030900420905

theorem tailTrace_1050052 : CollatzResearch.WordTrace tailWord_1050052 prefixEnd_1050052 539181388215030900420905 := by
  unfold tailWord_1050052
  simp only [CollatzResearch.WordTrace]
  refine ⟨19149271395924206724576205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25532361861232275632768273 19149271395924206724576205)
  ·
    refine ⟨7180976773471577521716077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19149271395924206724576205 7180976773471577521716077)
    ·
      refine ⟨2692866290051841570643529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7180976773471577521716077 2692866290051841570643529)
      ·
        refine ⟨2019649717538881177982647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2692866290051841570643529 2019649717538881177982647)
        ·
          refine ⟨3029474576308321766973971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2019649717538881177982647 3029474576308321766973971)
          ·
            refine ⟨4544211864462482650460957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3029474576308321766973971 4544211864462482650460957)
            ·
              refine ⟨1704079449173430993922859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4544211864462482650460957 1704079449173430993922859)
              ·
                refine ⟨2556119173760146490884289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1704079449173430993922859 2556119173760146490884289)
                ·
                  refine ⟨1917089380320109868163217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2556119173760146490884289 1917089380320109868163217)
                  ·
                    refine ⟨1437817035240082401122413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1917089380320109868163217 1437817035240082401122413)
                    ·
                      refine ⟨539181388215030900420905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1437817035240082401122413 539181388215030900420905)
                      ·
                        rfl

theorem cell23_1050052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1050052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050052 prefixEnd_1050052 := by exact prefixLift 1050052
  have htrace : WordTrace (prefixWord ++ tailWord_1050052) baseStart_1050052 baseEnd_1050052 := by
    simpa [prefixWord, tailWord_1050052, baseEnd_1050052] using wordTrace_append hprefix tailTrace_1050052
  have hstable : (prefixWord ++ tailWord_1050052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050052).length < 2 ^ (prefixWord ++ tailWord_1050052).sum := by decide
  have hdescent : baseEnd_1050052 < baseStart_1050052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050102 : List Nat := [5, 1, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_1050102 : Nat := 118140960795 + 1050102 * 2 ^ 59
def prefixEnd_1050102 : Nat := 4983230072969 + 3 ^ 40 * 1050102 * 2
def baseEnd_1050102 : Nat := 179735687415918568265225

theorem tailTrace_1050102 : CollatzResearch.WordTrace tailWord_1050102 prefixEnd_1050102 179735687415918568265225 := by
  unfold tailWord_1050102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2393772902604204499279535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25533577627778181325648373 2393772902604204499279535)
  ·
    refine ⟨3590659353906306748919303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2393772902604204499279535 3590659353906306748919303)
    ·
      refine ⟨5385989030859460123378955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3590659353906306748919303 5385989030859460123378955)
      ·
        refine ⟨8078983546289190185068433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5385989030859460123378955 8078983546289190185068433)
        ·
          refine ⟨6059237659716892638801325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8078983546289190185068433 6059237659716892638801325)
          ·
            refine ⟨2272214122393834739550497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6059237659716892638801325 2272214122393834739550497)
            ·
              refine ⟨1704160591795376054662873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2272214122393834739550497 1704160591795376054662873)
              ·
                refine ⟨1278120443846532040997155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1704160591795376054662873 1278120443846532040997155)
                ·
                  refine ⟨1917180665769798061495733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1278120443846532040997155 1917180665769798061495733)
                  ·
                    refine ⟨179735687415918568265225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1917180665769798061495733 179735687415918568265225)
                    ·
                      rfl

theorem cell23_1050102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_1050102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050102 prefixEnd_1050102 := by exact prefixLift 1050102
  have htrace : WordTrace (prefixWord ++ tailWord_1050102) baseStart_1050102 baseEnd_1050102 := by
    simpa [prefixWord, tailWord_1050102, baseEnd_1050102] using wordTrace_append hprefix tailTrace_1050102
  have hstable : (prefixWord ++ tailWord_1050102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050102).length < 2 ^ (prefixWord ++ tailWord_1050102).sum := by decide
  have hdescent : baseEnd_1050102 < baseStart_1050102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050172 : List Nat := [2, 2, 2, 2, 4, 1, 1, 2, 1, 3, 3]
def baseStart_1050172 : Nat := 118140960795 + 1050172 * 2 ^ 59
def prefixEnd_1050172 : Nat := 4983230072969 + 3 ^ 40 * 1050172 * 2
def baseEnd_1050172 : Nat := 539243005893570430920353

theorem tailTrace_1050172 : CollatzResearch.WordTrace tailWord_1050172 prefixEnd_1050172 539243005893570430920353 := by
  unfold tailWord_1050172
  simp only [CollatzResearch.WordTrace]
  refine ⟨19151459775706836971760385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25535279700942449295680513 19151459775706836971760385)
  ·
    refine ⟨14363594831780127728820289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19151459775706836971760385 14363594831780127728820289)
    ·
      refine ⟨10772696123835095796615217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14363594831780127728820289 10772696123835095796615217)
      ·
        refine ⟨8079522092876321847461413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10772696123835095796615217 8079522092876321847461413)
        ·
          refine ⟨1514910392414310346399015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8079522092876321847461413 1514910392414310346399015)
          ·
            refine ⟨2272365588621465519598523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514910392414310346399015 2272365588621465519598523)
            ·
              refine ⟨3408548382932198279397785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2272365588621465519598523 3408548382932198279397785)
              ·
                refine ⟨2556411287199148709548339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3408548382932198279397785 2556411287199148709548339)
                ·
                  refine ⟨3834616930798723064322509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2556411287199148709548339 3834616930798723064322509)
                  ·
                    refine ⟨1437981349049521149120941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3834616930798723064322509 1437981349049521149120941)
                    ·
                      refine ⟨539243005893570430920353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1437981349049521149120941 539243005893570430920353)
                      ·
                        rfl

theorem cell23_1050172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_1050172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050172 prefixEnd_1050172 := by exact prefixLift 1050172
  have htrace : WordTrace (prefixWord ++ tailWord_1050172) baseStart_1050172 baseEnd_1050172 := by
    simpa [prefixWord, tailWord_1050172, baseEnd_1050172] using wordTrace_append hprefix tailTrace_1050172
  have hstable : (prefixWord ++ tailWord_1050172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050172).length < 2 ^ (prefixWord ++ tailWord_1050172).sum := by decide
  have hdescent : baseEnd_1050172 < baseStart_1050172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050212 : List Nat := [2, 3, 1, 1, 2, 3, 1, 3, 1, 4, 2]
def baseStart_1050212 : Nat := 118140960795 + 1050212 * 2 ^ 59
def prefixEnd_1050212 : Nat := 4983230072969 + 3 ^ 40 * 1050212 * 2
def baseEnd_1050212 : Nat := 539263545119750274420169

theorem tailTrace_1050212 : CollatzResearch.WordTrace tailWord_1050212 prefixEnd_1050212 539263545119750274420169 := by
  unfold tailWord_1050212
  simp only [CollatzResearch.WordTrace]
  refine ⟨19152189235634380387488445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25536252314179173849984593 19152189235634380387488445)
  ·
    refine ⟨7182070963362892645308167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19152189235634380387488445 7182070963362892645308167)
    ·
      refine ⟨10773106445044338967962251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7182070963362892645308167 10773106445044338967962251)
      ·
        refine ⟨16159659667566508451943377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10773106445044338967962251 16159659667566508451943377)
        ·
          refine ⟨12119744750674881338957533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16159659667566508451943377 12119744750674881338957533)
          ·
            refine ⟨4544904281503080502109075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12119744750674881338957533 4544904281503080502109075)
            ·
              refine ⟨6817356422254620753163613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4544904281503080502109075 6817356422254620753163613)
              ·
                refine ⟨2556508658345482782436355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6817356422254620753163613 2556508658345482782436355)
                ·
                  refine ⟨3834762987518224173654533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2556508658345482782436355 3834762987518224173654533)
                  ·
                    refine ⟨719018060159667032560225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3834762987518224173654533 719018060159667032560225)
                    ·
                      refine ⟨539263545119750274420169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 719018060159667032560225 539263545119750274420169)
                      ·
                        rfl

theorem cell23_1050212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_1050212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050212 prefixEnd_1050212 := by exact prefixLift 1050212
  have htrace : WordTrace (prefixWord ++ tailWord_1050212) baseStart_1050212 baseEnd_1050212 := by
    simpa [prefixWord, tailWord_1050212, baseEnd_1050212] using wordTrace_append hprefix tailTrace_1050212
  have hstable : (prefixWord ++ tailWord_1050212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050212).length < 2 ^ (prefixWord ++ tailWord_1050212).sum := by decide
  have hdescent : baseEnd_1050212 < baseStart_1050212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050229 : List Nat := [1, 3, 4, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_1050229 : Nat := 118140960795 + 1050229 * 2 ^ 59
def prefixEnd_1050229 : Nat := 4983230072969 + 3 ^ 40 * 1050229 * 2
def baseEnd_1050229 : Nat := 539272274290876707907591

theorem tailTrace_1050229 : CollatzResearch.WordTrace tailWord_1050229 prefixEnd_1050229 539272274290876707907591 := by
  unfold tailWord_1050229
  simp only [CollatzResearch.WordTrace]
  refine ⟨38304998512207172678345741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25536665674804781785563827 38304998512207172678345741)
  ·
    refine ⟨14364374442077689754379653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38304998512207172678345741 14364374442077689754379653)
    ·
      refine ⟨2693320207889566828946185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14364374442077689754379653 2693320207889566828946185)
      ·
        refine ⟨2019990155917175121709639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2693320207889566828946185 2019990155917175121709639)
        ·
          refine ⟨3029985233875762682564459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2019990155917175121709639 3029985233875762682564459)
          ·
            refine ⟨4544977850813644023846689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3029985233875762682564459 4544977850813644023846689)
            ·
              refine ⟨3408733388110233017885017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4544977850813644023846689 3408733388110233017885017)
              ·
                refine ⟨2556550041082674763413763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3408733388110233017885017 2556550041082674763413763)
                ·
                  refine ⟨3834825061624012145120645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2556550041082674763413763 3834825061624012145120645)
                  ·
                    refine ⟨719029699054502277210121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3834825061624012145120645 719029699054502277210121)
                    ·
                      refine ⟨539272274290876707907591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 719029699054502277210121 539272274290876707907591)
                      ·
                        rfl

theorem cell23_1050229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_1050229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050229 prefixEnd_1050229 := by exact prefixLift 1050229
  have htrace : WordTrace (prefixWord ++ tailWord_1050229) baseStart_1050229 baseEnd_1050229 := by
    simpa [prefixWord, tailWord_1050229, baseEnd_1050229] using wordTrace_append hprefix tailTrace_1050229
  have hstable : (prefixWord ++ tailWord_1050229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050229).length < 2 ^ (prefixWord ++ tailWord_1050229).sum := by decide
  have hdescent : baseEnd_1050229 < baseStart_1050229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050245 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 4, 3, 3]
def baseStart_1050245 : Nat := 118140960795 + 1050245 * 2 ^ 59
def prefixEnd_1050245 : Nat := 4983230072969 + 3 ^ 40 * 1050245 * 2
def baseEnd_1050245 : Nat := 539280489981348645307517

theorem tailTrace_1050245 : CollatzResearch.WordTrace tailWord_1050245 prefixEnd_1050245 539280489981348645307517 := by
  unfold tailWord_1050245
  simp only [CollatzResearch.WordTrace]
  refine ⟨38305582080149207410928189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25537054720099471607285459 38305582080149207410928189)
  ·
    refine ⟨14364593280055952779098071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38305582080149207410928189 14364593280055952779098071)
    ·
      refine ⟨21546889920083929168647107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14364593280055952779098071 21546889920083929168647107)
      ·
        refine ⟨32320334880125893752970661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21546889920083929168647107 32320334880125893752970661)
        ·
          refine ⟨6060062790023605078681999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32320334880125893752970661 6060062790023605078681999)
          ·
            refine ⟨9090094185035407618022999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6060062790023605078681999 9090094185035407618022999)
            ·
              refine ⟨13635141277553111427034499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9090094185035407618022999 13635141277553111427034499)
              ·
                refine ⟨20452711916329667140551749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13635141277553111427034499 20452711916329667140551749)
                ·
                  refine ⟨3834883484311812588853453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20452711916329667140551749 3834883484311812588853453)
                  ·
                    refine ⟨1438081306616929720820045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3834883484311812588853453 1438081306616929720820045)
                    ·
                      refine ⟨539280489981348645307517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1438081306616929720820045 539280489981348645307517)
                      ·
                        rfl

theorem cell23_1050245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_1050245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050245 prefixEnd_1050245 := by exact prefixLift 1050245
  have htrace : WordTrace (prefixWord ++ tailWord_1050245) baseStart_1050245 baseEnd_1050245 := by
    simpa [prefixWord, tailWord_1050245, baseEnd_1050245] using wordTrace_append hprefix tailTrace_1050245
  have hstable : (prefixWord ++ tailWord_1050245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050245).length < 2 ^ (prefixWord ++ tailWord_1050245).sum := by decide
  have hdescent : baseEnd_1050245 < baseStart_1050245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050302 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_1050302 : Nat := 118140960795 + 1050302 * 2 ^ 59
def prefixEnd_1050302 : Nat := 4983230072969 + 3 ^ 40 * 1050302 * 2
def baseEnd_1050302 : Nat := 539309758378654922294755

theorem tailTrace_1050302 : CollatzResearch.WordTrace tailWord_1050302 prefixEnd_1050302 539309758378654922294755 := by
  unfold tailWord_1050302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4788457630117838268219145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25538440693961804097168773 4788457630117838268219145)
  ·
    refine ⟨3591343222588378701164359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4788457630117838268219145 3591343222588378701164359)
    ·
      refine ⟨5387014833882568051746539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3591343222588378701164359 5387014833882568051746539)
      ·
        refine ⟨8080522250823852077619809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5387014833882568051746539 8080522250823852077619809)
        ·
          refine ⟨6060391688117889058214857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8080522250823852077619809 6060391688117889058214857)
          ·
            refine ⟨4545293766088416793661143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6060391688117889058214857 4545293766088416793661143)
            ·
              refine ⟨6817940649132625190491715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4545293766088416793661143 6817940649132625190491715)
              ·
                refine ⟨10226910973698937785737573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6817940649132625190491715 10226910973698937785737573)
                ·
                  refine ⟨1917545807568550834825795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10226910973698937785737573 1917545807568550834825795)
                  ·
                    refine ⟨2876318711352826252238693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1917545807568550834825795 2876318711352826252238693)
                    ·
                      refine ⟨539309758378654922294755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2876318711352826252238693 539309758378654922294755)
                      ·
                        rfl

theorem cell23_1050302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_1050302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050302 prefixEnd_1050302 := by exact prefixLift 1050302
  have htrace : WordTrace (prefixWord ++ tailWord_1050302) baseStart_1050302 baseEnd_1050302 := by
    simpa [prefixWord, tailWord_1050302, baseEnd_1050302] using wordTrace_append hprefix tailTrace_1050302
  have hstable : (prefixWord ++ tailWord_1050302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050302).length < 2 ^ (prefixWord ++ tailWord_1050302).sum := by decide
  have hdescent : baseEnd_1050302 < baseStart_1050302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050352 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 7, 1, 3]
def baseStart_1050352 : Nat := 118140960795 + 1050352 * 2 ^ 59
def prefixEnd_1050352 : Nat := 4983230072969 + 3 ^ 40 * 1050352 * 2
def baseEnd_1050352 : Nat := 539335432411379726669525

theorem tailTrace_1050352 : CollatzResearch.WordTrace tailWord_1050352 prefixEnd_1050352 539335432411379726669525 := by
  unfold tailWord_1050352
  simp only [CollatzResearch.WordTrace]
  refine ⟨19154742345380782342536655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25539656460507709790048873 19154742345380782342536655)
  ·
    refine ⟨28732113518071173513804983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19154742345380782342536655 28732113518071173513804983)
    ·
      refine ⟨43098170277106760270707475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28732113518071173513804983 43098170277106760270707475)
      ·
        refine ⟨64647255415660140406061213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43098170277106760270707475 64647255415660140406061213)
        ·
          refine ⟨24242720780872552652272955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64647255415660140406061213 24242720780872552652272955)
          ·
            refine ⟨36364081171308828978409433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24242720780872552652272955 36364081171308828978409433)
            ·
              refine ⟨27273060878481621733807075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36364081171308828978409433 27273060878481621733807075)
              ·
                refine ⟨40909591317722432600710613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27273060878481621733807075 40909591317722432600710613)
                ·
                  refine ⟨958818546509119514079155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 40909591317722432600710613 958818546509119514079155)
                  ·
                    refine ⟨1438227819763679271118733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 958818546509119514079155 1438227819763679271118733)
                    ·
                      refine ⟨539335432411379726669525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1438227819763679271118733 539335432411379726669525)
                      ·
                        rfl

theorem cell23_1050352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 7, 1, 3].length) (baseStart_1050352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050352 prefixEnd_1050352 := by exact prefixLift 1050352
  have htrace : WordTrace (prefixWord ++ tailWord_1050352) baseStart_1050352 baseEnd_1050352 := by
    simpa [prefixWord, tailWord_1050352, baseEnd_1050352] using wordTrace_append hprefix tailTrace_1050352
  have hstable : (prefixWord ++ tailWord_1050352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050352).length < 2 ^ (prefixWord ++ tailWord_1050352).sum := by decide
  have hdescent : baseEnd_1050352 < baseStart_1050352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050362 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2]
def baseStart_1050362 : Nat := 118140960795 + 1050362 * 2 ^ 59
def prefixEnd_1050362 : Nat := 4983230072969 + 3 ^ 40 * 1050362 * 2
def baseEnd_1050362 : Nat := 539340567217924687544479

theorem tailTrace_1050362 : CollatzResearch.WordTrace tailWord_1050362 prefixEnd_1050362 539340567217924687544479 := by
  unfold tailWord_1050362
  simp only [CollatzResearch.WordTrace]
  refine ⟨9577462355181334098234335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25539899613816890928624893 9577462355181334098234335)
  ·
    refine ⟨14366193532772001147351503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9577462355181334098234335 14366193532772001147351503)
    ·
      refine ⟨21549290299158001721027255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14366193532772001147351503 21549290299158001721027255)
      ·
        refine ⟨32323935448737002581540883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21549290299158001721027255 32323935448737002581540883)
        ·
          refine ⟨48485903173105503872311325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32323935448737002581540883 48485903173105503872311325)
          ·
            refine ⟨18182213689914563952116747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48485903173105503872311325 18182213689914563952116747)
            ·
              refine ⟨27273320534871845928175121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18182213689914563952116747 27273320534871845928175121)
              ·
                refine ⟨20454990401153884446131341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27273320534871845928175121 20454990401153884446131341)
                ·
                  refine ⟨7670621400432706667299253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20454990401153884446131341 7670621400432706667299253)
                  ·
                    refine ⟨719120756290566250059305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7670621400432706667299253 719120756290566250059305)
                    ·
                      refine ⟨539340567217924687544479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 719120756290566250059305 539340567217924687544479)
                      ·
                        rfl

theorem cell23_1050362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2].length) (baseStart_1050362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050362 prefixEnd_1050362 := by exact prefixLift 1050362
  have htrace : WordTrace (prefixWord ++ tailWord_1050362) baseStart_1050362 baseEnd_1050362 := by
    simpa [prefixWord, tailWord_1050362, baseEnd_1050362] using wordTrace_append hprefix tailTrace_1050362
  have hstable : (prefixWord ++ tailWord_1050362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050362).length < 2 ^ (prefixWord ++ tailWord_1050362).sum := by decide
  have hdescent : baseEnd_1050362 < baseStart_1050362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050372 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 3, 5]
def baseStart_1050372 : Nat := 118140960795 + 1050372 * 2 ^ 59
def prefixEnd_1050372 : Nat := 4983230072969 + 3 ^ 40 * 1050372 * 2
def baseEnd_1050372 : Nat := 179781900674823216139811

theorem tailTrace_1050372 : CollatzResearch.WordTrace tailWord_1050372 prefixEnd_1050372 179781900674823216139811 := by
  unfold tailWord_1050372
  simp only [CollatzResearch.WordTrace]
  refine ⟨19155107075344554050400685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25540142767126072067200913 19155107075344554050400685)
  ·
    refine ⟨7183165153254207768900257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19155107075344554050400685 7183165153254207768900257)
    ·
      refine ⟨5387373864940655826675193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7183165153254207768900257 5387373864940655826675193)
      ·
        refine ⟨4040530398705491870006395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5387373864940655826675193 4040530398705491870006395)
        ·
          refine ⟨6060795598058237805009593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4040530398705491870006395 6060795598058237805009593)
          ·
            refine ⟨4545596698543678353757195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6060795598058237805009593 4545596698543678353757195)
            ·
              refine ⟨6818395047815517530635793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4545596698543678353757195 6818395047815517530635793)
              ·
                refine ⟨5113796285861638147976845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6818395047815517530635793 5113796285861638147976845)
                ·
                  refine ⟨1917673607198114305491317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5113796285861638147976845 1917673607198114305491317)
                  ·
                    refine ⟨179781900674823216139811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1917673607198114305491317 179781900674823216139811)
                    ·
                      rfl

theorem cell23_1050372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_1050372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050372 prefixEnd_1050372 := by exact prefixLift 1050372
  have htrace : WordTrace (prefixWord ++ tailWord_1050372) baseStart_1050372 baseEnd_1050372 := by
    simpa [prefixWord, tailWord_1050372, baseEnd_1050372] using wordTrace_append hprefix tailTrace_1050372
  have hstable : (prefixWord ++ tailWord_1050372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050372).length < 2 ^ (prefixWord ++ tailWord_1050372).sum := by decide
  have hdescent : baseEnd_1050372 < baseStart_1050372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050386 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_1050386 : Nat := 118140960795 + 1050386 * 2 ^ 59
def prefixEnd_1050386 : Nat := 4983230072969 + 3 ^ 40 * 1050386 * 2
def baseEnd_1050386 : Nat := 539352890753632593644369

theorem tailTrace_1050386 : CollatzResearch.WordTrace tailWord_1050386 prefixEnd_1050386 539352890753632593644369 := by
  unfold tailWord_1050386
  simp only [CollatzResearch.WordTrace]
  refine ⟨9577681193159597122952753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25540483181758925661207341 9577681193159597122952753)
  ·
    refine ⟨7183260894869697842214565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9577681193159597122952753 7183260894869697842214565)
    ·
      refine ⟨1346861417788068345415231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7183260894869697842214565 1346861417788068345415231)
      ·
        refine ⟨2020292126682102518122847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1346861417788068345415231 2020292126682102518122847)
        ·
          refine ⟨3030438190023153777184271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2020292126682102518122847 3030438190023153777184271)
          ·
            refine ⟨4545657285034730665776407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3030438190023153777184271 4545657285034730665776407)
            ·
              refine ⟨6818485927552095998664611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4545657285034730665776407 6818485927552095998664611)
              ·
                refine ⟨10227728891328143997996917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6818485927552095998664611 10227728891328143997996917)
                ·
                  refine ⟨958849583562013499812211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10227728891328143997996917 958849583562013499812211)
                  ·
                    refine ⟨1438274375343020249718317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 958849583562013499812211 1438274375343020249718317)
                    ·
                      refine ⟨539352890753632593644369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1438274375343020249718317 539352890753632593644369)
                      ·
                        rfl

theorem cell23_1050386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_1050386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050386 prefixEnd_1050386 := by exact prefixLift 1050386
  have htrace : WordTrace (prefixWord ++ tailWord_1050386) baseStart_1050386 baseEnd_1050386 := by
    simpa [prefixWord, tailWord_1050386, baseEnd_1050386] using wordTrace_append hprefix tailTrace_1050386
  have hstable : (prefixWord ++ tailWord_1050386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050386).length < 2 ^ (prefixWord ++ tailWord_1050386).sum := by decide
  have hdescent : baseEnd_1050386 < baseStart_1050386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050392 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 3, 1, 4]
def baseStart_1050392 : Nat := 118140960795 + 1050392 * 2 ^ 59
def prefixEnd_1050392 : Nat := 4983230072969 + 3 ^ 40 * 1050392 * 2
def baseEnd_1050392 : Nat := 539355971637559570169341

theorem tailTrace_1050392 : CollatzResearch.WordTrace tailWord_1050392 prefixEnd_1050392 539355971637559570169341 := by
  unfold tailWord_1050392
  simp only [CollatzResearch.WordTrace]
  refine ⟨19155471805308325758264715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25540629073744434344352953 19155471805308325758264715)
  ·
    refine ⟨28733207707962488637397073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19155471805308325758264715 28733207707962488637397073)
    ·
      refine ⟨21549905780971866478047805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28733207707962488637397073 21549905780971866478047805)
      ·
        refine ⟨8081214667864449929267927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21549905780971866478047805 8081214667864449929267927)
        ·
          refine ⟨12121822001796674893901891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8081214667864449929267927 12121822001796674893901891)
          ·
            refine ⟨18182733002695012340852837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12121822001796674893901891 18182733002695012340852837)
            ·
              refine ⟨3409262438005314813909907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18182733002695012340852837 3409262438005314813909907)
              ·
                refine ⟨5113893657007972220864861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3409262438005314813909907 5113893657007972220864861)
                ·
                  refine ⟨1917710121377989582824323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5113893657007972220864861 1917710121377989582824323)
                  ·
                    refine ⟨2876565182066984374236485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1917710121377989582824323 2876565182066984374236485)
                    ·
                      refine ⟨539355971637559570169341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2876565182066984374236485 539355971637559570169341)
                      ·
                        rfl

theorem cell23_1050392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_1050392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050392 prefixEnd_1050392 := by exact prefixLift 1050392
  have htrace : WordTrace (prefixWord ++ tailWord_1050392) baseStart_1050392 baseEnd_1050392 := by
    simpa [prefixWord, tailWord_1050392, baseEnd_1050392] using wordTrace_append hprefix tailTrace_1050392
  have hstable : (prefixWord ++ tailWord_1050392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050392).length < 2 ^ (prefixWord ++ tailWord_1050392).sum := by decide
  have hdescent : baseEnd_1050392 < baseStart_1050392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050395 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 5]
def baseStart_1050395 : Nat := 118140960795 + 1050395 * 2 ^ 59
def prefixEnd_1050395 : Nat := 4983230072969 + 3 ^ 40 * 1050395 * 2
def baseEnd_1050395 : Nat := 539357512079523058431827

theorem tailTrace_1050395 : CollatzResearch.WordTrace tailWord_1050395 prefixEnd_1050395 539357512079523058431827 := by
  unfold tailWord_1050395
  simp only [CollatzResearch.WordTrace]
  refine ⟨38311053029605783028888639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25540702019737188685925759 38311053029605783028888639)
  ·
    refine ⟨57466579544408674543332959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38311053029605783028888639 57466579544408674543332959)
    ·
      refine ⟨86199869316613011814999439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57466579544408674543332959 86199869316613011814999439)
      ·
        refine ⟨129299803974919517722499159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86199869316613011814999439 129299803974919517722499159)
        ·
          refine ⟨193949705962379276583748739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129299803974919517722499159 193949705962379276583748739)
          ·
            refine ⟨290924558943568914875623109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193949705962379276583748739 290924558943568914875623109)
            ·
              refine ⟨54548354801919171539179333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 290924558943568914875623109 54548354801919171539179333)
              ·
                refine ⟨10227816525359844663596125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54548354801919171539179333 10227816525359844663596125)
                ·
                  refine ⟨3835431197009941748848547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10227816525359844663596125 3835431197009941748848547)
                  ·
                    refine ⟨5753146795514912623272821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3835431197009941748848547 5753146795514912623272821)
                    ·
                      refine ⟨539357512079523058431827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5753146795514912623272821 539357512079523058431827)
                      ·
                        rfl

theorem cell23_1050395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 5].length) (baseStart_1050395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050395 prefixEnd_1050395 := by exact prefixLift 1050395
  have htrace : WordTrace (prefixWord ++ tailWord_1050395) baseStart_1050395 baseEnd_1050395 := by
    simpa [prefixWord, tailWord_1050395, baseEnd_1050395] using wordTrace_append hprefix tailTrace_1050395
  have hstable : (prefixWord ++ tailWord_1050395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050395).length < 2 ^ (prefixWord ++ tailWord_1050395).sum := by decide
  have hdescent : baseEnd_1050395 < baseStart_1050395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050402 : List Nat := [3, 3, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_1050402 : Nat := 118140960795 + 1050402 * 2 ^ 59
def prefixEnd_1050402 : Nat := 4983230072969 + 3 ^ 40 * 1050402 * 2
def baseEnd_1050402 : Nat := 179787035481368177014765

theorem tailTrace_1050402 : CollatzResearch.WordTrace tailWord_1050402 prefixEnd_1050402 179787035481368177014765 := by
  unfold tailWord_1050402
  simp only [CollatzResearch.WordTrace]
  refine ⟨9577827085145105806098365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25540872227053615482928973 9577827085145105806098365)
  ·
    refine ⟨3591685156929414677286887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9577827085145105806098365 3591685156929414677286887)
    ·
      refine ⟨5387527735394122015930331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3591685156929414677286887 5387527735394122015930331)
      ·
        refine ⟨8081291603091183023895497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5387527735394122015930331 8081291603091183023895497)
        ·
          refine ⟨6060968702318387267921623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8081291603091183023895497 6060968702318387267921623)
          ·
            refine ⟨9091453053477580901882435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6060968702318387267921623 9091453053477580901882435)
            ·
              refine ⟨13637179580216371352823653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9091453053477580901882435 13637179580216371352823653)
              ·
                refine ⟨2556971171290569628654435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13637179580216371352823653 2556971171290569628654435)
                ·
                  refine ⟨3835456756935854442981653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2556971171290569628654435 3835456756935854442981653)
                  ·
                    refine ⟨179787035481368177014765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3835456756935854442981653 179787035481368177014765)
                    ·
                      rfl

theorem cell23_1050402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_1050402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050402 prefixEnd_1050402 := by exact prefixLift 1050402
  have htrace : WordTrace (prefixWord ++ tailWord_1050402) baseStart_1050402 baseEnd_1050402 := by
    simpa [prefixWord, tailWord_1050402, baseEnd_1050402] using wordTrace_append hprefix tailTrace_1050402
  have hstable : (prefixWord ++ tailWord_1050402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050402).length < 2 ^ (prefixWord ++ tailWord_1050402).sum := by decide
  have hdescent : baseEnd_1050402 < baseStart_1050402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050419 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 4, 4]
def baseStart_1050419 : Nat := 118140960795 + 1050419 * 2 ^ 59
def prefixEnd_1050419 : Nat := 4983230072969 + 3 ^ 40 * 1050419 * 2
def baseEnd_1050419 : Nat := 179789945205076988177239

theorem tailTrace_1050419 : CollatzResearch.WordTrace tailWord_1050419 prefixEnd_1050419 179789945205076988177239 := by
  unfold tailWord_1050419
  simp only [CollatzResearch.WordTrace]
  refine ⟨38311928381518835127762311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25541285587679223418508207 38311928381518835127762311)
  ·
    refine ⟨57467892572278252691643467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38311928381518835127762311 57467892572278252691643467)
    ·
      refine ⟨86201838858417379037465201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57467892572278252691643467 86201838858417379037465201)
      ·
        refine ⟨64651379143813034278098901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86201838858417379037465201 64651379143813034278098901)
        ·
          refine ⟨1515266698683117990892943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 64651379143813034278098901 1515266698683117990892943)
          ·
            refine ⟨2272900048024676986339415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515266698683117990892943 2272900048024676986339415)
            ·
              refine ⟨3409350072037015479509123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2272900048024676986339415 3409350072037015479509123)
              ·
                refine ⟨5114025108055523219263685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3409350072037015479509123 5114025108055523219263685)
                ·
                  refine ⟨958879707760410603611941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5114025108055523219263685 958879707760410603611941)
                  ·
                    refine ⟨179789945205076988177239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 958879707760410603611941 179789945205076988177239)
                    ·
                      rfl

theorem cell23_1050419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 4].length) (baseStart_1050419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050419 prefixEnd_1050419 := by exact prefixLift 1050419
  have htrace : WordTrace (prefixWord ++ tailWord_1050419) baseStart_1050419 baseEnd_1050419 := by
    simpa [prefixWord, tailWord_1050419, baseEnd_1050419] using wordTrace_append hprefix tailTrace_1050419
  have hstable : (prefixWord ++ tailWord_1050419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050419).length < 2 ^ (prefixWord ++ tailWord_1050419).sum := by decide
  have hdescent : baseEnd_1050419 < baseStart_1050419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050426 : List Nat := [3, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2]
def baseStart_1050426 : Nat := 118140960795 + 1050426 * 2 ^ 59
def prefixEnd_1050426 : Nat := 4983230072969 + 3 ^ 40 * 1050426 * 2
def baseEnd_1050426 : Nat := 539373429979812437144185

theorem tailTrace_1050426 : CollatzResearch.WordTrace tailWord_1050426 prefixEnd_1050426 539373429979812437144185 := by
  unfold tailWord_1050426
  simp only [CollatzResearch.WordTrace]
  refine ⟨9578045923123368830816783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25541455794995650215511421 9578045923123368830816783)
  ·
    refine ⟨14367068884685053246225175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9578045923123368830816783 14367068884685053246225175)
    ·
      refine ⟨21550603327027579869337763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14367068884685053246225175 21550603327027579869337763)
      ·
        refine ⟨32325904990541369804006645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21550603327027579869337763 32325904990541369804006645)
        ·
          refine ⟨3030553592863253419125623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32325904990541369804006645 3030553592863253419125623)
          ·
            refine ⟨4545830389294880128688435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3030553592863253419125623 4545830389294880128688435)
            ·
              refine ⟨6818745583942320193032653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4545830389294880128688435 6818745583942320193032653)
              ·
                refine ⟨2557029593978370072387245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6818745583942320193032653 2557029593978370072387245)
                ·
                  refine ⟨958886097741888777145217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2557029593978370072387245 958886097741888777145217)
                  ·
                    refine ⟨719164573306416582858913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 958886097741888777145217 719164573306416582858913)
                    ·
                      refine ⟨539373429979812437144185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 719164573306416582858913 539373429979812437144185)
                      ·
                        rfl

theorem cell23_1050426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2].length) (baseStart_1050426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050426 prefixEnd_1050426 := by exact prefixLift 1050426
  have htrace : WordTrace (prefixWord ++ tailWord_1050426) baseStart_1050426 baseEnd_1050426 := by
    simpa [prefixWord, tailWord_1050426, baseEnd_1050426] using wordTrace_append hprefix tailTrace_1050426
  have hstable : (prefixWord ++ tailWord_1050426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050426).length < 2 ^ (prefixWord ++ tailWord_1050426).sum := by decide
  have hdescent : baseEnd_1050426 < baseStart_1050426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050429 : List Nat := [1, 4, 1, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1050429 : Nat := 118140960795 + 1050429 * 2 ^ 59
def prefixEnd_1050429 : Nat := 4983230072969 + 3 ^ 40 * 1050429 * 2
def baseEnd_1050429 : Nat := 539374970421775925406671

theorem tailTrace_1050429 : CollatzResearch.WordTrace tailWord_1050429 prefixEnd_1050429 539374970421775925406671 := by
  unfold tailWord_1050429
  simp only [CollatzResearch.WordTrace]
  refine ⟨38312293111482606835626341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25541528740988404557084227 38312293111482606835626341)
  ·
    refine ⟨7183554958402988781679939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38312293111482606835626341 7183554958402988781679939)
    ·
      refine ⟨10775332437604483172519909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7183554958402988781679939 10775332437604483172519909)
      ·
        refine ⟨2020374832050840594847483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10775332437604483172519909 2020374832050840594847483)
        ·
          refine ⟨3030562248076260892271225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2020374832050840594847483 3030562248076260892271225)
          ·
            refine ⟨2272921686057195669203419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3030562248076260892271225 2272921686057195669203419)
            ·
              refine ⟨3409382529085793503805129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2272921686057195669203419 3409382529085793503805129)
              ·
                refine ⟨2557036896814345127853847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3409382529085793503805129 2557036896814345127853847)
                ·
                  refine ⟨3835555345221517691780771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2557036896814345127853847 3835555345221517691780771)
                  ·
                    refine ⟨5753333017832276537671157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3835555345221517691780771 5753333017832276537671157)
                    ·
                      refine ⟨539374970421775925406671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5753333017832276537671157 539374970421775925406671)
                      ·
                        rfl

theorem cell23_1050429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1050429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050429 prefixEnd_1050429 := by exact prefixLift 1050429
  have htrace : WordTrace (prefixWord ++ tailWord_1050429) baseStart_1050429 baseEnd_1050429 := by
    simpa [prefixWord, tailWord_1050429, baseEnd_1050429] using wordTrace_append hprefix tailTrace_1050429
  have hstable : (prefixWord ++ tailWord_1050429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050429).length < 2 ^ (prefixWord ++ tailWord_1050429).sum := by decide
  have hdescent : baseEnd_1050429 < baseStart_1050429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050449 : List Nat := [1, 2, 2, 1, 5, 3, 2, 7]
def baseStart_1050449 : Nat := 118140960795 + 1050449 * 2 ^ 59
def prefixEnd_1050449 : Nat := 4983230072969 + 3 ^ 40 * 1050449 * 2
def baseEnd_1050449 : Nat := 19977231112402438783577

theorem tailTrace_1050449 : CollatzResearch.WordTrace tailWord_1050449 prefixEnd_1050449 19977231112402438783577 := by
  unfold tailWord_1050449
  simp only [CollatzResearch.WordTrace]
  refine ⟨38313022571410150251354401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25542015047606766834236267 38313022571410150251354401)
  ·
    refine ⟨28734766928557612688515801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38313022571410150251354401 28734766928557612688515801)
    ·
      refine ⟨21551075196418209516386851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28734766928557612688515801 21551075196418209516386851)
      ·
        refine ⟨32326612794627314274580277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21551075196418209516386851 32326612794627314274580277)
        ·
          refine ⟨3030619949496310713241901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32326612794627314274580277 3030619949496310713241901)
          ·
            refine ⟨1136482481061116517465713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3030619949496310713241901 1136482481061116517465713)
            ·
              refine ⟨852361860795837388099285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1136482481061116517465713 852361860795837388099285)
              ·
                refine ⟨19977231112402438783577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 852361860795837388099285 19977231112402438783577)
                ·
                  rfl

theorem cell23_1050449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 7].length) (baseStart_1050449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050449 prefixEnd_1050449 := by exact prefixLift 1050449
  have htrace : WordTrace (prefixWord ++ tailWord_1050449) baseStart_1050449 baseEnd_1050449 := by
    simpa [prefixWord, tailWord_1050449, baseEnd_1050449] using wordTrace_append hprefix tailTrace_1050449
  have hstable : (prefixWord ++ tailWord_1050449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050449).length < 2 ^ (prefixWord ++ tailWord_1050449).sum := by decide
  have hdescent : baseEnd_1050449 < baseStart_1050449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050469 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 5, 3, 2]
def baseStart_1050469 : Nat := 118140960795 + 1050469 * 2 ^ 59
def prefixEnd_1050469 : Nat := 4983230072969 + 3 ^ 40 * 1050469 * 2
def baseEnd_1050469 : Nat := 539395509647955768906487

theorem tailTrace_1050469 : CollatzResearch.WordTrace tailWord_1050469 prefixEnd_1050469 539395509647955768906487 := by
  unfold tailWord_1050469
  simp only [CollatzResearch.WordTrace]
  refine ⟨38313752031337693667082461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25542501354225129111388307 38313752031337693667082461)
  ·
    refine ⟨14367657011751635125155923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38313752031337693667082461 14367657011751635125155923)
    ·
      refine ⟨21551485517627452687733885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14367657011751635125155923 21551485517627452687733885)
      ·
        refine ⟨8081807069110294757900207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21551485517627452687733885 8081807069110294757900207)
        ·
          refine ⟨12122710603665442136850311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8081807069110294757900207 12122710603665442136850311)
          ·
            refine ⟨18184065905498163205275467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12122710603665442136850311 18184065905498163205275467)
            ·
              refine ⟨27276098858247244807913201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18184065905498163205275467 27276098858247244807913201)
              ·
                refine ⟨20457074143685433605934901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27276098858247244807913201 20457074143685433605934901)
                ·
                  refine ⟨1917850700970509400556397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20457074143685433605934901 1917850700970509400556397)
                  ·
                    refine ⟨719194012863941025208649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1917850700970509400556397 719194012863941025208649)
                    ·
                      refine ⟨539395509647955768906487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 719194012863941025208649 539395509647955768906487)
                      ·
                        rfl

theorem cell23_1050469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_1050469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050469 prefixEnd_1050469 := by exact prefixLift 1050469
  have htrace : WordTrace (prefixWord ++ tailWord_1050469) baseStart_1050469 baseEnd_1050469 := by
    simpa [prefixWord, tailWord_1050469, baseEnd_1050469] using wordTrace_append hprefix tailTrace_1050469
  have hstable : (prefixWord ++ tailWord_1050469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050469).length < 2 ^ (prefixWord ++ tailWord_1050469).sum := by decide
  have hdescent : baseEnd_1050469 < baseStart_1050469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050472 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1050472 : Nat := 118140960795 + 1050472 * 2 ^ 59
def prefixEnd_1050472 : Nat := 4983230072969 + 3 ^ 40 * 1050472 * 2
def baseEnd_1050472 : Nat := 539397050089919257168973

theorem tailTrace_1050472 : CollatzResearch.WordTrace tailWord_1050472 prefixEnd_1050472 539397050089919257168973 := by
  unfold tailWord_1050472
  simp only [CollatzResearch.WordTrace]
  refine ⟨19156930725163412589720835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25542574300217883452961113 19156930725163412589720835)
  ·
    refine ⟨28735396087745118884581253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19156930725163412589720835 28735396087745118884581253)
    ·
      refine ⟨5387886766452209790858985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28735396087745118884581253 5387886766452209790858985)
      ·
        refine ⟨4040915074839157343144239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5387886766452209790858985 4040915074839157343144239)
        ·
          refine ⟨6061372612258736014716359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4040915074839157343144239 6061372612258736014716359)
          ·
            refine ⟨9092058918388104022074539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6061372612258736014716359 9092058918388104022074539)
            ·
              refine ⟨13638088377582156033111809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9092058918388104022074539 13638088377582156033111809)
              ·
                refine ⟨10228566283186617024833857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13638088377582156033111809 10228566283186617024833857)
                ·
                  refine ⟨7671424712389962768625393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10228566283186617024833857 7671424712389962768625393)
                  ·
                    refine ⟨5753568534292472076469045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7671424712389962768625393 5753568534292472076469045)
                    ·
                      refine ⟨539397050089919257168973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5753568534292472076469045 539397050089919257168973)
                      ·
                        rfl

theorem cell23_1050472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1050472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050472 prefixEnd_1050472 := by exact prefixLift 1050472
  have htrace : WordTrace (prefixWord ++ tailWord_1050472) baseStart_1050472 baseEnd_1050472 := by
    simpa [prefixWord, tailWord_1050472, baseEnd_1050472] using wordTrace_append hprefix tailTrace_1050472
  have hstable : (prefixWord ++ tailWord_1050472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050472).length < 2 ^ (prefixWord ++ tailWord_1050472).sum := by decide
  have hdescent : baseEnd_1050472 < baseStart_1050472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050482 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_1050482 : Nat := 118140960795 + 1050482 * 2 ^ 59
def prefixEnd_1050482 : Nat := 4983230072969 + 3 ^ 40 * 1050482 * 2
def baseEnd_1050482 : Nat := 539402184896464218043927

theorem tailTrace_1050482 : CollatzResearch.WordTrace tailWord_1050482 prefixEnd_1050482 539402184896464218043927 := by
  unfold tailWord_1050482
  simp only [CollatzResearch.WordTrace]
  refine ⟨9578556545072649221826425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25542817453527064591537133 9578556545072649221826425)
  ·
    refine ⟨7183917408804486916369819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9578556545072649221826425 7183917408804486916369819)
    ·
      refine ⟨10775876113206730374554729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7183917408804486916369819 10775876113206730374554729)
      ·
        refine ⟨8081907084905047780916047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10775876113206730374554729 8081907084905047780916047)
        ·
          refine ⟨12122860627357571671374071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8081907084905047780916047 12122860627357571671374071)
          ·
            refine ⟨18184290941036357507061107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12122860627357571671374071 18184290941036357507061107)
            ·
              refine ⟨27276436411554536260591661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18184290941036357507061107 27276436411554536260591661)
              ·
                refine ⟨10228663654332951097721873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27276436411554536260591661 10228663654332951097721873)
                ·
                  refine ⟨7671497740749713323291405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10228663654332951097721873 7671497740749713323291405)
                  ·
                    refine ⟨2876811652781142496234277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7671497740749713323291405 2876811652781142496234277)
                    ·
                      refine ⟨539402184896464218043927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2876811652781142496234277 539402184896464218043927)
                      ·
                        rfl

theorem cell23_1050482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_1050482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050482 prefixEnd_1050482 := by exact prefixLift 1050482
  have htrace : WordTrace (prefixWord ++ tailWord_1050482) baseStart_1050482 baseEnd_1050482 := by
    simpa [prefixWord, tailWord_1050482, baseEnd_1050482] using wordTrace_append hprefix tailTrace_1050482
  have hstable : (prefixWord ++ tailWord_1050482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050482).length < 2 ^ (prefixWord ++ tailWord_1050482).sum := by decide
  have hdescent : baseEnd_1050482 < baseStart_1050482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050516 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_1050516 : Nat := 118140960795 + 1050516 * 2 ^ 59
def prefixEnd_1050516 : Nat := 4983230072969 + 3 ^ 40 * 1050516 * 2
def baseEnd_1050516 : Nat := 539419643238717085018771

theorem tailTrace_1050516 : CollatzResearch.WordTrace tailWord_1050516 prefixEnd_1050516 539419643238717085018771 := by
  unfold tailWord_1050516
  simp only [CollatzResearch.WordTrace]
  refine ⟨19157733131083710347021701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25543644174778280462695601 19157733131083710347021701)
  ·
    refine ⟨3592074962078195690066569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19157733131083710347021701 3592074962078195690066569)
    ·
      refine ⟨2694056221558646767549927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3592074962078195690066569 2694056221558646767549927)
      ·
        refine ⟨4041084332337970151324891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2694056221558646767549927 4041084332337970151324891)
        ·
          refine ⟨6061626498506955226987337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4041084332337970151324891 6061626498506955226987337)
          ·
            refine ⟨4546219873880216420240503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6061626498506955226987337 4546219873880216420240503)
            ·
              refine ⟨6819329810820324630360755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4546219873880216420240503 6819329810820324630360755)
              ·
                refine ⟨10228994716230486945541133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6819329810820324630360755 10228994716230486945541133)
                ·
                  refine ⟨3835873018586432604577925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10228994716230486945541133 3835873018586432604577925)
                  ·
                    refine ⟨719226190984956113358361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3835873018586432604577925 719226190984956113358361)
                    ·
                      refine ⟨539419643238717085018771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 719226190984956113358361 539419643238717085018771)
                      ·
                        rfl

theorem cell23_1050516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_1050516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050516 prefixEnd_1050516 := by exact prefixLift 1050516
  have htrace : WordTrace (prefixWord ++ tailWord_1050516) baseStart_1050516 baseEnd_1050516 := by
    simpa [prefixWord, tailWord_1050516, baseEnd_1050516] using wordTrace_append hprefix tailTrace_1050516
  have hstable : (prefixWord ++ tailWord_1050516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050516).length < 2 ^ (prefixWord ++ tailWord_1050516).sum := by decide
  have hdescent : baseEnd_1050516 < baseStart_1050516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050549 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_1050549 : Nat := 118140960795 + 1050549 * 2 ^ 59
def prefixEnd_1050549 : Nat := 4983230072969 + 3 ^ 40 * 1050549 * 2
def baseEnd_1050549 : Nat := 539436588100315455906119

theorem tailTrace_1050549 : CollatzResearch.WordTrace tailWord_1050549 prefixEnd_1050549 539436588100315455906119 := by
  unfold tailWord_1050549
  simp only [CollatzResearch.WordTrace]
  refine ⟨38316669871047867329994701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25544446580698578219996467 38316669871047867329994701)
  ·
    refine ⟨14368751201642950248748013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38316669871047867329994701 14368751201642950248748013)
    ·
      refine ⟨5388281700616106343280505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14368751201642950248748013 5388281700616106343280505)
      ·
        refine ⟨4041211275462079757460379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5388281700616106343280505 4041211275462079757460379)
        ·
          refine ⟨6061816913193119636190569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4041211275462079757460379 6061816913193119636190569)
          ·
            refine ⟨4546362684894839727142927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6061816913193119636190569 4546362684894839727142927)
            ·
              refine ⟨6819544027342259590714391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4546362684894839727142927 6819544027342259590714391)
              ·
                refine ⟨10229316041013389386071587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6819544027342259590714391 10229316041013389386071587)
                ·
                  refine ⟨15343974061520084079107381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10229316041013389386071587 15343974061520084079107381)
                  ·
                    refine ⟨1438497568267507882416317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15343974061520084079107381 1438497568267507882416317)
                    ·
                      refine ⟨539436588100315455906119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1438497568267507882416317 539436588100315455906119)
                      ·
                        rfl

theorem cell23_1050549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_1050549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050549 prefixEnd_1050549 := by exact prefixLift 1050549
  have htrace : WordTrace (prefixWord ++ tailWord_1050549) baseStart_1050549 baseEnd_1050549 := by
    simpa [prefixWord, tailWord_1050549, baseEnd_1050549] using wordTrace_append hprefix tailTrace_1050549
  have hstable : (prefixWord ++ tailWord_1050549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050549).length < 2 ^ (prefixWord ++ tailWord_1050549).sum := by decide
  have hdescent : baseEnd_1050549 < baseStart_1050549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050552 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 1, 7]
def baseStart_1050552 : Nat := 118140960795 + 1050552 * 2 ^ 59
def prefixEnd_1050552 : Nat := 4983230072969 + 3 ^ 40 * 1050552 * 2
def baseEnd_1050552 : Nat := 179812709514092981389535

theorem tailTrace_1050552 : CollatzResearch.WordTrace tailWord_1050552 prefixEnd_1050552 179812709514092981389535 := by
  unfold tailWord_1050552
  simp only [CollatzResearch.WordTrace]
  refine ⟨19158389645018499421176955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25544519526691332561569273 19158389645018499421176955)
  ·
    refine ⟨28737584467527749131765433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19158389645018499421176955 28737584467527749131765433)
    ·
      refine ⟨21553188350645811848824075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28737584467527749131765433 21553188350645811848824075)
      ·
        refine ⟨32329782525968717773236113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21553188350645811848824075 32329782525968717773236113)
        ·
          refine ⟨24247336894476538329927085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32329782525968717773236113 24247336894476538329927085)
          ·
            refine ⟨9092751335428701873722657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24247336894476538329927085 9092751335428701873722657)
            ·
              refine ⟨6819563501571526405291993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9092751335428701873722657 6819563501571526405291993)
              ·
                refine ⟨5114672626178644803968995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6819563501571526405291993 5114672626178644803968995)
                ·
                  refine ⟨7672008939267967205953493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5114672626178644803968995 7672008939267967205953493)
                  ·
                    refine ⟨179812709514092981389535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7672008939267967205953493 179812709514092981389535)
                    ·
                      rfl

theorem cell23_1050552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_1050552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050552 prefixEnd_1050552 := by exact prefixLift 1050552
  have htrace : WordTrace (prefixWord ++ tailWord_1050552) baseStart_1050552 baseEnd_1050552 := by
    simpa [prefixWord, tailWord_1050552, baseEnd_1050552] using wordTrace_append hprefix tailTrace_1050552
  have hstable : (prefixWord ++ tailWord_1050552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050552).length < 2 ^ (prefixWord ++ tailWord_1050552).sum := by decide
  have hdescent : baseEnd_1050552 < baseStart_1050552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050556 : List Nat := [2, 2, 2, 5, 1, 1, 1, 2, 7]
def baseStart_1050556 : Nat := 118140960795 + 1050556 * 2 ^ 59
def prefixEnd_1050556 : Nat := 4983230072969 + 3 ^ 40 * 1050556 * 2
def baseEnd_1050556 : Nat := 59937798051655214279843

theorem tailTrace_1050556 : CollatzResearch.WordTrace tailWord_1050556 prefixEnd_1050556 59937798051655214279843 := by
  unfold tailWord_1050556
  simp only [CollatzResearch.WordTrace]
  refine ⟨19158462591011253762749761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25544616788015005016999681 19158462591011253762749761)
  ·
    refine ⟨14368846943258440322062321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19158462591011253762749761 14368846943258440322062321)
    ·
      refine ⟨10776635207443830241546741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14368846943258440322062321 10776635207443830241546741)
      ·
        refine ⟨1010309550697859085145007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10776635207443830241546741 1010309550697859085145007)
        ·
          refine ⟨1515464326046788627717511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010309550697859085145007 1515464326046788627717511)
          ·
            refine ⟨2273196489070182941576267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515464326046788627717511 2273196489070182941576267)
            ·
              refine ⟨3409794733605274412364401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2273196489070182941576267 3409794733605274412364401)
              ·
                refine ⟨2557346050203955809273301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3409794733605274412364401 2557346050203955809273301)
                ·
                  refine ⟨59937798051655214279843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2557346050203955809273301 59937798051655214279843)
                  ·
                    rfl

theorem cell23_1050556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 7].length) (baseStart_1050556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050556 prefixEnd_1050556 := by exact prefixLift 1050556
  have htrace : WordTrace (prefixWord ++ tailWord_1050556) baseStart_1050556 baseEnd_1050556 := by
    simpa [prefixWord, tailWord_1050556, baseEnd_1050556] using wordTrace_append hprefix tailTrace_1050556
  have hstable : (prefixWord ++ tailWord_1050556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050556).length < 2 ^ (prefixWord ++ tailWord_1050556).sum := by decide
  have hdescent : baseEnd_1050556 < baseStart_1050556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050559 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 2, 5, 2]
def baseStart_1050559 : Nat := 118140960795 + 1050559 * 2 ^ 59
def prefixEnd_1050559 : Nat := 4983230072969 + 3 ^ 40 * 1050559 * 2
def baseEnd_1050559 : Nat := 539441722906860416781073

theorem tailTrace_1050559 : CollatzResearch.WordTrace tailWord_1050559 prefixEnd_1050559 539441722906860416781073 := by
  unfold tailWord_1050559
  simp only [CollatzResearch.WordTrace]
  refine ⟨38317034601011639037858731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25544689734007759358572487 38317034601011639037858731)
  ·
    refine ⟨57475551901517458556788097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38317034601011639037858731 57475551901517458556788097)
    ·
      refine ⟨43106663926138093917591073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57475551901517458556788097 43106663926138093917591073)
      ·
        refine ⟨32329997944603570438193305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43106663926138093917591073 32329997944603570438193305)
        ·
          refine ⟨24247498458452677828644979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32329997944603570438193305 24247498458452677828644979)
          ·
            refine ⟨36371247687679016742967469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24247498458452677828644979 36371247687679016742967469)
            ·
              refine ⟨13639217882879631278612801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36371247687679016742967469 13639217882879631278612801)
              ·
                refine ⟨10229413412159723458959601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13639217882879631278612801 10229413412159723458959601)
                ·
                  refine ⟨7672060059119792594219701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10229413412159723458959601 7672060059119792594219701)
                  ·
                    refine ⟨719255630542480555708097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7672060059119792594219701 719255630542480555708097)
                    ·
                      refine ⟨539441722906860416781073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 719255630542480555708097 539441722906860416781073)
                      ·
                        rfl

theorem cell23_1050559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 5, 2].length) (baseStart_1050559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050559 prefixEnd_1050559 := by exact prefixLift 1050559
  have htrace : WordTrace (prefixWord ++ tailWord_1050559) baseStart_1050559 baseEnd_1050559 := by
    simpa [prefixWord, tailWord_1050559, baseEnd_1050559] using wordTrace_append hprefix tailTrace_1050559
  have hstable : (prefixWord ++ tailWord_1050559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050559).length < 2 ^ (prefixWord ++ tailWord_1050559).sum := by decide
  have hdescent : baseEnd_1050559 < baseStart_1050559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050592 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 5]
def baseStart_1050592 : Nat := 118140960795 + 1050592 * 2 ^ 59
def prefixEnd_1050592 : Nat := 4983230072969 + 3 ^ 40 * 1050592 * 2
def baseEnd_1050592 : Nat := 539458667768458787668421

theorem tailTrace_1050592 : CollatzResearch.WordTrace tailWord_1050592 prefixEnd_1050592 539458667768458787668421 := by
  unfold tailWord_1050592
  simp only [CollatzResearch.WordTrace]
  refine ⟨19159119104946042836905015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25545492139928057115873353 19159119104946042836905015)
  ·
    refine ⟨28738678657419064255357523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19159119104946042836905015 28738678657419064255357523)
    ·
      refine ⟨43108017986128596383036285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28738678657419064255357523 43108017986128596383036285)
      ·
        refine ⟨16165506744798223643638607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43108017986128596383036285 16165506744798223643638607)
        ·
          refine ⟨24248260117197335465457911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16165506744798223643638607 24248260117197335465457911)
          ·
            refine ⟨36372390175796003198186867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24248260117197335465457911 36372390175796003198186867)
            ·
              refine ⟨54558585263694004797280301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36372390175796003198186867 54558585263694004797280301)
              ·
                refine ⟨20459469473885251798980113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54558585263694004797280301 20459469473885251798980113)
                ·
                  refine ⟨15344602105413938849235085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20459469473885251798980113 15344602105413938849235085)
                  ·
                    refine ⟨5754225789530227068463157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15344602105413938849235085 5754225789530227068463157)
                    ·
                      refine ⟨539458667768458787668421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5754225789530227068463157 539458667768458787668421)
                      ·
                        rfl

theorem cell23_1050592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_1050592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050592 prefixEnd_1050592 := by exact prefixLift 1050592
  have htrace : WordTrace (prefixWord ++ tailWord_1050592) baseStart_1050592 baseEnd_1050592 := by
    simpa [prefixWord, tailWord_1050592, baseEnd_1050592] using wordTrace_append hprefix tailTrace_1050592
  have hstable : (prefixWord ++ tailWord_1050592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050592).length < 2 ^ (prefixWord ++ tailWord_1050592).sum := by decide
  have hdescent : baseEnd_1050592 < baseStart_1050592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050650 : List Nat := [3, 1, 1, 3, 1, 4, 3, 2, 1, 4]
def baseStart_1050650 : Nat := 118140960795 + 1050650 * 2 ^ 59
def prefixEnd_1050650 : Nat := 4983230072969 + 3 ^ 40 * 1050650 * 2
def baseEnd_1050650 : Nat := 179829483215473186914385

theorem tailTrace_1050650 : CollatzResearch.WordTrace tailWord_1050650 prefixEnd_1050650 179829483215473186914385 := by
  unfold tailWord_1050650
  simp only [CollatzResearch.WordTrace]
  refine ⟨9580088410920490394855351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25546902429121307719614269 9580088410920490394855351)
  ·
    refine ⟨14370132616380735592283027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9580088410920490394855351 14370132616380735592283027)
    ·
      refine ⟨21555198924571103388424541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14370132616380735592283027 21555198924571103388424541)
      ·
        refine ⟨8083199596714163770659203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21555198924571103388424541 8083199596714163770659203)
        ·
          refine ⟨12124799395071245655988805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8083199596714163770659203 12124799395071245655988805)
          ·
            refine ⟨2273399886575858560497901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12124799395071245655988805 2273399886575858560497901)
            ·
              refine ⟨852524957465946960186713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2273399886575858560497901 852524957465946960186713)
              ·
                refine ⟨639393718099460220140035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 852524957465946960186713 639393718099460220140035)
                ·
                  refine ⟨959090577149190330210053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639393718099460220140035 959090577149190330210053)
                  ·
                    refine ⟨179829483215473186914385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 959090577149190330210053 179829483215473186914385)
                    ·
                      rfl

theorem cell23_1050650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 1, 4].length) (baseStart_1050650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050650 prefixEnd_1050650 := by exact prefixLift 1050650
  have htrace : WordTrace (prefixWord ++ tailWord_1050650) baseStart_1050650 baseEnd_1050650 := by
    simpa [prefixWord, tailWord_1050650, baseEnd_1050650] using wordTrace_append hprefix tailTrace_1050650
  have hstable : (prefixWord ++ tailWord_1050650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050650).length < 2 ^ (prefixWord ++ tailWord_1050650).sum := by decide
  have hdescent : baseEnd_1050650 < baseStart_1050650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050659 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 3, 5]
def baseStart_1050659 : Nat := 118140960795 + 1050659 * 2 ^ 59
def prefixEnd_1050659 : Nat := 4983230072969 + 3 ^ 40 * 1050659 * 2
def baseEnd_1050659 : Nat := 179831023657436675176871

theorem tailTrace_1050659 : CollatzResearch.WordTrace tailWord_1050659 prefixEnd_1050659 179831023657436675176871 := by
  unfold tailWord_1050659
  simp only [CollatzResearch.WordTrace]
  refine ⟨38320681900649356116499031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25547121267099570744332687 38320681900649356116499031)
  ·
    refine ⟨57481022850974034174748547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38320681900649356116499031 57481022850974034174748547)
    ·
      refine ⟨86221534276461051262122821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57481022850974034174748547 86221534276461051262122821)
      ·
        refine ⟨16166537676836447111648029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86221534276461051262122821 16166537676836447111648029)
        ·
          refine ⟨6062451628813667666868011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16166537676836447111648029 6062451628813667666868011)
          ·
            refine ⟨9093677443220501500302017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6062451628813667666868011 9093677443220501500302017)
            ·
              refine ⟨6820258082415376125226513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9093677443220501500302017 6820258082415376125226513)
              ·
                refine ⟨5115193561811532093919885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6820258082415376125226513 5115193561811532093919885)
                ·
                  refine ⟨1918197585679324535219957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5115193561811532093919885 1918197585679324535219957)
                  ·
                    refine ⟨179831023657436675176871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1918197585679324535219957 179831023657436675176871)
                    ·
                      rfl

theorem cell23_1050659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 5].length) (baseStart_1050659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050659 prefixEnd_1050659 := by exact prefixLift 1050659
  have htrace : WordTrace (prefixWord ++ tailWord_1050659) baseStart_1050659 baseEnd_1050659 := by
    simpa [prefixWord, tailWord_1050659, baseEnd_1050659] using wordTrace_append hprefix tailTrace_1050659
  have hstable : (prefixWord ++ tailWord_1050659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050659).length < 2 ^ (prefixWord ++ tailWord_1050659).sum := by decide
  have hdescent : baseEnd_1050659 < baseStart_1050659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050663 : List Nat := [1, 1, 7, 1, 2, 1, 1, 3, 6]
def baseStart_1050663 : Nat := 118140960795 + 1050663 * 2 ^ 59
def prefixEnd_1050663 : Nat := 4983230072969 + 3 ^ 40 * 1050663 * 2
def baseEnd_1050663 : Nat := 59943902766103112208955

theorem tailTrace_1050663 : CollatzResearch.WordTrace tailWord_1050663 prefixEnd_1050663 59943902766103112208955 := by
  unfold tailWord_1050663
  simp only [CollatzResearch.WordTrace]
  refine ⟨38320827792634864799644643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25547218528423243199763095 38320827792634864799644643)
  ·
    refine ⟨57481241688952297199466965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38320827792634864799644643 57481241688952297199466965)
    ·
      refine ⟨1347216602084819465612507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 57481241688952297199466965 1347216602084819465612507)
      ·
        refine ⟨2020824903127229198418761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1347216602084819465612507 2020824903127229198418761)
        ·
          refine ⟨1515618677345421898814071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2020824903127229198418761 1515618677345421898814071)
          ·
            refine ⟨2273428016018132848221107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515618677345421898814071 2273428016018132848221107)
            ·
              refine ⟨3410142024027199272331661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2273428016018132848221107 3410142024027199272331661)
              ·
                refine ⟨1278803259010199727124373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3410142024027199272331661 1278803259010199727124373)
                ·
                  refine ⟨59943902766103112208955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1278803259010199727124373 59943902766103112208955)
                  ·
                    rfl

theorem cell23_1050663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 6].length) (baseStart_1050663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050663 prefixEnd_1050663 := by exact prefixLift 1050663
  have htrace : WordTrace (prefixWord ++ tailWord_1050663) baseStart_1050663 baseEnd_1050663 := by
    simpa [prefixWord, tailWord_1050663, baseEnd_1050663] using wordTrace_append hprefix tailTrace_1050663
  have hstable : (prefixWord ++ tailWord_1050663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050663).length < 2 ^ (prefixWord ++ tailWord_1050663).sum := by decide
  have hdescent : baseEnd_1050663 < baseStart_1050663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050713 : List Nat := [1, 2, 1, 2, 2, 1, 4, 3, 3, 2, 2]
def baseStart_1050713 : Nat := 118140960795 + 1050713 * 2 ^ 59
def prefixEnd_1050713 : Nat := 4983230072969 + 3 ^ 40 * 1050713 * 2
def baseEnd_1050713 : Nat := 539520798927652814255365

theorem tailTrace_1050713 : CollatzResearch.WordTrace tailWord_1050713 prefixEnd_1050713 539520798927652814255365 := by
  unfold tailWord_1050713
  simp only [CollatzResearch.WordTrace]
  refine ⟨38322651442453723338964793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25548434294969148892643195 38322651442453723338964793)
  ·
    refine ⟨28741988581840292504223595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38322651442453723338964793 28741988581840292504223595)
    ·
      refine ⟨43112982872760438756335393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28741988581840292504223595 43112982872760438756335393)
      ·
        refine ⟨32334737154570329067251545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43112982872760438756335393 32334737154570329067251545)
        ·
          refine ⟨24251052865927746800438659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32334737154570329067251545 24251052865927746800438659)
          ·
            refine ⟨36376579298891620200657989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24251052865927746800438659 36376579298891620200657989)
            ·
              refine ⟨6820608618542178787623373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36376579298891620200657989 6820608618542178787623373)
              ·
                refine ⟨2557728231953317045358765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6820608618542178787623373 2557728231953317045358765)
                ·
                  refine ⟨959148086982493892009537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2557728231953317045358765 959148086982493892009537)
                  ·
                    refine ⟨719361065236870419007153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 959148086982493892009537 719361065236870419007153)
                    ·
                      refine ⟨539520798927652814255365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 719361065236870419007153 539520798927652814255365)
                      ·
                        rfl

theorem cell23_1050713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 2, 2].length) (baseStart_1050713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050713 prefixEnd_1050713 := by exact prefixLift 1050713
  have htrace : WordTrace (prefixWord ++ tailWord_1050713) baseStart_1050713 baseEnd_1050713 := by
    simpa [prefixWord, tailWord_1050713, baseEnd_1050713] using wordTrace_append hprefix tailTrace_1050713
  have hstable : (prefixWord ++ tailWord_1050713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050713).length < 2 ^ (prefixWord ++ tailWord_1050713).sum := by decide
  have hdescent : baseEnd_1050713 < baseStart_1050713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050733 : List Nat := [1, 5, 1, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_1050733 : Nat := 118140960795 + 1050733 * 2 ^ 59
def prefixEnd_1050733 : Nat := 4983230072969 + 3 ^ 40 * 1050733 * 2
def baseEnd_1050733 : Nat := 539531068540742736005273

theorem tailTrace_1050733 : CollatzResearch.WordTrace tailWord_1050733 prefixEnd_1050733 539531068540742736005273 := by
  unfold tailWord_1050733
  simp only [CollatzResearch.WordTrace]
  refine ⟨38323380902381266754692853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25548920601587511169795235 38323380902381266754692853)
  ·
    refine ⟨3592816959598243758252455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38323380902381266754692853 3592816959598243758252455)
    ·
      refine ⟨5389225439397365637378683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3592816959598243758252455 5389225439397365637378683)
      ·
        refine ⟨8083838159096048456068025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5389225439397365637378683 8083838159096048456068025)
        ·
          refine ⟨6062878619322036342051019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8083838159096048456068025 6062878619322036342051019)
          ·
            refine ⟨9094317928983054513076529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6062878619322036342051019 9094317928983054513076529)
            ·
              refine ⟨6820738446737290884807397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9094317928983054513076529 6820738446737290884807397)
              ·
                refine ⟨1278888458763242040901387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6820738446737290884807397 1278888458763242040901387)
                ·
                  refine ⟨1918332688144863061352081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1278888458763242040901387 1918332688144863061352081)
                  ·
                    refine ⟨1438749516108647296014061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1918332688144863061352081 1438749516108647296014061)
                    ·
                      refine ⟨539531068540742736005273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1438749516108647296014061 539531068540742736005273)
                      ·
                        rfl

theorem cell23_1050733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_1050733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050733 prefixEnd_1050733 := by exact prefixLift 1050733
  have htrace : WordTrace (prefixWord ++ tailWord_1050733) baseStart_1050733 baseEnd_1050733 := by
    simpa [prefixWord, tailWord_1050733, baseEnd_1050733] using wordTrace_append hprefix tailTrace_1050733
  have hstable : (prefixWord ++ tailWord_1050733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050733).length < 2 ^ (prefixWord ++ tailWord_1050733).sum := by decide
  have hdescent : baseEnd_1050733 < baseStart_1050733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050736 : List Nat := [2, 1, 1, 1, 5, 3, 3, 7]
def baseStart_1050736 : Nat := 118140960795 + 1050736 * 2 ^ 59
def prefixEnd_1050736 : Nat := 4983230072969 + 3 ^ 40 * 1050736 * 2
def baseEnd_1050736 : Nat := 19982689221581712009917

theorem tailTrace_1050736 : CollatzResearch.WordTrace tailWord_1050736 prefixEnd_1050736 19982689221581712009917 := by
  unfold tailWord_1050736
  simp only [CollatzResearch.WordTrace]
  refine ⟨19161745160685199133526031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25548993547580265511368041 19161745160685199133526031)
  ·
    refine ⟨28742617741027798700289047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19161745160685199133526031 28742617741027798700289047)
    ·
      refine ⟨43113926611541698050433571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28742617741027798700289047 43113926611541698050433571)
      ·
        refine ⟨64670889917312547075650357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43113926611541698050433571 64670889917312547075650357)
        ·
          refine ⟨6062895929748051288342221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64670889917312547075650357 6062895929748051288342221)
          ·
            refine ⟨2273585973655519233128333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6062895929748051288342221 2273585973655519233128333)
            ·
              refine ⟨852594740120819712423125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2273585973655519233128333 852594740120819712423125)
              ·
                refine ⟨19982689221581712009917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 852594740120819712423125 19982689221581712009917)
                ·
                  rfl

theorem cell23_1050736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 7].length) (baseStart_1050736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050736 prefixEnd_1050736 := by exact prefixLift 1050736
  have htrace : WordTrace (prefixWord ++ tailWord_1050736) baseStart_1050736 baseEnd_1050736 := by
    simpa [prefixWord, tailWord_1050736, baseEnd_1050736] using wordTrace_append hprefix tailTrace_1050736
  have hstable : (prefixWord ++ tailWord_1050736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050736).length < 2 ^ (prefixWord ++ tailWord_1050736).sum := by decide
  have hdescent : baseEnd_1050736 < baseStart_1050736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050779 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 2, 6]
def baseStart_1050779 : Nat := 118140960795 + 1050779 * 2 ^ 59
def prefixEnd_1050779 : Nat := 4983230072969 + 3 ^ 40 * 1050779 * 2
def baseEnd_1050779 : Nat := 179851562883616518676687

theorem tailTrace_1050779 : CollatzResearch.WordTrace tailWord_1050779 prefixEnd_1050779 179851562883616518676687 := by
  unfold tailWord_1050779
  simp only [CollatzResearch.WordTrace]
  refine ⟨38325058660214616610867391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25550039106809744407244927 38325058660214616610867391)
  ·
    refine ⟨57487587990321924916301087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38325058660214616610867391 57487587990321924916301087)
    ·
      refine ⟨86231381985482887374451631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57487587990321924916301087 86231381985482887374451631)
      ·
        refine ⟨129347072978224331061677447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86231381985482887374451631 129347072978224331061677447)
        ·
          refine ⟨194020609467336496592516171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129347072978224331061677447 194020609467336496592516171)
          ·
            refine ⟨291030914201004744888774257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194020609467336496592516171 291030914201004744888774257)
            ·
              refine ⟨218273185650753558666580693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291030914201004744888774257 218273185650753558666580693)
              ·
                refine ⟨5115777788689536531247985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 218273185650753558666580693 5115777788689536531247985)
                ·
                  refine ⟨3836833341517152398435989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5115777788689536531247985 3836833341517152398435989)
                  ·
                    refine ⟨179851562883616518676687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3836833341517152398435989 179851562883616518676687)
                    ·
                      rfl

theorem cell23_1050779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 6].length) (baseStart_1050779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050779 prefixEnd_1050779 := by exact prefixLift 1050779
  have htrace : WordTrace (prefixWord ++ tailWord_1050779) baseStart_1050779 baseEnd_1050779 := by
    simpa [prefixWord, tailWord_1050779, baseEnd_1050779] using wordTrace_append hprefix tailTrace_1050779
  have hstable : (prefixWord ++ tailWord_1050779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050779).length < 2 ^ (prefixWord ++ tailWord_1050779).sum := by decide
  have hdescent : baseEnd_1050779 < baseStart_1050779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050798 : List Nat := [4, 1, 4, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_1050798 : Nat := 118140960795 + 1050798 * 2 ^ 59
def prefixEnd_1050798 : Nat := 4983230072969 + 3 ^ 40 * 1050798 * 2
def baseEnd_1050798 : Nat := 539564444783284981692475

theorem tailTrace_1050798 : CollatzResearch.WordTrace tailWord_1050798 prefixEnd_1050798 539564444783284981692475 := by
  unfold tailWord_1050798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4790718955893222856976131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25550501098097188570539365 4790718955893222856976131)
  ·
    refine ⟨7186078433839834285464197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4790718955893222856976131 7186078433839834285464197)
    ·
      refine ⟨1347389706344968928524537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7186078433839834285464197 1347389706344968928524537)
      ·
        refine ⟨1010542279758726696393403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1347389706344968928524537 1010542279758726696393403)
        ·
          refine ⟨1515813419638090044590105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010542279758726696393403 1515813419638090044590105)
          ·
            refine ⟨1136860064728567533442579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1515813419638090044590105 1136860064728567533442579)
            ·
              refine ⟨1705290097092851300163869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136860064728567533442579 1705290097092851300163869)
              ·
                refine ⟨639483786409819237561451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1705290097092851300163869 639483786409819237561451)
                ·
                  refine ⟨959225679614728856342177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639483786409819237561451 959225679614728856342177)
                  ·
                    refine ⟨719419259711046642256633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 959225679614728856342177 719419259711046642256633)
                    ·
                      refine ⟨539564444783284981692475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 719419259711046642256633 539564444783284981692475)
                      ·
                        rfl

theorem cell23_1050798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_1050798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050798 prefixEnd_1050798 := by exact prefixLift 1050798
  have htrace : WordTrace (prefixWord ++ tailWord_1050798) baseStart_1050798 baseEnd_1050798 := by
    simpa [prefixWord, tailWord_1050798, baseEnd_1050798] using wordTrace_append hprefix tailTrace_1050798
  have hstable : (prefixWord ++ tailWord_1050798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050798).length < 2 ^ (prefixWord ++ tailWord_1050798).sum := by decide
  have hdescent : baseEnd_1050798 < baseStart_1050798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050903 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 5, 4]
def baseStart_1050903 : Nat := 118140960795 + 1050903 * 2 ^ 59
def prefixEnd_1050903 : Nat := 4983230072969 + 3 ^ 40 * 1050903 * 2
def baseEnd_1050903 : Nat := 179872786750669023626497

theorem tailTrace_1050903 : CollatzResearch.WordTrace tailWord_1050903 prefixEnd_1050903 179872786750669023626497 := by
  unfold tailWord_1050903
  simp only [CollatzResearch.WordTrace]
  refine ⟨38329581311765385788381363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25553054207843590525587575 38329581311765385788381363)
  ·
    refine ⟨57494371967648078682572045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38329581311765385788381363 57494371967648078682572045)
    ·
      refine ⟨21560389487868029505964517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57494371967648078682572045 21560389487868029505964517)
      ·
        refine ⟨4042573028975255532368347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21560389487868029505964517 4042573028975255532368347)
        ·
          refine ⟨6063859543462883298552521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4042573028975255532368347 6063859543462883298552521)
          ·
            refine ⟨4547894657597162473914391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6063859543462883298552521 4547894657597162473914391)
            ·
              refine ⟨6821841986395743710871587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4547894657597162473914391 6821841986395743710871587)
              ·
                refine ⟨10232762979593615566307381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6821841986395743710871587 10232762979593615566307381)
                ·
                  refine ⟨959321529336901459341317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10232762979593615566307381 959321529336901459341317)
                  ·
                    refine ⟨179872786750669023626497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 959321529336901459341317 179872786750669023626497)
                    ·
                      rfl

theorem cell23_1050903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_1050903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050903 prefixEnd_1050903 := by exact prefixLift 1050903
  have htrace : WordTrace (prefixWord ++ tailWord_1050903) baseStart_1050903 baseEnd_1050903 := by
    simpa [prefixWord, tailWord_1050903, baseEnd_1050903] using wordTrace_append hprefix tailTrace_1050903
  have hstable : (prefixWord ++ tailWord_1050903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050903).length < 2 ^ (prefixWord ++ tailWord_1050903).sum := by decide
  have hdescent : baseEnd_1050903 < baseStart_1050903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050936 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 1, 2, 6]
def baseStart_1050936 : Nat := 118140960795 + 1050936 * 2 ^ 59
def prefixEnd_1050936 : Nat := 4983230072969 + 3 ^ 40 * 1050936 * 2
def baseEnd_1050936 : Nat := 539635305113605441766839

theorem tailTrace_1050936 : CollatzResearch.WordTrace tailWord_1050936 prefixEnd_1050936 539635305113605441766839 := by
  unfold tailWord_1050936
  simp only [CollatzResearch.WordTrace]
  refine ⟨19165392460322916212166331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25553856613763888282888441 19165392460322916212166331)
  ·
    refine ⟨28748088690484374318249497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19165392460322916212166331 28748088690484374318249497)
    ·
      refine ⟨21561066517863280738687123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28748088690484374318249497 21561066517863280738687123)
      ·
        refine ⟨32341599776794921108030685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21561066517863280738687123 32341599776794921108030685)
        ·
          refine ⟨12128099916298095415511507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32341599776794921108030685 12128099916298095415511507)
          ·
            refine ⟨18192149874447143123267261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12128099916298095415511507 18192149874447143123267261)
            ·
              refine ⟨6822056202917678671225223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18192149874447143123267261 6822056202917678671225223)
              ·
                refine ⟨10233084304376518006837835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6822056202917678671225223 10233084304376518006837835)
                ·
                  refine ⟨15349626456564777010256753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10233084304376518006837835 15349626456564777010256753)
                  ·
                    refine ⟨11512219842423582757692565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15349626456564777010256753 11512219842423582757692565)
                    ·
                      refine ⟨539635305113605441766839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11512219842423582757692565 539635305113605441766839)
                      ·
                        rfl

theorem cell23_1050936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_1050936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050936 prefixEnd_1050936 := by exact prefixLift 1050936
  have htrace : WordTrace (prefixWord ++ tailWord_1050936) baseStart_1050936 baseEnd_1050936 := by
    simpa [prefixWord, tailWord_1050936, baseEnd_1050936] using wordTrace_append hprefix tailTrace_1050936
  have hstable : (prefixWord ++ tailWord_1050936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050936).length < 2 ^ (prefixWord ++ tailWord_1050936).sum := by decide
  have hdescent : baseEnd_1050936 < baseStart_1050936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050937 : List Nat := [1, 2, 1, 6, 1, 1, 2, 4, 1, 4]
def baseStart_1050937 : Nat := 118140960795 + 1050937 * 2 ^ 59
def prefixEnd_1050937 : Nat := 4983230072969 + 3 ^ 40 * 1050937 * 2
def baseEnd_1050937 : Nat := 179878606198086645951445

theorem tailTrace_1050937 : CollatzResearch.WordTrace tailWord_1050937 prefixEnd_1050937 179878606198086645951445 := by
  unfold tailWord_1050937
  simp only [CollatzResearch.WordTrace]
  refine ⟨38330821393642209595119065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25553880929094806396746043 38330821393642209595119065)
  ·
    refine ⟨28748116045231657196339299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38330821393642209595119065 28748116045231657196339299)
    ·
      refine ⟨43122174067847485794508949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28748116045231657196339299 43122174067847485794508949)
      ·
        refine ⟨2021351909430350896617607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43122174067847485794508949 2021351909430350896617607)
        ·
          refine ⟨3032027864145526344926411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2021351909430350896617607 3032027864145526344926411)
          ·
            refine ⟨4548041796218289517389617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3032027864145526344926411 4548041796218289517389617)
            ·
              refine ⟨3411031347163717138042213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4548041796218289517389617 3411031347163717138042213)
              ·
                refine ⟨639568377593196963382915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3411031347163717138042213 639568377593196963382915)
                ·
                  refine ⟨959352566389795445074373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639568377593196963382915 959352566389795445074373)
                  ·
                    refine ⟨179878606198086645951445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 959352566389795445074373 179878606198086645951445)
                    ·
                      rfl

theorem cell23_1050937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 1, 4].length) (baseStart_1050937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050937 prefixEnd_1050937 := by exact prefixLift 1050937
  have htrace : WordTrace (prefixWord ++ tailWord_1050937) baseStart_1050937 baseEnd_1050937 := by
    simpa [prefixWord, tailWord_1050937, baseEnd_1050937] using wordTrace_append hprefix tailTrace_1050937
  have hstable : (prefixWord ++ tailWord_1050937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050937).length < 2 ^ (prefixWord ++ tailWord_1050937).sum := by decide
  have hdescent : baseEnd_1050937 < baseStart_1050937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050960 : List Nat := [2, 1, 1, 1, 1, 6, 2, 2, 3, 1, 3]
def baseStart_1050960 : Nat := 118140960795 + 1050960 * 2 ^ 59
def prefixEnd_1050960 : Nat := 4983230072969 + 3 ^ 40 * 1050960 * 2
def baseEnd_1050960 : Nat := 539647628649313347866729

theorem tailTrace_1050960 : CollatzResearch.WordTrace tailWord_1050960 prefixEnd_1050960 539647628649313347866729 := by
  unfold tailWord_1050960
  simp only [CollatzResearch.WordTrace]
  refine ⟨19165830136279442261603167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25554440181705923015470889 19165830136279442261603167)
  ·
    refine ⟨28748745204419163392404751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19165830136279442261603167 28748745204419163392404751)
    ·
      refine ⟨43123117806628745088607127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28748745204419163392404751 43123117806628745088607127)
      ·
        refine ⟨64684676709943117632910691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43123117806628745088607127 64684676709943117632910691)
        ·
          refine ⟨97027015064914676449366037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64684676709943117632910691 97027015064914676449366037)
          ·
            refine ⟨4548141331167875458564033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 97027015064914676449366037 4548141331167875458564033)
            ·
              refine ⟨3411105998375906593923025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4548141331167875458564033 3411105998375906593923025)
              ·
                refine ⟨2558329498781929945442269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3411105998375906593923025 2558329498781929945442269)
                ·
                  refine ⟨959373562043223729540851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2558329498781929945442269 959373562043223729540851)
                  ·
                    refine ⟨1439060343064835594311277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 959373562043223729540851 1439060343064835594311277)
                    ·
                      refine ⟨539647628649313347866729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1439060343064835594311277 539647628649313347866729)
                      ·
                        rfl

theorem cell23_1050960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 3, 1, 3].length) (baseStart_1050960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050960 prefixEnd_1050960 := by exact prefixLift 1050960
  have htrace : WordTrace (prefixWord ++ tailWord_1050960) baseStart_1050960 baseEnd_1050960 := by
    simpa [prefixWord, tailWord_1050960, baseEnd_1050960] using wordTrace_append hprefix tailTrace_1050960
  have hstable : (prefixWord ++ tailWord_1050960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050960).length < 2 ^ (prefixWord ++ tailWord_1050960).sum := by decide
  have hdescent : baseEnd_1050960 < baseStart_1050960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050970 : List Nat := [3, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2]
def baseStart_1050970 : Nat := 118140960795 + 1050970 * 2 ^ 59
def prefixEnd_1050970 : Nat := 4983230072969 + 3 ^ 40 * 1050970 * 2
def baseEnd_1050970 : Nat := 539652763455858308741683

theorem tailTrace_1050970 : CollatzResearch.WordTrace tailWord_1050970 prefixEnd_1050970 539652763455858308741683 := by
  unfold tailWord_1050970
  simp only [CollatzResearch.WordTrace]
  refine ⟨9583006250630664057767591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25554683335015104154046909 9583006250630664057767591)
  ·
    refine ⟨14374509375945996086651387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9583006250630664057767591 14374509375945996086651387)
    ·
      refine ⟨21561764063918994129977081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14374509375945996086651387 21561764063918994129977081)
      ·
        refine ⟨16171323047939245597482811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21561764063918994129977081 16171323047939245597482811)
        ·
          refine ⟨24256984571908868396224217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16171323047939245597482811 24256984571908868396224217)
          ·
            refine ⟨18192738428931651297168163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24256984571908868396224217 18192738428931651297168163)
            ·
              refine ⟨27289107643397476945752245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18192738428931651297168163 27289107643397476945752245)
              ·
                refine ⟨2558353841568513463664273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27289107643397476945752245 2558353841568513463664273)
                ·
                  refine ⟨1918765381176385097748205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2558353841568513463664273 1918765381176385097748205)
                  ·
                    refine ⟨719537017941144411655577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1918765381176385097748205 719537017941144411655577)
                    ·
                      refine ⟨539652763455858308741683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 719537017941144411655577 539652763455858308741683)
                      ·
                        rfl

theorem cell23_1050970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_1050970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1050970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1050970 prefixEnd_1050970 := by exact prefixLift 1050970
  have htrace : WordTrace (prefixWord ++ tailWord_1050970) baseStart_1050970 baseEnd_1050970 := by
    simpa [prefixWord, tailWord_1050970, baseEnd_1050970] using wordTrace_append hprefix tailTrace_1050970
  have hstable : (prefixWord ++ tailWord_1050970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050970).length < 2 ^ (prefixWord ++ tailWord_1050970).sum := by decide
  have hdescent : baseEnd_1050970 < baseStart_1050970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051003 : List Nat := [1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 5]
def baseStart_1051003 : Nat := 118140960795 + 1051003 * 2 ^ 59
def prefixEnd_1051003 : Nat := 4983230072969 + 3 ^ 40 * 1051003 * 2
def baseEnd_1051003 : Nat := 539669708317456679629031

theorem tailTrace_1051003 : CollatzResearch.WordTrace tailWord_1051003 prefixEnd_1051003 539669708317456679629031 := by
  unfold tailWord_1051003
  simp only [CollatzResearch.WordTrace]
  refine ⟨38333228611403102867021663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25555485740935401911347775 38333228611403102867021663)
  ·
    refine ⟨57499842917104654300532495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38333228611403102867021663 57499842917104654300532495)
    ·
      refine ⟨86249764375656981450798743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57499842917104654300532495 86249764375656981450798743)
      ·
        refine ⟨129374646563485472176198115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86249764375656981450798743 129374646563485472176198115)
        ·
          refine ⟨194061969845228208264297173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129374646563485472176198115 194061969845228208264297173)
          ·
            refine ⟨4548327418247536131194465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 194061969845228208264297173 4548327418247536131194465)
            ·
              refine ⟨3411245563685652098395849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4548327418247536131194465 3411245563685652098395849)
              ·
                refine ⟨2558434172764239073796887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3411245563685652098395849 2558434172764239073796887)
                ·
                  refine ⟨3837651259146358610695331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2558434172764239073796887 3837651259146358610695331)
                  ·
                    refine ⟨5756476888719537916042997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3837651259146358610695331 5756476888719537916042997)
                    ·
                      refine ⟨539669708317456679629031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5756476888719537916042997 539669708317456679629031)
                      ·
                        rfl

theorem cell23_1051003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 5].length) (baseStart_1051003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051003 prefixEnd_1051003 := by exact prefixLift 1051003
  have htrace : WordTrace (prefixWord ++ tailWord_1051003) baseStart_1051003 baseEnd_1051003 := by
    simpa [prefixWord, tailWord_1051003, baseEnd_1051003] using wordTrace_append hprefix tailTrace_1051003
  have hstable : (prefixWord ++ tailWord_1051003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051003).length < 2 ^ (prefixWord ++ tailWord_1051003).sum := by decide
  have hdescent : baseEnd_1051003 < baseStart_1051003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051013 : List Nat := [1, 3, 1, 1, 3, 1, 1, 5, 1, 2, 4]
def baseStart_1051013 : Nat := 118140960795 + 1051013 * 2 ^ 59
def prefixEnd_1051013 : Nat := 4983230072969 + 3 ^ 40 * 1051013 * 2
def baseEnd_1051013 : Nat := 539674843124001640503985

theorem tailTrace_1051013 : CollatzResearch.WordTrace tailWord_1051013 prefixEnd_1051013 539674843124001640503985 := by
  unfold tailWord_1051013
  simp only [CollatzResearch.WordTrace]
  refine ⟨38333593341366874574885693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25555728894244583049923795 38333593341366874574885693)
  ·
    refine ⟨14375097503012577965582135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38333593341366874574885693 14375097503012577965582135)
    ·
      refine ⟨21562646254518866948373203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14375097503012577965582135 21562646254518866948373203)
      ·
        refine ⟨32343969381778300422559805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21562646254518866948373203 32343969381778300422559805)
        ·
          refine ⟨12128988518166862658459927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32343969381778300422559805 12128988518166862658459927)
          ·
            refine ⟨18193482777250293987689891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12128988518166862658459927 18193482777250293987689891)
            ·
              refine ⟨27290224165875440981534837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18193482777250293987689891 27290224165875440981534837)
              ·
                refine ⟨2558458515550822592018891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27290224165875440981534837 2558458515550822592018891)
                ·
                  refine ⟨3837687773326233888028337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2558458515550822592018891 3837687773326233888028337)
                  ·
                    refine ⟨2878265829994675416021253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3837687773326233888028337 2878265829994675416021253)
                    ·
                      refine ⟨539674843124001640503985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2878265829994675416021253 539674843124001640503985)
                      ·
                        rfl

theorem cell23_1051013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_1051013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051013 prefixEnd_1051013 := by exact prefixLift 1051013
  have htrace : WordTrace (prefixWord ++ tailWord_1051013) baseStart_1051013 baseEnd_1051013 := by
    simpa [prefixWord, tailWord_1051013, baseEnd_1051013] using wordTrace_append hprefix tailTrace_1051013
  have hstable : (prefixWord ++ tailWord_1051013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051013).length < 2 ^ (prefixWord ++ tailWord_1051013).sum := by decide
  have hdescent : baseEnd_1051013 < baseStart_1051013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051017 : List Nat := [1, 2, 1, 1, 6, 3, 1, 2, 1, 1, 4]
def baseStart_1051017 : Nat := 118140960795 + 1051017 * 2 ^ 59
def prefixEnd_1051017 : Nat := 4983230072969 + 3 ^ 40 * 1051017 * 2
def baseEnd_1051017 : Nat := 539676897046619624853967

theorem tailTrace_1051017 : CollatzResearch.WordTrace tailWord_1051017 prefixEnd_1051017 539676897046619624853967 := by
  unfold tailWord_1051017
  simp only [CollatzResearch.WordTrace]
  refine ⟨38333739233352383258031305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25555826155568255505354203 38333739233352383258031305)
  ·
    refine ⟨28750304425014287443523479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38333739233352383258031305 28750304425014287443523479)
    ·
      refine ⟨43125456637521431165285219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28750304425014287443523479 43125456637521431165285219)
      ·
        refine ⟨64688184956282146747927829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43125456637521431165285219 64688184956282146747927829)
        ·
          refine ⟨3032258669825725628809117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64688184956282146747927829 3032258669825725628809117)
          ·
            refine ⟨1137097001184647110803419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3032258669825725628809117 1137097001184647110803419)
            ·
              refine ⟨1705645501776970666205129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137097001184647110803419 1705645501776970666205129)
              ·
                refine ⟨1279234126332727999653847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1705645501776970666205129 1279234126332727999653847)
                ·
                  refine ⟨1918851189499091999480771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279234126332727999653847 1918851189499091999480771)
                  ·
                    refine ⟨2878276784248637999221157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1918851189499091999480771 2878276784248637999221157)
                    ·
                      refine ⟨539676897046619624853967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2878276784248637999221157 539676897046619624853967)
                      ·
                        rfl

theorem cell23_1051017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 1, 4].length) (baseStart_1051017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051017 prefixEnd_1051017 := by exact prefixLift 1051017
  have htrace : WordTrace (prefixWord ++ tailWord_1051017) baseStart_1051017 baseEnd_1051017 := by
    simpa [prefixWord, tailWord_1051017, baseEnd_1051017] using wordTrace_append hprefix tailTrace_1051017
  have hstable : (prefixWord ++ tailWord_1051017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051017).length < 2 ^ (prefixWord ++ tailWord_1051017).sum := by decide
  have hdescent : baseEnd_1051017 < baseStart_1051017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051020 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 3, 2, 3]
def baseStart_1051020 : Nat := 118140960795 + 1051020 * 2 ^ 59
def prefixEnd_1051020 : Nat := 4983230072969 + 3 ^ 40 * 1051020 * 2
def baseEnd_1051020 : Nat := 539678437488583113116453

theorem tailTrace_1051020 : CollatzResearch.WordTrace tailWord_1051020 prefixEnd_1051020 539678437488583113116453 := by
  unfold tailWord_1051020
  simp only [CollatzResearch.WordTrace]
  refine ⟨19166924326170757385195257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25555899101561009846927009 19166924326170757385195257)
  ·
    refine ⟨14375193244628068038896443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19166924326170757385195257 14375193244628068038896443)
    ·
      refine ⟨21562789866942102058344665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14375193244628068038896443 21562789866942102058344665)
      ·
        refine ⟨16172092400206576543758499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21562789866942102058344665 16172092400206576543758499)
        ·
          refine ⟨24258138600309864815637749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16172092400206576543758499 24258138600309864815637749)
          ·
            refine ⟨2274200493779049826466039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24258138600309864815637749 2274200493779049826466039)
            ·
              refine ⟨3411300740668574739699059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2274200493779049826466039 3411300740668574739699059)
              ·
                refine ⟨5116951111002862109548589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3411300740668574739699059 5116951111002862109548589)
                ·
                  refine ⟨1918856666626073291080721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5116951111002862109548589 1918856666626073291080721)
                  ·
                    refine ⟨1439142499969554968310541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1918856666626073291080721 1439142499969554968310541)
                    ·
                      refine ⟨539678437488583113116453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1439142499969554968310541 539678437488583113116453)
                      ·
                        rfl

theorem cell23_1051020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_1051020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051020 prefixEnd_1051020 := by exact prefixLift 1051020
  have htrace : WordTrace (prefixWord ++ tailWord_1051020) baseStart_1051020 baseEnd_1051020 := by
    simpa [prefixWord, tailWord_1051020, baseEnd_1051020] using wordTrace_append hprefix tailTrace_1051020
  have hstable : (prefixWord ++ tailWord_1051020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051020).length < 2 ^ (prefixWord ++ tailWord_1051020).sum := by decide
  have hdescent : baseEnd_1051020 < baseStart_1051020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051037 : List Nat := [1, 4, 2, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_1051037 : Nat := 118140960795 + 1051037 * 2 ^ 59
def prefixEnd_1051037 : Nat := 4983230072969 + 3 ^ 40 * 1051037 * 2
def baseEnd_1051037 : Nat := 539687166659709546603875

theorem tailTrace_1051037 : CollatzResearch.WordTrace tailWord_1051037 prefixEnd_1051037 539687166659709546603875 := by
  unfold tailWord_1051037
  simp only [CollatzResearch.WordTrace]
  refine ⟨38334468693279926673759365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25556312462186617782506243 38334468693279926673759365)
  ·
    refine ⟨7187712879989986251329881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38334468693279926673759365 7187712879989986251329881)
    ·
      refine ⟨5390784659992489688497411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7187712879989986251329881 5390784659992489688497411)
      ·
        refine ⟨8086176989988734532746117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5390784659992489688497411 8086176989988734532746117)
        ·
          refine ⟨1516158185622887724889897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8086176989988734532746117 1516158185622887724889897)
          ·
            refine ⟨1137118639217165793667423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1516158185622887724889897 1137118639217165793667423)
            ·
              refine ⟨1705677958825748690501135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137118639217165793667423 1705677958825748690501135)
              ·
                refine ⟨2558516938238623035751703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705677958825748690501135 2558516938238623035751703)
                ·
                  refine ⟨3837775407357934553627555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2558516938238623035751703 3837775407357934553627555)
                  ·
                    refine ⟨5756663111036901830441333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3837775407357934553627555 5756663111036901830441333)
                    ·
                      refine ⟨539687166659709546603875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5756663111036901830441333 539687166659709546603875)
                      ·
                        rfl

theorem cell23_1051037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_1051037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051037 prefixEnd_1051037 := by exact prefixLift 1051037
  have htrace : WordTrace (prefixWord ++ tailWord_1051037) baseStart_1051037 baseEnd_1051037 := by
    simpa [prefixWord, tailWord_1051037, baseEnd_1051037] using wordTrace_append hprefix tailTrace_1051037
  have hstable : (prefixWord ++ tailWord_1051037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051037).length < 2 ^ (prefixWord ++ tailWord_1051037).sum := by decide
  have hdescent : baseEnd_1051037 < baseStart_1051037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051147 : List Nat := [1, 1, 1, 1, 7, 1, 3, 3, 5]
def baseStart_1051147 : Nat := 118140960795 + 1051147 * 2 ^ 59
def prefixEnd_1051147 : Nat := 4983230072969 + 3 ^ 40 * 1051147 * 2
def baseEnd_1051147 : Nat := 59971516614633790692041

theorem tailTrace_1051147 : CollatzResearch.WordTrace tailWord_1051147 prefixEnd_1051147 59971516614633790692041 := by
  unfold tailWord_1051147
  simp only [CollatzResearch.WordTrace]
  refine ⟨38338480722881415460263695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25558987148587610306842463 38338480722881415460263695)
  ·
    refine ⟨57507721084322123190395543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38338480722881415460263695 57507721084322123190395543)
    ·
      refine ⟨86261581626483184785593315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57507721084322123190395543 86261581626483184785593315)
      ·
        refine ⟨129392372439724777178389973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86261581626483184785593315 129392372439724777178389973)
        ·
          refine ⟨3032633729056049465118515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 129392372439724777178389973 3032633729056049465118515)
          ·
            refine ⟨4548950593584074197677773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3032633729056049465118515 4548950593584074197677773)
            ·
              refine ⟨1705856472594027824129165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4548950593584074197677773 1705856472594027824129165)
              ·
                refine ⟨639696177222760434048437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1705856472594027824129165 639696177222760434048437)
                ·
                  refine ⟨59971516614633790692041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 639696177222760434048437 59971516614633790692041)
                  ·
                    rfl

theorem cell23_1051147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 5].length) (baseStart_1051147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051147 prefixEnd_1051147 := by exact prefixLift 1051147
  have htrace : WordTrace (prefixWord ++ tailWord_1051147) baseStart_1051147 baseEnd_1051147 := by
    simpa [prefixWord, tailWord_1051147, baseEnd_1051147] using wordTrace_append hprefix tailTrace_1051147
  have hstable : (prefixWord ++ tailWord_1051147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051147).length < 2 ^ (prefixWord ++ tailWord_1051147).sum := by decide
  have hdescent : baseEnd_1051147 < baseStart_1051147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051160 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 4, 5]
def baseStart_1051160 : Nat := 118140960795 + 1051160 * 2 ^ 59
def prefixEnd_1051160 : Nat := 4983230072969 + 3 ^ 40 * 1051160 * 2
def baseEnd_1051160 : Nat := 179916774926737521788603

theorem tailTrace_1051160 : CollatzResearch.WordTrace tailWord_1051160 prefixEnd_1051160 179916774926737521788603 := by
  unfold tailWord_1051160
  simp only [CollatzResearch.WordTrace]
  refine ⟨19169477435917159340243467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25559303247889545786991289 19169477435917159340243467)
  ·
    refine ⟨28754216153875739010365201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19169477435917159340243467 28754216153875739010365201)
    ·
      refine ⟨21565662115406804257773901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28754216153875739010365201 21565662115406804257773901)
      ·
        refine ⟨8087123293277551596665213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21565662115406804257773901 8087123293277551596665213)
        ·
          refine ⟨3032671234979081848749455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8087123293277551596665213 3032671234979081848749455)
          ·
            refine ⟨4549006852468622773124183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3032671234979081848749455 4549006852468622773124183)
            ·
              refine ⟨6823510278702934159686275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4549006852468622773124183 6823510278702934159686275)
              ·
                refine ⟨10235265418054401239529413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6823510278702934159686275 10235265418054401239529413)
                ·
                  refine ⟨1919112265885200232411765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10235265418054401239529413 1919112265885200232411765)
                  ·
                    refine ⟨179916774926737521788603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1919112265885200232411765 179916774926737521788603)
                    ·
                      rfl

theorem cell23_1051160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_1051160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051160 prefixEnd_1051160 := by exact prefixLift 1051160
  have htrace : WordTrace (prefixWord ++ tailWord_1051160) baseStart_1051160 baseEnd_1051160 := by
    simpa [prefixWord, tailWord_1051160, baseEnd_1051160] using wordTrace_append hprefix tailTrace_1051160
  have hstable : (prefixWord ++ tailWord_1051160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051160).length < 2 ^ (prefixWord ++ tailWord_1051160).sum := by decide
  have hdescent : baseEnd_1051160 < baseStart_1051160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051163 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 4]
def baseStart_1051163 : Nat := 118140960795 + 1051163 * 2 ^ 59
def prefixEnd_1051163 : Nat := 4983230072969 + 3 ^ 40 * 1051163 * 2
def baseEnd_1051163 : Nat := 539751865222176053628295

theorem tailTrace_1051163 : CollatzResearch.WordTrace tailWord_1051163 prefixEnd_1051163 539751865222176053628295 := by
  unfold tailWord_1051163
  simp only [CollatzResearch.WordTrace]
  refine ⟨38339064290823450192846143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25559376193882300128564095 38339064290823450192846143)
  ·
    refine ⟨57508596436235175289269215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38339064290823450192846143 57508596436235175289269215)
    ·
      refine ⟨86262894654352762933903823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57508596436235175289269215 86262894654352762933903823)
      ·
        refine ⟨129394341981529144400855735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86262894654352762933903823 129394341981529144400855735)
        ·
          refine ⟨194091512972293716601283603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129394341981529144400855735 194091512972293716601283603)
          ·
            refine ⟨291137269458440574901925405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194091512972293716601283603 291137269458440574901925405)
            ·
              refine ⟨109176476046915215588222027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 291137269458440574901925405 109176476046915215588222027)
              ·
                refine ⟨163764714070372823382333041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109176476046915215588222027 163764714070372823382333041)
                ·
                  refine ⟨122823535552779617536749781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163764714070372823382333041 122823535552779617536749781)
                  ·
                    refine ⟨2878676614518272286017573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 122823535552779617536749781 2878676614518272286017573)
                    ·
                      refine ⟨539751865222176053628295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2878676614518272286017573 539751865222176053628295)
                      ·
                        rfl

theorem cell23_1051163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 4].length) (baseStart_1051163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051163 prefixEnd_1051163 := by exact prefixLift 1051163
  have htrace : WordTrace (prefixWord ++ tailWord_1051163) baseStart_1051163 baseEnd_1051163 := by
    simpa [prefixWord, tailWord_1051163, baseEnd_1051163] using wordTrace_append hprefix tailTrace_1051163
  have hstable : (prefixWord ++ tailWord_1051163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051163).length < 2 ^ (prefixWord ++ tailWord_1051163).sum := by decide
  have hdescent : baseEnd_1051163 < baseStart_1051163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051164 : List Nat := [2, 2, 3, 1, 2, 3, 3, 2, 5]
def baseStart_1051164 : Nat := 118140960795 + 1051164 * 2 ^ 59
def prefixEnd_1051164 : Nat := 4983230072969 + 3 ^ 40 * 1051164 * 2
def baseEnd_1051164 : Nat := 59972486522536727746199

theorem tailTrace_1051164 : CollatzResearch.WordTrace tailWord_1051164 prefixEnd_1051164 59972486522536727746199 := by
  unfold tailWord_1051164
  simp only [CollatzResearch.WordTrace]
  refine ⟨19169550381909913681816273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25559400509213218242421697 19169550381909913681816273)
  ·
    refine ⟨14377162786432435261362205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19169550381909913681816273 14377162786432435261362205)
    ·
      refine ⟨5391436044912163223010827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14377162786432435261362205 5391436044912163223010827)
      ·
        refine ⟨8087154067368244834516241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5391436044912163223010827 8087154067368244834516241)
        ·
          refine ⟨6065365550526183625887181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8087154067368244834516241 6065365550526183625887181)
          ·
            refine ⟨2274512081447318859707693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6065365550526183625887181 2274512081447318859707693)
            ·
              refine ⟨852942030542744572390385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2274512081447318859707693 852942030542744572390385)
              ·
                refine ⟨639706522907058429292789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 852942030542744572390385 639706522907058429292789)
                ·
                  refine ⟨59972486522536727746199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 639706522907058429292789 59972486522536727746199)
                  ·
                    rfl

theorem cell23_1051164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 5].length) (baseStart_1051164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051164 prefixEnd_1051164 := by exact prefixLift 1051164
  have htrace : WordTrace (prefixWord ++ tailWord_1051164) baseStart_1051164 baseEnd_1051164 := by
    simpa [prefixWord, tailWord_1051164, baseEnd_1051164] using wordTrace_append hprefix tailTrace_1051164
  have hstable : (prefixWord ++ tailWord_1051164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051164).length < 2 ^ (prefixWord ++ tailWord_1051164).sum := by decide
  have hdescent : baseEnd_1051164 < baseStart_1051164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051183 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 5]
def baseStart_1051183 : Nat := 118140960795 + 1051183 * 2 ^ 59
def prefixEnd_1051183 : Nat := 4983230072969 + 3 ^ 40 * 1051183 * 2
def baseEnd_1051183 : Nat := 539762134835265975378203

theorem tailTrace_1051183 : CollatzResearch.WordTrace tailWord_1051183 prefixEnd_1051183 539762134835265975378203 := by
  unfold tailWord_1051183
  simp only [CollatzResearch.WordTrace]
  refine ⟨38339793750750993608574203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25559862500500662405716135 38339793750750993608574203)
  ·
    refine ⟨57509690626126490412861305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38339793750750993608574203 57509690626126490412861305)
    ·
      refine ⟨43132267969594867809645979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57509690626126490412861305 43132267969594867809645979)
      ·
        refine ⟨64698401954392301714468969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43132267969594867809645979 64698401954392301714468969)
        ·
          refine ⟨48523801465794226285851727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64698401954392301714468969 48523801465794226285851727)
          ·
            refine ⟨72785702198691339428777591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48523801465794226285851727 72785702198691339428777591)
            ·
              refine ⟨109178553298037009143166387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72785702198691339428777591 109178553298037009143166387)
              ·
                refine ⟨163767829947055513714749581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109178553298037009143166387 163767829947055513714749581)
                ·
                  refine ⟨61412936230145817643031093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163767829947055513714749581 61412936230145817643031093)
                  ·
                    refine ⟨5757462771576170404034165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61412936230145817643031093 5757462771576170404034165)
                    ·
                      refine ⟨539762134835265975378203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5757462771576170404034165 539762134835265975378203)
                      ·
                        rfl

theorem cell23_1051183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_1051183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051183 prefixEnd_1051183 := by exact prefixLift 1051183
  have htrace : WordTrace (prefixWord ++ tailWord_1051183) baseStart_1051183 baseEnd_1051183 := by
    simpa [prefixWord, tailWord_1051183, baseEnd_1051183] using wordTrace_append hprefix tailTrace_1051183
  have hstable : (prefixWord ++ tailWord_1051183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051183).length < 2 ^ (prefixWord ++ tailWord_1051183).sum := by decide
  have hdescent : baseEnd_1051183 < baseStart_1051183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051197 : List Nat := [1, 4, 1, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_1051197 : Nat := 118140960795 + 1051197 * 2 ^ 59
def prefixEnd_1051197 : Nat := 4983230072969 + 3 ^ 40 * 1051197 * 2
def baseEnd_1051197 : Nat := 539769323564428920603139

theorem tailTrace_1051197 : CollatzResearch.WordTrace tailWord_1051197 prefixEnd_1051197 539769323564428920603139 := by
  unfold tailWord_1051197
  simp only [CollatzResearch.WordTrace]
  refine ⟨38340304372700273999583845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25560202915133515999722563 38340304372700273999583845)
  ·
    refine ⟨7188807069881301374921971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38340304372700273999583845 7188807069881301374921971)
    ·
      refine ⟨10783210604821952062382957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7188807069881301374921971 10783210604821952062382957)
      ·
        refine ⟨4043703976808232023393609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10783210604821952062382957 4043703976808232023393609)
        ·
          refine ⟨3032777982606174017545207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4043703976808232023393609 3032777982606174017545207)
          ·
            refine ⟨4549166973909261026317811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3032777982606174017545207 4549166973909261026317811)
            ·
              refine ⟨6823750460863891539476717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4549166973909261026317811 6823750460863891539476717)
              ·
                refine ⟨2558906422823959327303769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6823750460863891539476717 2558906422823959327303769)
                ·
                  refine ⟨1919179817117969495477827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2558906422823959327303769 1919179817117969495477827)
                  ·
                    refine ⟨2878769725676954243216741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1919179817117969495477827 2878769725676954243216741)
                    ·
                      refine ⟨539769323564428920603139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2878769725676954243216741 539769323564428920603139)
                      ·
                        rfl

theorem cell23_1051197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_1051197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051197 prefixEnd_1051197 := by exact prefixLift 1051197
  have htrace : WordTrace (prefixWord ++ tailWord_1051197) baseStart_1051197 baseEnd_1051197 := by
    simpa [prefixWord, tailWord_1051197, baseEnd_1051197] using wordTrace_append hprefix tailTrace_1051197
  have hstable : (prefixWord ++ tailWord_1051197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051197).length < 2 ^ (prefixWord ++ tailWord_1051197).sum := by decide
  have hdescent : baseEnd_1051197 < baseStart_1051197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051200 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 3]
def baseStart_1051200 : Nat := 118140960795 + 1051200 * 2 ^ 59
def prefixEnd_1051200 : Nat := 4983230072969 + 3 ^ 40 * 1051200 * 2
def baseEnd_1051200 : Nat := 539770864006392408865625

theorem tailTrace_1051200 : CollatzResearch.WordTrace tailWord_1051200 prefixEnd_1051200 539770864006392408865625 := by
  unfold tailWord_1051200
  simp only [CollatzResearch.WordTrace]
  refine ⟨19170206895844702755971527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25560275861126270341295369 19170206895844702755971527)
  ·
    refine ⟨28755310343767054133957291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19170206895844702755971527 28755310343767054133957291)
    ·
      refine ⟨43132965515650581200935937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28755310343767054133957291 43132965515650581200935937)
      ·
        refine ⟨32349724136737935900701953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43132965515650581200935937 32349724136737935900701953)
        ·
          refine ⟨24262293102553451925526465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32349724136737935900701953 24262293102553451925526465)
          ·
            refine ⟨18196719826915088944144849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24262293102553451925526465 18196719826915088944144849)
            ·
              refine ⟨13647539870186316708108637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18196719826915088944144849 13647539870186316708108637)
              ·
                refine ⟨5117827451319868765540739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13647539870186316708108637 5117827451319868765540739)
                ·
                  refine ⟨7676741176979803148311109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5117827451319868765540739 7676741176979803148311109)
                  ·
                    refine ⟨1439388970683713090308333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7676741176979803148311109 1439388970683713090308333)
                    ·
                      refine ⟨539770864006392408865625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1439388970683713090308333 539770864006392408865625)
                      ·
                        rfl

theorem cell23_1051200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_1051200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051200 prefixEnd_1051200 := by exact prefixLift 1051200
  have htrace : WordTrace (prefixWord ++ tailWord_1051200) baseStart_1051200 baseEnd_1051200 := by
    simpa [prefixWord, tailWord_1051200, baseEnd_1051200] using wordTrace_append hprefix tailTrace_1051200
  have hstable : (prefixWord ++ tailWord_1051200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051200).length < 2 ^ (prefixWord ++ tailWord_1051200).sum := by decide
  have hdescent : baseEnd_1051200 < baseStart_1051200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051203 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 10]
def baseStart_1051203 : Nat := 118140960795 + 1051203 * 2 ^ 59
def prefixEnd_1051203 : Nat := 4983230072969 + 3 ^ 40 * 1051203 * 2
def baseEnd_1051203 : Nat := 59974711605372877458679

theorem tailTrace_1051203 : CollatzResearch.WordTrace tailWord_1051203 prefixEnd_1051203 59974711605372877458679 := by
  unfold tailWord_1051203
  simp only [CollatzResearch.WordTrace]
  refine ⟨38340523210678537024302263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25560348807119024682868175 38340523210678537024302263)
  ·
    refine ⟨57510784816017805536453395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38340523210678537024302263 57510784816017805536453395)
    ·
      refine ⟨86266177224026708304680093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57510784816017805536453395 86266177224026708304680093)
      ·
        refine ⟨32349816459010015614255035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86266177224026708304680093 32349816459010015614255035)
        ·
          refine ⟨48524724688515023421382553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32349816459010015614255035 48524724688515023421382553)
          ·
            refine ⟨36393543516386267566036915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48524724688515023421382553 36393543516386267566036915)
            ·
              refine ⟨54590315274579401349055373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36393543516386267566036915 54590315274579401349055373)
              ·
                refine ⟨20471368227967275505895765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54590315274579401349055373 20471368227967275505895765)
                ·
                  refine ⟨59974711605372877458679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 20471368227967275505895765 59974711605372877458679)
                  ·
                    rfl

theorem cell23_1051203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 10].length) (baseStart_1051203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051203 prefixEnd_1051203 := by exact prefixLift 1051203
  have htrace : WordTrace (prefixWord ++ tailWord_1051203) baseStart_1051203 baseEnd_1051203 := by
    simpa [prefixWord, tailWord_1051203, baseEnd_1051203] using wordTrace_append hprefix tailTrace_1051203
  have hstable : (prefixWord ++ tailWord_1051203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051203).length < 2 ^ (prefixWord ++ tailWord_1051203).sum := by decide
  have hdescent : baseEnd_1051203 < baseStart_1051203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051217 : List Nat := [1, 2, 2, 1, 3, 3, 2, 2, 2, 2, 3]
def baseStart_1051217 : Nat := 118140960795 + 1051217 * 2 ^ 59
def prefixEnd_1051217 : Nat := 4983230072969 + 3 ^ 40 * 1051217 * 2
def baseEnd_1051217 : Nat := 539779593177518842353047

theorem tailTrace_1051217 : CollatzResearch.WordTrace tailWord_1051217 prefixEnd_1051217 539779593177518842353047 := by
  unfold tailWord_1051217
  simp only [CollatzResearch.WordTrace]
  refine ⟨38341033832627817415311905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25560689221751878276874603 38341033832627817415311905)
  ·
    refine ⟨28755775374470863061483929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38341033832627817415311905 28755775374470863061483929)
    ·
      refine ⟨21566831530853147296112947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28755775374470863061483929 21566831530853147296112947)
      ·
        refine ⟨32350247296279720944169421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21566831530853147296112947 32350247296279720944169421)
        ·
          refine ⟨12131342736104895354063533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32350247296279720944169421 12131342736104895354063533)
          ·
            refine ⟨4549253526039335757773825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12131342736104895354063533 4549253526039335757773825)
            ·
              refine ⟨3411940144529501818330369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4549253526039335757773825 3411940144529501818330369)
              ·
                refine ⟨2558955108397126363747777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3411940144529501818330369 2558955108397126363747777)
                ·
                  refine ⟨1919216331297844772810833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2558955108397126363747777 1919216331297844772810833)
                  ·
                    refine ⟨1439412248473383579608125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1919216331297844772810833 1439412248473383579608125)
                    ·
                      refine ⟨539779593177518842353047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1439412248473383579608125 539779593177518842353047)
                      ·
                        rfl

theorem cell23_1051217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_1051217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051217 prefixEnd_1051217 := by exact prefixLift 1051217
  have htrace : WordTrace (prefixWord ++ tailWord_1051217) baseStart_1051217 baseEnd_1051217 := by
    simpa [prefixWord, tailWord_1051217, baseEnd_1051217] using wordTrace_append hprefix tailTrace_1051217
  have hstable : (prefixWord ++ tailWord_1051217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051217).length < 2 ^ (prefixWord ++ tailWord_1051217).sum := by decide
  have hdescent : baseEnd_1051217 < baseStart_1051217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051247 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 5, 1, 3]
def baseStart_1051247 : Nat := 118140960795 + 1051247 * 2 ^ 59
def prefixEnd_1051247 : Nat := 4983230072969 + 3 ^ 40 * 1051247 * 2
def baseEnd_1051247 : Nat := 539794997597153724977909

theorem tailTrace_1051247 : CollatzResearch.WordTrace tailWord_1051247 prefixEnd_1051247 539794997597153724977909 := by
  unfold tailWord_1051247
  simp only [CollatzResearch.WordTrace]
  refine ⟨38342128022519132538903995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25561418681679421692602663 38342128022519132538903995)
  ·
    refine ⟨57513192033778698808355993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38342128022519132538903995 57513192033778698808355993)
    ·
      refine ⟨43134894025334024106266995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57513192033778698808355993 43134894025334024106266995)
      ·
        refine ⟨64702341038001036159400493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43134894025334024106266995 64702341038001036159400493)
        ·
          refine ⟨24263377889250388559775185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64702341038001036159400493 24263377889250388559775185)
          ·
            refine ⟨18197533416937791419831389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24263377889250388559775185 18197533416937791419831389)
            ·
              refine ⟨6824075031351671782436771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18197533416937791419831389 6824075031351671782436771)
              ·
                refine ⟨10236112547027507673655157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6824075031351671782436771 10236112547027507673655157)
                ·
                  refine ⟨959635551283828844405171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10236112547027507673655157 959635551283828844405171)
                  ·
                    refine ⟨1439453326925743266607757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 959635551283828844405171 1439453326925743266607757)
                    ·
                      refine ⟨539794997597153724977909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1439453326925743266607757 539794997597153724977909)
                      ·
                        rfl

theorem cell23_1051247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 1, 3].length) (baseStart_1051247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051247 prefixEnd_1051247 := by exact prefixLift 1051247
  have htrace : WordTrace (prefixWord ++ tailWord_1051247) baseStart_1051247 baseEnd_1051247 := by
    simpa [prefixWord, tailWord_1051247, baseEnd_1051247] using wordTrace_append hprefix tailTrace_1051247
  have hstable : (prefixWord ++ tailWord_1051247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051247).length < 2 ^ (prefixWord ++ tailWord_1051247).sum := by decide
  have hdescent : baseEnd_1051247 < baseStart_1051247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051324 : List Nat := [2, 2, 2, 3, 1, 1, 1, 5, 1, 2, 3]
def baseStart_1051324 : Nat := 118140960795 + 1051324 * 2 ^ 59
def prefixEnd_1051324 : Nat := 4983230072969 + 3 ^ 40 * 1051324 * 2
def baseEnd_1051324 : Nat := 539834535607549923715055

theorem tailTrace_1051324 : CollatzResearch.WordTrace tailWord_1051324 prefixEnd_1051324 539834535607549923715055 := by
  unfold tailWord_1051324
  simp only [CollatzResearch.WordTrace]
  refine ⟨19172468221620087344728513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25563290962160116459638017 19172468221620087344728513)
  ·
    refine ⟨14379351166215065508546385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19172468221620087344728513 14379351166215065508546385)
    ·
      refine ⟨10784513374661299131409789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14379351166215065508546385 10784513374661299131409789)
      ·
        refine ⟨4044192515497987174278671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10784513374661299131409789 4044192515497987174278671)
        ·
          refine ⟨6066288773246980761418007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4044192515497987174278671 6066288773246980761418007)
          ·
            refine ⟨9099433159870471142127011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6066288773246980761418007 9099433159870471142127011)
            ·
              refine ⟨13649149739805706713190517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9099433159870471142127011 13649149739805706713190517)
              ·
                refine ⟨1279607788106785004361611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13649149739805706713190517 1279607788106785004361611)
                ·
                  refine ⟨1919411682160177506542417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279607788106785004361611 1919411682160177506542417)
                  ·
                    refine ⟨1439558761620133129906813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1919411682160177506542417 1439558761620133129906813)
                    ·
                      refine ⟨539834535607549923715055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1439558761620133129906813 539834535607549923715055)
                      ·
                        rfl

theorem cell23_1051324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_1051324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051324 prefixEnd_1051324 := by exact prefixLift 1051324
  have htrace : WordTrace (prefixWord ++ tailWord_1051324) baseStart_1051324 baseEnd_1051324 := by
    simpa [prefixWord, tailWord_1051324, baseEnd_1051324] using wordTrace_append hprefix tailTrace_1051324
  have hstable : (prefixWord ++ tailWord_1051324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051324).length < 2 ^ (prefixWord ++ tailWord_1051324).sum := by decide
  have hdescent : baseEnd_1051324 < baseStart_1051324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051338 : List Nat := [3, 1, 2, 1, 4, 3, 1, 1, 3, 2, 2]
def baseStart_1051338 : Nat := 118140960795 + 1051338 * 2 ^ 59
def prefixEnd_1051338 : Nat := 4983230072969 + 3 ^ 40 * 1051338 * 2
def baseEnd_1051338 : Nat := 539841724336712868939991

theorem tailTrace_1051338 : CollatzResearch.WordTrace tailWord_1051338 prefixEnd_1051338 539841724336712868939991 := by
  unfold tailWord_1051338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9586361766297363770116667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25563631376792970053644445 9586361766297363770116667)
  ·
    refine ⟨14379542649446045655175001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9586361766297363770116667 14379542649446045655175001)
    ·
      refine ⟨10784656987084534241381251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14379542649446045655175001 10784656987084534241381251)
      ·
        refine ⟨16176985480626801362071877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10784656987084534241381251 16176985480626801362071877)
        ·
          refine ⟨3033184777617525255388477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16176985480626801362071877 3033184777617525255388477)
          ·
            refine ⟨1137444291606571970770679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3033184777617525255388477 1137444291606571970770679)
            ·
              refine ⟨1706166437409857956156019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137444291606571970770679 1706166437409857956156019)
              ·
                refine ⟨2559249656114786934234029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1706166437409857956156019 2559249656114786934234029)
                ·
                  refine ⟨959718621043045100337761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2559249656114786934234029 959718621043045100337761)
                  ·
                    refine ⟨719788965782283825253321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 959718621043045100337761 719788965782283825253321)
                    ·
                      refine ⟨539841724336712868939991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 719788965782283825253321 539841724336712868939991)
                      ·
                        rfl

theorem cell23_1051338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_1051338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051338 prefixEnd_1051338 := by exact prefixLift 1051338
  have htrace : WordTrace (prefixWord ++ tailWord_1051338) baseStart_1051338 baseEnd_1051338 := by
    simpa [prefixWord, tailWord_1051338, baseEnd_1051338] using wordTrace_append hprefix tailTrace_1051338
  have hstable : (prefixWord ++ tailWord_1051338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051338).length < 2 ^ (prefixWord ++ tailWord_1051338).sum := by decide
  have hdescent : baseEnd_1051338 < baseStart_1051338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051360 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 8]
def baseStart_1051360 : Nat := 118140960795 + 1051360 * 2 ^ 59
def prefixEnd_1051360 : Nat := 4983230072969 + 3 ^ 40 * 1051360 * 2
def baseEnd_1051360 : Nat := 539853020911111782864889

theorem tailTrace_1051360 : CollatzResearch.WordTrace tailWord_1051360 prefixEnd_1051360 539853020911111782864889 := by
  unfold tailWord_1051360
  simp only [CollatzResearch.WordTrace]
  refine ⟨19173124735554876418883767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25564166314073168558511689 19173124735554876418883767)
  ·
    refine ⟨28759687103332314628325651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19173124735554876418883767 28759687103332314628325651)
    ·
      refine ⟨43139530654998471942488477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28759687103332314628325651 43139530654998471942488477)
      ·
        refine ⟨16177323995624426978433179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43139530654998471942488477 16177323995624426978433179)
        ·
          refine ⟨24265985993436640467649769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16177323995624426978433179 24265985993436640467649769)
          ·
            refine ⟨18199489495077480350737327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24265985993436640467649769 18199489495077480350737327)
            ·
              refine ⟨27299234242616220526105991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18199489495077480350737327 27299234242616220526105991)
              ·
                refine ⟨40948851363924330789158987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27299234242616220526105991 40948851363924330789158987)
                ·
                  refine ⟨61423277045886496183738481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40948851363924330789158987 61423277045886496183738481)
                  ·
                    refine ⟨46067457784414872137803861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61423277045886496183738481 46067457784414872137803861)
                    ·
                      refine ⟨539853020911111782864889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 46067457784414872137803861 539853020911111782864889)
                      ·
                        rfl

theorem cell23_1051360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_1051360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051360 prefixEnd_1051360 := by exact prefixLift 1051360
  have htrace : WordTrace (prefixWord ++ tailWord_1051360) baseStart_1051360 baseEnd_1051360 := by
    simpa [prefixWord, tailWord_1051360, baseEnd_1051360] using wordTrace_append hprefix tailTrace_1051360
  have hstable : (prefixWord ++ tailWord_1051360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051360).length < 2 ^ (prefixWord ++ tailWord_1051360).sum := by decide
  have hdescent : baseEnd_1051360 < baseStart_1051360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051394 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_1051394 : Nat := 118140960795 + 1051394 * 2 ^ 59
def prefixEnd_1051394 : Nat := 4983230072969 + 3 ^ 40 * 1051394 * 2
def baseEnd_1051394 : Nat := 539870479253364649839733

theorem tailTrace_1051394 : CollatzResearch.WordTrace tailWord_1051394 prefixEnd_1051394 539870479253364649839733 := by
  unfold tailWord_1051394
  simp only [CollatzResearch.WordTrace]
  refine ⟨9586872388246644161126309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25564993035324384429670157 9586872388246644161126309)
  ·
    refine ⟨1797538572796245780211183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9586872388246644161126309 1797538572796245780211183)
    ·
      refine ⟨2696307859194368670316775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1797538572796245780211183 2696307859194368670316775)
      ·
        refine ⟨4044461788791553005475163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2696307859194368670316775 4044461788791553005475163)
        ·
          refine ⟨6066692683187329508212745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4044461788791553005475163 6066692683187329508212745)
          ·
            refine ⟨4550019512390497131159559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6066692683187329508212745 4550019512390497131159559)
            ·
              refine ⟨6825029268585745696739339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4550019512390497131159559 6825029268585745696739339)
              ·
                refine ⟨10237543902878618545109009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6825029268585745696739339 10237543902878618545109009)
                ·
                  refine ⟨7678157927158963908831757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10237543902878618545109009 7678157927158963908831757)
                  ·
                    refine ⟨2879309222684611465811909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7678157927158963908831757 2879309222684611465811909)
                    ·
                      refine ⟨539870479253364649839733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2879309222684611465811909 539870479253364649839733)
                      ·
                        rfl

theorem cell23_1051394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_1051394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051394 prefixEnd_1051394 := by exact prefixLift 1051394
  have htrace : WordTrace (prefixWord ++ tailWord_1051394) baseStart_1051394 baseEnd_1051394 := by
    simpa [prefixWord, tailWord_1051394, baseEnd_1051394] using wordTrace_append hprefix tailTrace_1051394
  have hstable : (prefixWord ++ tailWord_1051394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051394).length < 2 ^ (prefixWord ++ tailWord_1051394).sum := by decide
  have hdescent : baseEnd_1051394 < baseStart_1051394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051407 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 4]
def baseStart_1051407 : Nat := 118140960795 + 1051407 * 2 ^ 59
def prefixEnd_1051407 : Nat := 4983230072969 + 3 ^ 40 * 1051407 * 2
def baseEnd_1051407 : Nat := 539877154501873098977173

theorem tailTrace_1051407 : CollatzResearch.WordTrace tailWord_1051407 prefixEnd_1051407 539877154501873098977173 := by
  unfold tailWord_1051407
  simp only [CollatzResearch.WordTrace]
  refine ⟨38347963701939479864728475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25565309134626319909818983 38347963701939479864728475)
  ·
    refine ⟨57521945552909219797092713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38347963701939479864728475 57521945552909219797092713)
    ·
      refine ⟨43141459164681914847819535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57521945552909219797092713 43141459164681914847819535)
      ·
        refine ⟨64712188747022872271729303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43141459164681914847819535 64712188747022872271729303)
        ·
          refine ⟨97068283120534308407593955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64712188747022872271729303 97068283120534308407593955)
          ·
            refine ⟨145602424680801462611390933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97068283120534308407593955 145602424680801462611390933)
            ·
              refine ⟨3412556828456284279954475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 145602424680801462611390933 3412556828456284279954475)
              ·
                refine ⟨5118835242684426419931713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3412556828456284279954475 5118835242684426419931713)
                ·
                  refine ⟨3839126432013319814948785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5118835242684426419931713 3839126432013319814948785)
                  ·
                    refine ⟨2879344824009989861211589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3839126432013319814948785 2879344824009989861211589)
                    ·
                      refine ⟨539877154501873098977173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2879344824009989861211589 539877154501873098977173)
                      ·
                        rfl

theorem cell23_1051407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_1051407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051407 prefixEnd_1051407 := by exact prefixLift 1051407
  have htrace : WordTrace (prefixWord ++ tailWord_1051407) baseStart_1051407 baseEnd_1051407 := by
    simpa [prefixWord, tailWord_1051407, baseEnd_1051407] using wordTrace_append hprefix tailTrace_1051407
  have hstable : (prefixWord ++ tailWord_1051407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051407).length < 2 ^ (prefixWord ++ tailWord_1051407).sum := by decide
  have hdescent : baseEnd_1051407 < baseStart_1051407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051411 : List Nat := [1, 1, 1, 2, 1, 3, 3, 5, 2, 2, 2]
def baseStart_1051411 : Nat := 118140960795 + 1051411 * 2 ^ 59
def prefixEnd_1051411 : Nat := 4983230072969 + 3 ^ 40 * 1051411 * 2
def baseEnd_1051411 : Nat := 539879208424491083327155

theorem tailTrace_1051411 : CollatzResearch.WordTrace tailWord_1051411 prefixEnd_1051411 539879208424491083327155 := by
  unfold tailWord_1051411
  simp only [CollatzResearch.WordTrace]
  refine ⟨38348109593924988547874087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25565406395949992365249391 38348109593924988547874087)
  ·
    refine ⟨57522164390887482821811131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38348109593924988547874087 57522164390887482821811131)
    ·
      refine ⟨86283246586331224232716697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57522164390887482821811131 86283246586331224232716697)
      ·
        refine ⟨64712434939748418174537523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86283246586331224232716697 64712434939748418174537523)
        ·
          refine ⟨97068652409622627261806285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64712434939748418174537523 97068652409622627261806285)
          ·
            refine ⟨36400744653608485223177357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97068652409622627261806285 36400744653608485223177357)
            ·
              refine ⟨13650279245103181958691509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36400744653608485223177357 13650279245103181958691509)
              ·
                refine ⟨1279713679228423308627329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13650279245103181958691509 1279713679228423308627329)
                ·
                  refine ⟨959785259421317481470497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1279713679228423308627329 959785259421317481470497)
                  ·
                    refine ⟨719838944565988111102873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 959785259421317481470497 719838944565988111102873)
                    ·
                      refine ⟨539879208424491083327155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 719838944565988111102873 539879208424491083327155)
                      ·
                        rfl

theorem cell23_1051411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 2, 2].length) (baseStart_1051411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051411 prefixEnd_1051411 := by exact prefixLift 1051411
  have htrace : WordTrace (prefixWord ++ tailWord_1051411) baseStart_1051411 baseEnd_1051411 := by
    simpa [prefixWord, tailWord_1051411, baseEnd_1051411] using wordTrace_append hprefix tailTrace_1051411
  have hstable : (prefixWord ++ tailWord_1051411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051411).length < 2 ^ (prefixWord ++ tailWord_1051411).sum := by decide
  have hdescent : baseEnd_1051411 < baseStart_1051411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051427 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 3]
def baseStart_1051427 : Nat := 118140960795 + 1051427 * 2 ^ 59
def prefixEnd_1051427 : Nat := 4983230072969 + 3 ^ 40 * 1051427 * 2
def baseEnd_1051427 : Nat := 539887424114963020727081

theorem tailTrace_1051427 : CollatzResearch.WordTrace tailWord_1051427 prefixEnd_1051427 539887424114963020727081 := by
  unfold tailWord_1051427
  simp only [CollatzResearch.WordTrace]
  refine ⟨38348693161867023280456535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25565795441244682186971023 38348693161867023280456535)
  ·
    refine ⟨57523039742800534920684803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38348693161867023280456535 57523039742800534920684803)
    ·
      refine ⟨86284559614200802381027205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57523039742800534920684803 86284559614200802381027205)
      ·
        refine ⟨16178354927662650446442601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86284559614200802381027205 16178354927662650446442601)
        ·
          refine ⟨12133766195746987834831951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16178354927662650446442601 12133766195746987834831951)
          ·
            refine ⟨18200649293620481752247927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12133766195746987834831951 18200649293620481752247927)
            ·
              refine ⟨27300973940430722628371891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18200649293620481752247927 27300973940430722628371891)
              ·
                refine ⟨40951460910646083942557837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27300973940430722628371891 40951460910646083942557837)
                ·
                  refine ⟨15356797841492281478459189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40951460910646083942557837 15356797841492281478459189)
                  ·
                    refine ⟨1439699797639901388605549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15356797841492281478459189 1439699797639901388605549)
                    ·
                      refine ⟨539887424114963020727081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1439699797639901388605549 539887424114963020727081)
                      ·
                        rfl

theorem cell23_1051427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_1051427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051427 prefixEnd_1051427 := by exact prefixLift 1051427
  have htrace : WordTrace (prefixWord ++ tailWord_1051427) baseStart_1051427 baseEnd_1051427 := by
    simpa [prefixWord, tailWord_1051427, baseEnd_1051427] using wordTrace_append hprefix tailTrace_1051427
  have hstable : (prefixWord ++ tailWord_1051427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051427).length < 2 ^ (prefixWord ++ tailWord_1051427).sum := by decide
  have hdescent : baseEnd_1051427 < baseStart_1051427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051445 : List Nat := [1, 3, 3, 1, 3, 3, 1, 2, 2, 2, 2]
def baseStart_1051445 : Nat := 118140960795 + 1051445 * 2 ^ 59
def prefixEnd_1051445 : Nat := 4983230072969 + 3 ^ 40 * 1051445 * 2
def baseEnd_1051445 : Nat := 539896666766743950301999

theorem tailTrace_1051445 : CollatzResearch.WordTrace tailWord_1051445 prefixEnd_1051445 539896666766743950301999 := by
  unfold tailWord_1051445
  simp only [CollatzResearch.WordTrace]
  refine ⟨38349349675801812354611789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25566233117201208236407859 38349349675801812354611789)
  ·
    refine ⟨14381006128425679632979421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38349349675801812354611789 14381006128425679632979421)
    ·
      refine ⟨5392877298159629862367283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14381006128425679632979421 5392877298159629862367283)
      ·
        refine ⟨8089315947239444793550925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5392877298159629862367283 8089315947239444793550925)
        ·
          refine ⟨3033493480214791797581597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8089315947239444793550925 3033493480214791797581597)
          ·
            refine ⟨1137560055080546924093099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3033493480214791797581597 1137560055080546924093099)
            ·
              refine ⟨1706340082620820386139649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137560055080546924093099 1706340082620820386139649)
              ·
                refine ⟨1279755061965615289604737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1706340082620820386139649 1279755061965615289604737)
                ·
                  refine ⟨959816296474211467203553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1279755061965615289604737 959816296474211467203553)
                  ·
                    refine ⟨719862222355658600402665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 959816296474211467203553 719862222355658600402665)
                    ·
                      refine ⟨539896666766743950301999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 719862222355658600402665 539896666766743950301999)
                      ·
                        rfl

theorem cell23_1051445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_1051445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051445 prefixEnd_1051445 := by exact prefixLift 1051445
  have htrace : WordTrace (prefixWord ++ tailWord_1051445) baseStart_1051445 baseEnd_1051445 := by
    simpa [prefixWord, tailWord_1051445, baseEnd_1051445] using wordTrace_append hprefix tailTrace_1051445
  have hstable : (prefixWord ++ tailWord_1051445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051445).length < 2 ^ (prefixWord ++ tailWord_1051445).sum := by decide
  have hdescent : baseEnd_1051445 < baseStart_1051445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051447 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 4, 5]
def baseStart_1051447 : Nat := 118140960795 + 1051447 * 2 ^ 59
def prefixEnd_1051447 : Nat := 4983230072969 + 3 ^ 40 * 1051447 * 2
def baseEnd_1051447 : Nat := 179965897909350980825663

theorem tailTrace_1051447 : CollatzResearch.WordTrace tailWord_1051447 prefixEnd_1051447 179965897909350980825663 := by
  unfold tailWord_1051447
  simp only [CollatzResearch.WordTrace]
  refine ⟨38349422621794566696184595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25566281747863044464123063 38349422621794566696184595)
  ·
    refine ⟨57524133932691850044276893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38349422621794566696184595 57524133932691850044276893)
    ·
      refine ⟨21571550224759443766603835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57524133932691850044276893 21571550224759443766603835)
      ·
        refine ⟨32357325337139165649905753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21571550224759443766603835 32357325337139165649905753)
        ·
          refine ⟨24267994002854374237429315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32357325337139165649905753 24267994002854374237429315)
          ·
            refine ⟨36401991004281561356143973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24267994002854374237429315 36401991004281561356143973)
            ·
              refine ⟨6825373313302792754276995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36401991004281561356143973 6825373313302792754276995)
              ·
                refine ⟨10238059969954189131415493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6825373313302792754276995 10238059969954189131415493)
                ·
                  refine ⟨1919636244366410462140405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10238059969954189131415493 1919636244366410462140405)
                  ·
                    refine ⟨179965897909350980825663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1919636244366410462140405 179965897909350980825663)
                    ·
                      rfl

theorem cell23_1051447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_1051447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051447 prefixEnd_1051447 := by exact prefixLift 1051447
  have htrace : WordTrace (prefixWord ++ tailWord_1051447) baseStart_1051447 baseEnd_1051447 := by
    simpa [prefixWord, tailWord_1051447, baseEnd_1051447] using wordTrace_append hprefix tailTrace_1051447
  have hstable : (prefixWord ++ tailWord_1051447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051447).length < 2 ^ (prefixWord ++ tailWord_1051447).sum := by decide
  have hdescent : baseEnd_1051447 < baseStart_1051447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051462 : List Nat := [6, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_1051462 : Nat := 118140960795 + 1051462 * 2 ^ 59
def prefixEnd_1051462 : Nat := 4983230072969 + 3 ^ 40 * 1051462 * 2
def baseEnd_1051462 : Nat := 539905395937870383789421

theorem tailTrace_1051462 : CollatzResearch.WordTrace tailWord_1051462 prefixEnd_1051462 539905395937870383789421 := by
  unfold tailWord_1051462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1198436553648132008061895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25566646477826816171987093 1198436553648132008061895)
  ·
    refine ⟨1797654830472198012092843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1198436553648132008061895 1797654830472198012092843)
    ·
      refine ⟨2696482245708297018139265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1797654830472198012092843 2696482245708297018139265)
      ·
        refine ⟨2022361684281222763604449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2696482245708297018139265 2022361684281222763604449)
        ·
          refine ⟨1516771263210917072703337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2022361684281222763604449 1516771263210917072703337)
          ·
            refine ⟨1137578447408187804527503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1516771263210917072703337 1137578447408187804527503)
            ·
              refine ⟨1706367671112281706791255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137578447408187804527503 1706367671112281706791255)
              ·
                refine ⟨2559551506668422560186883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1706367671112281706791255 2559551506668422560186883)
                ·
                  refine ⟨3839327260002633840280325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2559551506668422560186883 3839327260002633840280325)
                  ·
                    refine ⟨719873861250493845052561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3839327260002633840280325 719873861250493845052561)
                    ·
                      refine ⟨539905395937870383789421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 719873861250493845052561 539905395937870383789421)
                      ·
                        rfl

theorem cell23_1051462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_1051462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051462 prefixEnd_1051462 := by exact prefixLift 1051462
  have htrace : WordTrace (prefixWord ++ tailWord_1051462) baseStart_1051462 baseEnd_1051462 := by
    simpa [prefixWord, tailWord_1051462, baseEnd_1051462] using wordTrace_append hprefix tailTrace_1051462
  have hstable : (prefixWord ++ tailWord_1051462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051462).length < 2 ^ (prefixWord ++ tailWord_1051462).sum := by decide
  have hdescent : baseEnd_1051462 < baseStart_1051462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051477 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 2, 8]
def baseStart_1051477 : Nat := 118140960795 + 1051477 * 2 ^ 59
def prefixEnd_1051477 : Nat := 4983230072969 + 3 ^ 40 * 1051477 * 2
def baseEnd_1051477 : Nat := 179971032715895941700617

theorem tailTrace_1051477 : CollatzResearch.WordTrace tailWord_1051477 prefixEnd_1051477 179971032715895941700617 := by
  unfold tailWord_1051477
  simp only [CollatzResearch.WordTrace]
  refine ⟨38350516811685881819776685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25567011207790587879851123 38350516811685881819776685)
  ·
    refine ⟨14381443804382205682416257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38350516811685881819776685 14381443804382205682416257)
    ·
      refine ⟨10786082853286654261812193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14381443804382205682416257 10786082853286654261812193)
      ·
        refine ⟨8089562139964990696359145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10786082853286654261812193 8089562139964990696359145)
        ·
          refine ⟨6067171604973743022269359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8089562139964990696359145 6067171604973743022269359)
          ·
            refine ⟨9100757407460614533404039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6067171604973743022269359 9100757407460614533404039)
            ·
              refine ⟨13651136111190921800106059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9100757407460614533404039 13651136111190921800106059)
              ·
                refine ⟨20476704166786382700159089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13651136111190921800106059 20476704166786382700159089)
                ·
                  refine ⟨15357528125089787025119317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20476704166786382700159089 15357528125089787025119317)
                  ·
                    refine ⟨179971032715895941700617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15357528125089787025119317 179971032715895941700617)
                    ·
                      rfl

theorem cell23_1051477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_1051477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051477 prefixEnd_1051477 := by exact prefixLift 1051477
  have htrace : WordTrace (prefixWord ++ tailWord_1051477) baseStart_1051477 baseEnd_1051477 := by
    simpa [prefixWord, tailWord_1051477, baseEnd_1051477] using wordTrace_append hprefix tailTrace_1051477
  have hstable : (prefixWord ++ tailWord_1051477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051477).length < 2 ^ (prefixWord ++ tailWord_1051477).sum := by decide
  have hdescent : baseEnd_1051477 < baseStart_1051477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051504 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 3]
def baseStart_1051504 : Nat := 118140960795 + 1051504 * 2 ^ 59
def prefixEnd_1051504 : Nat := 4983230072969 + 3 ^ 40 * 1051504 * 2
def baseEnd_1051504 : Nat := 539926962125359219464227

theorem tailTrace_1051504 : CollatzResearch.WordTrace tailWord_1051504 prefixEnd_1051504 539926962125359219464227 := by
  unfold tailWord_1051504
  simp only [CollatzResearch.WordTrace]
  refine ⟨19175750791294032715504783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25567667721725376954006377 19175750791294032715504783)
  ·
    refine ⟨28763626186941049073257175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19175750791294032715504783 28763626186941049073257175)
    ·
      refine ⟨43145439280411573609885763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28763626186941049073257175 43145439280411573609885763)
      ·
        refine ⟨64718158920617360414828645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43145439280411573609885763 64718158920617360414828645)
        ·
          refine ⟨12134654797615755077780371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64718158920617360414828645 12134654797615755077780371)
          ·
            refine ⟨18201982196423632616670557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12134654797615755077780371 18201982196423632616670557)
            ·
              refine ⟨6825743323658862231251459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18201982196423632616670557 6825743323658862231251459)
              ·
                refine ⟨10238614985488293346877189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6825743323658862231251459 10238614985488293346877189)
                ·
                  refine ⟨1919740309779055002539473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10238614985488293346877189 1919740309779055002539473)
                  ·
                    refine ⟨1439805232334291251904605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1919740309779055002539473 1439805232334291251904605)
                    ·
                      refine ⟨539926962125359219464227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1439805232334291251904605 539926962125359219464227)
                      ·
                        rfl

theorem cell23_1051504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 3].length) (baseStart_1051504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051504 prefixEnd_1051504 := by exact prefixLift 1051504
  have htrace : WordTrace (prefixWord ++ tailWord_1051504) baseStart_1051504 baseEnd_1051504 := by
    simpa [prefixWord, tailWord_1051504, baseEnd_1051504] using wordTrace_append hprefix tailTrace_1051504
  have hstable : (prefixWord ++ tailWord_1051504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051504).length < 2 ^ (prefixWord ++ tailWord_1051504).sum := by decide
  have hdescent : baseEnd_1051504 < baseStart_1051504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051507 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 8]
def baseStart_1051507 : Nat := 118140960795 + 1051507 * 2 ^ 59
def prefixEnd_1051507 : Nat := 4983230072969 + 3 ^ 40 * 1051507 * 2
def baseEnd_1051507 : Nat := 59992055840813634191857

theorem tailTrace_1051507 : CollatzResearch.WordTrace tailWord_1051507 prefixEnd_1051507 59992055840813634191857 := by
  unfold tailWord_1051507
  simp only [CollatzResearch.WordTrace]
  refine ⟨38351611001577196943368775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25567740667718131295579183 38351611001577196943368775)
  ·
    refine ⟨57527416502365795415053163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38351611001577196943368775 57527416502365795415053163)
    ·
      refine ⟨86291124753548693122579745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57527416502365795415053163 86291124753548693122579745)
      ·
        refine ⟨64718343565161519841934809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86291124753548693122579745 64718343565161519841934809)
        ·
          refine ⟨48538757673871139881451107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64718343565161519841934809 48538757673871139881451107)
          ·
            refine ⟨72808136510806709822176661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48538757673871139881451107 72808136510806709822176661)
            ·
              refine ⟨3412881398944064522914531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72808136510806709822176661 3412881398944064522914531)
              ·
                refine ⟨5119322098416096784371797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3412881398944064522914531 5119322098416096784371797)
                ·
                  refine ⟨59992055840813634191857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5119322098416096784371797 59992055840813634191857)
                  ·
                    rfl

theorem cell23_1051507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 8].length) (baseStart_1051507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051507 prefixEnd_1051507 := by exact prefixLift 1051507
  have htrace : WordTrace (prefixWord ++ tailWord_1051507) baseStart_1051507 baseEnd_1051507 := by
    simpa [prefixWord, tailWord_1051507, baseEnd_1051507] using wordTrace_append hprefix tailTrace_1051507
  have hstable : (prefixWord ++ tailWord_1051507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051507).length < 2 ^ (prefixWord ++ tailWord_1051507).sum := by decide
  have hdescent : baseEnd_1051507 < baseStart_1051507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051511 : List Nat := [1, 1, 3, 1, 1, 2, 1, 8, 1, 4]
def baseStart_1051511 : Nat := 118140960795 + 1051511 * 2 ^ 59
def prefixEnd_1051511 : Nat := 4983230072969 + 3 ^ 40 * 1051511 * 2
def baseEnd_1051511 : Nat := 179976852163313564025565

theorem tailTrace_1051511 : CollatzResearch.WordTrace tailWord_1051511 prefixEnd_1051511 179976852163313564025565 := by
  unfold tailWord_1051511
  simp only [CollatzResearch.WordTrace]
  refine ⟨38351756893562705626514387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25567837929041803751009591 38351756893562705626514387)
  ·
    refine ⟨57527635340344058439771581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38351756893562705626514387 57527635340344058439771581)
    ·
      refine ⟨21572863252629021914914343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57527635340344058439771581 21572863252629021914914343)
      ·
        refine ⟨32359294878943532872371515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21572863252629021914914343 32359294878943532872371515)
        ·
          refine ⟨48538942318415299308557273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32359294878943532872371515 48538942318415299308557273)
          ·
            refine ⟨36404206738811474481417955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48538942318415299308557273 36404206738811474481417955)
            ·
              refine ⟨54606310108217211722126933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36404206738811474481417955 54606310108217211722126933)
              ·
                refine ⟨639917696580670449868675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 54606310108217211722126933 639917696580670449868675)
                ·
                  refine ⟨959876544871005674803013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639917696580670449868675 959876544871005674803013)
                  ·
                    refine ⟨179976852163313564025565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 959876544871005674803013 179976852163313564025565)
                    ·
                      rfl

theorem cell23_1051511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 1, 4].length) (baseStart_1051511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051511 prefixEnd_1051511 := by exact prefixLift 1051511
  have htrace : WordTrace (prefixWord ++ tailWord_1051511) baseStart_1051511 baseEnd_1051511 := by
    simpa [prefixWord, tailWord_1051511, baseEnd_1051511] using wordTrace_append hprefix tailTrace_1051511
  have hstable : (prefixWord ++ tailWord_1051511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051511).length < 2 ^ (prefixWord ++ tailWord_1051511).sum := by decide
  have hdescent : baseEnd_1051511 < baseStart_1051511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051561 : List Nat := [1, 2, 1, 1, 1, 1, 5, 4, 2, 3, 2]
def baseStart_1051561 : Nat := 118140960795 + 1051561 * 2 ^ 59
def prefixEnd_1051561 : Nat := 4983230072969 + 3 ^ 40 * 1051561 * 2
def baseEnd_1051561 : Nat := 539956230522665496451465

theorem tailTrace_1051561 : CollatzResearch.WordTrace tailWord_1051561 prefixEnd_1051561 539956230522665496451465 := by
  unfold tailWord_1051561
  simp only [CollatzResearch.WordTrace]
  refine ⟨38353580543381564165834537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25569053695587709443889691 38353580543381564165834537)
  ·
    refine ⟨28765185407536173124375903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38353580543381564165834537 28765185407536173124375903)
    ·
      refine ⟨43147778111304259686563855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28765185407536173124375903 43147778111304259686563855)
      ·
        refine ⟨64721667166956389529845783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43147778111304259686563855 64721667166956389529845783)
        ·
          refine ⟨97082500750434584294768675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64721667166956389529845783 97082500750434584294768675)
          ·
            refine ⟨145623751125651876442153013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97082500750434584294768675 145623751125651876442153013)
            ·
              refine ⟨13652226668029863416451845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145623751125651876442153013 13652226668029863416451845)
              ·
                refine ⟨2559792500255599390584721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13652226668029863416451845 2559792500255599390584721)
                ·
                  refine ⟨1919844375191699542938541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2559792500255599390584721 1919844375191699542938541)
                  ·
                    refine ⟨719941640696887328601953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1919844375191699542938541 719941640696887328601953)
                    ·
                      refine ⟨539956230522665496451465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 719941640696887328601953 539956230522665496451465)
                      ·
                        rfl

theorem cell23_1051561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 3, 2].length) (baseStart_1051561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051561 prefixEnd_1051561 := by exact prefixLift 1051561
  have htrace : WordTrace (prefixWord ++ tailWord_1051561) baseStart_1051561 baseEnd_1051561 := by
    simpa [prefixWord, tailWord_1051561, baseEnd_1051561] using wordTrace_append hprefix tailTrace_1051561
  have hstable : (prefixWord ++ tailWord_1051561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051561).length < 2 ^ (prefixWord ++ tailWord_1051561).sum := by decide
  have hdescent : baseEnd_1051561 < baseStart_1051561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051584 : List Nat := [2, 1, 1, 2, 3, 3, 1, 3, 1, 6]
def baseStart_1051584 : Nat := 118140960795 + 1051584 * 2 ^ 59
def prefixEnd_1051584 : Nat := 4983230072969 + 3 ^ 40 * 1051584 * 2
def baseEnd_1051584 : Nat := 179989346859239635487953

theorem tailTrace_1051584 : CollatzResearch.WordTrace tailWord_1051584 prefixEnd_1051584 179989346859239635487953 := by
  unfold tailWord_1051584
  simp only [CollatzResearch.WordTrace]
  refine ⟨19177209711149119546960903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25569612948198826062614537 19177209711149119546960903)
  ·
    refine ⟨28765814566723679320441355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19177209711149119546960903 28765814566723679320441355)
    ·
      refine ⟨43148721850085518980662033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28765814566723679320441355 43148721850085518980662033)
      ·
        refine ⟨32361541387564139235496525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43148721850085518980662033 32361541387564139235496525)
        ·
          refine ⟨12135578020336552213311197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32361541387564139235496525 12135578020336552213311197)
          ·
            refine ⟨4550841757626207079991699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12135578020336552213311197 4550841757626207079991699)
            ·
              refine ⟨6826262636439310619987549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4550841757626207079991699 6826262636439310619987549)
              ·
                refine ⟨2559848488664741482495331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6826262636439310619987549 2559848488664741482495331)
                ·
                  refine ⟨3839772732997112223742997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2559848488664741482495331 3839772732997112223742997)
                  ·
                    refine ⟨179989346859239635487953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3839772732997112223742997 179989346859239635487953)
                    ·
                      rfl

theorem cell23_1051584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 1, 6].length) (baseStart_1051584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051584 prefixEnd_1051584 := by exact prefixLift 1051584
  have htrace : WordTrace (prefixWord ++ tailWord_1051584) baseStart_1051584 baseEnd_1051584 := by
    simpa [prefixWord, tailWord_1051584, baseEnd_1051584] using wordTrace_append hprefix tailTrace_1051584
  have hstable : (prefixWord ++ tailWord_1051584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051584).length < 2 ^ (prefixWord ++ tailWord_1051584).sum := by decide
  have hdescent : baseEnd_1051584 < baseStart_1051584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051602 : List Nat := [3, 2, 2, 3, 1, 2, 2, 3, 1, 1, 3]
def baseStart_1051602 : Nat := 118140960795 + 1051602 * 2 ^ 59
def prefixEnd_1051602 : Nat := 4983230072969 + 3 ^ 40 * 1051602 * 2
def baseEnd_1051602 : Nat := 539977283229499836038777

theorem tailTrace_1051602 : CollatzResearch.WordTrace tailWord_1051602 prefixEnd_1051602 539977283229499836038777 := by
  unfold tailWord_1051602
  simp only [CollatzResearch.WordTrace]
  refine ⟨9588768984058257042019265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25570050624155352112051373 9588768984058257042019265)
  ·
    refine ⟨7191576738043692781514449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9588768984058257042019265 7191576738043692781514449)
    ·
      refine ⟨5393682553532769586135837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7191576738043692781514449 5393682553532769586135837)
      ·
        refine ⟨2022630957574788594800939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5393682553532769586135837 2022630957574788594800939)
        ·
          refine ⟨3033946436362182892201409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2022630957574788594800939 3033946436362182892201409)
          ·
            refine ⟨2275459827271637169151057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3033946436362182892201409 2275459827271637169151057)
            ·
              refine ⟨1706594870453727876863293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2275459827271637169151057 1706594870453727876863293)
              ·
                refine ⟨639973076420147953823735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1706594870453727876863293 639973076420147953823735)
                ·
                  refine ⟨959959614630221930735603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639973076420147953823735 959959614630221930735603)
                  ·
                    refine ⟨1439939421945332896103405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 959959614630221930735603 1439939421945332896103405)
                    ·
                      refine ⟨539977283229499836038777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1439939421945332896103405 539977283229499836038777)
                      ·
                        rfl

theorem cell23_1051602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_1051602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051602 prefixEnd_1051602 := by exact prefixLift 1051602
  have htrace : WordTrace (prefixWord ++ tailWord_1051602) baseStart_1051602 baseEnd_1051602 := by
    simpa [prefixWord, tailWord_1051602, baseEnd_1051602] using wordTrace_append hprefix tailTrace_1051602
  have hstable : (prefixWord ++ tailWord_1051602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051602).length < 2 ^ (prefixWord ++ tailWord_1051602).sum := by decide
  have hdescent : baseEnd_1051602 < baseStart_1051602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051605 : List Nat := [1, 3, 2, 3, 3, 2, 2, 1, 1, 5]
def baseStart_1051605 : Nat := 118140960795 + 1051605 * 2 ^ 59
def prefixEnd_1051605 : Nat := 4983230072969 + 3 ^ 40 * 1051605 * 2
def baseEnd_1051605 : Nat := 179992941223821108100421

theorem tailTrace_1051605 : CollatzResearch.WordTrace tailWord_1051605 prefixEnd_1051605 179992941223821108100421 := by
  unfold tailWord_1051605
  simp only [CollatzResearch.WordTrace]
  refine ⟨38355185355222159680436269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25570123570148106453624179 38355185355222159680436269)
  ·
    refine ⟨14383194508208309880163601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38355185355222159680436269 14383194508208309880163601)
    ·
      refine ⟨10787395881156232410122701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14383194508208309880163601 10787395881156232410122701)
      ·
        refine ⟨4045273455433587153796013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10787395881156232410122701 4045273455433587153796013)
        ·
          refine ⟨1516977545787595182673505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4045273455433587153796013 1516977545787595182673505)
          ·
            refine ⟨1137733159340696387005129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1516977545787595182673505 1137733159340696387005129)
            ·
              refine ⟨853299869505522290253847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1137733159340696387005129 853299869505522290253847)
              ·
                refine ⟨1279949804258283435380771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853299869505522290253847 1279949804258283435380771)
                ·
                  refine ⟨1919924706387425153071157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279949804258283435380771 1919924706387425153071157)
                  ·
                    refine ⟨179992941223821108100421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1919924706387425153071157 179992941223821108100421)
                    ·
                      rfl

theorem cell23_1051605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_1051605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051605 prefixEnd_1051605 := by exact prefixLift 1051605
  have htrace : WordTrace (prefixWord ++ tailWord_1051605) baseStart_1051605 baseEnd_1051605 := by
    simpa [prefixWord, tailWord_1051605, baseEnd_1051605] using wordTrace_append hprefix tailTrace_1051605
  have hstable : (prefixWord ++ tailWord_1051605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051605).length < 2 ^ (prefixWord ++ tailWord_1051605).sum := by decide
  have hdescent : baseEnd_1051605 < baseStart_1051605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051608 : List Nat := [2, 1, 2, 2, 2, 3, 4, 1, 1, 1, 4]
def baseStart_1051608 : Nat := 118140960795 + 1051608 * 2 ^ 59
def prefixEnd_1051608 : Nat := 4983230072969 + 3 ^ 40 * 1051608 * 2
def baseEnd_1051608 : Nat := 539980364113426812563749

theorem tailTrace_1051608 : CollatzResearch.WordTrace tailWord_1051608 prefixEnd_1051608 539980364113426812563749 := by
  unfold tailWord_1051608
  simp only [CollatzResearch.WordTrace]
  refine ⟨19177647387105645596397739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25570196516140860795196985 19177647387105645596397739)
  ·
    refine ⟨28766471080658468394596609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19177647387105645596397739 28766471080658468394596609)
    ·
      refine ⟨21574853310493851295947457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28766471080658468394596609 21574853310493851295947457)
      ·
        refine ⟨16181139982870388471960593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21574853310493851295947457 16181139982870388471960593)
        ·
          refine ⟨12135854987152791353970445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16181139982870388471960593 12135854987152791353970445)
          ·
            refine ⟨4550945620182296757738917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12135854987152791353970445 4550945620182296757738917)
            ·
              refine ⟨853302303784180642076047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4550945620182296757738917 853302303784180642076047)
              ·
                refine ⟨1279953455676270963114071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853302303784180642076047 1279953455676270963114071)
                ·
                  refine ⟨1919930183514406444671107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279953455676270963114071 1919930183514406444671107)
                  ·
                    refine ⟨2879895275271609667006661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1919930183514406444671107 2879895275271609667006661)
                    ·
                      refine ⟨539980364113426812563749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2879895275271609667006661 539980364113426812563749)
                      ·
                        rfl

theorem cell23_1051608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_1051608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051608 prefixEnd_1051608 := by exact prefixLift 1051608
  have htrace : WordTrace (prefixWord ++ tailWord_1051608) baseStart_1051608 baseEnd_1051608 := by
    simpa [prefixWord, tailWord_1051608, baseEnd_1051608] using wordTrace_append hprefix tailTrace_1051608
  have hstable : (prefixWord ++ tailWord_1051608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051608).length < 2 ^ (prefixWord ++ tailWord_1051608).sum := by decide
  have hdescent : baseEnd_1051608 < baseStart_1051608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051638 : List Nat := [5, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_1051638 : Nat := 118140960795 + 1051638 * 2 ^ 59
def prefixEnd_1051638 : Nat := 4983230072969 + 3 ^ 40 * 1051638 * 2
def baseEnd_1051638 : Nat := 539995768533061695188611

theorem tailTrace_1051638 : CollatzResearch.WordTrace tailWord_1051638 prefixEnd_1051638 539995768533061695188611 := by
  unfold tailWord_1051638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2397274310256412894774223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25570925976068404210925045 2397274310256412894774223)
  ·
    refine ⟨3595911465384619342161335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2397274310256412894774223 3595911465384619342161335)
    ·
      refine ⟨5393867198076929013242003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3595911465384619342161335 5393867198076929013242003)
      ·
        refine ⟨8090800797115393519863005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5393867198076929013242003 8090800797115393519863005)
        ·
          refine ⟨3034050298918272569948627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8090800797115393519863005 3034050298918272569948627)
          ·
            refine ⟨4551075448377408854922941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3034050298918272569948627 4551075448377408854922941)
            ·
              refine ⟨1706653293141528320596103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4551075448377408854922941 1706653293141528320596103)
              ·
                refine ⟨2559979939712292480894155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1706653293141528320596103 2559979939712292480894155)
                ·
                  refine ⟨3839969909568438721341233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2559979939712292480894155 3839969909568438721341233)
                  ·
                    refine ⟨2879977432176329041005925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3839969909568438721341233 2879977432176329041005925)
                    ·
                      refine ⟨539995768533061695188611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2879977432176329041005925 539995768533061695188611)
                      ·
                        rfl

theorem cell23_1051638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_1051638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051638 prefixEnd_1051638 := by exact prefixLift 1051638
  have htrace : WordTrace (prefixWord ++ tailWord_1051638) baseStart_1051638 baseEnd_1051638 := by
    simpa [prefixWord, tailWord_1051638, baseEnd_1051638] using wordTrace_append hprefix tailTrace_1051638
  have hstable : (prefixWord ++ tailWord_1051638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051638).length < 2 ^ (prefixWord ++ tailWord_1051638).sum := by decide
  have hdescent : baseEnd_1051638 < baseStart_1051638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051658 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 4, 1, 3]
def baseStart_1051658 : Nat := 118140960795 + 1051658 * 2 ^ 59
def prefixEnd_1051658 : Nat := 4983230072969 + 3 ^ 40 * 1051658 * 2
def baseEnd_1051658 : Nat := 540006038146151616938519

theorem tailTrace_1051658 : CollatzResearch.WordTrace tailWord_1051658 prefixEnd_1051658 540006038146151616938519 := by
  unfold tailWord_1051658
  simp only [CollatzResearch.WordTrace]
  refine ⟨9589279606007537433028907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25571412282686766488077085 9589279606007537433028907)
  ·
    refine ⟨14383919409011306149543361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9589279606007537433028907 14383919409011306149543361)
    ·
      refine ⟨10787939556758479612157521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14383919409011306149543361 10787939556758479612157521)
      ·
        refine ⟨8090954667568859709118141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10787939556758479612157521 8090954667568859709118141)
        ·
          refine ⟨3034108000338322390919303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8090954667568859709118141 3034108000338322390919303)
          ·
            refine ⟨4551162000507483586378955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3034108000338322390919303 4551162000507483586378955)
            ·
              refine ⟨6826743000761225379568433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4551162000507483586378955 6826743000761225379568433)
              ·
                refine ⟨5120057250570919034676325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6826743000761225379568433 5120057250570919034676325)
                ·
                  refine ⟨960010734482047319001811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5120057250570919034676325 960010734482047319001811)
                  ·
                    refine ⟨1440016101723070978502717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 960010734482047319001811 1440016101723070978502717)
                    ·
                      refine ⟨540006038146151616938519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1440016101723070978502717 540006038146151616938519)
                      ·
                        rfl

theorem cell23_1051658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_1051658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051658 prefixEnd_1051658 := by exact prefixLift 1051658
  have htrace : WordTrace (prefixWord ++ tailWord_1051658) baseStart_1051658 baseEnd_1051658 := by
    simpa [prefixWord, tailWord_1051658, baseEnd_1051658] using wordTrace_append hprefix tailTrace_1051658
  have hstable : (prefixWord ++ tailWord_1051658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051658).length < 2 ^ (prefixWord ++ tailWord_1051658).sum := by decide
  have hdescent : baseEnd_1051658 < baseStart_1051658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051698 : List Nat := [3, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2]
def baseStart_1051698 : Nat := 118140960795 + 1051698 * 2 ^ 59
def prefixEnd_1051698 : Nat := 4983230072969 + 3 ^ 40 * 1051698 * 2
def baseEnd_1051698 : Nat := 540026577372331460438335

theorem tailTrace_1051698 : CollatzResearch.WordTrace tailWord_1051698 prefixEnd_1051698 540026577372331460438335 := by
  unfold tailWord_1051698
  simp only [CollatzResearch.WordTrace]
  refine ⟨9589644335971309140892937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25572384895923491042381165 9589644335971309140892937)
  ·
    refine ⟨7192233251978481855669703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9589644335971309140892937 7192233251978481855669703)
    ·
      refine ⟨10788349877967722783504555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7192233251978481855669703 10788349877967722783504555)
      ·
        refine ⟨16182524816951584175256833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10788349877967722783504555 16182524816951584175256833)
        ·
          refine ⟨12136893612713688131442625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16182524816951584175256833 12136893612713688131442625)
          ·
            refine ⟨9102670209535266098581969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12136893612713688131442625 9102670209535266098581969)
            ·
              refine ⟨6827002657151449573936477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9102670209535266098581969 6827002657151449573936477)
              ·
                refine ⟨2560125996431793590226179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6827002657151449573936477 2560125996431793590226179)
                ·
                  refine ⟨3840188994647690385339269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2560125996431793590226179 3840188994647690385339269)
                  ·
                    refine ⟨720035436496441947251113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3840188994647690385339269 720035436496441947251113)
                    ·
                      refine ⟨540026577372331460438335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 720035436496441947251113 540026577372331460438335)
                      ·
                        rfl

theorem cell23_1051698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_1051698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051698 prefixEnd_1051698 := by exact prefixLift 1051698
  have htrace : WordTrace (prefixWord ++ tailWord_1051698) baseStart_1051698 baseEnd_1051698 := by
    simpa [prefixWord, tailWord_1051698, baseEnd_1051698] using wordTrace_append hprefix tailTrace_1051698
  have hstable : (prefixWord ++ tailWord_1051698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051698).length < 2 ^ (prefixWord ++ tailWord_1051698).sum := by decide
  have hdescent : baseEnd_1051698 < baseStart_1051698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051702 : List Nat := [5, 1, 2, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_1051702 : Nat := 118140960795 + 1051702 * 2 ^ 59
def prefixEnd_1051702 : Nat := 4983230072969 + 3 ^ 40 * 1051702 * 2
def baseEnd_1051702 : Nat := 540028631294949444788317

theorem tailTrace_1051702 : CollatzResearch.WordTrace tailWord_1051702 prefixEnd_1051702 540028631294949444788317 := by
  unfold tailWord_1051702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2397420202241921577919835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25572482157247163497811573 2397420202241921577919835)
  ·
    refine ⟨3596130303362882366879753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2397420202241921577919835 3596130303362882366879753)
    ·
      refine ⟨2697097727522161775159815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3596130303362882366879753 2697097727522161775159815)
      ·
        refine ⟨4045646591283242662739723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2697097727522161775159815 4045646591283242662739723)
        ·
          refine ⟨6068469886924863994109585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4045646591283242662739723 6068469886924863994109585)
          ·
            refine ⟨4551352415193647995582189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6068469886924863994109585 4551352415193647995582189)
            ·
              refine ⟨1706757155697617998343321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4551352415193647995582189 1706757155697617998343321)
              ·
                refine ⟨1280067866773213498757491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1706757155697617998343321 1280067866773213498757491)
                ·
                  refine ⟨1920101800159820248136237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1280067866773213498757491 1920101800159820248136237)
                  ·
                    refine ⟨720038175059932593051089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1920101800159820248136237 720038175059932593051089)
                    ·
                      refine ⟨540028631294949444788317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 720038175059932593051089 540028631294949444788317)
                      ·
                        rfl

theorem cell23_1051702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_1051702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051702 prefixEnd_1051702 := by exact prefixLift 1051702
  have htrace : WordTrace (prefixWord ++ tailWord_1051702) baseStart_1051702 baseEnd_1051702 := by
    simpa [prefixWord, tailWord_1051702, baseEnd_1051702] using wordTrace_append hprefix tailTrace_1051702
  have hstable : (prefixWord ++ tailWord_1051702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051702).length < 2 ^ (prefixWord ++ tailWord_1051702).sum := by decide
  have hdescent : baseEnd_1051702 < baseStart_1051702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051811 : List Nat := [1, 1, 1, 4, 1, 1, 1, 7, 6]
def baseStart_1051811 : Nat := 118140960795 + 1051811 * 2 ^ 59
def prefixEnd_1051811 : Nat := 4983230072969 + 3 ^ 40 * 1051811 * 2
def baseEnd_1051811 : Nat := 60009400076254390925035

theorem tailTrace_1051811 : CollatzResearch.WordTrace tailWord_1051811 prefixEnd_1051811 60009400076254390925035 := by
  unfold tailWord_1051811
  simp only [CollatzResearch.WordTrace]
  refine ⟨38362698792475856862435287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25575132528317237908290191 38362698792475856862435287)
  ·
    refine ⟨57544048188713785293652931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38362698792475856862435287 57544048188713785293652931)
    ·
      refine ⟨86316072283070677940479397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57544048188713785293652931 86316072283070677940479397)
      ·
        refine ⟨16184263553075752113839887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86316072283070677940479397 16184263553075752113839887)
        ·
          refine ⟨24276395329613628170759831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16184263553075752113839887 24276395329613628170759831)
          ·
            refine ⟨36414592994420442256139747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24276395329613628170759831 36414592994420442256139747)
            ·
              refine ⟨54621889491630663384209621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36414592994420442256139747 54621889491630663384209621)
              ·
                refine ⟨1280200534960093673067413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 54621889491630663384209621 1280200534960093673067413)
                ·
                  refine ⟨60009400076254390925035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1280200534960093673067413 60009400076254390925035)
                  ·
                    rfl

theorem cell23_1051811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 6].length) (baseStart_1051811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051811 prefixEnd_1051811 := by exact prefixLift 1051811
  have htrace : WordTrace (prefixWord ++ tailWord_1051811) baseStart_1051811 baseEnd_1051811 := by
    simpa [prefixWord, tailWord_1051811, baseEnd_1051811] using wordTrace_append hprefix tailTrace_1051811
  have hstable : (prefixWord ++ tailWord_1051811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051811).length < 2 ^ (prefixWord ++ tailWord_1051811).sum := by decide
  have hdescent : baseEnd_1051811 < baseStart_1051811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051815 : List Nat := [1, 1, 6, 2, 1, 1, 2, 2, 3, 4]
def baseStart_1051815 : Nat := 118140960795 + 1051815 * 2 ^ 59
def prefixEnd_1051815 : Nat := 4983230072969 + 3 ^ 40 * 1051815 * 2
def baseEnd_1051815 : Nat := 180028884869635834225099

theorem tailTrace_1051815 : CollatzResearch.WordTrace tailWord_1051815 prefixEnd_1051815 180028884869635834225099 := by
  unfold tailWord_1051815
  simp only [CollatzResearch.WordTrace]
  refine ⟨38362844684461365545580899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25575229789640910363720599 38362844684461365545580899)
  ·
    refine ⟨57544267026692048318371349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38362844684461365545580899 57544267026692048318371349)
    ·
      refine ⟨2697387516876189764923657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57544267026692048318371349 2697387516876189764923657)
      ·
        refine ⟨2023040637657142323692743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2697387516876189764923657 2023040637657142323692743)
        ·
          refine ⟨3034560956485713485539115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2023040637657142323692743 3034560956485713485539115)
          ·
            refine ⟨4551841434728570228308673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3034560956485713485539115 4551841434728570228308673)
            ·
              refine ⟨3413881076046427671231505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4551841434728570228308673 3413881076046427671231505)
              ·
                refine ⟨2560410807034820753423629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3413881076046427671231505 2560410807034820753423629)
                ·
                  refine ⟨960154052638057782533861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2560410807034820753423629 960154052638057782533861)
                  ·
                    refine ⟨180028884869635834225099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 960154052638057782533861 180028884869635834225099)
                    ·
                      rfl

theorem cell23_1051815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_1051815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051815 prefixEnd_1051815 := by exact prefixLift 1051815
  have htrace : WordTrace (prefixWord ++ tailWord_1051815) baseStart_1051815 baseEnd_1051815 := by
    simpa [prefixWord, tailWord_1051815, baseEnd_1051815] using wordTrace_append hprefix tailTrace_1051815
  have hstable : (prefixWord ++ tailWord_1051815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051815).length < 2 ^ (prefixWord ++ tailWord_1051815).sum := by decide
  have hdescent : baseEnd_1051815 < baseStart_1051815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051858 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 3, 5]
def baseStart_1051858 : Nat := 118140960795 + 1051858 * 2 ^ 59
def prefixEnd_1051858 : Nat := 4983230072969 + 3 ^ 40 * 1051858 * 2
def baseEnd_1051858 : Nat := 180036244759016944812533

theorem tailTrace_1051858 : CollatzResearch.WordTrace tailWord_1051858 prefixEnd_1051858 180036244759016944812533 := by
  unfold tailWord_1051858
  simp only [CollatzResearch.WordTrace]
  refine ⟨9591103255826395972349057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25576275348870389259597485 9591103255826395972349057)
  ·
    refine ⟨7193327441869796979261793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9591103255826395972349057 7193327441869796979261793)
    ·
      refine ⟨5394995581402347734446345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7193327441869796979261793 5394995581402347734446345)
      ·
        refine ⟨4046246686051760800834759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5394995581402347734446345 4046246686051760800834759)
        ·
          refine ⟨6069370029077641201252139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4046246686051760800834759 6069370029077641201252139)
          ·
            refine ⟨9104055043616461801878209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6069370029077641201252139 9104055043616461801878209)
            ·
              refine ⟨6828041282712346351408657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9104055043616461801878209 6828041282712346351408657)
              ·
                refine ⟨5121030962034259763556493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6828041282712346351408657 5121030962034259763556493)
                ·
                  refine ⟨1920386610762847411333685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5121030962034259763556493 1920386610762847411333685)
                  ·
                    refine ⟨180036244759016944812533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1920386610762847411333685 180036244759016944812533)
                    ·
                      rfl

theorem cell23_1051858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_1051858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051858 prefixEnd_1051858 := by exact prefixLift 1051858
  have htrace : WordTrace (prefixWord ++ tailWord_1051858) baseStart_1051858 baseEnd_1051858 := by
    simpa [prefixWord, tailWord_1051858, baseEnd_1051858] using wordTrace_append hprefix tailTrace_1051858
  have hstable : (prefixWord ++ tailWord_1051858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051858).length < 2 ^ (prefixWord ++ tailWord_1051858).sum := by decide
  have hdescent : baseEnd_1051858 < baseStart_1051858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051862 : List Nat := [5, 2, 1, 2, 2, 1, 1, 3, 6]
def baseStart_1051862 : Nat := 118140960795 + 1051862 * 2 ^ 59
def prefixEnd_1051862 : Nat := 4983230072969 + 3 ^ 40 * 1051862 * 2
def baseEnd_1051862 : Nat := 60012309799963202087509

theorem tailTrace_1051862 : CollatzResearch.WordTrace tailWord_1051862 prefixEnd_1051862 60012309799963202087509 := by
  unfold tailWord_1051862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2397784932205693285783865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25576372610194061715027893 2397784932205693285783865)
  ·
    refine ⟨1798338699154269964337899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2397784932205693285783865 1798338699154269964337899)
    ·
      refine ⟨2697508048731404946506849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1798338699154269964337899 2697508048731404946506849)
      ·
        refine ⟨2023131036548553709880137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2697508048731404946506849 2023131036548553709880137)
        ·
          refine ⟨1517348277411415282410103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2023131036548553709880137 1517348277411415282410103)
          ·
            refine ⟨2276022416117122923615155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517348277411415282410103 2276022416117122923615155)
            ·
              refine ⟨3414033624175684385422733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276022416117122923615155 3414033624175684385422733)
              ·
                refine ⟨1280262609065881644533525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3414033624175684385422733 1280262609065881644533525)
                ·
                  refine ⟨60012309799963202087509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1280262609065881644533525 60012309799963202087509)
                  ·
                    rfl

theorem cell23_1051862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_1051862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051862 prefixEnd_1051862 := by exact prefixLift 1051862
  have htrace : WordTrace (prefixWord ++ tailWord_1051862) baseStart_1051862 baseEnd_1051862 := by
    simpa [prefixWord, tailWord_1051862, baseEnd_1051862] using wordTrace_append hprefix tailTrace_1051862
  have hstable : (prefixWord ++ tailWord_1051862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051862).length < 2 ^ (prefixWord ++ tailWord_1051862).sum := by decide
  have hdescent : baseEnd_1051862 < baseStart_1051862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051882 : List Nat := [3, 1, 3, 1, 1, 4, 2, 1, 2, 3, 2]
def baseStart_1051882 : Nat := 118140960795 + 1051882 * 2 ^ 59
def prefixEnd_1051882 : Nat := 4983230072969 + 3 ^ 40 * 1051882 * 2
def baseEnd_1051882 : Nat := 540121057812758740537489

theorem tailTrace_1051882 : CollatzResearch.WordTrace tailWord_1051882 prefixEnd_1051882 540121057812758740537489 := by
  unfold tailWord_1051882
  simp only [CollatzResearch.WordTrace]
  refine ⟨9591322093804658997067475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25576858916812423992179933 9591322093804658997067475)
  ·
    refine ⟨14386983140706988495601213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9591322093804658997067475 14386983140706988495601213)
    ·
      refine ⟨5395118677765120685850455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14386983140706988495601213 5395118677765120685850455)
      ·
        refine ⟨8092678016647681028775683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5395118677765120685850455 8092678016647681028775683)
        ·
          refine ⟨12139017024971521543163525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8092678016647681028775683 12139017024971521543163525)
          ·
            refine ⟨2276065692182160289343161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12139017024971521543163525 2276065692182160289343161)
            ·
              refine ⟨1707049269136620217007371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2276065692182160289343161 1707049269136620217007371)
              ·
                refine ⟨2560573903704930325511057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1707049269136620217007371 2560573903704930325511057)
                ·
                  refine ⟨1920430427778697744133293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2560573903704930325511057 1920430427778697744133293)
                  ·
                    refine ⟨720161410417011654049985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1920430427778697744133293 720161410417011654049985)
                    ·
                      refine ⟨540121057812758740537489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 720161410417011654049985 540121057812758740537489)
                      ·
                        rfl

theorem cell23_1051882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_1051882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051882 prefixEnd_1051882 := by exact prefixLift 1051882
  have htrace : WordTrace (prefixWord ++ tailWord_1051882) baseStart_1051882 baseEnd_1051882 := by
    simpa [prefixWord, tailWord_1051882, baseEnd_1051882] using wordTrace_append hprefix tailTrace_1051882
  have hstable : (prefixWord ++ tailWord_1051882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051882).length < 2 ^ (prefixWord ++ tailWord_1051882).sum := by decide
  have hdescent : baseEnd_1051882 < baseStart_1051882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051895 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 5, 2, 2]
def baseStart_1051895 : Nat := 118140960795 + 1051895 * 2 ^ 59
def prefixEnd_1051895 : Nat := 4983230072969 + 3 ^ 40 * 1051895 * 2
def baseEnd_1051895 : Nat := 540127733061267189674929

theorem tailTrace_1051895 : CollatzResearch.WordTrace tailWord_1051895 prefixEnd_1051895 540127733061267189674929 := by
  unfold tailWord_1051895
  simp only [CollatzResearch.WordTrace]
  refine ⟨38365762524171539208493139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25577175016114359472328759 38365762524171539208493139)
  ·
    refine ⟨57548643786257308812739709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38365762524171539208493139 57548643786257308812739709)
    ·
      refine ⟨21580741419846490804777391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57548643786257308812739709 21580741419846490804777391)
      ·
        refine ⟨32371112129769736207166087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21580741419846490804777391 32371112129769736207166087)
        ·
          refine ⟨48556668194654604310749131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32371112129769736207166087 48556668194654604310749131)
          ·
            refine ⟨72835002291981906466123697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48556668194654604310749131 72835002291981906466123697)
            ·
              refine ⟨54626251718986429849592773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72835002291981906466123697 54626251718986429849592773)
              ·
                refine ⟨10242422197309955596798645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54626251718986429849592773 10242422197309955596798645)
                ·
                  refine ⟨960227080997808337199873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10242422197309955596798645 960227080997808337199873)
                  ·
                    refine ⟨720170310748356252899905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 960227080997808337199873 720170310748356252899905)
                    ·
                      refine ⟨540127733061267189674929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 720170310748356252899905 540127733061267189674929)
                      ·
                        rfl

theorem cell23_1051895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 2, 2].length) (baseStart_1051895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051895 prefixEnd_1051895 := by exact prefixLift 1051895
  have htrace : WordTrace (prefixWord ++ tailWord_1051895) baseStart_1051895 baseEnd_1051895 := by
    simpa [prefixWord, tailWord_1051895, baseEnd_1051895] using wordTrace_append hprefix tailTrace_1051895
  have hstable : (prefixWord ++ tailWord_1051895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051895).length < 2 ^ (prefixWord ++ tailWord_1051895).sum := by decide
  have hdescent : baseEnd_1051895 < baseStart_1051895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051905 : List Nat := [1, 2, 4, 1, 1, 3, 1, 4, 2, 4]
def baseStart_1051905 : Nat := 118140960795 + 1051905 * 2 ^ 59
def prefixEnd_1051905 : Nat := 4983230072969 + 3 ^ 40 * 1051905 * 2
def baseEnd_1051905 : Nat := 180044289289270716849961

theorem tailTrace_1051905 : CollatzResearch.WordTrace tailWord_1051905 prefixEnd_1051905 180044289289270716849961 := by
  unfold tailWord_1051905
  simp only [CollatzResearch.WordTrace]
  refine ⟨38366127254135310916357169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25577418169423540610904779 38366127254135310916357169)
  ·
    refine ⟨28774595440601483187267877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38366127254135310916357169 28774595440601483187267877)
    ·
      refine ⟨5395236645112778097612727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28774595440601483187267877 5395236645112778097612727)
      ·
        refine ⟨8092854967669167146419091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5395236645112778097612727 8092854967669167146419091)
        ·
          refine ⟨12139282451503750719628637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8092854967669167146419091 12139282451503750719628637)
          ·
            refine ⟨4552230919313906519860739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12139282451503750719628637 4552230919313906519860739)
            ·
              refine ⟨6828346378970859779791109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4552230919313906519860739 6828346378970859779791109)
              ·
                refine ⟨1280314946057036208710833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6828346378970859779791109 1280314946057036208710833)
                ·
                  refine ⟨960236209542777156533125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1280314946057036208710833 960236209542777156533125)
                  ·
                    refine ⟨180044289289270716849961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 960236209542777156533125 180044289289270716849961)
                    ·
                      rfl

theorem cell23_1051905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_1051905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051905 prefixEnd_1051905 := by exact prefixLift 1051905
  have htrace : WordTrace (prefixWord ++ tailWord_1051905) baseStart_1051905 baseEnd_1051905 := by
    simpa [prefixWord, tailWord_1051905, baseEnd_1051905] using wordTrace_append hprefix tailTrace_1051905
  have hstable : (prefixWord ++ tailWord_1051905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051905).length < 2 ^ (prefixWord ++ tailWord_1051905).sum := by decide
  have hdescent : baseEnd_1051905 < baseStart_1051905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051906 : List Nat := [3, 4, 1, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_1051906 : Nat := 118140960795 + 1051906 * 2 ^ 59
def prefixEnd_1051906 : Nat := 4983230072969 + 3 ^ 40 * 1051906 * 2
def baseEnd_1051906 : Nat := 540133381348466646637379

theorem tailTrace_1051906 : CollatzResearch.WordTrace tailWord_1051906 prefixEnd_1051906 540133381348466646637379 := by
  unfold tailWord_1051906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9591540931782922021785893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25577442484754458724762381 9591540931782922021785893)
  ·
    refine ⟨1798413924709297879084855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9591540931782922021785893 1798413924709297879084855)
    ·
      refine ⟨2697620887063946818627283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1798413924709297879084855 2697620887063946818627283)
      ·
        refine ⟨4046431330595920227940925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2697620887063946818627283 4046431330595920227940925)
        ·
          refine ⟨1517411748973470085477847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4046431330595920227940925 1517411748973470085477847)
          ·
            refine ⟨2276117623460205128216771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517411748973470085477847 2276117623460205128216771)
            ·
              refine ⟨3414176435190307692325157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276117623460205128216771 3414176435190307692325157)
              ·
                refine ⟨640158081598182692310967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3414176435190307692325157 640158081598182692310967)
                ·
                  refine ⟨960237122397274038466451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640158081598182692310967 960237122397274038466451)
                  ·
                    refine ⟨1440355683595911057699677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 960237122397274038466451 1440355683595911057699677)
                    ·
                      refine ⟨540133381348466646637379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1440355683595911057699677 540133381348466646637379)
                      ·
                        rfl

theorem cell23_1051906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_1051906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051906 prefixEnd_1051906 := by exact prefixLift 1051906
  have htrace : WordTrace (prefixWord ++ tailWord_1051906) baseStart_1051906 baseEnd_1051906 := by
    simpa [prefixWord, tailWord_1051906, baseEnd_1051906] using wordTrace_append hprefix tailTrace_1051906
  have hstable : (prefixWord ++ tailWord_1051906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051906).length < 2 ^ (prefixWord ++ tailWord_1051906).sum := by decide
  have hdescent : baseEnd_1051906 < baseStart_1051906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051918 : List Nat := [4, 1, 1, 2, 1, 3, 3, 8]
def baseStart_1051918 : Nat := 118140960795 + 1051918 * 2 ^ 59
def prefixEnd_1051918 : Nat := 4983230072969 + 3 ^ 40 * 1051918 * 2
def baseEnd_1051918 : Nat := 20005168263567429618049

theorem tailTrace_1051918 : CollatzResearch.WordTrace tailWord_1051918 prefixEnd_1051918 20005168263567429618049 := by
  unfold tailWord_1051918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4795825175386026767072551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25577734268725476091053605 4795825175386026767072551)
  ·
    refine ⟨7193737763079040150608827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4795825175386026767072551 7193737763079040150608827)
    ·
      refine ⟨10790606644618560225913241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7193737763079040150608827 10790606644618560225913241)
      ·
        refine ⟨8092954983463920169434931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10790606644618560225913241 8092954983463920169434931)
        ·
          refine ⟨12139432475195880254152397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8092954983463920169434931 12139432475195880254152397)
          ·
            refine ⟨4552287178198455095307149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12139432475195880254152397 4552287178198455095307149)
            ·
              refine ⟨1707107691824420660740181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4552287178198455095307149 1707107691824420660740181)
              ·
                refine ⟨20005168263567429618049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1707107691824420660740181 20005168263567429618049)
                ·
                  rfl

theorem cell23_1051918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 8].length) (baseStart_1051918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051918 prefixEnd_1051918 := by exact prefixLift 1051918
  have htrace : WordTrace (prefixWord ++ tailWord_1051918) baseStart_1051918 baseEnd_1051918 := by
    simpa [prefixWord, tailWord_1051918, baseEnd_1051918] using wordTrace_append hprefix tailTrace_1051918
  have hstable : (prefixWord ++ tailWord_1051918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051918).length < 2 ^ (prefixWord ++ tailWord_1051918).sum := by decide
  have hdescent : baseEnd_1051918 < baseStart_1051918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051931 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 4, 7]
def baseStart_1051931 : Nat := 118140960795 + 1051931 * 2 ^ 59
def prefixEnd_1051931 : Nat := 4983230072969 + 3 ^ 40 * 1051931 * 2
def baseEnd_1051931 : Nat := 180048739454943016274921

theorem tailTrace_1051931 : CollatzResearch.WordTrace tailWord_1051931 prefixEnd_1051931 180048739454943016274921 := by
  unfold tailWord_1051931
  simp only [CollatzResearch.WordTrace]
  refine ⟨38367075552041117356803647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25578050368027411571202431 38367075552041117356803647)
  ·
    refine ⟨57550613328061676035205471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38367075552041117356803647 57550613328061676035205471)
    ·
      refine ⟨86325919992092514052808207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57550613328061676035205471 86325919992092514052808207)
      ·
        refine ⟨129488879988138771079212311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86325919992092514052808207 129488879988138771079212311)
        ·
          refine ⟨194233319982208156618818467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129488879988138771079212311 194233319982208156618818467)
          ·
            refine ⟨291349979973312234928227701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194233319982208156618818467 291349979973312234928227701)
            ·
              refine ⟨27314060622498022024521347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 291349979973312234928227701 27314060622498022024521347)
              ·
                refine ⟨40971090933747033036782021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27314060622498022024521347 40971090933747033036782021)
                ·
                  refine ⟨7682079550077568694396629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40971090933747033036782021 7682079550077568694396629)
                  ·
                    refine ⟨180048739454943016274921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7682079550077568694396629 180048739454943016274921)
                    ·
                      rfl

theorem cell23_1051931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 7].length) (baseStart_1051931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051931 prefixEnd_1051931 := by exact prefixLift 1051931
  have htrace : WordTrace (prefixWord ++ tailWord_1051931) baseStart_1051931 baseEnd_1051931 := by
    simpa [prefixWord, tailWord_1051931, baseEnd_1051931] using wordTrace_append hprefix tailTrace_1051931
  have hstable : (prefixWord ++ tailWord_1051931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051931).length < 2 ^ (prefixWord ++ tailWord_1051931).sum := by decide
  have hdescent : baseEnd_1051931 < baseStart_1051931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051935 : List Nat := [1, 1, 2, 4, 4, 1, 3, 7]
def baseStart_1051935 : Nat := 118140960795 + 1051935 * 2 ^ 59
def prefixEnd_1051935 : Nat := 4983230072969 + 3 ^ 40 * 1051935 * 2
def baseEnd_1051935 : Nat := 20005491566201741969435

theorem tailTrace_1051935 : CollatzResearch.WordTrace tailWord_1051935 prefixEnd_1051935 20005491566201741969435 := by
  unfold tailWord_1051935
  simp only [CollatzResearch.WordTrace]
  refine ⟨38367221444026626039949259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25578147629351084026632839 38367221444026626039949259)
  ·
    refine ⟨57550832166039939059923889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38367221444026626039949259 57550832166039939059923889)
    ·
      refine ⟨43163124124529954294942917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57550832166039939059923889 43163124124529954294942917)
      ·
        refine ⟨8093085773349366430301797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43163124124529954294942917 8093085773349366430301797)
        ·
          refine ⟨1517453582503006205681587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8093085773349366430301797 1517453582503006205681587)
          ·
            refine ⟨2276180373754509308522381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517453582503006205681587 2276180373754509308522381)
            ·
              refine ⟨853567640157940990695893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2276180373754509308522381 853567640157940990695893)
              ·
                refine ⟨20005491566201741969435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 853567640157940990695893 20005491566201741969435)
                ·
                  rfl

theorem cell23_1051935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 7].length) (baseStart_1051935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051935 prefixEnd_1051935 := by exact prefixLift 1051935
  have htrace : WordTrace (prefixWord ++ tailWord_1051935) baseStart_1051935 baseEnd_1051935 := by
    simpa [prefixWord, tailWord_1051935, baseEnd_1051935] using wordTrace_append hprefix tailTrace_1051935
  have hstable : (prefixWord ++ tailWord_1051935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051935).length < 2 ^ (prefixWord ++ tailWord_1051935).sum := by decide
  have hdescent : baseEnd_1051935 < baseStart_1051935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051946 : List Nat := [3, 1, 4, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_1051946 : Nat := 118140960795 + 1051946 * 2 ^ 59
def prefixEnd_1051946 : Nat := 4983230072969 + 3 ^ 40 * 1051946 * 2
def baseEnd_1051946 : Nat := 540153920574646490137195

theorem tailTrace_1051946 : CollatzResearch.WordTrace tailWord_1051946 prefixEnd_1051946 540153920574646490137195 := by
  unfold tailWord_1051946
  simp only [CollatzResearch.WordTrace]
  refine ⟨9591905661746693729649923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25578415097991183279066461 9591905661746693729649923)
  ·
    refine ⟨14387858492620040594474885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9591905661746693729649923 14387858492620040594474885)
    ·
      refine ⟨2697723467366257611464041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14387858492620040594474885 2697723467366257611464041)
      ·
        refine ⟨2023292600524693208598031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2697723467366257611464041 2023292600524693208598031)
        ·
          refine ⟨3034938900787039812897047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2023292600524693208598031 3034938900787039812897047)
          ·
            refine ⟨4552408351180559719345571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3034938900787039812897047 4552408351180559719345571)
            ·
              refine ⟨6828612526770839579018357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4552408351180559719345571 6828612526770839579018357)
              ·
                refine ⟨640182424384766210532971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6828612526770839579018357 640182424384766210532971)
                ·
                  refine ⟨960273636577149315799457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640182424384766210532971 960273636577149315799457)
                  ·
                    refine ⟨720205227432861986849593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 960273636577149315799457 720205227432861986849593)
                    ·
                      refine ⟨540153920574646490137195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 720205227432861986849593 540153920574646490137195)
                      ·
                        rfl

theorem cell23_1051946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_1051946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051946 prefixEnd_1051946 := by exact prefixLift 1051946
  have htrace : WordTrace (prefixWord ++ tailWord_1051946) baseStart_1051946 baseEnd_1051946 := by
    simpa [prefixWord, tailWord_1051946, baseEnd_1051946] using wordTrace_append hprefix tailTrace_1051946
  have hstable : (prefixWord ++ tailWord_1051946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051946).length < 2 ^ (prefixWord ++ tailWord_1051946).sum := by decide
  have hdescent : baseEnd_1051946 < baseStart_1051946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051949 : List Nat := [1, 5, 3, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_1051949 : Nat := 118140960795 + 1051949 * 2 ^ 59
def prefixEnd_1051949 : Nat := 4983230072969 + 3 ^ 40 * 1051949 * 2
def baseEnd_1051949 : Nat := 540155461016609978399681

theorem tailTrace_1051949 : CollatzResearch.WordTrace tailWord_1051949 prefixEnd_1051949 540155461016609978399681 := by
  unfold tailWord_1051949
  simp only [CollatzResearch.WordTrace]
  refine ⟨38367732065975906430958901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25578488043983937620639267 38367732065975906430958901)
  ·
    refine ⟨3596974881185241227902397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38367732065975906430958901 3596974881185241227902397)
    ·
      refine ⟨1348865580444465460463399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3596974881185241227902397 1348865580444465460463399)
      ·
        refine ⟨2023298370666698190695099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1348865580444465460463399 2023298370666698190695099)
        ·
          refine ⟨3034947556000047286042649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2023298370666698190695099 3034947556000047286042649)
          ·
            refine ⟨2276210667000035464531987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3034947556000047286042649 2276210667000035464531987)
            ·
              refine ⟨3414316000500053196797981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276210667000035464531987 3414316000500053196797981)
              ·
                refine ⟨1280368500187519948799243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3414316000500053196797981 1280368500187519948799243)
                ·
                  refine ⟨1920552750281279923198865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1280368500187519948799243 1920552750281279923198865)
                  ·
                    refine ⟨1440414562710959942399149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1920552750281279923198865 1440414562710959942399149)
                    ·
                      refine ⟨540155461016609978399681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1440414562710959942399149 540155461016609978399681)
                      ·
                        rfl

theorem cell23_1051949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_1051949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051949 prefixEnd_1051949 := by exact prefixLift 1051949
  have htrace : WordTrace (prefixWord ++ tailWord_1051949) baseStart_1051949 baseEnd_1051949 := by
    simpa [prefixWord, tailWord_1051949, baseEnd_1051949] using wordTrace_append hprefix tailTrace_1051949
  have hstable : (prefixWord ++ tailWord_1051949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051949).length < 2 ^ (prefixWord ++ tailWord_1051949).sum := by decide
  have hdescent : baseEnd_1051949 < baseStart_1051949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051989 : List Nat := [1, 3, 2, 2, 3, 2, 2, 2, 1, 3, 2]
def baseStart_1051989 : Nat := 118140960795 + 1051989 * 2 ^ 59
def prefixEnd_1051989 : Nat := 4983230072969 + 3 ^ 40 * 1051989 * 2
def baseEnd_1051989 : Nat := 540176000242789821899497

theorem tailTrace_1051989 : CollatzResearch.WordTrace tailWord_1051989 prefixEnd_1051989 540176000242789821899497 := by
  unfold tailWord_1051989
  simp only [CollatzResearch.WordTrace]
  refine ⟨38369190985830993262415021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25579460657220662174943347 38369190985830993262415021)
  ·
    refine ⟨14388446619686622473405633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38369190985830993262415021 14388446619686622473405633)
    ·
      refine ⟨10791334964764966855054225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14388446619686622473405633 10791334964764966855054225)
      ·
        refine ⟨8093501223573725141290669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10791334964764966855054225 8093501223573725141290669)
        ·
          refine ⟨3035062958840146927984001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8093501223573725141290669 3035062958840146927984001)
          ·
            refine ⟨2276297219130110195988001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3035062958840146927984001 2276297219130110195988001)
            ·
              refine ⟨1707222914347582646991001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2276297219130110195988001 1707222914347582646991001)
              ·
                refine ⟨1280417185760686985243251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1707222914347582646991001 1280417185760686985243251)
                ·
                  refine ⟨1920625778641030477864877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1280417185760686985243251 1920625778641030477864877)
                  ·
                    refine ⟨720234666990386429199329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1920625778641030477864877 720234666990386429199329)
                    ·
                      refine ⟨540176000242789821899497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 720234666990386429199329 540176000242789821899497)
                      ·
                        rfl

theorem cell23_1051989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_1051989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051989 prefixEnd_1051989 := by exact prefixLift 1051989
  have htrace : WordTrace (prefixWord ++ tailWord_1051989) baseStart_1051989 baseEnd_1051989 := by
    simpa [prefixWord, tailWord_1051989, baseEnd_1051989] using wordTrace_append hprefix tailTrace_1051989
  have hstable : (prefixWord ++ tailWord_1051989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051989).length < 2 ^ (prefixWord ++ tailWord_1051989).sum := by decide
  have hdescent : baseEnd_1051989 < baseStart_1051989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051997 : List Nat := [1, 4, 5, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_1051997 : Nat := 118140960795 + 1051997 * 2 ^ 59
def prefixEnd_1051997 : Nat := 4983230072969 + 3 ^ 40 * 1051997 * 2
def baseEnd_1051997 : Nat := 540180108088025790599461

theorem tailTrace_1051997 : CollatzResearch.WordTrace tailWord_1051997 prefixEnd_1051997 540180108088025790599461 := by
  unfold tailWord_1051997
  simp only [CollatzResearch.WordTrace]
  refine ⟨38369482769802010628706245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25579655179868007085804163 38369482769802010628706245)
  ·
    refine ⟨7194278019337876992882421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38369482769802010628706245 7194278019337876992882421)
    ·
      refine ⟨674463564312925968082727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7194278019337876992882421 674463564312925968082727)
      ·
        refine ⟨1011695346469388952124091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674463564312925968082727 1011695346469388952124091)
        ·
          refine ⟨1517543019704083428186137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011695346469388952124091 1517543019704083428186137)
          ·
            refine ⟨1138157264778062571139603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1517543019704083428186137 1138157264778062571139603)
            ·
              refine ⟨1707235897167093856709405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138157264778062571139603 1707235897167093856709405)
              ·
                refine ⟨640213461437660196266027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1707235897167093856709405 640213461437660196266027)
                ·
                  refine ⟨960320192156490294399041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640213461437660196266027 960320192156490294399041)
                  ·
                    refine ⟨720240144117367720799281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 960320192156490294399041 720240144117367720799281)
                    ·
                      refine ⟨540180108088025790599461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 720240144117367720799281 540180108088025790599461)
                      ·
                        rfl

theorem cell23_1051997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_1051997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1051997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1051997 prefixEnd_1051997 := by exact prefixLift 1051997
  have htrace : WordTrace (prefixWord ++ tailWord_1051997) baseStart_1051997 baseEnd_1051997 := by
    simpa [prefixWord, tailWord_1051997, baseEnd_1051997] using wordTrace_append hprefix tailTrace_1051997
  have hstable : (prefixWord ++ tailWord_1051997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051997).length < 2 ^ (prefixWord ++ tailWord_1051997).sum := by decide
  have hdescent : baseEnd_1051997 < baseStart_1051997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052002 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_1052002 : Nat := 118140960795 + 1052002 * 2 ^ 59
def prefixEnd_1052002 : Nat := 4983230072969 + 3 ^ 40 * 1052002 * 2
def baseEnd_1052002 : Nat := 540182675491298271036937

theorem tailTrace_1052002 : CollatzResearch.WordTrace tailWord_1052002 prefixEnd_1052002 540182675491298271036937 := by
  unfold tailWord_1052002
  simp only [CollatzResearch.WordTrace]
  refine ⟨9592416283695974120659565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25579776756522597655092173 9592416283695974120659565)
  ·
    refine ⟨3597156106385990295247337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9592416283695974120659565 3597156106385990295247337)
    ·
      refine ⟨2697867079789492721435503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3597156106385990295247337 2697867079789492721435503)
      ·
        refine ⟨4046800619684239082153255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2697867079789492721435503 4046800619684239082153255)
        ·
          refine ⟨6070200929526358623229883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4046800619684239082153255 6070200929526358623229883)
          ·
            refine ⟨9105301394289537934844825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6070200929526358623229883 9105301394289537934844825)
            ·
              refine ⟨6828976045717153451133619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9105301394289537934844825 6828976045717153451133619)
              ·
                refine ⟨10243464068575730176700429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6828976045717153451133619 10243464068575730176700429)
                ·
                  refine ⟨3841299025715898816262661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10243464068575730176700429 3841299025715898816262661)
                  ·
                    refine ⟨720243567321731028049249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3841299025715898816262661 720243567321731028049249)
                    ·
                      refine ⟨540182675491298271036937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 720243567321731028049249 540182675491298271036937)
                      ·
                        rfl

theorem cell23_1052002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_1052002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052002 prefixEnd_1052002 := by exact prefixLift 1052002
  have htrace : WordTrace (prefixWord ++ tailWord_1052002) baseStart_1052002 baseEnd_1052002 := by
    simpa [prefixWord, tailWord_1052002, baseEnd_1052002] using wordTrace_append hprefix tailTrace_1052002
  have hstable : (prefixWord ++ tailWord_1052002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052002).length < 2 ^ (prefixWord ++ tailWord_1052002).sum := by decide
  have hdescent : baseEnd_1052002 < baseStart_1052002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052018 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_1052018 : Nat := 118140960795 + 1052018 * 2 ^ 59
def prefixEnd_1052018 : Nat := 4983230072969 + 3 ^ 40 * 1052018 * 2
def baseEnd_1052018 : Nat := 540190891181770208436863

theorem tailTrace_1052018 : CollatzResearch.WordTrace tailWord_1052018 prefixEnd_1052018 540190891181770208436863 := by
  unfold tailWord_1052018
  simp only [CollatzResearch.WordTrace]
  refine ⟨9592562175681482803805177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25580165801817287476813805 9592562175681482803805177)
  ·
    refine ⟨7194421631761112102853883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9592562175681482803805177 7194421631761112102853883)
    ·
      refine ⟨10791632447641668154280825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7194421631761112102853883 10791632447641668154280825)
      ·
        refine ⟨8093724335731251115710619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10791632447641668154280825 8093724335731251115710619)
        ·
          refine ⟨12140586503596876673565929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8093724335731251115710619 12140586503596876673565929)
          ·
            refine ⟨9105439877697657505174447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12140586503596876673565929 9105439877697657505174447)
            ·
              refine ⟨13658159816546486257761671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9105439877697657505174447 13658159816546486257761671)
              ·
                refine ⟨20487239724819729386642507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13658159816546486257761671 20487239724819729386642507)
                ·
                  refine ⟨30730859587229594079963761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20487239724819729386642507 30730859587229594079963761)
                  ·
                    refine ⟨23048144690422195559972821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30730859587229594079963761 23048144690422195559972821)
                    ·
                      refine ⟨540190891181770208436863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23048144690422195559972821 540190891181770208436863)
                      ·
                        rfl

theorem cell23_1052018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_1052018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052018 prefixEnd_1052018 := by exact prefixLift 1052018
  have htrace : WordTrace (prefixWord ++ tailWord_1052018) baseStart_1052018 baseEnd_1052018 := by
    simpa [prefixWord, tailWord_1052018, baseEnd_1052018] using wordTrace_append hprefix tailTrace_1052018
  have hstable : (prefixWord ++ tailWord_1052018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052018).length < 2 ^ (prefixWord ++ tailWord_1052018).sum := by decide
  have hdescent : baseEnd_1052018 < baseStart_1052018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052025 : List Nat := [1, 2, 1, 3, 2, 1, 2, 6, 5]
def baseStart_1052025 : Nat := 118140960795 + 1052025 * 2 ^ 59
def prefixEnd_1052025 : Nat := 4983230072969 + 3 ^ 40 * 1052025 * 2
def baseEnd_1052025 : Nat := 60021609505150186783259

theorem tailTrace_1052025 : CollatzResearch.WordTrace tailWord_1052025 prefixEnd_1052025 60021609505150186783259 := by
  unfold tailWord_1052025
  simp only [CollatzResearch.WordTrace]
  refine ⟨38370504013700571410725529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25580336009133714273817019 38370504013700571410725529)
  ·
    refine ⟨28777878010275428558044147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38370504013700571410725529 28777878010275428558044147)
    ·
      refine ⟨43166817015413142837066221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28777878010275428558044147 43166817015413142837066221)
      ·
        refine ⟨16187556380779928563899833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43166817015413142837066221 16187556380779928563899833)
        ·
          refine ⟨12140667285584946422924875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16187556380779928563899833 12140667285584946422924875)
          ·
            refine ⟨18211000928377419634387313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12140667285584946422924875 18211000928377419634387313)
            ·
              refine ⟨13658250696283064725790485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18211000928377419634387313 13658250696283064725790485)
              ·
                refine ⟨640230501388268659021429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13658250696283064725790485 640230501388268659021429)
                ·
                  refine ⟨60021609505150186783259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 640230501388268659021429 60021609505150186783259)
                  ·
                    rfl

theorem cell23_1052025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 5].length) (baseStart_1052025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052025 prefixEnd_1052025 := by exact prefixLift 1052025
  have htrace : WordTrace (prefixWord ++ tailWord_1052025) baseStart_1052025 baseEnd_1052025 := by
    simpa [prefixWord, tailWord_1052025, baseEnd_1052025] using wordTrace_append hprefix tailTrace_1052025
  have hstable : (prefixWord ++ tailWord_1052025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052025).length < 2 ^ (prefixWord ++ tailWord_1052025).sum := by decide
  have hdescent : baseEnd_1052025 < baseStart_1052025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052030 : List Nat := [4, 2, 3, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_1052030 : Nat := 118140960795 + 1052030 * 2 ^ 59
def prefixEnd_1052030 : Nat := 4983230072969 + 3 ^ 40 * 1052030 * 2
def baseEnd_1052030 : Nat := 540197052949624161486809

theorem tailTrace_1052030 : CollatzResearch.WordTrace tailWord_1052030 prefixEnd_1052030 540197052949624161486809 := by
  unfold tailWord_1052030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4796335797335307158082193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25580457585788304843105029 4796335797335307158082193)
  ·
    refine ⟨3597251848001480368561645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4796335797335307158082193 3597251848001480368561645)
    ·
      refine ⟨1348969443000555138210617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3597251848001480368561645 1348969443000555138210617)
      ·
        refine ⟨1011727082250416353657963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1348969443000555138210617 1011727082250416353657963)
        ·
          refine ⟨1517590623375624530486945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011727082250416353657963 1517590623375624530486945)
          ·
            refine ⟨1138192967531718397865209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1517590623375624530486945 1138192967531718397865209)
            ·
              refine ⟨853644725648788798398907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1138192967531718397865209 853644725648788798398907)
              ·
                refine ⟨1280467088473183197598361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853644725648788798398907 1280467088473183197598361)
                ·
                  refine ⟨960350316354887398198771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1280467088473183197598361 960350316354887398198771)
                  ·
                    refine ⟨1440525474532331097298157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 960350316354887398198771 1440525474532331097298157)
                    ·
                      refine ⟨540197052949624161486809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1440525474532331097298157 540197052949624161486809)
                      ·
                        rfl

theorem cell23_1052030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_1052030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052030 prefixEnd_1052030 := by exact prefixLift 1052030
  have htrace : WordTrace (prefixWord ++ tailWord_1052030) baseStart_1052030 baseEnd_1052030 := by
    simpa [prefixWord, tailWord_1052030, baseEnd_1052030] using wordTrace_append hprefix tailTrace_1052030
  have hstable : (prefixWord ++ tailWord_1052030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052030).length < 2 ^ (prefixWord ++ tailWord_1052030).sum := by decide
  have hdescent : baseEnd_1052030 < baseStart_1052030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052036 : List Nat := [2, 3, 2, 1, 1, 3, 4, 1, 2, 2, 2]
def baseStart_1052036 : Nat := 118140960795 + 1052036 * 2 ^ 59
def prefixEnd_1052036 : Nat := 4983230072969 + 3 ^ 40 * 1052036 * 2
def baseEnd_1052036 : Nat := 540200133833551138011781

theorem tailTrace_1052036 : CollatzResearch.WordTrace tailWord_1052036 prefixEnd_1052036 540200133833551138011781 := by
  unfold tailWord_1052036
  simp only [CollatzResearch.WordTrace]
  refine ⟨19185452608330360144687981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25580603477773813526250641 19185452608330360144687981)
  ·
    refine ⟨7194544728123885054257993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19185452608330360144687981 7194544728123885054257993)
    ·
      refine ⟨5395908546092913790693495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7194544728123885054257993 5395908546092913790693495)
      ·
        refine ⟨8093862819139370686040243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5395908546092913790693495 8093862819139370686040243)
        ·
          refine ⟨12140794228709056029060365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8093862819139370686040243 12140794228709056029060365)
          ·
            refine ⟨4552797835765896010897637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12140794228709056029060365 4552797835765896010897637)
            ·
              refine ⟨853649594206105502043307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4552797835765896010897637 853649594206105502043307)
              ·
                refine ⟨1280474391309158253064961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853649594206105502043307 1280474391309158253064961)
                ·
                  refine ⟨960355793481868689798721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1280474391309158253064961 960355793481868689798721)
                  ·
                    refine ⟨720266845111401517349041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 960355793481868689798721 720266845111401517349041)
                    ·
                      refine ⟨540200133833551138011781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 720266845111401517349041 540200133833551138011781)
                      ·
                        rfl

theorem cell23_1052036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_1052036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052036 prefixEnd_1052036 := by exact prefixLift 1052036
  have htrace : WordTrace (prefixWord ++ tailWord_1052036) baseStart_1052036 baseEnd_1052036 := by
    simpa [prefixWord, tailWord_1052036, baseEnd_1052036] using wordTrace_append hprefix tailTrace_1052036
  have hstable : (prefixWord ++ tailWord_1052036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052036).length < 2 ^ (prefixWord ++ tailWord_1052036).sum := by decide
  have hdescent : baseEnd_1052036 < baseStart_1052036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052095 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 3]
def baseStart_1052095 : Nat := 118140960795 + 1052095 * 2 ^ 59
def prefixEnd_1052095 : Nat := 4983230072969 + 3 ^ 40 * 1052095 * 2
def baseEnd_1052095 : Nat := 540230429192166407174009

theorem tailTrace_1052095 : CollatzResearch.WordTrace tailWord_1052095 prefixEnd_1052095 540230429192166407174009 := by
  unfold tailWord_1052095
  simp only [CollatzResearch.WordTrace]
  refine ⟨38373057123446973365773739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25582038082297982243849159 38373057123446973365773739)
  ·
    refine ⟨57559585685170460048660609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38373057123446973365773739 57559585685170460048660609)
    ·
      refine ⟨43169689263877845036495457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57559585685170460048660609 43169689263877845036495457)
      ·
        refine ⟨32377266947908383777371593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43169689263877845036495457 32377266947908383777371593)
        ·
          refine ⟨24282950210931287833028695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32377266947908383777371593 24282950210931287833028695)
          ·
            refine ⟨36424425316396931749543043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24282950210931287833028695 36424425316396931749543043)
            ·
              refine ⟨54636637974595397624314565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36424425316396931749543043 54636637974595397624314565)
              ·
                refine ⟨10244369620236637054558981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54636637974595397624314565 10244369620236637054558981)
                ·
                  refine ⟨1920819303794369447729809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10244369620236637054558981 1920819303794369447729809)
                  ·
                    refine ⟨1440614477845777085797357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1920819303794369447729809 1440614477845777085797357)
                    ·
                      refine ⟨540230429192166407174009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1440614477845777085797357 540230429192166407174009)
                      ·
                        rfl

theorem cell23_1052095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_1052095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052095 prefixEnd_1052095 := by exact prefixLift 1052095
  have htrace : WordTrace (prefixWord ++ tailWord_1052095) baseStart_1052095 baseEnd_1052095 := by
    simpa [prefixWord, tailWord_1052095, baseEnd_1052095] using wordTrace_append hprefix tailTrace_1052095
  have hstable : (prefixWord ++ tailWord_1052095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052095).length < 2 ^ (prefixWord ++ tailWord_1052095).sum := by decide
  have hdescent : baseEnd_1052095 < baseStart_1052095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052135 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_1052135 : Nat := 118140960795 + 1052135 * 2 ^ 59
def prefixEnd_1052135 : Nat := 4983230072969 + 3 ^ 40 * 1052135 * 2
def baseEnd_1052135 : Nat := 540250968418346250673825

theorem tailTrace_1052135 : CollatzResearch.WordTrace tailWord_1052135 prefixEnd_1052135 540250968418346250673825 := by
  unfold tailWord_1052135
  simp only [CollatzResearch.WordTrace]
  refine ⟨38374516043302060197229859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25583010695534706798153239 38374516043302060197229859)
  ·
    refine ⟨57561774064953090295844789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38374516043302060197229859 57561774064953090295844789)
    ·
      refine ⟨5396416318589352215235449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57561774064953090295844789 5396416318589352215235449)
      ·
        refine ⟨4047312238942014161426587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5396416318589352215235449 4047312238942014161426587)
        ·
          refine ⟨6070968358413021242139881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4047312238942014161426587 6070968358413021242139881)
          ·
            refine ⟨4553226268809765931604911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6070968358413021242139881 4553226268809765931604911)
            ·
              refine ⟨6829839403214648897407367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4553226268809765931604911 6829839403214648897407367)
              ·
                refine ⟨10244759104821973346111051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6829839403214648897407367 10244759104821973346111051)
                ·
                  refine ⟨15367138657232960019166577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10244759104821973346111051 15367138657232960019166577)
                  ·
                    refine ⟨11525353992924720014374933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15367138657232960019166577 11525353992924720014374933)
                    ·
                      refine ⟨540250968418346250673825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11525353992924720014374933 540250968418346250673825)
                      ·
                        rfl

theorem cell23_1052135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_1052135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052135 prefixEnd_1052135 := by exact prefixLift 1052135
  have htrace : WordTrace (prefixWord ++ tailWord_1052135) baseStart_1052135 baseEnd_1052135 := by
    simpa [prefixWord, tailWord_1052135, baseEnd_1052135] using wordTrace_append hprefix tailTrace_1052135
  have hstable : (prefixWord ++ tailWord_1052135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052135).length < 2 ^ (prefixWord ++ tailWord_1052135).sum := by decide
  have hdescent : baseEnd_1052135 < baseStart_1052135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052152 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 1, 5, 2]
def baseStart_1052152 : Nat := 118140960795 + 1052152 * 2 ^ 59
def prefixEnd_1052152 : Nat := 4983230072969 + 3 ^ 40 * 1052152 * 2
def baseEnd_1052152 : Nat := 540259697589472684161247

theorem tailTrace_1052152 : CollatzResearch.WordTrace tailWord_1052152 prefixEnd_1052152 540259697589472684161247 := by
  unfold tailWord_1052152
  simp only [CollatzResearch.WordTrace]
  refine ⟨19187568042120236050299355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25583424056160314733732473 19187568042120236050299355)
  ·
    refine ⟨28781352063180354075449033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19187568042120236050299355 28781352063180354075449033)
    ·
      refine ⟨21586014047385265556586775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28781352063180354075449033 21586014047385265556586775)
      ·
        refine ⟨32379021071077898334880163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21586014047385265556586775 32379021071077898334880163)
        ·
          refine ⟨48568531606616847502320245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32379021071077898334880163 48568531606616847502320245)
          ·
            refine ⟨4553299838120329453342523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48568531606616847502320245 4553299838120329453342523)
            ·
              refine ⟨6829949757180494180013785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4553299838120329453342523 6829949757180494180013785)
              ·
                refine ⟨5122462317885370635010339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6829949757180494180013785 5122462317885370635010339)
                ·
                  refine ⟨7683693476828055952515509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5122462317885370635010339 7683693476828055952515509)
                  ·
                    refine ⟨720346263452630245548329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7683693476828055952515509 720346263452630245548329)
                    ·
                      refine ⟨540259697589472684161247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 720346263452630245548329 540259697589472684161247)
                      ·
                        rfl

theorem cell23_1052152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 1, 5, 2].length) (baseStart_1052152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052152 prefixEnd_1052152 := by exact prefixLift 1052152
  have htrace : WordTrace (prefixWord ++ tailWord_1052152) baseStart_1052152 baseEnd_1052152 := by
    simpa [prefixWord, tailWord_1052152, baseEnd_1052152] using wordTrace_append hprefix tailTrace_1052152
  have hstable : (prefixWord ++ tailWord_1052152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052152).length < 2 ^ (prefixWord ++ tailWord_1052152).sum := by decide
  have hdescent : baseEnd_1052152 < baseStart_1052152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052193 : List Nat := [1, 2, 3, 2, 2, 3, 3, 2, 1, 1, 3]
def baseStart_1052193 : Nat := 118140960795 + 1052193 * 2 ^ 59
def prefixEnd_1052193 : Nat := 4983230072969 + 3 ^ 40 * 1052193 * 2
def baseEnd_1052193 : Nat := 540280750296307023748559

theorem tailTrace_1052193 : CollatzResearch.WordTrace tailWord_1052193 prefixEnd_1052193 540280750296307023748559 := by
  unfold tailWord_1052193
  simp only [CollatzResearch.WordTrace]
  refine ⟨38376631477091936102841233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25584420984727957401894155 38376631477091936102841233)
  ·
    refine ⟨28782473607818952077130925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38376631477091936102841233 28782473607818952077130925)
    ·
      refine ⟨10793427602932107028924097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28782473607818952077130925 10793427602932107028924097)
      ·
        refine ⟨8095070702199080271693073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10793427602932107028924097 8095070702199080271693073)
        ·
          refine ⟨6071303026649310203769805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8095070702199080271693073 6071303026649310203769805)
          ·
            refine ⟨2276738634993491326413677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6071303026649310203769805 2276738634993491326413677)
            ·
              refine ⟨853776988122559247405129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2276738634993491326413677 853776988122559247405129)
              ·
                refine ⟨640332741091919435553847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 853776988122559247405129 640332741091919435553847)
                ·
                  refine ⟨960499111637879153330771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640332741091919435553847 960499111637879153330771)
                  ·
                    refine ⟨1440748667456818729996157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 960499111637879153330771 1440748667456818729996157)
                    ·
                      refine ⟨540280750296307023748559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1440748667456818729996157 540280750296307023748559)
                      ·
                        rfl

theorem cell23_1052193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_1052193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052193 prefixEnd_1052193 := by exact prefixLift 1052193
  have htrace : WordTrace (prefixWord ++ tailWord_1052193) baseStart_1052193 baseEnd_1052193 := by
    simpa [prefixWord, tailWord_1052193, baseEnd_1052193] using wordTrace_append hprefix tailTrace_1052193
  have hstable : (prefixWord ++ tailWord_1052193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052193).length < 2 ^ (prefixWord ++ tailWord_1052193).sum := by decide
  have hdescent : baseEnd_1052193 < baseStart_1052193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052202 : List Nat := [3, 1, 4, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_1052202 : Nat := 118140960795 + 1052202 * 2 ^ 59
def prefixEnd_1052202 : Nat := 4983230072969 + 3 ^ 40 * 1052202 * 2
def baseEnd_1052202 : Nat := 540285371622197488536017

theorem tailTrace_1052202 : CollatzResearch.WordTrace tailWord_1052202 prefixEnd_1052202 540285371622197488536017 := by
  unfold tailWord_1052202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9594239933514832659979715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25584639822706220426612573 9594239933514832659979715)
  ·
    refine ⟨14391359900272248989969573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9594239933514832659979715 14391359900272248989969573)
    ·
      refine ⟨2698379981301046685619295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14391359900272248989969573 2698379981301046685619295)
      ·
        refine ⟨4047569971951570028428943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2698379981301046685619295 4047569971951570028428943)
        ·
          refine ⟨6071354957927355042643415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4047569971951570028428943 6071354957927355042643415)
          ·
            refine ⟨9107032436891032563965123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6071354957927355042643415 9107032436891032563965123)
            ·
              refine ⟨13660548655336548845947685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9107032436891032563965123 13660548655336548845947685)
              ·
                refine ⟨2561352872875602908615191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13660548655336548845947685 2561352872875602908615191)
                ·
                  refine ⟨3842029309313404362922787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2561352872875602908615191 3842029309313404362922787)
                  ·
                    refine ⟨5763043963970106544384181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3842029309313404362922787 5763043963970106544384181)
                    ·
                      refine ⟨540285371622197488536017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5763043963970106544384181 540285371622197488536017)
                      ·
                        rfl

theorem cell23_1052202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_1052202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052202 prefixEnd_1052202 := by exact prefixLift 1052202
  have htrace : WordTrace (prefixWord ++ tailWord_1052202) baseStart_1052202 baseEnd_1052202 := by
    simpa [prefixWord, tailWord_1052202, baseEnd_1052202] using wordTrace_append hprefix tailTrace_1052202
  have hstable : (prefixWord ++ tailWord_1052202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052202).length < 2 ^ (prefixWord ++ tailWord_1052202).sum := by decide
  have hdescent : baseEnd_1052202 < baseStart_1052202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052236 : List Nat := [2, 2, 1, 3, 1, 4, 3, 1, 1, 2, 3]
def baseStart_1052236 : Nat := 118140960795 + 1052236 * 2 ^ 59
def prefixEnd_1052236 : Nat := 4983230072969 + 3 ^ 40 * 1052236 * 2
def baseEnd_1052236 : Nat := 540302829964450355510861

theorem tailTrace_1052236 : CollatzResearch.WordTrace tailWord_1052236 prefixEnd_1052236 540302829964450355510861 := by
  unfold tailWord_1052236
  simp only [CollatzResearch.WordTrace]
  refine ⟨19189099907968077223328281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25585466543957436297771041 19189099907968077223328281)
  ·
    refine ⟨14391824930976057917496211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19189099907968077223328281 14391824930976057917496211)
    ·
      refine ⟨21587737396464086876244317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14391824930976057917496211 21587737396464086876244317)
      ·
        refine ⟨8095401523674032578591619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21587737396464086876244317 8095401523674032578591619)
        ·
          refine ⟨12143102285511048867887429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8095401523674032578591619 12143102285511048867887429)
          ·
            refine ⟨2276831678533321662728893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12143102285511048867887429 2276831678533321662728893)
            ·
              refine ⟨853811879449995623523335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2276831678533321662728893 853811879449995623523335)
              ·
                refine ⟨1280717819174993435285003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853811879449995623523335 1280717819174993435285003)
                ·
                  refine ⟨1921076728762490152927505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1280717819174993435285003 1921076728762490152927505)
                  ·
                    refine ⟨1440807546571867614695629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1921076728762490152927505 1440807546571867614695629)
                    ·
                      refine ⟨540302829964450355510861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1440807546571867614695629 540302829964450355510861)
                      ·
                        rfl

theorem cell23_1052236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_1052236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052236 prefixEnd_1052236 := by exact prefixLift 1052236
  have htrace : WordTrace (prefixWord ++ tailWord_1052236) baseStart_1052236 baseEnd_1052236 := by
    simpa [prefixWord, tailWord_1052236, baseEnd_1052236] using wordTrace_append hprefix tailTrace_1052236
  have hstable : (prefixWord ++ tailWord_1052236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052236).length < 2 ^ (prefixWord ++ tailWord_1052236).sum := by decide
  have hdescent : baseEnd_1052236 < baseStart_1052236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052252 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 2, 7]
def baseStart_1052252 : Nat := 118140960795 + 1052252 * 2 ^ 59
def prefixEnd_1052252 : Nat := 4983230072969 + 3 ^ 40 * 1052252 * 2
def baseEnd_1052252 : Nat := 180103681884974097636929

theorem tailTrace_1052252 : CollatzResearch.WordTrace tailWord_1052252 prefixEnd_1052252 180103681884974097636929 := by
  unfold tailWord_1052252
  simp only [CollatzResearch.WordTrace]
  refine ⟨19189391691939094589619505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25585855589252126119492673 19189391691939094589619505)
  ·
    refine ⟨14392043768954320942214629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19189391691939094589619505 14392043768954320942214629)
    ·
      refine ⟨2698508206678935176665243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14392043768954320942214629 2698508206678935176665243)
      ·
        refine ⟨4047762310018402764997865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2698508206678935176665243 4047762310018402764997865)
        ·
          refine ⟨3035821732513802073748399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4047762310018402764997865 3035821732513802073748399)
          ·
            refine ⟨4553732598770703110622599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3035821732513802073748399 4553732598770703110622599)
            ·
              refine ⟨6830598898156054665933899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4553732598770703110622599 6830598898156054665933899)
              ·
                refine ⟨10245898347234081998900849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6830598898156054665933899 10245898347234081998900849)
                ·
                  refine ⟨7684423760425561499175637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10245898347234081998900849 7684423760425561499175637)
                  ·
                    refine ⟨180103681884974097636929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7684423760425561499175637 180103681884974097636929)
                    ·
                      rfl

theorem cell23_1052252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_1052252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052252 prefixEnd_1052252 := by exact prefixLift 1052252
  have htrace : WordTrace (prefixWord ++ tailWord_1052252) baseStart_1052252 baseEnd_1052252 := by
    simpa [prefixWord, tailWord_1052252, baseEnd_1052252] using wordTrace_append hprefix tailTrace_1052252
  have hstable : (prefixWord ++ tailWord_1052252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052252).length < 2 ^ (prefixWord ++ tailWord_1052252).sum := by decide
  have hdescent : baseEnd_1052252 < baseStart_1052252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052259 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 3, 3, 2]
def baseStart_1052259 : Nat := 118140960795 + 1052259 * 2 ^ 59
def prefixEnd_1052259 : Nat := 4983230072969 + 3 ^ 40 * 1052259 * 2
def baseEnd_1052259 : Nat := 540314640019503765523255

theorem tailTrace_1052259 : CollatzResearch.WordTrace tailWord_1052259 prefixEnd_1052259 540314640019503765523255 := by
  unfold tailWord_1052259
  simp only [CollatzResearch.WordTrace]
  refine ⟨38379038694852829374743831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25586025796568552916495887 38379038694852829374743831)
  ·
    refine ⟨57568558042279244062115747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38379038694852829374743831 57568558042279244062115747)
    ·
      refine ⟨86352837063418866093173621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57568558042279244062115747 86352837063418866093173621)
      ·
        refine ⟨8095578474695518696235027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86352837063418866093173621 8095578474695518696235027)
        ·
          refine ⟨12143367712043278044352541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8095578474695518696235027 12143367712043278044352541)
          ·
            refine ⟨4553762892016229266632203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12143367712043278044352541 4553762892016229266632203)
            ·
              refine ⟨6830644338024343899948305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4553762892016229266632203 6830644338024343899948305)
              ·
                refine ⟨5122983253518257924961229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6830644338024343899948305 5122983253518257924961229)
                ·
                  refine ⟨1921118720069346721860461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5122983253518257924961229 1921118720069346721860461)
                  ·
                    refine ⟨720419520026005020697673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1921118720069346721860461 720419520026005020697673)
                    ·
                      refine ⟨540314640019503765523255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 720419520026005020697673 540314640019503765523255)
                      ·
                        rfl

theorem cell23_1052259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_1052259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052259 prefixEnd_1052259 := by exact prefixLift 1052259
  have htrace : WordTrace (prefixWord ++ tailWord_1052259) baseStart_1052259 baseEnd_1052259 := by
    simpa [prefixWord, tailWord_1052259, baseEnd_1052259] using wordTrace_append hprefix tailTrace_1052259
  have hstable : (prefixWord ++ tailWord_1052259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052259).length < 2 ^ (prefixWord ++ tailWord_1052259).sum := by decide
  have hdescent : baseEnd_1052259 < baseStart_1052259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052265 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 1, 8]
def baseStart_1052265 : Nat := 118140960795 + 1052265 * 2 ^ 59
def prefixEnd_1052265 : Nat := 4983230072969 + 3 ^ 40 * 1052265 * 2
def baseEnd_1052265 : Nat := 180105906967810247349409

theorem tailTrace_1052265 : CollatzResearch.WordTrace tailWord_1052265 prefixEnd_1052265 180105906967810247349409 := by
  unfold tailWord_1052265
  simp only [CollatzResearch.WordTrace]
  refine ⟨38379257532831092399462249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25586171688554061599641499 38379257532831092399462249)
  ·
    refine ⟨28784443149623319299596687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38379257532831092399462249 28784443149623319299596687)
    ·
      refine ⟨43176664724434978949395031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28784443149623319299596687 43176664724434978949395031)
      ·
        refine ⟨64764997086652468424092547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43176664724434978949395031 64764997086652468424092547)
        ·
          refine ⟨97147495629978702636138821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64764997086652468424092547 97147495629978702636138821)
          ·
            refine ⟨18215155430621006744276029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97147495629978702636138821 18215155430621006744276029)
            ·
              refine ⟨6830683286482877529103511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18215155430621006744276029 6830683286482877529103511)
              ·
                refine ⟨10246024929724316293655267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6830683286482877529103511 10246024929724316293655267)
                ·
                  refine ⟨15369037394586474440482901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10246024929724316293655267 15369037394586474440482901)
                  ·
                    refine ⟨180105906967810247349409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15369037394586474440482901 180105906967810247349409)
                    ·
                      rfl

theorem cell23_1052265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 8].length) (baseStart_1052265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052265 prefixEnd_1052265 := by exact prefixLift 1052265
  have htrace : WordTrace (prefixWord ++ tailWord_1052265) baseStart_1052265 baseEnd_1052265 := by
    simpa [prefixWord, tailWord_1052265, baseEnd_1052265] using wordTrace_append hprefix tailTrace_1052265
  have hstable : (prefixWord ++ tailWord_1052265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052265).length < 2 ^ (prefixWord ++ tailWord_1052265).sum := by decide
  have hdescent : baseEnd_1052265 < baseStart_1052265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052266 : List Nat := [3, 1, 3, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_1052266 : Nat := 118140960795 + 1052266 * 2 ^ 59
def prefixEnd_1052266 : Nat := 4983230072969 + 3 ^ 40 * 1052266 * 2
def baseEnd_1052266 : Nat := 540318234384085238135723

theorem tailTrace_1052266 : CollatzResearch.WordTrace tailWord_1052266 prefixEnd_1052266 540318234384085238135723 := by
  unfold tailWord_1052266
  simp only [CollatzResearch.WordTrace]
  refine ⟨9594823501456867392562163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25586196003884979713499101 9594823501456867392562163)
  ·
    refine ⟨14392235252185301088843245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9594823501456867392562163 14392235252185301088843245)
    ·
      refine ⟨5397088219569487908316217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14392235252185301088843245 5397088219569487908316217)
      ·
        refine ⟨4047816164677115931237163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5397088219569487908316217 4047816164677115931237163)
        ·
          refine ⟨6071724247015673896855745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4047816164677115931237163 6071724247015673896855745)
          ·
            refine ⟨4553793185261755422641809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6071724247015673896855745 4553793185261755422641809)
            ·
              refine ⟨3415344888946316566981357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4553793185261755422641809 3415344888946316566981357)
              ·
                refine ⟨1280754333354868712618009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3415344888946316566981357 1280754333354868712618009)
                ·
                  refine ⟨960565750016151534463507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1280754333354868712618009 960565750016151534463507)
                  ·
                    refine ⟨1440848625024227301695261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 960565750016151534463507 1440848625024227301695261)
                    ·
                      refine ⟨540318234384085238135723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1440848625024227301695261 540318234384085238135723)
                      ·
                        rfl

theorem cell23_1052266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_1052266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052266 prefixEnd_1052266 := by exact prefixLift 1052266
  have htrace : WordTrace (prefixWord ++ tailWord_1052266) baseStart_1052266 baseEnd_1052266 := by
    simpa [prefixWord, tailWord_1052266, baseEnd_1052266] using wordTrace_append hprefix tailTrace_1052266
  have hstable : (prefixWord ++ tailWord_1052266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052266).length < 2 ^ (prefixWord ++ tailWord_1052266).sum := by decide
  have hdescent : baseEnd_1052266 < baseStart_1052266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052305 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 9]
def baseStart_1052305 : Nat := 118140960795 + 1052305 * 2 ^ 59
def prefixEnd_1052305 : Nat := 4983230072969 + 3 ^ 40 * 1052305 * 2
def baseEnd_1052305 : Nat := 540338260129610585548043

theorem tailTrace_1052305 : CollatzResearch.WordTrace tailWord_1052305 prefixEnd_1052305 540338260129610585548043 := by
  unfold tailWord_1052305
  simp only [CollatzResearch.WordTrace]
  refine ⟨38380716452686179230918369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25587144301790786153945579 38380716452686179230918369)
  ·
    refine ⟨28785537339514634423188777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38380716452686179230918369 28785537339514634423188777)
    ·
      refine ⟨21589153004635975817391583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28785537339514634423188777 21589153004635975817391583)
      ·
        refine ⟨32383729506953963726087375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21589153004635975817391583 32383729506953963726087375)
        ·
          refine ⟨48575594260430945589131063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32383729506953963726087375 48575594260430945589131063)
          ·
            refine ⟨72863391390646418383696595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48575594260430945589131063 72863391390646418383696595)
            ·
              refine ⟨109295087085969627575544893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72863391390646418383696595 109295087085969627575544893)
              ·
                refine ⟨40985657657238610340829335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109295087085969627575544893 40985657657238610340829335)
                ·
                  refine ⟨61478486485857915511244003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40985657657238610340829335 61478486485857915511244003)
                  ·
                    refine ⟨92217729728786873266866005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61478486485857915511244003 92217729728786873266866005)
                    ·
                      refine ⟨540338260129610585548043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 92217729728786873266866005 540338260129610585548043)
                      ·
                        rfl

theorem cell23_1052305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_1052305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052305 prefixEnd_1052305 := by exact prefixLift 1052305
  have htrace : WordTrace (prefixWord ++ tailWord_1052305) baseStart_1052305 baseEnd_1052305 := by
    simpa [prefixWord, tailWord_1052305, baseEnd_1052305] using wordTrace_append hprefix tailTrace_1052305
  have hstable : (prefixWord ++ tailWord_1052305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052305).length < 2 ^ (prefixWord ++ tailWord_1052305).sum := by decide
  have hdescent : baseEnd_1052305 < baseStart_1052305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052312 : List Nat := [2, 1, 2, 4, 1, 2, 1, 3, 7]
def baseStart_1052312 : Nat := 118140960795 + 1052312 * 2 ^ 59
def prefixEnd_1052312 : Nat := 4983230072969 + 3 ^ 40 * 1052312 * 2
def baseEnd_1052312 : Nat := 60037983832688006462279

theorem tailTrace_1052312 : CollatzResearch.WordTrace tailWord_1052312 prefixEnd_1052312 60037983832688006462279 := by
  unfold tailWord_1052312
  simp only [CollatzResearch.WordTrace]
  refine ⟨19190485881830409713211595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25587314509107212950948793 19190485881830409713211595)
  ·
    refine ⟨28785728822745614569817393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19190485881830409713211595 28785728822745614569817393)
    ·
      refine ⟨21589296617059210927363045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28785728822745614569817393 21589296617059210927363045)
      ·
        refine ⟨4047993115698602048880571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21589296617059210927363045 4047993115698602048880571)
        ·
          refine ⟨6071989673547903073320857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4047993115698602048880571 6071989673547903073320857)
          ·
            refine ⟨4553992255160927304990643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6071989673547903073320857 4553992255160927304990643)
            ·
              refine ⟨6830988382741390957485965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4553992255160927304990643 6830988382741390957485965)
              ·
                refine ⟨2561620643528021609057237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6830988382741390957485965 2561620643528021609057237)
                ·
                  refine ⟨60037983832688006462279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2561620643528021609057237 60037983832688006462279)
                  ·
                    rfl

theorem cell23_1052312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 7].length) (baseStart_1052312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052312 prefixEnd_1052312 := by exact prefixLift 1052312
  have htrace : WordTrace (prefixWord ++ tailWord_1052312) baseStart_1052312 baseEnd_1052312 := by
    simpa [prefixWord, tailWord_1052312, baseEnd_1052312] using wordTrace_append hprefix tailTrace_1052312
  have hstable : (prefixWord ++ tailWord_1052312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052312).length < 2 ^ (prefixWord ++ tailWord_1052312).sum := by decide
  have hdescent : baseEnd_1052312 < baseStart_1052312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052315 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 6]
def baseStart_1052315 : Nat := 118140960795 + 1052315 * 2 ^ 59
def prefixEnd_1052315 : Nat := 4983230072969 + 3 ^ 40 * 1052315 * 2
def baseEnd_1052315 : Nat := 540343394936155546422997

theorem tailTrace_1052315 : CollatzResearch.WordTrace tailWord_1052315 prefixEnd_1052315 540343394936155546422997 := by
  unfold tailWord_1052315
  simp only [CollatzResearch.WordTrace]
  refine ⟨38381081182649950938782399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25587387455099967292521599 38381081182649950938782399)
  ·
    refine ⟨57571621773974926408173599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38381081182649950938782399 57571621773974926408173599)
    ·
      refine ⟨86357432660962389612260399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57571621773974926408173599 86357432660962389612260399)
      ·
        refine ⟨129536148991443584418390599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86357432660962389612260399 129536148991443584418390599)
        ·
          refine ⟨194304223487165376627585899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129536148991443584418390599 194304223487165376627585899)
          ·
            refine ⟨291456335230748064941378849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194304223487165376627585899 291456335230748064941378849)
            ·
              refine ⟨218592251423061048706034137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291456335230748064941378849 218592251423061048706034137)
              ·
                refine ⟨163944188567295786529525603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218592251423061048706034137 163944188567295786529525603)
                ·
                  refine ⟨245916282850943679794288405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163944188567295786529525603 245916282850943679794288405)
                  ·
                    refine ⟨11527325758637984990357269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 245916282850943679794288405 11527325758637984990357269)
                    ·
                      refine ⟨540343394936155546422997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11527325758637984990357269 540343394936155546422997)
                      ·
                        rfl

theorem cell23_1052315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 6].length) (baseStart_1052315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052315 prefixEnd_1052315 := by exact prefixLift 1052315
  have htrace : WordTrace (prefixWord ++ tailWord_1052315) baseStart_1052315 baseEnd_1052315 := by
    simpa [prefixWord, tailWord_1052315, baseEnd_1052315] using wordTrace_append hprefix tailTrace_1052315
  have hstable : (prefixWord ++ tailWord_1052315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052315).length < 2 ^ (prefixWord ++ tailWord_1052315).sum := by decide
  have hdescent : baseEnd_1052315 < baseStart_1052315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052323 : List Nat := [1, 1, 1, 4, 1, 1, 7, 1, 2, 2, 2]
def baseStart_1052323 : Nat := 118140960795 + 1052323 * 2 ^ 59
def prefixEnd_1052323 : Nat := 4983230072969 + 3 ^ 40 * 1052323 * 2
def baseEnd_1052323 : Nat := 540347502781391515122961

theorem tailTrace_1052323 : CollatzResearch.WordTrace tailWord_1052323 prefixEnd_1052323 540347502781391515122961 := by
  unfold tailWord_1052323
  simp only [CollatzResearch.WordTrace]
  refine ⟨38381372966620968305073623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25587581977747312203382415 38381372966620968305073623)
  ·
    refine ⟨57572059449931452457610435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38381372966620968305073623 57572059449931452457610435)
    ·
      refine ⟨86358089174897178686415653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57572059449931452457610435 86358089174897178686415653)
      ·
        refine ⟨16192141720293221003702935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86358089174897178686415653 16192141720293221003702935)
        ·
          refine ⟨24288212580439831505554403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16192141720293221003702935 24288212580439831505554403)
          ·
            refine ⟨36432318870659747258331605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24288212580439831505554403 36432318870659747258331605)
            ·
              refine ⟨853882473531087826367147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 36432318870659747258331605 853882473531087826367147)
              ·
                refine ⟨1280823710296631739550721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853882473531087826367147 1280823710296631739550721)
                ·
                  refine ⟨960617782722473804663041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1280823710296631739550721 960617782722473804663041)
                  ·
                    refine ⟨720463337041855353497281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 960617782722473804663041 720463337041855353497281)
                    ·
                      refine ⟨540347502781391515122961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 720463337041855353497281 540347502781391515122961)
                      ·
                        rfl

theorem cell23_1052323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_1052323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052323 prefixEnd_1052323 := by exact prefixLift 1052323
  have htrace : WordTrace (prefixWord ++ tailWord_1052323) baseStart_1052323 baseEnd_1052323 := by
    simpa [prefixWord, tailWord_1052323, baseEnd_1052323] using wordTrace_append hprefix tailTrace_1052323
  have hstable : (prefixWord ++ tailWord_1052323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052323).length < 2 ^ (prefixWord ++ tailWord_1052323).sum := by decide
  have hdescent : baseEnd_1052323 < baseStart_1052323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052346 : List Nat := [3, 1, 1, 1, 2, 6, 1, 3, 5]
def baseStart_1052346 : Nat := 118140960795 + 1052346 * 2 ^ 59
def prefixEnd_1052346 : Nat := 4983230072969 + 3 ^ 40 * 1052346 * 2
def baseEnd_1052346 : Nat := 60039923648493880570595

theorem tailTrace_1052346 : CollatzResearch.WordTrace tailWord_1052346 prefixEnd_1052346 60039923648493880570595 := by
  unfold tailWord_1052346
  simp only [CollatzResearch.WordTrace]
  refine ⟨9595552961384410808290223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25588141230358428822107261 9595552961384410808290223)
  ·
    refine ⟨14393329442076616212435335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9595552961384410808290223 14393329442076616212435335)
    ·
      refine ⟨21589994163114924318653003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14393329442076616212435335 21589994163114924318653003)
      ·
        refine ⟨32384991244672386477979505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21589994163114924318653003 32384991244672386477979505)
        ·
          refine ⟨24288743433504289858484629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32384991244672386477979505 24288743433504289858484629)
          ·
            refine ⟨1138534848445513587116467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24288743433504289858484629 1138534848445513587116467)
            ·
              refine ⟨1707802272668270380674701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138534848445513587116467 1707802272668270380674701)
              ·
                refine ⟨640425852250601392753013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1707802272668270380674701 640425852250601392753013)
                ·
                  refine ⟨60039923648493880570595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 640425852250601392753013 60039923648493880570595)
                  ·
                    rfl

theorem cell23_1052346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 5].length) (baseStart_1052346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052346 prefixEnd_1052346 := by exact prefixLift 1052346
  have htrace : WordTrace (prefixWord ++ tailWord_1052346) baseStart_1052346 baseEnd_1052346 := by
    simpa [prefixWord, tailWord_1052346, baseEnd_1052346] using wordTrace_append hprefix tailTrace_1052346
  have hstable : (prefixWord ++ tailWord_1052346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052346).length < 2 ^ (prefixWord ++ tailWord_1052346).sum := by decide
  have hdescent : baseEnd_1052346 < baseStart_1052346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052352 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 5]
def baseStart_1052352 : Nat := 118140960795 + 1052352 * 2 ^ 59
def prefixEnd_1052352 : Nat := 4983230072969 + 3 ^ 40 * 1052352 * 2
def baseEnd_1052352 : Nat := 540362393720371901660327

theorem tailTrace_1052352 : CollatzResearch.WordTrace tailWord_1052352 prefixEnd_1052352 540362393720371901660327 := by
  unfold tailWord_1052352
  simp only [CollatzResearch.WordTrace]
  refine ⟨19191215341757953128939655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25588287122343937505252873 19191215341757953128939655)
  ·
    refine ⟨28786823012636929693409483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19191215341757953128939655 28786823012636929693409483)
    ·
      refine ⟨43180234518955394540114225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28786823012636929693409483 43180234518955394540114225)
      ·
        refine ⟨32385175889216545905085669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43180234518955394540114225 32385175889216545905085669)
        ·
          refine ⟨6072220479228102357203563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32385175889216545905085669 6072220479228102357203563)
          ·
            refine ⟨9108330718842153535805345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6072220479228102357203563 9108330718842153535805345)
            ·
              refine ⟨6831248039131615151854009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9108330718842153535805345 6831248039131615151854009)
              ·
                refine ⟨5123436029348711363890507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6831248039131615151854009 5123436029348711363890507)
                ·
                  refine ⟨7685154044023067045835761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5123436029348711363890507 7685154044023067045835761)
                  ·
                    refine ⟨5763865533017300284376821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7685154044023067045835761 5763865533017300284376821)
                    ·
                      refine ⟨540362393720371901660327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5763865533017300284376821 540362393720371901660327)
                      ·
                        rfl

theorem cell23_1052352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_1052352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052352 prefixEnd_1052352 := by exact prefixLift 1052352
  have htrace : WordTrace (prefixWord ++ tailWord_1052352) baseStart_1052352 baseEnd_1052352 := by
    simpa [prefixWord, tailWord_1052352, baseEnd_1052352] using wordTrace_append hprefix tailTrace_1052352
  have hstable : (prefixWord ++ tailWord_1052352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052352).length < 2 ^ (prefixWord ++ tailWord_1052352).sum := by decide
  have hdescent : baseEnd_1052352 < baseStart_1052352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052389 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 5, 4]
def baseStart_1052389 : Nat := 118140960795 + 1052389 * 2 ^ 59
def prefixEnd_1052389 : Nat := 4983230072969 + 3 ^ 40 * 1052389 * 2
def baseEnd_1052389 : Nat := 180127130834862752299219

theorem tailTrace_1052389 : CollatzResearch.WordTrace tailWord_1052389 prefixEnd_1052389 180127130834862752299219 := by
  unfold tailWord_1052389
  simp only [CollatzResearch.WordTrace]
  refine ⟨38383780184381861576976221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25589186789587907717984147 38383780184381861576976221)
  ·
    refine ⟨14393917569143198091366083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38383780184381861576976221 14393917569143198091366083)
    ·
      refine ⟨21590876353714797137049125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14393917569143198091366083 21590876353714797137049125)
      ·
        refine ⟨4048289316321524463196711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21590876353714797137049125 4048289316321524463196711)
        ·
          refine ⟨6072433974482286694795067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4048289316321524463196711 6072433974482286694795067)
          ·
            refine ⟨9108650961723430042192601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6072433974482286694795067 9108650961723430042192601)
            ·
              refine ⟨6831488221292572531644451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9108650961723430042192601 6831488221292572531644451)
              ·
                refine ⟨10247232331938858797466677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6831488221292572531644451 10247232331938858797466677)
                ·
                  refine ⟨960678031119268012262501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10247232331938858797466677 960678031119268012262501)
                  ·
                    refine ⟨180127130834862752299219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 960678031119268012262501 180127130834862752299219)
                    ·
                      rfl

theorem cell23_1052389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_1052389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052389 prefixEnd_1052389 := by exact prefixLift 1052389
  have htrace : WordTrace (prefixWord ++ tailWord_1052389) baseStart_1052389 baseEnd_1052389 := by
    simpa [prefixWord, tailWord_1052389, baseEnd_1052389] using wordTrace_append hprefix tailTrace_1052389
  have hstable : (prefixWord ++ tailWord_1052389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052389).length < 2 ^ (prefixWord ++ tailWord_1052389).sum := by decide
  have hdescent : baseEnd_1052389 < baseStart_1052389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052449 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 3, 5]
def baseStart_1052449 : Nat := 118140960795 + 1052449 * 2 ^ 59
def prefixEnd_1052449 : Nat := 4983230072969 + 3 ^ 40 * 1052449 * 2
def baseEnd_1052449 : Nat := 180137400447952674049127

theorem tailTrace_1052449 : CollatzResearch.WordTrace tailWord_1052449 prefixEnd_1052449 180137400447952674049127 := by
  unfold tailWord_1052449
  simp only [CollatzResearch.WordTrace]
  refine ⟨38385968564164491824160401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25590645709442994549440267 38385968564164491824160401)
  ·
    refine ⟨28789476423123368868120301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38385968564164491824160401 28789476423123368868120301)
    ·
      refine ⟨10796053658671263325545113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28789476423123368868120301 10796053658671263325545113)
      ·
        refine ⟨8097040244003447494158835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10796053658671263325545113 8097040244003447494158835)
        ·
          refine ⟨12145560366005171241238253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8097040244003447494158835 12145560366005171241238253)
          ·
            refine ⟨4554585137251939215464345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12145560366005171241238253 4554585137251939215464345)
            ·
              refine ⟨3415938852938954411598259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4554585137251939215464345 3415938852938954411598259)
              ·
                refine ⟨5123908279408431617397389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3415938852938954411598259 5123908279408431617397389)
                ·
                  refine ⟨1921465604778161856524021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5123908279408431617397389 1921465604778161856524021)
                  ·
                    refine ⟨180137400447952674049127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1921465604778161856524021 180137400447952674049127)
                    ·
                      rfl

theorem cell23_1052449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_1052449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052449 prefixEnd_1052449 := by exact prefixLift 1052449
  have htrace : WordTrace (prefixWord ++ tailWord_1052449) baseStart_1052449 baseEnd_1052449 := by
    simpa [prefixWord, tailWord_1052449, baseEnd_1052449] using wordTrace_append hprefix tailTrace_1052449
  have hstable : (prefixWord ++ tailWord_1052449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052449).length < 2 ^ (prefixWord ++ tailWord_1052449).sum := by decide
  have hdescent : baseEnd_1052449 < baseStart_1052449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052466 : List Nat := [3, 2, 1, 1, 3, 3, 1, 3, 1, 5]
def baseStart_1052466 : Nat := 118140960795 + 1052466 * 2 ^ 59
def prefixEnd_1052466 : Nat := 4983230072969 + 3 ^ 40 * 1052466 * 2
def baseEnd_1052466 : Nat := 180140310171661485211601

theorem tailTrace_1052466 : CollatzResearch.WordTrace tailWord_1052466 prefixEnd_1052466 180140310171661485211601 := by
  unfold tailWord_1052466
  simp only [CollatzResearch.WordTrace]
  refine ⟨9596647151275725931882313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25591059070068602485019501 9596647151275725931882313)
  ·
    refine ⟨7197485363456794448911735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9596647151275725931882313 7197485363456794448911735)
    ·
      refine ⟨10796228045185191673367603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7197485363456794448911735 10796228045185191673367603)
      ·
        refine ⟨16194342067777787510051405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10796228045185191673367603 16194342067777787510051405)
        ·
          refine ⟨6072878275416670316269277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16194342067777787510051405 6072878275416670316269277)
          ·
            refine ⟨2277329353281251368600979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6072878275416670316269277 2277329353281251368600979)
            ·
              refine ⟨3415994029921877052901469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2277329353281251368600979 3415994029921877052901469)
              ·
                refine ⟨1280997761220703894838051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3415994029921877052901469 1280997761220703894838051)
                ·
                  refine ⟨1921496641831055842257077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1280997761220703894838051 1921496641831055842257077)
                  ·
                    refine ⟨180140310171661485211601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1921496641831055842257077 180140310171661485211601)
                    ·
                      rfl

theorem cell23_1052466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_1052466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052466 prefixEnd_1052466 := by exact prefixLift 1052466
  have htrace : WordTrace (prefixWord ++ tailWord_1052466) baseStart_1052466 baseEnd_1052466 := by
    simpa [prefixWord, tailWord_1052466, baseEnd_1052466] using wordTrace_append hprefix tailTrace_1052466
  have hstable : (prefixWord ++ tailWord_1052466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052466).length < 2 ^ (prefixWord ++ tailWord_1052466).sum := by decide
  have hdescent : baseEnd_1052466 < baseStart_1052466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052489 : List Nat := [1, 2, 1, 1, 2, 4, 3, 2, 1, 1, 5]
def baseStart_1052489 : Nat := 118140960795 + 1052489 * 2 ^ 59
def prefixEnd_1052489 : Nat := 4983230072969 + 3 ^ 40 * 1052489 * 2
def baseEnd_1052489 : Nat := 540432740570037865647197

theorem tailTrace_1052489 : CollatzResearch.WordTrace tailWord_1052489 prefixEnd_1052489 540432740570037865647197 := by
  unfold tailWord_1052489
  simp only [CollatzResearch.WordTrace]
  refine ⟨38387427484019578655616521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25591618322679719103744347 38387427484019578655616521)
  ·
    refine ⟨28790570613014683991712391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38387427484019578655616521 28790570613014683991712391)
    ·
      refine ⟨43185855919522025987568587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28790570613014683991712391 43185855919522025987568587)
      ·
        refine ⟨64778783879283038981352881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43185855919522025987568587 64778783879283038981352881)
        ·
          refine ⟨48584087909462279236014661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64778783879283038981352881 48584087909462279236014661)
          ·
            refine ⟨9109516483024177356752749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48584087909462279236014661 9109516483024177356752749)
            ·
              refine ⟨3416068681134066508782281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9109516483024177356752749 3416068681134066508782281)
              ·
                refine ⟨2562051510850549881586711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3416068681134066508782281 2562051510850549881586711)
                ·
                  refine ⟨3843077266275824822380067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562051510850549881586711 3843077266275824822380067)
                  ·
                    refine ⟨5764615899413737233570101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3843077266275824822380067 5764615899413737233570101)
                    ·
                      refine ⟨540432740570037865647197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5764615899413737233570101 540432740570037865647197)
                      ·
                        rfl

theorem cell23_1052489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 1, 5].length) (baseStart_1052489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052489 prefixEnd_1052489 := by exact prefixLift 1052489
  have htrace : WordTrace (prefixWord ++ tailWord_1052489) baseStart_1052489 baseEnd_1052489 := by
    simpa [prefixWord, tailWord_1052489, baseEnd_1052489] using wordTrace_append hprefix tailTrace_1052489
  have hstable : (prefixWord ++ tailWord_1052489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052489).length < 2 ^ (prefixWord ++ tailWord_1052489).sum := by decide
  have hdescent : baseEnd_1052489 < baseStart_1052489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052503 : List Nat := [1, 1, 3, 2, 5, 1, 2, 2, 1, 1, 4]
def baseStart_1052503 : Nat := 118140960795 + 1052503 * 2 ^ 59
def prefixEnd_1052503 : Nat := 4983230072969 + 3 ^ 40 * 1052503 * 2
def baseEnd_1052503 : Nat := 540439929299200810872133

theorem tailTrace_1052503 : CollatzResearch.WordTrace tailWord_1052503 prefixEnd_1052503 540439929299200810872133 := by
  unfold tailWord_1052503
  simp only [CollatzResearch.WordTrace]
  refine ⟨38387938105968859046626163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25591958737312572697750775 38387938105968859046626163)
  ·
    refine ⟨57581907158953288569939245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38387938105968859046626163 57581907158953288569939245)
    ·
      refine ⟨21593215184607483213727217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57581907158953288569939245 21593215184607483213727217)
      ·
        refine ⟨16194911388455612410295413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21593215184607483213727217 16194911388455612410295413)
        ·
          refine ⟨1518272942667713663465195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16194911388455612410295413 1518272942667713663465195)
          ·
            refine ⟨2277409414001570495197793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1518272942667713663465195 2277409414001570495197793)
            ·
              refine ⟨1708057060501177871398345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2277409414001570495197793 1708057060501177871398345)
              ·
                refine ⟨1281042795375883403548759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1708057060501177871398345 1281042795375883403548759)
                ·
                  refine ⟨1921564193063825105323139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1281042795375883403548759 1921564193063825105323139)
                  ·
                    refine ⟨2882346289595737657984709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1921564193063825105323139 2882346289595737657984709)
                    ·
                      refine ⟨540439929299200810872133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2882346289595737657984709 540439929299200810872133)
                      ·
                        rfl

theorem cell23_1052503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_1052503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052503 prefixEnd_1052503 := by exact prefixLift 1052503
  have htrace : WordTrace (prefixWord ++ tailWord_1052503) baseStart_1052503 baseEnd_1052503 := by
    simpa [prefixWord, tailWord_1052503, baseEnd_1052503] using wordTrace_append hprefix tailTrace_1052503
  have hstable : (prefixWord ++ tailWord_1052503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052503).length < 2 ^ (prefixWord ++ tailWord_1052503).sum := by decide
  have hdescent : baseEnd_1052503 < baseStart_1052503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052526 : List Nat := [4, 1, 2, 3, 1, 3, 9]
def baseStart_1052526 : Nat := 118140960795 + 1052526 * 2 ^ 59
def prefixEnd_1052526 : Nat := 4983230072969 + 3 ^ 40 * 1052526 * 2
def baseEnd_1052526 : Nat := 6672243695731533591167

theorem tailTrace_1052526 : CollatzResearch.WordTrace tailWord_1052526 prefixEnd_1052526 6672243695731533591167 := by
  unfold tailWord_1052526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4798597123110691746839179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25592517989923689316475621 4798597123110691746839179)
  ·
    refine ⟨7197895684666037620258769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4798597123110691746839179 7197895684666037620258769)
    ·
      refine ⟨5398421763499528215194077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7197895684666037620258769 5398421763499528215194077)
      ·
        refine ⟨2024408161312323080697779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5398421763499528215194077 2024408161312323080697779)
        ·
          refine ⟨3036612241968484621046669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2024408161312323080697779 3036612241968484621046669)
          ·
            refine ⟨1138729590738181732892501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3036612241968484621046669 1138729590738181732892501)
            ·
              refine ⟨6672243695731533591167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1138729590738181732892501 6672243695731533591167)
              ·
                rfl

theorem cell23_1052526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 9].length) (baseStart_1052526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052526 prefixEnd_1052526 := by exact prefixLift 1052526
  have htrace : WordTrace (prefixWord ++ tailWord_1052526) baseStart_1052526 baseEnd_1052526 := by
    simpa [prefixWord, tailWord_1052526, baseEnd_1052526] using wordTrace_append hprefix tailTrace_1052526
  have hstable : (prefixWord ++ tailWord_1052526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052526).length < 2 ^ (prefixWord ++ tailWord_1052526).sum := by decide
  have hdescent : baseEnd_1052526 < baseStart_1052526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052537 : List Nat := [1, 2, 1, 3, 2, 2, 5, 2, 1, 2, 2]
def baseStart_1052537 : Nat := 118140960795 + 1052537 * 2 ^ 59
def prefixEnd_1052537 : Nat := 4983230072969 + 3 ^ 40 * 1052537 * 2
def baseEnd_1052537 : Nat := 540457387641453677846977

theorem tailTrace_1052537 : CollatzResearch.WordTrace tailWord_1052537 prefixEnd_1052537 540457387641453677846977 := by
  unfold tailWord_1052537
  simp only [CollatzResearch.WordTrace]
  refine ⟨38389178187845682853363865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25592785458563788568909243 38389178187845682853363865)
  ·
    refine ⟨28791883640884262140022899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38389178187845682853363865 28791883640884262140022899)
    ·
      refine ⟨43187825461326393210034349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28791883640884262140022899 43187825461326393210034349)
      ·
        refine ⟨16195434547997397453762881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43187825461326393210034349 16195434547997397453762881)
        ·
          refine ⟨12146575910998048090322161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16195434547997397453762881 12146575910998048090322161)
          ·
            refine ⟨9109931933248536067741621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12146575910998048090322161 9109931933248536067741621)
            ·
              refine ⟨854056118742050256350777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9109931933248536067741621 854056118742050256350777)
              ·
                refine ⟨640542089056537692263083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 854056118742050256350777 640542089056537692263083)
                ·
                  refine ⟨960813133584806538394625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640542089056537692263083 960813133584806538394625)
                  ·
                    refine ⟨720609850188604903795969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 960813133584806538394625 720609850188604903795969)
                    ·
                      refine ⟨540457387641453677846977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 720609850188604903795969 540457387641453677846977)
                      ·
                        rfl

theorem cell23_1052537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_1052537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052537 prefixEnd_1052537 := by exact prefixLift 1052537
  have htrace : WordTrace (prefixWord ++ tailWord_1052537) baseStart_1052537 baseEnd_1052537 := by
    simpa [prefixWord, tailWord_1052537, baseEnd_1052537] using wordTrace_append hprefix tailTrace_1052537
  have hstable : (prefixWord ++ tailWord_1052537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052537).length < 2 ^ (prefixWord ++ tailWord_1052537).sum := by decide
  have hdescent : baseEnd_1052537 < baseStart_1052537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052553 : List Nat := [1, 2, 1, 1, 5, 1, 3, 3, 2, 1, 3]
def baseStart_1052553 : Nat := 118140960795 + 1052553 * 2 ^ 59
def prefixEnd_1052553 : Nat := 4983230072969 + 3 ^ 40 * 1052553 * 2
def baseEnd_1052553 : Nat := 540465603331925615246903

theorem tailTrace_1052553 : CollatzResearch.WordTrace tailWord_1052553 prefixEnd_1052553 540465603331925615246903 := by
  unfold tailWord_1052553
  simp only [CollatzResearch.WordTrace]
  refine ⟨38389761755787717585946313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25593174503858478390630875 38389761755787717585946313)
  ·
    refine ⟨28792321316840788189459735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38389761755787717585946313 28792321316840788189459735)
    ·
      refine ⟨43188481975261182284189603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28792321316840788189459735 43188481975261182284189603)
      ·
        refine ⟨64782722962891773426284405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43188481975261182284189603 64782722962891773426284405)
        ·
          refine ⟨6073380277771103758714163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64782722962891773426284405 6073380277771103758714163)
          ·
            refine ⟨9110070416656655638071245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6073380277771103758714163 9110070416656655638071245)
            ·
              refine ⟨3416276406246245864276717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9110070416656655638071245 3416276406246245864276717)
              ·
                refine ⟨1281103652342342199103769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3416276406246245864276717 1281103652342342199103769)
                ·
                  refine ⟨960827739256756649327827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1281103652342342199103769 960827739256756649327827)
                  ·
                    refine ⟨1441241608885134973991741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 960827739256756649327827 1441241608885134973991741)
                    ·
                      refine ⟨540465603331925615246903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1441241608885134973991741 540465603331925615246903)
                      ·
                        rfl

theorem cell23_1052553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 1, 3].length) (baseStart_1052553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052553 prefixEnd_1052553 := by exact prefixLift 1052553
  have htrace : WordTrace (prefixWord ++ tailWord_1052553) baseStart_1052553 baseEnd_1052553 := by
    simpa [prefixWord, tailWord_1052553, baseEnd_1052553] using wordTrace_append hprefix tailTrace_1052553
  have hstable : (prefixWord ++ tailWord_1052553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052553).length < 2 ^ (prefixWord ++ tailWord_1052553).sum := by decide
  have hdescent : baseEnd_1052553 < baseStart_1052553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052574 : List Nat := [4, 3, 1, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_1052574 : Nat := 118140960795 + 1052574 * 2 ^ 59
def prefixEnd_1052574 : Nat := 4983230072969 + 3 ^ 40 * 1052574 * 2
def baseEnd_1052574 : Nat := 540476386425670033084307

theorem tailTrace_1052574 : CollatzResearch.WordTrace tailWord_1052574 prefixEnd_1052574 540476386425670033084307 := by
  unfold tailWord_1052574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4798815961088954771557597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25593685125807758781640517 4798815961088954771557597)
  ·
    refine ⟨1799555985408358039334099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4798815961088954771557597 1799555985408358039334099)
    ·
      refine ⟨2699333978112537059001149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1799555985408358039334099 2699333978112537059001149)
      ·
        refine ⟨1012250241792201397125431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2699333978112537059001149 1012250241792201397125431)
        ·
          refine ⟨1518375362688302095688147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1012250241792201397125431 1518375362688302095688147)
          ·
            refine ⟨2277563044032453143532221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1518375362688302095688147 2277563044032453143532221)
            ·
              refine ⟨854086141512169928824583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2277563044032453143532221 854086141512169928824583)
              ·
                refine ⟨1281129212268254893236875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854086141512169928824583 1281129212268254893236875)
                ·
                  refine ⟨1921693818402382339855313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1281129212268254893236875 1921693818402382339855313)
                  ·
                    refine ⟨1441270363801786754891485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1921693818402382339855313 1441270363801786754891485)
                    ·
                      refine ⟨540476386425670033084307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1441270363801786754891485 540476386425670033084307)
                      ·
                        rfl

theorem cell23_1052574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_1052574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052574 prefixEnd_1052574 := by exact prefixLift 1052574
  have htrace : WordTrace (prefixWord ++ tailWord_1052574) baseStart_1052574 baseEnd_1052574 := by
    simpa [prefixWord, tailWord_1052574, baseEnd_1052574] using wordTrace_append hprefix tailTrace_1052574
  have hstable : (prefixWord ++ tailWord_1052574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052574).length < 2 ^ (prefixWord ++ tailWord_1052574).sum := by decide
  have hdescent : baseEnd_1052574 < baseStart_1052574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052599 : List Nat := [1, 1, 3, 1, 3, 1, 1, 5, 7]
def baseStart_1052599 : Nat := 118140960795 + 1052599 * 2 ^ 59
def prefixEnd_1052599 : Nat := 4983230072969 + 3 ^ 40 * 1052599 * 2
def baseEnd_1052599 : Nat := 60054358160225826141299

theorem tailTrace_1052599 : CollatzResearch.WordTrace tailWord_1052599 prefixEnd_1052599 60054358160225826141299 := by
  unfold tailWord_1052599
  simp only [CollatzResearch.WordTrace]
  refine ⟨38391439513621067442120851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25594293009080711628080567 38391439513621067442120851)
  ·
    refine ⟨57587159270431601163181277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38391439513621067442120851 57587159270431601163181277)
    ·
      refine ⟨21595184726411850436192979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57587159270431601163181277 21595184726411850436192979)
      ·
        refine ⟨32392777089617775654289469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21595184726411850436192979 32392777089617775654289469)
        ·
          refine ⟨12147291408606665870358551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32392777089617775654289469 12147291408606665870358551)
          ·
            refine ⟨18220937112909998805537827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12147291408606665870358551 18220937112909998805537827)
            ·
              refine ⟨27331405669364998208306741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18220937112909998805537827 27331405669364998208306741)
              ·
                refine ⟨2562319281502968582028757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27331405669364998208306741 2562319281502968582028757)
                ·
                  refine ⟨60054358160225826141299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2562319281502968582028757 60054358160225826141299)
                  ·
                    rfl

theorem cell23_1052599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 7].length) (baseStart_1052599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052599 prefixEnd_1052599 := by exact prefixLift 1052599
  have htrace : WordTrace (prefixWord ++ tailWord_1052599) baseStart_1052599 baseEnd_1052599 := by
    simpa [prefixWord, tailWord_1052599, baseEnd_1052599] using wordTrace_append hprefix tailTrace_1052599
  have hstable : (prefixWord ++ tailWord_1052599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052599).length < 2 ^ (prefixWord ++ tailWord_1052599).sum := by decide
  have hdescent : baseEnd_1052599 < baseStart_1052599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052606 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_1052606 : Nat := 118140960795 + 1052606 * 2 ^ 59
def prefixEnd_1052606 : Nat := 4983230072969 + 3 ^ 40 * 1052606 * 2
def baseEnd_1052606 : Nat := 540492817806613907884159

theorem tailTrace_1052606 : CollatzResearch.WordTrace tailWord_1052606 prefixEnd_1052606 540492817806613907884159 := by
  unfold tailWord_1052606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4798961853074463454703209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25594463216397138425083781 4798961853074463454703209)
  ·
    refine ⟨3599221389805847591027407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4798961853074463454703209 3599221389805847591027407)
    ·
      refine ⟨5398832084708771386541111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3599221389805847591027407 5398832084708771386541111)
      ·
        refine ⟨8098248127063157079811667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5398832084708771386541111 8098248127063157079811667)
        ·
          refine ⟨12147372190594735619717501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8098248127063157079811667 12147372190594735619717501)
          ·
            refine ⟨4555264571473025857394063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12147372190594735619717501 4555264571473025857394063)
            ·
              refine ⟨6832896857209538786091095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4555264571473025857394063 6832896857209538786091095)
              ·
                refine ⟨10249345285814308179136643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6832896857209538786091095 10249345285814308179136643)
                ·
                  refine ⟨15374017928721462268704965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10249345285814308179136643 15374017928721462268704965)
                  ·
                    refine ⟨2882628361635274175382181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15374017928721462268704965 2882628361635274175382181)
                    ·
                      refine ⟨540492817806613907884159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2882628361635274175382181 540492817806613907884159)
                      ·
                        rfl

theorem cell23_1052606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_1052606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052606 prefixEnd_1052606 := by exact prefixLift 1052606
  have htrace : WordTrace (prefixWord ++ tailWord_1052606) baseStart_1052606 baseEnd_1052606 := by
    simpa [prefixWord, tailWord_1052606, baseEnd_1052606] using wordTrace_append hprefix tailTrace_1052606
  have hstable : (prefixWord ++ tailWord_1052606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052606).length < 2 ^ (prefixWord ++ tailWord_1052606).sum := by decide
  have hdescent : baseEnd_1052606 < baseStart_1052606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052616 : List Nat := [2, 1, 3, 1, 4, 2, 1, 2, 7]
def baseStart_1052616 : Nat := 118140960795 + 1052616 * 2 ^ 59
def prefixEnd_1052616 : Nat := 4983230072969 + 3 ^ 40 * 1052616 * 2
def baseEnd_1052616 : Nat := 60055328068128763195457

theorem tailTrace_1052616 : CollatzResearch.WordTrace tailWord_1052616 prefixEnd_1052616 60055328068128763195457 := by
  unfold tailWord_1052616
  simp only [CollatzResearch.WordTrace]
  refine ⟨19196029777279739672744851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25594706369706319563659801 19196029777279739672744851)
  ·
    refine ⟨28794044665919609509117277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19196029777279739672744851 28794044665919609509117277)
    ·
      refine ⟨10797766749719853565918979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28794044665919609509117277 10797766749719853565918979)
      ·
        refine ⟨16196650124579780348878469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10797766749719853565918979 16196650124579780348878469)
        ·
          refine ⟨3036871898358708815414713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16196650124579780348878469 3036871898358708815414713)
          ·
            refine ⟨2277653923769031611561035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3036871898358708815414713 2277653923769031611561035)
            ·
              refine ⟨3416480885653547417341553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2277653923769031611561035 3416480885653547417341553)
              ·
                refine ⟨2562360664240160563006165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3416480885653547417341553 2562360664240160563006165)
                ·
                  refine ⟨60055328068128763195457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2562360664240160563006165 60055328068128763195457)
                  ·
                    rfl

theorem cell23_1052616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 7].length) (baseStart_1052616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052616 prefixEnd_1052616 := by exact prefixLift 1052616
  have htrace : WordTrace (prefixWord ++ tailWord_1052616) baseStart_1052616 baseEnd_1052616 := by
    simpa [prefixWord, tailWord_1052616, baseEnd_1052616] using wordTrace_append hprefix tailTrace_1052616
  have hstable : (prefixWord ++ tailWord_1052616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052616).length < 2 ^ (prefixWord ++ tailWord_1052616).sum := by decide
  have hdescent : baseEnd_1052616 < baseStart_1052616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052703 : List Nat := [1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 3]
def baseStart_1052703 : Nat := 118140960795 + 1052703 * 2 ^ 59
def prefixEnd_1052703 : Nat := 4983230072969 + 3 ^ 40 * 1052703 * 2
def baseEnd_1052703 : Nat := 540542625430100028371213

theorem tailTrace_1052703 : CollatzResearch.WordTrace tailWord_1052703 prefixEnd_1052703 540542625430100028371213 := by
  unfold tailWord_1052703
  simp only [CollatzResearch.WordTrace]
  refine ⟨38395232705244293203906763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25596821803496195469271175 38395232705244293203906763)
  ·
    refine ⟨57592849057866439805860145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38395232705244293203906763 57592849057866439805860145)
    ·
      refine ⟨43194636793399829854395109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57592849057866439805860145 43194636793399829854395109)
      ·
        refine ⟨8098994398762468097699083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43194636793399829854395109 8098994398762468097699083)
        ·
          refine ⟨12148491598143702146548625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8098994398762468097699083 12148491598143702146548625)
          ·
            refine ⟨9111368698607776609911469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12148491598143702146548625 9111368698607776609911469)
            ·
              refine ⟨3416763261977916228716801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9111368698607776609911469 3416763261977916228716801)
              ·
                refine ⟨2562572446483437171537601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3416763261977916228716801 2562572446483437171537601)
                ·
                  refine ⟨1921929334862577878653201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2562572446483437171537601 1921929334862577878653201)
                  ·
                    refine ⟨1441447001146933408989901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1921929334862577878653201 1441447001146933408989901)
                    ·
                      refine ⟨540542625430100028371213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1441447001146933408989901 540542625430100028371213)
                      ·
                        rfl

theorem cell23_1052703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_1052703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052703 prefixEnd_1052703 := by exact prefixLift 1052703
  have htrace : WordTrace (prefixWord ++ tailWord_1052703) baseStart_1052703 baseEnd_1052703 := by
    simpa [prefixWord, tailWord_1052703, baseEnd_1052703] using wordTrace_append hprefix tailTrace_1052703
  have hstable : (prefixWord ++ tailWord_1052703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052703).length < 2 ^ (prefixWord ++ tailWord_1052703).sum := by decide
  have hdescent : baseEnd_1052703 < baseStart_1052703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052706 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 8]
def baseStart_1052706 : Nat := 118140960795 + 1052706 * 2 ^ 59
def prefixEnd_1052706 : Nat := 4983230072969 + 3 ^ 40 * 1052706 * 2
def baseEnd_1052706 : Nat := 60060462874673724070411

theorem tailTrace_1052706 : CollatzResearch.WordTrace tailWord_1052706 prefixEnd_1052706 60060462874673724070411 := by
  unfold tailWord_1052706
  simp only [CollatzResearch.WordTrace]
  refine ⟨9598835531058356179066493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25596894749488949810843981 9598835531058356179066493)
  ·
    refine ⟨3599563324146883567149935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9598835531058356179066493 3599563324146883567149935)
    ·
      refine ⟨5399344986220325350724903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3599563324146883567149935 5399344986220325350724903)
      ·
        refine ⟨8099017479330488026087355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5399344986220325350724903 8099017479330488026087355)
        ·
          refine ⟨12148526218995732039131033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8099017479330488026087355 12148526218995732039131033)
          ·
            refine ⟨9111394664246799029348275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12148526218995732039131033 9111394664246799029348275)
            ·
              refine ⟨13667091996370198544022413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9111394664246799029348275 13667091996370198544022413)
              ·
                refine ⟨5125159498638824454008405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13667091996370198544022413 5125159498638824454008405)
                ·
                  refine ⟨60060462874673724070411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5125159498638824454008405 60060462874673724070411)
                  ·
                    rfl

theorem cell23_1052706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_1052706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052706 prefixEnd_1052706 := by exact prefixLift 1052706
  have htrace : WordTrace (prefixWord ++ tailWord_1052706) baseStart_1052706 baseEnd_1052706 := by
    simpa [prefixWord, tailWord_1052706, baseEnd_1052706] using wordTrace_append hprefix tailTrace_1052706
  have hstable : (prefixWord ++ tailWord_1052706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052706).length < 2 ^ (prefixWord ++ tailWord_1052706).sum := by decide
  have hdescent : baseEnd_1052706 < baseStart_1052706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052716 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 3]
def baseStart_1052716 : Nat := 118140960795 + 1052716 * 2 ^ 59
def prefixEnd_1052716 : Nat := 4983230072969 + 3 ^ 40 * 1052716 * 2
def baseEnd_1052716 : Nat := 540549300678608477508653

theorem tailTrace_1052716 : CollatzResearch.WordTrace tailWord_1052716 prefixEnd_1052716 540549300678608477508653 := by
  unfold tailWord_1052716
  simp only [CollatzResearch.WordTrace]
  refine ⟨19197853427098598212065001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25597137902798130949420001 19197853427098598212065001)
  ·
    refine ⟨14398390070323948659048751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19197853427098598212065001 14398390070323948659048751)
    ·
      refine ⟨21597585105485922988573127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14398390070323948659048751 21597585105485922988573127)
      ·
        refine ⟨32396377658228884482859691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21597585105485922988573127 32396377658228884482859691)
        ·
          refine ⟨48594566487343326724289537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32396377658228884482859691 48594566487343326724289537)
          ·
            refine ⟨36445924865507495043217153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48594566487343326724289537 36445924865507495043217153)
            ·
              refine ⟨27334443649130621282412865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36445924865507495043217153 27334443649130621282412865)
              ·
                refine ⟨20500832736847965961809649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27334443649130621282412865 20500832736847965961809649)
                ·
                  refine ⟨15375624552635974471357237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20500832736847965961809649 15375624552635974471357237)
                  ·
                    refine ⟨1441464801809622606689741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15375624552635974471357237 1441464801809622606689741)
                    ·
                      refine ⟨540549300678608477508653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1441464801809622606689741 540549300678608477508653)
                      ·
                        rfl

theorem cell23_1052716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_1052716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052716 prefixEnd_1052716 := by exact prefixLift 1052716
  have htrace : WordTrace (prefixWord ++ tailWord_1052716) baseStart_1052716 baseEnd_1052716 := by
    simpa [prefixWord, tailWord_1052716, baseEnd_1052716] using wordTrace_append hprefix tailTrace_1052716
  have hstable : (prefixWord ++ tailWord_1052716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052716).length < 2 ^ (prefixWord ++ tailWord_1052716).sum := by decide
  have hdescent : baseEnd_1052716 < baseStart_1052716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052723 : List Nat := [1, 1, 1, 2, 4, 1, 6, 1, 6]
def baseStart_1052723 : Nat := 118140960795 + 1052723 * 2 ^ 59
def prefixEnd_1052723 : Nat := 4983230072969 + 3 ^ 40 * 1052723 * 2
def baseEnd_1052723 : Nat := 60061432782576661124569

theorem tailTrace_1052723 : CollatzResearch.WordTrace tailWord_1052723 prefixEnd_1052723 60061432782576661124569 := by
  unfold tailWord_1052723
  simp only [CollatzResearch.WordTrace]
  refine ⟨38395962165171836619634823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25597308110114557746423215 38395962165171836619634823)
  ·
    refine ⟨57593943247757754929452235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38395962165171836619634823 57593943247757754929452235)
    ·
      refine ⟨86390914871636632394178353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57593943247757754929452235 86390914871636632394178353)
      ·
        refine ⟨64793186153727474295633765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86390914871636632394178353 64793186153727474295633765)
        ·
          refine ⟨12148722403823901430431331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64793186153727474295633765 12148722403823901430431331)
          ·
            refine ⟨18223083605735852145646997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12148722403823901430431331 18223083605735852145646997)
            ·
              refine ⟨854207044018868069327203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18223083605735852145646997 854207044018868069327203)
              ·
                refine ⟨1281310566028302103990805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854207044018868069327203 1281310566028302103990805)
                ·
                  refine ⟨60061432782576661124569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1281310566028302103990805 60061432782576661124569)
                  ·
                    rfl

theorem cell23_1052723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 6].length) (baseStart_1052723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052723 prefixEnd_1052723 := by exact prefixLift 1052723
  have htrace : WordTrace (prefixWord ++ tailWord_1052723) baseStart_1052723 baseEnd_1052723 := by
    simpa [prefixWord, tailWord_1052723, baseEnd_1052723] using wordTrace_append hprefix tailTrace_1052723
  have hstable : (prefixWord ++ tailWord_1052723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052723).length < 2 ^ (prefixWord ++ tailWord_1052723).sum := by decide
  have hdescent : baseEnd_1052723 < baseStart_1052723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052760 : List Nat := [2, 1, 2, 2, 1, 4, 2, 2, 2, 3, 2]
def baseStart_1052760 : Nat := 118140960795 + 1052760 * 2 ^ 59
def prefixEnd_1052760 : Nat := 4983230072969 + 3 ^ 40 * 1052760 * 2
def baseEnd_1052760 : Nat := 540571893827406305358451

theorem tailTrace_1052760 : CollatzResearch.WordTrace tailWord_1052760 prefixEnd_1052760 540571893827406305358451 := by
  unfold tailWord_1052760
  simp only [CollatzResearch.WordTrace]
  refine ⟨19198655833018895969365867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25598207777358527959154489 19198655833018895969365867)
  ·
    refine ⟨28797983749528343954048801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19198655833018895969365867 28797983749528343954048801)
    ·
      refine ⟨21598487812146257965536601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28797983749528343954048801 21598487812146257965536601)
      ·
        refine ⟨16198865859109693474152451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21598487812146257965536601 16198865859109693474152451)
        ·
          refine ⟨24298298788664540211228677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16198865859109693474152451 24298298788664540211228677)
          ·
            refine ⟨4555931022874601289605377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24298298788664540211228677 4555931022874601289605377)
            ·
              refine ⟨3416948267155950967204033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4555931022874601289605377 3416948267155950967204033)
              ·
                refine ⟨2562711200366963225403025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3416948267155950967204033 2562711200366963225403025)
                ·
                  refine ⟨1922033400275222419052269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2562711200366963225403025 1922033400275222419052269)
                  ·
                    refine ⟨720762525103208407144601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1922033400275222419052269 720762525103208407144601)
                    ·
                      refine ⟨540571893827406305358451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 720762525103208407144601 540571893827406305358451)
                      ·
                        rfl

theorem cell23_1052760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_1052760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052760 prefixEnd_1052760 := by exact prefixLift 1052760
  have htrace : WordTrace (prefixWord ++ tailWord_1052760) baseStart_1052760 baseEnd_1052760 := by
    simpa [prefixWord, tailWord_1052760, baseEnd_1052760] using wordTrace_append hprefix tailTrace_1052760
  have hstable : (prefixWord ++ tailWord_1052760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052760).length < 2 ^ (prefixWord ++ tailWord_1052760).sum := by decide
  have hdescent : baseEnd_1052760 < baseStart_1052760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052773 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 3, 1, 4]
def baseStart_1052773 : Nat := 118140960795 + 1052773 * 2 ^ 59
def prefixEnd_1052773 : Nat := 4983230072969 + 3 ^ 40 * 1052773 * 2
def baseEnd_1052773 : Nat := 540578569075914754495891

theorem tailTrace_1052773 : CollatzResearch.WordTrace tailWord_1052773 prefixEnd_1052773 540578569075914754495891 := by
  unfold tailWord_1052773
  simp only [CollatzResearch.WordTrace]
  refine ⟨38397785814990695158954973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25598523876660463439303315 38397785814990695158954973)
  ·
    refine ⟨14399169680621510684608115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38397785814990695158954973 14399169680621510684608115)
    ·
      refine ⟨21598754520932266026912173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14399169680621510684608115 21598754520932266026912173)
      ·
        refine ⟨8099532945349599760092065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21598754520932266026912173 8099532945349599760092065)
        ·
          refine ⟨6074649709012199820069049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8099532945349599760092065 6074649709012199820069049)
          ·
            refine ⟨4555987281759149865051787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6074649709012199820069049 4555987281759149865051787)
            ·
              refine ⟨6833980922638724797577681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4555987281759149865051787 6833980922638724797577681)
              ·
                refine ⟨5125485691979043598183261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6833980922638724797577681 5125485691979043598183261)
                ·
                  refine ⟨1922057134492141349318723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5125485691979043598183261 1922057134492141349318723)
                  ·
                    refine ⟨2883085701738212023978085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1922057134492141349318723 2883085701738212023978085)
                    ·
                      refine ⟨540578569075914754495891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2883085701738212023978085 540578569075914754495891)
                      ·
                        rfl

theorem cell23_1052773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_1052773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052773 prefixEnd_1052773 := by exact prefixLift 1052773
  have htrace : WordTrace (prefixWord ++ tailWord_1052773) baseStart_1052773 baseEnd_1052773 := by
    simpa [prefixWord, tailWord_1052773, baseEnd_1052773] using wordTrace_append hprefix tailTrace_1052773
  have hstable : (prefixWord ++ tailWord_1052773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052773).length < 2 ^ (prefixWord ++ tailWord_1052773).sum := by decide
  have hdescent : baseEnd_1052773 < baseStart_1052773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052783 : List Nat := [1, 1, 2, 1, 3, 5, 2, 1, 1, 6]
def baseStart_1052783 : Nat := 118140960795 + 1052783 * 2 ^ 59
def prefixEnd_1052783 : Nat := 4983230072969 + 3 ^ 40 * 1052783 * 2
def baseEnd_1052783 : Nat := 180194567960819905123615

theorem tailTrace_1052783 : CollatzResearch.WordTrace tailWord_1052783 prefixEnd_1052783 180194567960819905123615 := by
  unfold tailWord_1052783
  simp only [CollatzResearch.WordTrace]
  refine ⟨38398150544954466866819003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25598767029969644577879335 38398150544954466866819003)
  ·
    refine ⟨57597225817431700300228505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38398150544954466866819003 57597225817431700300228505)
    ·
      refine ⟨43197919363073775225171379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57597225817431700300228505 43197919363073775225171379)
      ·
        refine ⟨64796879044610662837757069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43197919363073775225171379 64796879044610662837757069)
        ·
          refine ⟨24298829641728998564158901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64796879044610662837757069 24298829641728998564158901)
          ·
            refine ⟨2278015278912093615389897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24298829641728998564158901 2278015278912093615389897)
            ·
              refine ⟨1708511459184070211542423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2278015278912093615389897 1708511459184070211542423)
              ·
                refine ⟨2562767188776105317313635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1708511459184070211542423 2562767188776105317313635)
                ·
                  refine ⟨3844150783164157975970453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562767188776105317313635 3844150783164157975970453)
                  ·
                    refine ⟨180194567960819905123615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3844150783164157975970453 180194567960819905123615)
                    ·
                      rfl

theorem cell23_1052783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 6].length) (baseStart_1052783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052783 prefixEnd_1052783 := by exact prefixLift 1052783
  have htrace : WordTrace (prefixWord ++ tailWord_1052783) baseStart_1052783 baseEnd_1052783 := by
    simpa [prefixWord, tailWord_1052783, baseEnd_1052783] using wordTrace_append hprefix tailTrace_1052783
  have hstable : (prefixWord ++ tailWord_1052783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052783).length < 2 ^ (prefixWord ++ tailWord_1052783).sum := by decide
  have hdescent : baseEnd_1052783 < baseStart_1052783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052790 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_1052790 : Nat := 118140960795 + 1052790 * 2 ^ 59
def prefixEnd_1052790 : Nat := 4983230072969 + 3 ^ 40 * 1052790 * 2
def baseEnd_1052790 : Nat := 540587298247041187983313

theorem tailTrace_1052790 : CollatzResearch.WordTrace tailWord_1052790 prefixEnd_1052790 540587298247041187983313 := by
  unfold tailWord_1052790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2399900365995569191395239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25598937237286071374882549 2399900365995569191395239)
  ·
    refine ⟨3599850548993353787092859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2399900365995569191395239 3599850548993353787092859)
    ·
      refine ⟨5399775823490030680639289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3599850548993353787092859 5399775823490030680639289)
      ·
        refine ⟨4049831867617523010479467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5399775823490030680639289 4049831867617523010479467)
        ·
          refine ⟨6074747801426284515719201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4049831867617523010479467 6074747801426284515719201)
          ·
            refine ⟨4556060851069713386789401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6074747801426284515719201 4556060851069713386789401)
            ·
              refine ⟨3417045638302285040092051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4556060851069713386789401 3417045638302285040092051)
              ·
                refine ⟨5125568457453427560138077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3417045638302285040092051 5125568457453427560138077)
                ·
                  refine ⟨1922088171545035335051779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5125568457453427560138077 1922088171545035335051779)
                  ·
                    refine ⟨2883132257317553002577669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1922088171545035335051779 2883132257317553002577669)
                    ·
                      refine ⟨540587298247041187983313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2883132257317553002577669 540587298247041187983313)
                      ·
                        rfl

theorem cell23_1052790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_1052790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052790 prefixEnd_1052790 := by exact prefixLift 1052790
  have htrace : WordTrace (prefixWord ++ tailWord_1052790) baseStart_1052790 baseEnd_1052790 := by
    simpa [prefixWord, tailWord_1052790, baseEnd_1052790] using wordTrace_append hprefix tailTrace_1052790
  have hstable : (prefixWord ++ tailWord_1052790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052790).length < 2 ^ (prefixWord ++ tailWord_1052790).sum := by decide
  have hdescent : baseEnd_1052790 < baseStart_1052790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052803 : List Nat := [1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 4]
def baseStart_1052803 : Nat := 118140960795 + 1052803 * 2 ^ 59
def prefixEnd_1052803 : Nat := 4983230072969 + 3 ^ 40 * 1052803 * 2
def baseEnd_1052803 : Nat := 540593973495549637120753

theorem tailTrace_1052803 : CollatzResearch.WordTrace tailWord_1052803 prefixEnd_1052803 540593973495549637120753 := by
  unfold tailWord_1052803
  simp only [CollatzResearch.WordTrace]
  refine ⟨38398880004882010282547063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25599253336588006855031375 38398880004882010282547063)
  ·
    refine ⟨57598320007323015423820595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38398880004882010282547063 57598320007323015423820595)
    ·
      refine ⟨86397480010984523135730893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57598320007323015423820595 86397480010984523135730893)
      ·
        refine ⟨32399055004119196175899085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86397480010984523135730893 32399055004119196175899085)
        ·
          refine ⟨12149645626544698565962157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32399055004119196175899085 12149645626544698565962157)
          ·
            refine ⟨4556117109954261962235809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12149645626544698565962157 4556117109954261962235809)
            ·
              refine ⟨3417087832465696471676857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4556117109954261962235809 3417087832465696471676857)
              ·
                refine ⟨2562815874349272353757643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3417087832465696471676857 2562815874349272353757643)
                ·
                  refine ⟨3844223811523908530636465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562815874349272353757643 3844223811523908530636465)
                  ·
                    refine ⟨2883167858642931397977349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3844223811523908530636465 2883167858642931397977349)
                    ·
                      refine ⟨540593973495549637120753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2883167858642931397977349 540593973495549637120753)
                      ·
                        rfl

theorem cell23_1052803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_1052803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052803 prefixEnd_1052803 := by exact prefixLift 1052803
  have htrace : WordTrace (prefixWord ++ tailWord_1052803) baseStart_1052803 baseEnd_1052803 := by
    simpa [prefixWord, tailWord_1052803, baseEnd_1052803] using wordTrace_append hprefix tailTrace_1052803
  have hstable : (prefixWord ++ tailWord_1052803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052803).length < 2 ^ (prefixWord ++ tailWord_1052803).sum := by decide
  have hdescent : baseEnd_1052803 < baseStart_1052803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052824 : List Nat := [2, 1, 2, 4, 3, 1, 2, 1, 3, 2, 2]
def baseStart_1052824 : Nat := 118140960795 + 1052824 * 2 ^ 59
def prefixEnd_1052824 : Nat := 4983230072969 + 3 ^ 40 * 1052824 * 2
def baseEnd_1052824 : Nat := 540604756589294054958157

theorem tailTrace_1052824 : CollatzResearch.WordTrace tailWord_1052824 prefixEnd_1052824 540604756589294054958157 := by
  unfold tailWord_1052824
  simp only [CollatzResearch.WordTrace]
  refine ⟨19199822968902965434530763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25599763958537287246041017 19199822968902965434530763)
  ·
    refine ⟨28799734453354448151796145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19199822968902965434530763 28799734453354448151796145)
    ·
      refine ⟨21599800840015836113847109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28799734453354448151796145 21599800840015836113847109)
      ·
        refine ⟨4049962657502969271346333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21599800840015836113847109 4049962657502969271346333)
        ·
          refine ⟨1518735996563613476754875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4049962657502969271346333 1518735996563613476754875)
          ·
            refine ⟨2278103994845420215132313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1518735996563613476754875 2278103994845420215132313)
            ·
              refine ⟨1708577996134065161349235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2278103994845420215132313 1708577996134065161349235)
              ·
                refine ⟨2562866994201097742023853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1708577996134065161349235 2562866994201097742023853)
                ·
                  refine ⟨961075122825411653258945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2562866994201097742023853 961075122825411653258945)
                  ·
                    refine ⟨720806342119058739944209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 961075122825411653258945 720806342119058739944209)
                    ·
                      refine ⟨540604756589294054958157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 720806342119058739944209 540604756589294054958157)
                      ·
                        rfl

theorem cell23_1052824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_1052824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052824 prefixEnd_1052824 := by exact prefixLift 1052824
  have htrace : WordTrace (prefixWord ++ tailWord_1052824) baseStart_1052824 baseEnd_1052824 := by
    simpa [prefixWord, tailWord_1052824, baseEnd_1052824] using wordTrace_append hprefix tailTrace_1052824
  have hstable : (prefixWord ++ tailWord_1052824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052824).length < 2 ^ (prefixWord ++ tailWord_1052824).sum := by decide
  have hdescent : baseEnd_1052824 < baseStart_1052824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052834 : List Nat := [3, 3, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_1052834 : Nat := 118140960795 + 1052834 * 2 ^ 59
def prefixEnd_1052834 : Nat := 4983230072969 + 3 ^ 40 * 1052834 * 2
def baseEnd_1052834 : Nat := 180203297131946338611037

theorem tailTrace_1052834 : CollatzResearch.WordTrace tailWord_1052834 prefixEnd_1052834 180203297131946338611037 := by
  unfold tailWord_1052834
  simp only [CollatzResearch.WordTrace]
  refine ⟨9600002666942425644231389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25600007111846468384617037 9600002666942425644231389)
  ·
    refine ⟨3600001000103409616586771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9600002666942425644231389 3600001000103409616586771)
    ·
      refine ⟨5400001500155114424880157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3600001000103409616586771 5400001500155114424880157)
      ·
        refine ⟨2025000562558167909330059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5400001500155114424880157 2025000562558167909330059)
        ·
          refine ⟨3037500843837251863995089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2025000562558167909330059 3037500843837251863995089)
          ·
            refine ⟨2278125632877938897996317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3037500843837251863995089 2278125632877938897996317)
            ·
              refine ⟨854297112329227086748619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2278125632877938897996317 854297112329227086748619)
              ·
                refine ⟨1281445668493840630122929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854297112329227086748619 1281445668493840630122929)
                ·
                  refine ⟨961084251370380472592197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1281445668493840630122929 961084251370380472592197)
                  ·
                    refine ⟨180203297131946338611037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 961084251370380472592197 180203297131946338611037)
                    ·
                      rfl

theorem cell23_1052834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_1052834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052834 prefixEnd_1052834 := by exact prefixLift 1052834
  have htrace : WordTrace (prefixWord ++ tailWord_1052834) baseStart_1052834 baseEnd_1052834 := by
    simpa [prefixWord, tailWord_1052834, baseEnd_1052834] using wordTrace_append hprefix tailTrace_1052834
  have hstable : (prefixWord ++ tailWord_1052834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052834).length < 2 ^ (prefixWord ++ tailWord_1052834).sum := by decide
  have hdescent : baseEnd_1052834 < baseStart_1052834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052852 : List Nat := [2, 5, 3, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_1052852 : Nat := 118140960795 + 1052852 * 2 ^ 59
def prefixEnd_1052852 : Nat := 4983230072969 + 3 ^ 40 * 1052852 * 2
def baseEnd_1052852 : Nat := 540619134047619945408029

theorem tailTrace_1052852 : CollatzResearch.WordTrace tailWord_1052852 prefixEnd_1052852 540619134047619945408029 := by
  unfold tailWord_1052852
  simp only [CollatzResearch.WordTrace]
  refine ⟨19200333590852245825540405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25600444787802994434053873 19200333590852245825540405)
  ·
    refine ⟨1800031274142398046144413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19200333590852245825540405 1800031274142398046144413)
    ·
      refine ⟨675011727803399267304155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1800031274142398046144413 675011727803399267304155)
      ·
        refine ⟨1012517591705098900956233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675011727803399267304155 1012517591705098900956233)
        ·
          refine ⟨759388193778824175717175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1012517591705098900956233 759388193778824175717175)
          ·
            refine ⟨1139082290668236263575763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759388193778824175717175 1139082290668236263575763)
            ·
              refine ⟨1708623436002354395363645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139082290668236263575763 1708623436002354395363645)
              ·
                refine ⟨640733788500882898261367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1708623436002354395363645 640733788500882898261367)
                ·
                  refine ⟨961100682751324347392051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640733788500882898261367 961100682751324347392051)
                  ·
                    refine ⟨1441651024126986521088077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 961100682751324347392051 1441651024126986521088077)
                    ·
                      refine ⟨540619134047619945408029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1441651024126986521088077 540619134047619945408029)
                      ·
                        rfl

theorem cell23_1052852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_1052852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052852 prefixEnd_1052852 := by exact prefixLift 1052852
  have htrace : WordTrace (prefixWord ++ tailWord_1052852) baseStart_1052852 baseEnd_1052852 := by
    simpa [prefixWord, tailWord_1052852, baseEnd_1052852] using wordTrace_append hprefix tailTrace_1052852
  have hstable : (prefixWord ++ tailWord_1052852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052852).length < 2 ^ (prefixWord ++ tailWord_1052852).sum := by decide
  have hdescent : baseEnd_1052852 < baseStart_1052852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052933 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 4, 5]
def baseStart_1052933 : Nat := 118140960795 + 1052933 * 2 ^ 59
def prefixEnd_1052933 : Nat := 4983230072969 + 3 ^ 40 * 1052933 * 2
def baseEnd_1052933 : Nat := 180220241993544709498385

theorem tailTrace_1052933 : CollatzResearch.WordTrace tailWord_1052933 prefixEnd_1052933 180220241993544709498385 := by
  unfold tailWord_1052933
  simp only [CollatzResearch.WordTrace]
  refine ⟨38403621494411042484779453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25602414329607361656519635 38403621494411042484779453)
  ·
    refine ⟨14401358060404140931792295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38403621494411042484779453 14401358060404140931792295)
    ·
      refine ⟨21602037090606211397688443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14401358060404140931792295 21602037090606211397688443)
      ·
        refine ⟨32403055635909317096532665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21602037090606211397688443 32403055635909317096532665)
        ·
          refine ⟨24302291726931987822399499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32403055635909317096532665 24302291726931987822399499)
          ·
            refine ⟨36453437590397981733599249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24302291726931987822399499 36453437590397981733599249)
            ·
              refine ⟨27340078192798486300199437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36453437590397981733599249 27340078192798486300199437)
              ·
                refine ⟨10252529322299432362574789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27340078192798486300199437 10252529322299432362574789)
                ·
                  refine ⟨1922349247931143567982773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10252529322299432362574789 1922349247931143567982773)
                  ·
                    refine ⟨180220241993544709498385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1922349247931143567982773 180220241993544709498385)
                    ·
                      rfl

theorem cell23_1052933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_1052933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052933 prefixEnd_1052933 := by exact prefixLift 1052933
  have htrace : WordTrace (prefixWord ++ tailWord_1052933) baseStart_1052933 baseEnd_1052933 := by
    simpa [prefixWord, tailWord_1052933, baseEnd_1052933] using wordTrace_append hprefix tailTrace_1052933
  have hstable : (prefixWord ++ tailWord_1052933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052933).length < 2 ^ (prefixWord ++ tailWord_1052933).sum := by decide
  have hdescent : baseEnd_1052933 < baseStart_1052933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052937 : List Nat := [1, 2, 1, 1, 3, 4, 4, 2, 5]
def baseStart_1052937 : Nat := 118140960795 + 1052937 * 2 ^ 59
def prefixEnd_1052937 : Nat := 4983230072969 + 3 ^ 40 * 1052937 * 2
def baseEnd_1052937 : Nat := 60073642211472456982793

theorem tailTrace_1052937 : CollatzResearch.WordTrace tailWord_1052937 prefixEnd_1052937 60073642211472456982793 := by
  unfold tailWord_1052937
  simp only [CollatzResearch.WordTrace]
  refine ⟨38403767386396551167925065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25602511590931034111950043 38403767386396551167925065)
  ·
    refine ⟨28802825539797413375943799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38403767386396551167925065 28802825539797413375943799)
    ·
      refine ⟨43204238309696120063915699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28802825539797413375943799 43204238309696120063915699)
      ·
        refine ⟨64806357464544180095873549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43204238309696120063915699 64806357464544180095873549)
        ·
          refine ⟨24302384049204067535952581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64806357464544180095873549 24302384049204067535952581)
          ·
            refine ⟨4556697009225762662991109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24302384049204067535952581 4556697009225762662991109)
            ·
              refine ⟨854380689229830499310833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4556697009225762662991109 854380689229830499310833)
              ·
                refine ⟨640785516922372874483125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 854380689229830499310833 640785516922372874483125)
                ·
                  refine ⟨60073642211472456982793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 640785516922372874483125 60073642211472456982793)
                  ·
                    rfl

theorem cell23_1052937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 5].length) (baseStart_1052937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052937 prefixEnd_1052937 := by exact prefixLift 1052937
  have htrace : WordTrace (prefixWord ++ tailWord_1052937) baseStart_1052937 baseEnd_1052937 := by
    simpa [prefixWord, tailWord_1052937, baseEnd_1052937] using wordTrace_append hprefix tailTrace_1052937
  have hstable : (prefixWord ++ tailWord_1052937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052937).length < 2 ^ (prefixWord ++ tailWord_1052937).sum := by decide
  have hdescent : baseEnd_1052937 < baseStart_1052937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052940 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 1, 7, 2]
def baseStart_1052940 : Nat := 118140960795 + 1052940 * 2 ^ 59
def prefixEnd_1052940 : Nat := 4983230072969 + 3 ^ 40 * 1052940 * 2
def baseEnd_1052940 : Nat := 540664320345215601107623

theorem tailTrace_1052940 : CollatzResearch.WordTrace tailWord_1052940 prefixEnd_1052940 540664320345215601107623 := by
  unfold tailWord_1052940
  simp only [CollatzResearch.WordTrace]
  refine ⟨19201938402692841340142137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25602584536923788453522849 19201938402692841340142137)
  ·
    refine ⟨14401453802019631005106603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19201938402692841340142137 14401453802019631005106603)
    ·
      refine ⟨21602180703029446507659905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14401453802019631005106603 21602180703029446507659905)
      ·
        refine ⟨16201635527272084880744929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21602180703029446507659905 16201635527272084880744929)
        ·
          refine ⟨12151226645454063660558697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16201635527272084880744929 12151226645454063660558697)
          ·
            refine ⟨9113419984090547745419023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12151226645454063660558697 9113419984090547745419023)
            ·
              refine ⟨13670129976135821618128535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9113419984090547745419023 13670129976135821618128535)
              ·
                refine ⟨20505194964203732427192803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13670129976135821618128535 20505194964203732427192803)
                ·
                  refine ⟨30757792446305598640789205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20505194964203732427192803 30757792446305598640789205)
                  ·
                    refine ⟨720885760460287468143497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30757792446305598640789205 720885760460287468143497)
                    ·
                      refine ⟨540664320345215601107623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 720885760460287468143497 540664320345215601107623)
                      ·
                        rfl

theorem cell23_1052940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_1052940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052940 prefixEnd_1052940 := by exact prefixLift 1052940
  have htrace : WordTrace (prefixWord ++ tailWord_1052940) baseStart_1052940 baseEnd_1052940 := by
    simpa [prefixWord, tailWord_1052940, baseEnd_1052940] using wordTrace_append hprefix tailTrace_1052940
  have hstable : (prefixWord ++ tailWord_1052940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052940).length < 2 ^ (prefixWord ++ tailWord_1052940).sum := by decide
  have hdescent : baseEnd_1052940 < baseStart_1052940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052983 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 4]
def baseStart_1052983 : Nat := 118140960795 + 1052983 * 2 ^ 59
def prefixEnd_1052983 : Nat := 4983230072969 + 3 ^ 40 * 1052983 * 2
def baseEnd_1052983 : Nat := 540686400013358932869925

theorem tailTrace_1052983 : CollatzResearch.WordTrace tailWord_1052983 prefixEnd_1052983 540686400013358932869925 := by
  unfold tailWord_1052983
  simp only [CollatzResearch.WordTrace]
  refine ⟨38405445144229901024099603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25603630096153267349399735 38405445144229901024099603)
  ·
    refine ⟨57608167716344851536149405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38405445144229901024099603 57608167716344851536149405)
    ·
      refine ⟨21603062893629319326056027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57608167716344851536149405 21603062893629319326056027)
      ·
        refine ⟨32404594340443978989084041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21603062893629319326056027 32404594340443978989084041)
        ·
          refine ⟨24303445755332984241813031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32404594340443978989084041 24303445755332984241813031)
          ·
            refine ⟨36455168632999476362719547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24303445755332984241813031 36455168632999476362719547)
            ·
              refine ⟨54682752949499214544079321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36455168632999476362719547 54682752949499214544079321)
              ·
                refine ⟨41012064712124410908059491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54682752949499214544079321 41012064712124410908059491)
                ·
                  refine ⟨61518097068186616362089237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41012064712124410908059491 61518097068186616362089237)
                  ·
                    refine ⟨2883660800071247641972933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61518097068186616362089237 2883660800071247641972933)
                    ·
                      refine ⟨540686400013358932869925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2883660800071247641972933 540686400013358932869925)
                      ·
                        rfl

theorem cell23_1052983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_1052983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1052983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1052983 prefixEnd_1052983 := by exact prefixLift 1052983
  have htrace : WordTrace (prefixWord ++ tailWord_1052983) baseStart_1052983 baseEnd_1052983 := by
    simpa [prefixWord, tailWord_1052983, baseEnd_1052983] using wordTrace_append hprefix tailTrace_1052983
  have hstable : (prefixWord ++ tailWord_1052983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052983).length < 2 ^ (prefixWord ++ tailWord_1052983).sum := by decide
  have hdescent : baseEnd_1052983 < baseStart_1052983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053010 : List Nat := [3, 2, 2, 1, 1, 1, 2, 5, 6]
def baseStart_1053010 : Nat := 118140960795 + 1053010 * 2 ^ 59
def prefixEnd_1053010 : Nat := 4983230072969 + 3 ^ 40 * 1053010 * 2
def baseEnd_1053010 : Nat := 60077807110114480803589

theorem tailTrace_1053010 : CollatzResearch.WordTrace tailWord_1053010 prefixEnd_1053010 60077807110114480803589 := by
  unfold tailWord_1053010
  simp only [CollatzResearch.WordTrace]
  refine ⟨9601607478783021158833121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25604286610088056423554989 9601607478783021158833121)
  ·
    refine ⟨7201205609087265869124841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9601607478783021158833121 7201205609087265869124841)
    ·
      refine ⟨5400904206815449401843631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7201205609087265869124841 5400904206815449401843631)
      ·
        refine ⟨8101356310223174102765447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5400904206815449401843631 8101356310223174102765447)
        ·
          refine ⟨12152034465334761154148171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8101356310223174102765447 12152034465334761154148171)
          ·
            refine ⟨18228051698002141731222257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12152034465334761154148171 18228051698002141731222257)
            ·
              refine ⟨13671038773501606298416693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18228051698002141731222257 13671038773501606298416693)
              ·
                refine ⟨1281659885015775590476565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13671038773501606298416693 1281659885015775590476565)
                ·
                  refine ⟨60077807110114480803589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1281659885015775590476565 60077807110114480803589)
                  ·
                    rfl

theorem cell23_1053010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_1053010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053010 prefixEnd_1053010 := by exact prefixLift 1053010
  have htrace : WordTrace (prefixWord ++ tailWord_1053010) baseStart_1053010 baseEnd_1053010 := by
    simpa [prefixWord, tailWord_1053010, baseEnd_1053010] using wordTrace_append hprefix tailTrace_1053010
  have hstable : (prefixWord ++ tailWord_1053010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053010).length < 2 ^ (prefixWord ++ tailWord_1053010).sum := by decide
  have hdescent : baseEnd_1053010 < baseStart_1053010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053022 : List Nat := [4, 4, 2, 1, 2, 1, 1, 3, 5]
def baseStart_1053022 : Nat := 118140960795 + 1053022 * 2 ^ 59
def prefixEnd_1053022 : Nat := 4983230072969 + 3 ^ 40 * 1053022 * 2
def baseEnd_1053022 : Nat := 60078491750987142253583

theorem tailTrace_1053022 : CollatzResearch.WordTrace tailWord_1053022 prefixEnd_1053022 60078491750987142253583 := by
  unfold tailWord_1053022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4800858448886076335596165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25604578394059073789846213 4800858448886076335596165)
  ·
    refine ⟨900160959166139312924281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4800858448886076335596165 900160959166139312924281)
    ·
      refine ⟨675120719374604484693211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 900160959166139312924281 675120719374604484693211)
      ·
        refine ⟨1012681079061906727039817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675120719374604484693211 1012681079061906727039817)
        ·
          refine ⟨759510809296430045279863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1012681079061906727039817 759510809296430045279863)
          ·
            refine ⟨1139266213944645067919795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759510809296430045279863 1139266213944645067919795)
            ·
              refine ⟨1708899320916967601879693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139266213944645067919795 1708899320916967601879693)
              ·
                refine ⟨640837245343862850704885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1708899320916967601879693 640837245343862850704885)
                ·
                  refine ⟨60078491750987142253583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 640837245343862850704885 60078491750987142253583)
                  ·
                    rfl

theorem cell23_1053022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_1053022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053022 prefixEnd_1053022 := by exact prefixLift 1053022
  have htrace : WordTrace (prefixWord ++ tailWord_1053022) baseStart_1053022 baseEnd_1053022 := by
    simpa [prefixWord, tailWord_1053022, baseEnd_1053022] using wordTrace_append hprefix tailTrace_1053022
  have hstable : (prefixWord ++ tailWord_1053022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053022).length < 2 ^ (prefixWord ++ tailWord_1053022).sum := by decide
  have hdescent : baseEnd_1053022 < baseStart_1053022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053031 : List Nat := [1, 1, 5, 1, 3, 3, 1, 3, 1, 4]
def baseStart_1053031 : Nat := 118140960795 + 1053031 * 2 ^ 59
def prefixEnd_1053031 : Nat := 4983230072969 + 3 ^ 40 * 1053031 * 2
def baseEnd_1053031 : Nat := 180237015694924915023235

theorem tailTrace_1053031 : CollatzResearch.WordTrace tailWord_1053031 prefixEnd_1053031 180237015694924915023235 := by
  unfold tailWord_1053031
  simp only [CollatzResearch.WordTrace]
  refine ⟨38407195848056005221846947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25604797232037336814564631 38407195848056005221846947)
  ·
    refine ⟨57610793772084007832770421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38407195848056005221846947 57610793772084007832770421)
    ·
      refine ⟨5401011916132875734322227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57610793772084007832770421 5401011916132875734322227)
      ·
        refine ⟨8101517874199313601483341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5401011916132875734322227 8101517874199313601483341)
        ·
          refine ⟨3038069202824742600556253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8101517874199313601483341 3038069202824742600556253)
          ·
            refine ⟨1139275951059278475208595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3038069202824742600556253 1139275951059278475208595)
            ·
              refine ⟨1708913926588917712812893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139275951059278475208595 1708913926588917712812893)
              ·
                refine ⟨640842722470844142304835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1708913926588917712812893 640842722470844142304835)
                ·
                  refine ⟨961264083706266213457253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640842722470844142304835 961264083706266213457253)
                  ·
                    refine ⟨180237015694924915023235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 961264083706266213457253 180237015694924915023235)
                    ·
                      rfl

theorem cell23_1053031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_1053031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053031 prefixEnd_1053031 := by exact prefixLift 1053031
  have htrace : WordTrace (prefixWord ++ tailWord_1053031) baseStart_1053031 baseEnd_1053031 := by
    simpa [prefixWord, tailWord_1053031, baseEnd_1053031] using wordTrace_append hprefix tailTrace_1053031
  have hstable : (prefixWord ++ tailWord_1053031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053031).length < 2 ^ (prefixWord ++ tailWord_1053031).sum := by decide
  have hdescent : baseEnd_1053031 < baseStart_1053031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053097 : List Nat := [1, 2, 1, 1, 1, 1, 3, 7, 1, 2, 3]
def baseStart_1053097 : Nat := 118140960795 + 1053097 * 2 ^ 59
def prefixEnd_1053097 : Nat := 4983230072969 + 3 ^ 40 * 1053097 * 2
def baseEnd_1053097 : Nat := 540744936807971486844401

theorem tailTrace_1053097 : CollatzResearch.WordTrace tailWord_1053097 prefixEnd_1053097 540744936807971486844401 := by
  unfold tailWord_1053097
  simp only [CollatzResearch.WordTrace]
  refine ⟨38409603065816898493749545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25606402043877932329166363 38409603065816898493749545)
  ·
    refine ⟨28807202299362673870312159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38409603065816898493749545 28807202299362673870312159)
    ·
      refine ⟨43210803449044010805468239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28807202299362673870312159 43210803449044010805468239)
      ·
        refine ⟨64816205173566016208202359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43210803449044010805468239 64816205173566016208202359)
        ·
          refine ⟨97224307760349024312303539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64816205173566016208202359 97224307760349024312303539)
          ·
            refine ⟨145836461640523536468455309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97224307760349024312303539 145836461640523536468455309)
            ·
              refine ⟨54688673115196326175670741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145836461640523536468455309 54688673115196326175670741)
              ·
                refine ⟨1281765776137413894742283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 54688673115196326175670741 1281765776137413894742283)
                ·
                  refine ⟨1922648664206120842113425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1281765776137413894742283 1922648664206120842113425)
                  ·
                    refine ⟨1441986498154590631585069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1922648664206120842113425 1441986498154590631585069)
                    ·
                      refine ⟨540744936807971486844401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1441986498154590631585069 540744936807971486844401)
                      ·
                        rfl

theorem cell23_1053097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 2, 3].length) (baseStart_1053097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053097 prefixEnd_1053097 := by exact prefixLift 1053097
  have htrace : WordTrace (prefixWord ++ tailWord_1053097) baseStart_1053097 baseEnd_1053097 := by
    simpa [prefixWord, tailWord_1053097, baseEnd_1053097] using wordTrace_append hprefix tailTrace_1053097
  have hstable : (prefixWord ++ tailWord_1053097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053097).length < 2 ^ (prefixWord ++ tailWord_1053097).sum := by decide
  have hdescent : baseEnd_1053097 < baseStart_1053097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053117 : List Nat := [1, 4, 1, 2, 2, 4, 1, 8]
def baseStart_1053117 : Nat := 118140960795 + 1053117 * 2 ^ 59
def prefixEnd_1053117 : Nat := 4983230072969 + 3 ^ 40 * 1053117 * 2
def baseEnd_1053117 : Nat := 20027970608187459577567

theorem tailTrace_1053117 : CollatzResearch.WordTrace tailWord_1053117 prefixEnd_1053117 20027970608187459577567 := by
  unfold tailWord_1053117
  simp only [CollatzResearch.WordTrace]
  refine ⟨38410332525744441909477605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25606888350496294606318403 38410332525744441909477605)
  ·
    refine ⟨7201937348577082858027051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38410332525744441909477605 7201937348577082858027051)
    ·
      refine ⟨10802906022865624287040577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7201937348577082858027051 10802906022865624287040577)
      ·
        refine ⟨8102179517149218215280433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10802906022865624287040577 8102179517149218215280433)
        ·
          refine ⟨6076634637861913661460325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8102179517149218215280433 6076634637861913661460325)
          ·
            refine ⟨1139368994599108811523811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6076634637861913661460325 1139368994599108811523811)
            ·
              refine ⟨1709053491898663217285717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139368994599108811523811 1709053491898663217285717)
              ·
                refine ⟨20027970608187459577567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1709053491898663217285717 20027970608187459577567)
                ·
                  rfl

theorem cell23_1053117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 8].length) (baseStart_1053117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053117 prefixEnd_1053117 := by exact prefixLift 1053117
  have htrace : WordTrace (prefixWord ++ tailWord_1053117) baseStart_1053117 baseEnd_1053117 := by
    simpa [prefixWord, tailWord_1053117, baseEnd_1053117] using wordTrace_append hprefix tailTrace_1053117
  have hstable : (prefixWord ++ tailWord_1053117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053117).length < 2 ^ (prefixWord ++ tailWord_1053117).sum := by decide
  have hdescent : baseEnd_1053117 < baseStart_1053117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053127 : List Nat := [1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 3]
def baseStart_1053127 : Nat := 118140960795 + 1053127 * 2 ^ 59
def prefixEnd_1053127 : Nat := 4983230072969 + 3 ^ 40 * 1053127 * 2
def baseEnd_1053127 : Nat := 540760341227606369469263

theorem tailTrace_1053127 : CollatzResearch.WordTrace tailWord_1053127 prefixEnd_1053127 540760341227606369469263 := by
  unfold tailWord_1053127
  simp only [CollatzResearch.WordTrace]
  refine ⟨38410697255708213617341635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25607131503805475744894423 38410697255708213617341635)
  ·
    refine ⟨57616045883562320426012453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38410697255708213617341635 57616045883562320426012453)
    ·
      refine ⟨10803008603167935079877335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57616045883562320426012453 10803008603167935079877335)
      ·
        refine ⟨16204512904751902619816003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10803008603167935079877335 16204512904751902619816003)
        ·
          refine ⟨24306769357127853929724005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16204512904751902619816003 24306769357127853929724005)
          ·
            refine ⟨4557519254461472611823251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24306769357127853929724005 4557519254461472611823251)
            ·
              refine ⟨6836278881692208917734877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4557519254461472611823251 6836278881692208917734877)
              ·
                refine ⟨2563604580634578344150579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6836278881692208917734877 2563604580634578344150579)
                ·
                  refine ⟨3845406870951867516225869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2563604580634578344150579 3845406870951867516225869)
                  ·
                    refine ⟨1442027576606950318584701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3845406870951867516225869 1442027576606950318584701)
                    ·
                      refine ⟨540760341227606369469263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1442027576606950318584701 540760341227606369469263)
                      ·
                        rfl

theorem cell23_1053127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_1053127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053127 prefixEnd_1053127 := by exact prefixLift 1053127
  have htrace : WordTrace (prefixWord ++ tailWord_1053127) baseStart_1053127 baseEnd_1053127 := by
    simpa [prefixWord, tailWord_1053127, baseEnd_1053127] using wordTrace_append hprefix tailTrace_1053127
  have hstable : (prefixWord ++ tailWord_1053127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053127).length < 2 ^ (prefixWord ++ tailWord_1053127).sum := by decide
  have hdescent : baseEnd_1053127 < baseStart_1053127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053130 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 2, 7]
def baseStart_1053130 : Nat := 118140960795 + 1053130 * 2 ^ 59
def prefixEnd_1053130 : Nat := 4983230072969 + 3 ^ 40 * 1053130 * 2
def baseEnd_1053130 : Nat := 180253960556523285910583

theorem tailTrace_1053130 : CollatzResearch.WordTrace tailWord_1053130 prefixEnd_1053130 180253960556523285910583 := by
  unfold tailWord_1053130
  simp only [CollatzResearch.WordTrace]
  refine ⟨9602701668674336282425211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25607204449798230086467229 9602701668674336282425211)
  ·
    refine ⟨14404052503011504423637817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9602701668674336282425211 14404052503011504423637817)
    ·
      refine ⟨10803039377258628317728363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14404052503011504423637817 10803039377258628317728363)
      ·
        refine ⟨16204559065887942476592545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10803039377258628317728363 16204559065887942476592545)
        ·
          refine ⟨12153419299415956857444409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16204559065887942476592545 12153419299415956857444409)
          ·
            refine ⟨9115064474561967643083307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12153419299415956857444409 9115064474561967643083307)
            ·
              refine ⟨13672596711842951464624961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9115064474561967643083307 13672596711842951464624961)
              ·
                refine ⟨10254447533882213598468721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13672596711842951464624961 10254447533882213598468721)
                ·
                  refine ⟨7690835650411660198851541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10254447533882213598468721 7690835650411660198851541)
                  ·
                    refine ⟨180253960556523285910583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7690835650411660198851541 180253960556523285910583)
                    ·
                      rfl

theorem cell23_1053130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_1053130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053130 prefixEnd_1053130 := by exact prefixLift 1053130
  have htrace : WordTrace (prefixWord ++ tailWord_1053130) baseStart_1053130 baseEnd_1053130 := by
    simpa [prefixWord, tailWord_1053130, baseEnd_1053130] using wordTrace_append hprefix tailTrace_1053130
  have hstable : (prefixWord ++ tailWord_1053130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053130).length < 2 ^ (prefixWord ++ tailWord_1053130).sum := by decide
  have hdescent : baseEnd_1053130 < baseStart_1053130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053188 : List Nat := [2, 3, 2, 3, 1, 2, 2, 2, 1, 3, 2]
def baseStart_1053188 : Nat := 118140960795 + 1053188 * 2 ^ 59
def prefixEnd_1053188 : Nat := 4983230072969 + 3 ^ 40 * 1053188 * 2
def baseEnd_1053188 : Nat := 540791663547530630806483

theorem tailTrace_1053188 : CollatzResearch.WordTrace tailWord_1053188 prefixEnd_1053188 540791663547530630806483 := by
  unfold tailWord_1053188
  simp only [CollatzResearch.WordTrace]
  refine ⟨19206461054243610517656109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25608614738991480690208145 19206461054243610517656109)
  ·
    refine ⟨7202422895341353944121041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19206461054243610517656109 7202422895341353944121041)
    ·
      refine ⟨5401817171506015458090781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7202422895341353944121041 5401817171506015458090781)
      ·
        refine ⟨2025681439314755796784043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5401817171506015458090781 2025681439314755796784043)
        ·
          refine ⟨3038522158972133695176065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2025681439314755796784043 3038522158972133695176065)
          ·
            refine ⟨2278891619229100271382049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3038522158972133695176065 2278891619229100271382049)
            ·
              refine ⟨1709168714421825203536537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2278891619229100271382049 1709168714421825203536537)
              ·
                refine ⟨1281876535816368902652403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1709168714421825203536537 1281876535816368902652403)
                ·
                  refine ⟨1922814803724553353978605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1281876535816368902652403 1922814803724553353978605)
                  ·
                    refine ⟨721055551396707507741977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1922814803724553353978605 721055551396707507741977)
                    ·
                      refine ⟨540791663547530630806483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 721055551396707507741977 540791663547530630806483)
                      ·
                        rfl

theorem cell23_1053188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_1053188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053188 prefixEnd_1053188 := by exact prefixLift 1053188
  have htrace : WordTrace (prefixWord ++ tailWord_1053188) baseStart_1053188 baseEnd_1053188 := by
    simpa [prefixWord, tailWord_1053188, baseEnd_1053188] using wordTrace_append hprefix tailTrace_1053188
  have hstable : (prefixWord ++ tailWord_1053188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053188).length < 2 ^ (prefixWord ++ tailWord_1053188).sum := by decide
  have hdescent : baseEnd_1053188 < baseStart_1053188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053204 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1053204 : Nat := 118140960795 + 1053204 * 2 ^ 59
def prefixEnd_1053204 : Nat := 4983230072969 + 3 ^ 40 * 1053204 * 2
def baseEnd_1053204 : Nat := 540799879238002568206409

theorem tailTrace_1053204 : CollatzResearch.WordTrace tailWord_1053204 prefixEnd_1053204 540799879238002568206409 := by
  unfold tailWord_1053204
  simp only [CollatzResearch.WordTrace]
  refine ⟨19206752838214627883947333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25609003784286170511929777 19206752838214627883947333)
  ·
    refine ⟨3601266157165242728240125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19206752838214627883947333 3601266157165242728240125)
    ·
      refine ⟨1350474808936966023090047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3601266157165242728240125 1350474808936966023090047)
      ·
        refine ⟨2025712213405449034635071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1350474808936966023090047 2025712213405449034635071)
        ·
          refine ⟨3038568320108173551952607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2025712213405449034635071 3038568320108173551952607)
          ·
            refine ⟨4557852480162260327928911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3038568320108173551952607 4557852480162260327928911)
            ·
              refine ⟨6836778720243390491893367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4557852480162260327928911 6836778720243390491893367)
              ·
                refine ⟨10255168080365085737840051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6836778720243390491893367 10255168080365085737840051)
                ·
                  refine ⟨15382752120547628606760077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10255168080365085737840051 15382752120547628606760077)
                  ·
                    refine ⟨5768532045205360727535029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15382752120547628606760077 5768532045205360727535029)
                    ·
                      refine ⟨540799879238002568206409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5768532045205360727535029 540799879238002568206409)
                      ·
                        rfl

theorem cell23_1053204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1053204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053204 prefixEnd_1053204 := by exact prefixLift 1053204
  have htrace : WordTrace (prefixWord ++ tailWord_1053204) baseStart_1053204 baseEnd_1053204 := by
    simpa [prefixWord, tailWord_1053204, baseEnd_1053204] using wordTrace_append hprefix tailTrace_1053204
  have hstable : (prefixWord ++ tailWord_1053204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053204).length < 2 ^ (prefixWord ++ tailWord_1053204).sum := by decide
  have hdescent : baseEnd_1053204 < baseStart_1053204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053224 : List Nat := [2, 1, 5, 2, 1, 1, 3, 1, 7]
def baseStart_1053224 : Nat := 118140960795 + 1053224 * 2 ^ 59
def prefixEnd_1053224 : Nat := 4983230072969 + 3 ^ 40 * 1053224 * 2
def baseEnd_1053224 : Nat := 60090016539010276661813

theorem tailTrace_1053224 : CollatzResearch.WordTrace tailWord_1053224 prefixEnd_1053224 60090016539010276661813 := by
  unfold tailWord_1053224
  simp only [CollatzResearch.WordTrace]
  refine ⟨19207117568178399591811363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25609490090904532789081817 19207117568178399591811363)
  ·
    refine ⟨28810676352267599387717045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19207117568178399591811363 28810676352267599387717045)
    ·
      refine ⟨2701000908025087442598473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28810676352267599387717045 2701000908025087442598473)
      ·
        refine ⟨2025750681018815581948855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2701000908025087442598473 2025750681018815581948855)
        ·
          refine ⟨3038626021528223372923283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2025750681018815581948855 3038626021528223372923283)
          ·
            refine ⟨4557939032292335059384925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3038626021528223372923283 4557939032292335059384925)
            ·
              refine ⟨1709227137109625647269347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4557939032292335059384925 1709227137109625647269347)
              ·
                refine ⟨2563840705664438470904021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1709227137109625647269347 2563840705664438470904021)
                ·
                  refine ⟨60090016539010276661813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2563840705664438470904021 60090016539010276661813)
                  ·
                    rfl

theorem cell23_1053224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 7].length) (baseStart_1053224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1053224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1053224 prefixEnd_1053224 := by exact prefixLift 1053224
  have htrace : WordTrace (prefixWord ++ tailWord_1053224) baseStart_1053224 baseEnd_1053224 := by
    simpa [prefixWord, tailWord_1053224, baseEnd_1053224] using wordTrace_append hprefix tailTrace_1053224
  have hstable : (prefixWord ++ tailWord_1053224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053224).length < 2 ^ (prefixWord ++ tailWord_1053224).sum := by decide
  have hdescent : baseEnd_1053224 < baseStart_1053224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
