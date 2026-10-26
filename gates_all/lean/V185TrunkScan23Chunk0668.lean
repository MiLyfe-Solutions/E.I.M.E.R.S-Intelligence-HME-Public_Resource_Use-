import V185TrunkScan23Chunk0667

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3949655 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 5, 5]
def baseStart_3949655 : Nat := 118140960795 + 3949655 * 2 ^ 59
def prefixEnd_3949655 : Nat := 4983230072969 + 3 ^ 40 * 3949655 * 2
def baseEnd_3949655 : Nat := 676023811477949896782791

theorem tailTrace_3949655 : CollatzResearch.WordTrace tailWord_3949655 prefixEnd_3949655 676023811477949896782791 := by
  unfold tailWord_3949655
  simp only [CollatzResearch.WordTrace]
  refine ⟨144055752506081957215650419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96037168337387971477100279 144055752506081957215650419)
  ·
    refine ⟨216083628759122935823475629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144055752506081957215650419 216083628759122935823475629)
    ·
      refine ⟨81031360784671100933803361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216083628759122935823475629 81031360784671100933803361)
      ·
        refine ⟨60773520588503325700352521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81031360784671100933803361 60773520588503325700352521)
        ·
          refine ⟨45580140441377494275264391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60773520588503325700352521 45580140441377494275264391)
          ·
            refine ⟨68370210662066241412896587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45580140441377494275264391 68370210662066241412896587)
            ·
              refine ⟨102555315993099362119344881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68370210662066241412896587 102555315993099362119344881)
              ·
                refine ⟨76916486994824521589508661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102555315993099362119344881 76916486994824521589508661)
                ·
                  refine ⟨7210920655764798899016437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76916486994824521589508661 7210920655764798899016437)
                  ·
                    refine ⟨676023811477949896782791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7210920655764798899016437 676023811477949896782791)
                    ·
                      rfl

theorem cell23_3949655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_3949655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949655 prefixEnd_3949655 := by exact prefixLift 3949655
  have htrace : WordTrace (prefixWord ++ tailWord_3949655) baseStart_3949655 baseEnd_3949655 := by
    simpa [prefixWord, tailWord_3949655, baseEnd_3949655] using wordTrace_append hprefix tailTrace_3949655
  have hstable : (prefixWord ++ tailWord_3949655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949655).length < 2 ^ (prefixWord ++ tailWord_3949655).sum := by decide
  have hdescent : baseEnd_3949655 < baseStart_3949655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949692 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_3949692 : Nat := 118140960795 + 3949692 * 2 ^ 59
def prefixEnd_3949692 : Nat := 4983230072969 + 3 ^ 40 * 3949692 * 2
def baseEnd_3949692 : Nat := 2028090433218066045585703

theorem tailTrace_3949692 : CollatzResearch.WordTrace tailWord_3949692 prefixEnd_3949692 2028090433218066045585703 := by
  unfold tailWord_3949692
  simp only [CollatzResearch.WordTrace]
  refine ⟨72028551003473956267373665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96038068004631941689831553 72028551003473956267373665)
  ·
    refine ⟨54021413252605467200530249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72028551003473956267373665 54021413252605467200530249)
    ·
      refine ⟨40516059939454100400397687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54021413252605467200530249 40516059939454100400397687)
      ·
        refine ⟨60774089909181150600596531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40516059939454100400397687 60774089909181150600596531)
        ·
          refine ⟨91161134863771725900894797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60774089909181150600596531 91161134863771725900894797)
          ·
            refine ⟨34185425573914397212835549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91161134863771725900894797 34185425573914397212835549)
            ·
              refine ⟨12819534590217898954813331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34185425573914397212835549 12819534590217898954813331)
              ·
                refine ⟨19229301885326848432219997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12819534590217898954813331 19229301885326848432219997)
                ·
                  refine ⟨7210988206997568162082499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19229301885326848432219997 7210988206997568162082499)
                  ·
                    refine ⟨10816482310496352243123749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7210988206997568162082499 10816482310496352243123749)
                    ·
                      refine ⟨2028090433218066045585703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10816482310496352243123749 2028090433218066045585703)
                      ·
                        rfl

theorem cell23_3949692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_3949692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949692 prefixEnd_3949692 := by exact prefixLift 3949692
  have htrace : WordTrace (prefixWord ++ tailWord_3949692) baseStart_3949692 baseEnd_3949692 := by
    simpa [prefixWord, tailWord_3949692, baseEnd_3949692] using wordTrace_append hprefix tailTrace_3949692
  have hstable : (prefixWord ++ tailWord_3949692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949692).length < 2 ^ (prefixWord ++ tailWord_3949692).sum := by decide
  have hdescent : baseEnd_3949692 < baseStart_3949692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949719 : List Nat := [1, 1, 3, 3, 3, 1, 1, 4, 2, 4]
def baseStart_3949719 : Nat := 118140960795 + 3949719 * 2 ^ 59
def prefixEnd_3949719 : Nat := 4983230072969 + 3 ^ 40 * 3949719 * 2
def baseEnd_3949719 : Nat := 676034765731912479982693

theorem tailTrace_3949719 : CollatzResearch.WordTrace tailWord_3949719 prefixEnd_3949719 676034765731912479982693 := by
  unfold tailWord_3949719
  simp only [CollatzResearch.WordTrace]
  refine ⟨144058086777850096145980211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96038724518566730763986807 144058086777850096145980211)
  ·
    refine ⟨216087130166775144218970317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144058086777850096145980211 216087130166775144218970317)
    ·
      refine ⟨81032673812540679082113869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216087130166775144218970317 81032673812540679082113869)
      ·
        refine ⟨30387252679702754655792701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81032673812540679082113869 30387252679702754655792701)
        ·
          refine ⟨11395219754888532995922263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30387252679702754655792701 11395219754888532995922263)
          ·
            refine ⟨17092829632332799493883395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11395219754888532995922263 17092829632332799493883395)
            ·
              refine ⟨25639244448499199240825093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17092829632332799493883395 25639244448499199240825093)
              ·
                refine ⟨4807358334093599857654705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25639244448499199240825093 4807358334093599857654705)
                ·
                  refine ⟨3605518750570199893241029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4807358334093599857654705 3605518750570199893241029)
                  ·
                    refine ⟨676034765731912479982693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3605518750570199893241029 676034765731912479982693)
                    ·
                      rfl

theorem cell23_3949719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_3949719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949719 prefixEnd_3949719 := by exact prefixLift 3949719
  have htrace : WordTrace (prefixWord ++ tailWord_3949719) baseStart_3949719 baseEnd_3949719 := by
    simpa [prefixWord, tailWord_3949719, baseEnd_3949719] using wordTrace_append hprefix tailTrace_3949719
  have hstable : (prefixWord ++ tailWord_3949719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949719).length < 2 ^ (prefixWord ++ tailWord_3949719).sum := by decide
  have hdescent : baseEnd_3949719 < baseStart_3949719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949720 : List Nat := [2, 1, 2, 4, 2, 3, 2, 2, 1, 1, 3]
def baseStart_3949720 : Nat := 118140960795 + 3949720 * 2 ^ 59
def prefixEnd_3949720 : Nat := 4983230072969 + 3 ^ 40 * 3949720 * 2
def baseEnd_3949720 : Nat := 2028104810676391936035575

theorem tailTrace_3949720 : CollatzResearch.WordTrace tailWord_3949720 prefixEnd_3949720 2028104810676391936035575 := by
  unfold tailWord_3949720
  simp only [CollatzResearch.WordTrace]
  refine ⟨72029061625423236658383307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96038748833897648877844409 72029061625423236658383307)
  ·
    refine ⟨108043592438134854987574961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72029061625423236658383307 108043592438134854987574961)
    ·
      refine ⟨81032694328601141240681221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108043592438134854987574961 81032694328601141240681221)
      ·
        refine ⟨15193630186612713982627729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81032694328601141240681221 15193630186612713982627729)
        ·
          refine ⟨11395222639959535486970797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15193630186612713982627729 11395222639959535486970797)
          ·
            refine ⟨4273208489984825807614049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11395222639959535486970797 4273208489984825807614049)
            ·
              refine ⟨3204906367488619355710537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4273208489984825807614049 3204906367488619355710537)
              ·
                refine ⟨2403679775616464516782903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3204906367488619355710537 2403679775616464516782903)
                ·
                  refine ⟨3605519663424696775174355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2403679775616464516782903 3605519663424696775174355)
                  ·
                    refine ⟨5408279495137045162761533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3605519663424696775174355 5408279495137045162761533)
                    ·
                      refine ⟨2028104810676391936035575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5408279495137045162761533 2028104810676391936035575)
                      ·
                        rfl

theorem cell23_3949720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_3949720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949720 prefixEnd_3949720 := by exact prefixLift 3949720
  have htrace : WordTrace (prefixWord ++ tailWord_3949720) baseStart_3949720 baseEnd_3949720 := by
    simpa [prefixWord, tailWord_3949720, baseEnd_3949720] using wordTrace_append hprefix tailTrace_3949720
  have hstable : (prefixWord ++ tailWord_3949720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949720).length < 2 ^ (prefixWord ++ tailWord_3949720).sum := by decide
  have hdescent : baseEnd_3949720 < baseStart_3949720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949732 : List Nat := [2, 3, 1, 2, 3, 1, 3, 8]
def baseStart_3949732 : Nat := 118140960795 + 3949732 * 2 ^ 59
def prefixEnd_3949732 : Nat := 4983230072969 + 3 ^ 40 * 3949732 * 2
def baseEnd_3949732 : Nat := 75115221201638736632797

theorem tailTrace_3949732 : CollatzResearch.WordTrace tailWord_3949732 prefixEnd_3949732 75115221201638736632797 := by
  unfold tailWord_3949732
  simp only [CollatzResearch.WordTrace]
  refine ⟨72029280463401499683101725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96039040617868666244135633 72029280463401499683101725)
  ·
    refine ⟨27010980173775562381163147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72029280463401499683101725 27010980173775562381163147)
    ·
      refine ⟨40516470260663343571744721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27010980173775562381163147 40516470260663343571744721)
      ·
        refine ⟨30387352695497507678808541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40516470260663343571744721 30387352695497507678808541)
        ·
          refine ⟨11395257260811565379553203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30387352695497507678808541 11395257260811565379553203)
          ·
            refine ⟨17092885891217348069329805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11395257260811565379553203 17092885891217348069329805)
            ·
              refine ⟨6409832209206505525998677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17092885891217348069329805 6409832209206505525998677)
              ·
                refine ⟨75115221201638736632797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6409832209206505525998677 75115221201638736632797)
                ·
                  rfl

theorem cell23_3949732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 8].length) (baseStart_3949732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949732 prefixEnd_3949732 := by exact prefixLift 3949732
  have htrace : WordTrace (prefixWord ++ tailWord_3949732) baseStart_3949732 baseEnd_3949732 := by
    simpa [prefixWord, tailWord_3949732, baseEnd_3949732] using wordTrace_append hprefix tailTrace_3949732
  have hstable : (prefixWord ++ tailWord_3949732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949732).length < 2 ^ (prefixWord ++ tailWord_3949732).sum := by decide
  have hdescent : baseEnd_3949732 < baseStart_3949732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949760 : List Nat := [2, 1, 1, 2, 6, 1, 2, 3, 1, 2, 2]
def baseStart_3949760 : Nat := 118140960795 + 3949760 * 2 ^ 59
def prefixEnd_3949760 : Nat := 4983230072969 + 3 ^ 40 * 3949760 * 2
def baseEnd_3949760 : Nat := 2028125349902571779535391

theorem tailTrace_3949760 : CollatzResearch.WordTrace tailWord_3949760 prefixEnd_3949760 2028125349902571779535391 := by
  unfold tailWord_3949760
  simp only [CollatzResearch.WordTrace]
  refine ⟨72029791085350780074111367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96039721447134373432148489 72029791085350780074111367)
  ·
    refine ⟨108044686628026170111167051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72029791085350780074111367 108044686628026170111167051)
    ·
      refine ⟨162067029942039255166750577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108044686628026170111167051 162067029942039255166750577)
      ·
        refine ⟨121550272456529441375062933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162067029942039255166750577 121550272456529441375062933)
        ·
          refine ⟨5697669021399817564456075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121550272456529441375062933 5697669021399817564456075)
          ·
            refine ⟨8546503532099726346684113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5697669021399817564456075 8546503532099726346684113)
            ·
              refine ⟨6409877649074794760013085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8546503532099726346684113 6409877649074794760013085)
              ·
                refine ⟨2403704118403048035004907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6409877649074794760013085 2403704118403048035004907)
                ·
                  refine ⟨3605556177604572052507361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2403704118403048035004907 3605556177604572052507361)
                  ·
                    refine ⟨2704167133203429039380521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3605556177604572052507361 2704167133203429039380521)
                    ·
                      refine ⟨2028125349902571779535391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2704167133203429039380521 2028125349902571779535391)
                      ·
                        rfl

theorem cell23_3949760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 1, 2, 2].length) (baseStart_3949760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949760 prefixEnd_3949760 := by exact prefixLift 3949760
  have htrace : WordTrace (prefixWord ++ tailWord_3949760) baseStart_3949760 baseEnd_3949760 := by
    simpa [prefixWord, tailWord_3949760, baseEnd_3949760] using wordTrace_append hprefix tailTrace_3949760
  have hstable : (prefixWord ++ tailWord_3949760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949760).length < 2 ^ (prefixWord ++ tailWord_3949760).sum := by decide
  have hdescent : baseEnd_3949760 < baseStart_3949760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949792 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 2, 6]
def baseStart_3949792 : Nat := 118140960795 + 3949792 * 2 ^ 59
def prefixEnd_3949792 : Nat := 4983230072969 + 3 ^ 40 * 3949792 * 2
def baseEnd_3949792 : Nat := 676047260427838551445081

theorem tailTrace_3949792 : CollatzResearch.WordTrace tailWord_3949792 prefixEnd_3949792 676047260427838551445081 := by
  unfold tailWord_3949792
  simp only [CollatzResearch.WordTrace]
  refine ⟨72030374653292814806693815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96040499537723753075591753 72030374653292814806693815)
  ·
    refine ⟨108045561979939222210040723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72030374653292814806693815 108045561979939222210040723)
    ·
      refine ⟨162068342969908833315061085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108045561979939222210040723 162068342969908833315061085)
      ·
        refine ⟨60775628613715812493147907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162068342969908833315061085 60775628613715812493147907)
        ·
          refine ⟨91163442920573718739721861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60775628613715812493147907 91163442920573718739721861)
          ·
            refine ⟨17093145547607572263697849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91163442920573718739721861 17093145547607572263697849)
            ·
              refine ⟨12819859160705679197773387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17093145547607572263697849 12819859160705679197773387)
              ·
                refine ⟨19229788741058518796660081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12819859160705679197773387 19229788741058518796660081)
                ·
                  refine ⟨14422341555793889097495061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19229788741058518796660081 14422341555793889097495061)
                  ·
                    refine ⟨676047260427838551445081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14422341555793889097495061 676047260427838551445081)
                    ·
                      rfl

theorem cell23_3949792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 2, 6].length) (baseStart_3949792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949792 prefixEnd_3949792 := by exact prefixLift 3949792
  have htrace : WordTrace (prefixWord ++ tailWord_3949792) baseStart_3949792 baseEnd_3949792 := by
    simpa [prefixWord, tailWord_3949792, baseEnd_3949792] using wordTrace_append hprefix tailTrace_3949792
  have hstable : (prefixWord ++ tailWord_3949792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949792).length < 2 ^ (prefixWord ++ tailWord_3949792).sum := by decide
  have hdescent : baseEnd_3949792 < baseStart_3949792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949793 : List Nat := [1, 2, 3, 1, 3, 3, 3, 1, 2, 1, 3]
def baseStart_3949793 : Nat := 118140960795 + 3949793 * 2 ^ 59
def prefixEnd_3949793 : Nat := 4983230072969 + 3 ^ 40 * 3949793 * 2
def baseEnd_3949793 : Nat := 2028142294764170150422739

theorem tailTrace_3949793 : CollatzResearch.WordTrace tailWord_3949793 prefixEnd_3949793 2028142294764170150422739 := by
  unfold tailWord_3949793
  simp only [CollatzResearch.WordTrace]
  refine ⟨144060785779582006784174033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96040523853054671189449355 144060785779582006784174033)
  ·
    refine ⟨108045589334686505088130525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144060785779582006784174033 108045589334686505088130525)
    ·
      refine ⟨40517096000507439408048947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108045589334686505088130525 40517096000507439408048947)
      ·
        refine ⟨60775644000761159112073421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40517096000507439408048947 60775644000761159112073421)
        ·
          refine ⟨22790866500285434667027533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60775644000761159112073421 22790866500285434667027533)
          ·
            refine ⟨8546574937607038000135325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22790866500285434667027533 8546574937607038000135325)
            ·
              refine ⟨3204965601602639250050747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8546574937607038000135325 3204965601602639250050747)
              ·
                refine ⟨4807448402403958875076121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3204965601602639250050747 4807448402403958875076121)
                ·
                  refine ⟨3605586301802969156307091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4807448402403958875076121 3605586301802969156307091)
                  ·
                    refine ⟨5408379452704453734460637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3605586301802969156307091 5408379452704453734460637)
                    ·
                      refine ⟨2028142294764170150422739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5408379452704453734460637 2028142294764170150422739)
                      ·
                        rfl

theorem cell23_3949793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_3949793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949793 prefixEnd_3949793 := by exact prefixLift 3949793
  have htrace : WordTrace (prefixWord ++ tailWord_3949793) baseStart_3949793 baseEnd_3949793 := by
    simpa [prefixWord, tailWord_3949793, baseEnd_3949793] using wordTrace_append hprefix tailTrace_3949793
  have hstable : (prefixWord ++ tailWord_3949793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949793).length < 2 ^ (prefixWord ++ tailWord_3949793).sum := by decide
  have hdescent : baseEnd_3949793 < baseStart_3949793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949850 : List Nat := [3, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2]
def baseStart_3949850 : Nat := 118140960795 + 3949850 * 2 ^ 59
def prefixEnd_3949850 : Nat := 4983230072969 + 3 ^ 40 * 3949850 * 2
def baseEnd_3949850 : Nat := 2028171563161476427409977

theorem tailTrace_3949850 : CollatzResearch.WordTrace tailWord_3949850 prefixEnd_3949850 2028171563161476427409977 := by
  unfold tailWord_3949850
  simp only [CollatzResearch.WordTrace]
  refine ⟨36015716185093876379749751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96041909826917003679332669 36015716185093876379749751)
  ·
    refine ⟨54023574277640814569624627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36015716185093876379749751 54023574277640814569624627)
    ·
      refine ⟨81035361416461221854436941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54023574277640814569624627 81035361416461221854436941)
      ·
        refine ⟨30388260531172958195413853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81035361416461221854436941 30388260531172958195413853)
        ·
          refine ⟨11395597699189859323280195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30388260531172958195413853 11395597699189859323280195)
          ·
            refine ⟨17093396548784788984920293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11395597699189859323280195 17093396548784788984920293)
            ·
              refine ⟨3205011852897147934672555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17093396548784788984920293 3205011852897147934672555)
              ·
                refine ⟨4807517779345721902008833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3205011852897147934672555 4807517779345721902008833)
                ·
                  refine ⟨3605638334509291426506625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4807517779345721902008833 3605638334509291426506625)
                  ·
                    refine ⟨2704228750881968569879969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3605638334509291426506625 2704228750881968569879969)
                    ·
                      refine ⟨2028171563161476427409977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2704228750881968569879969 2028171563161476427409977)
                      ·
                        rfl

theorem cell23_3949850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_3949850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949850 prefixEnd_3949850 := by exact prefixLift 3949850
  have htrace : WordTrace (prefixWord ++ tailWord_3949850) baseStart_3949850 baseEnd_3949850 := by
    simpa [prefixWord, tailWord_3949850, baseEnd_3949850] using wordTrace_append hprefix tailTrace_3949850
  have hstable : (prefixWord ++ tailWord_3949850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949850).length < 2 ^ (prefixWord ++ tailWord_3949850).sum := by decide
  have hdescent : baseEnd_3949850 < baseStart_3949850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949852 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 3, 7]
def baseStart_3949852 : Nat := 118140960795 + 3949852 * 2 ^ 59
def prefixEnd_3949852 : Nat := 4983230072969 + 3 ^ 40 * 3949852 * 2
def baseEnd_3949852 : Nat := 676057530040928473194989

theorem tailTrace_3949852 : CollatzResearch.WordTrace tailWord_3949852 prefixEnd_3949852 676057530040928473194989 := by
  unfold tailWord_3949852
  simp only [CollatzResearch.WordTrace]
  refine ⟨72031468843184129930285905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96041958457578839907047873 72031468843184129930285905)
  ·
    refine ⟨54023601632388097447714429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72031468843184129930285905 54023601632388097447714429)
    ·
      refine ⟨20258850612145536542892911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54023601632388097447714429 20258850612145536542892911)
      ·
        refine ⟨30388275918218304814339367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20258850612145536542892911 30388275918218304814339367)
        ·
          refine ⟨45582413877327457221509051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30388275918218304814339367 45582413877327457221509051)
          ·
            refine ⟨68373620815991185832263577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45582413877327457221509051 68373620815991185832263577)
            ·
              refine ⟨51280215611993389374197683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68373620815991185832263577 51280215611993389374197683)
              ·
                refine ⟨76920323417990084061296525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51280215611993389374197683 76920323417990084061296525)
                ·
                  refine ⟨28845121281746281522986197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76920323417990084061296525 28845121281746281522986197)
                  ·
                    refine ⟨676057530040928473194989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28845121281746281522986197 676057530040928473194989)
                    ·
                      rfl

theorem cell23_3949852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_3949852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949852 prefixEnd_3949852 := by exact prefixLift 3949852
  have htrace : WordTrace (prefixWord ++ tailWord_3949852) baseStart_3949852 baseEnd_3949852 := by
    simpa [prefixWord, tailWord_3949852, baseEnd_3949852] using wordTrace_append hprefix tailTrace_3949852
  have hstable : (prefixWord ++ tailWord_3949852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949852).length < 2 ^ (prefixWord ++ tailWord_3949852).sum := by decide
  have hdescent : baseEnd_3949852 < baseStart_3949852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949854 : List Nat := [4, 3, 2, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_3949854 : Nat := 118140960795 + 3949854 * 2 ^ 59
def prefixEnd_3949854 : Nat := 4983230072969 + 3 ^ 40 * 3949854 * 2
def baseEnd_3949854 : Nat := 2028173617084094411759959

theorem tailTrace_3949854 : CollatzResearch.WordTrace tailWord_3949854 prefixEnd_3949854 2028173617084094411759959 := by
  unfold tailWord_3949854
  simp only [CollatzResearch.WordTrace]
  refine ⟨18007876329045126775268077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96042007088240676134763077 18007876329045126775268077)
  ·
    refine ⟨6752953623391922540725529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18007876329045126775268077 6752953623391922540725529)
    ·
      refine ⟨5064715217543941905544147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6752953623391922540725529 5064715217543941905544147)
      ·
        refine ⟨7597072826315912858316221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5064715217543941905544147 7597072826315912858316221)
        ·
          refine ⟨2848902309868467321868583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7597072826315912858316221 2848902309868467321868583)
          ·
            refine ⟨4273353464802700982802875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848902309868467321868583 4273353464802700982802875)
            ·
              refine ⟨6410030197204051474204313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4273353464802700982802875 6410030197204051474204313)
              ·
                refine ⟨4807522647903038605653235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6410030197204051474204313 4807522647903038605653235)
                ·
                  refine ⟨7211283971854557908479853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4807522647903038605653235 7211283971854557908479853)
                  ·
                    refine ⟨2704231489445459215679945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7211283971854557908479853 2704231489445459215679945)
                    ·
                      refine ⟨2028173617084094411759959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2704231489445459215679945 2028173617084094411759959)
                      ·
                        rfl

theorem cell23_3949854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_3949854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949854 prefixEnd_3949854 := by exact prefixLift 3949854
  have htrace : WordTrace (prefixWord ++ tailWord_3949854) baseStart_3949854 baseEnd_3949854 := by
    simpa [prefixWord, tailWord_3949854, baseEnd_3949854] using wordTrace_append hprefix tailTrace_3949854
  have hstable : (prefixWord ++ tailWord_3949854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949854).length < 2 ^ (prefixWord ++ tailWord_3949854).sum := by decide
  have hdescent : baseEnd_3949854 < baseStart_3949854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949933 : List Nat := [1, 5, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_3949933 : Nat := 118140960795 + 3949933 * 2 ^ 59
def prefixEnd_3949933 : Nat := 4983230072969 + 3 ^ 40 * 3949933 * 2
def baseEnd_3949933 : Nat := 676071394018599867557365

theorem tailTrace_3949933 : CollatzResearch.WordTrace tailWord_3949933 prefixEnd_3949933 676071394018599867557365 := by
  unfold tailWord_3949933
  simp only [CollatzResearch.WordTrace]
  refine ⟨144065891999074810694270453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96043927999383207129513635 144065891999074810694270453)
  ·
    refine ⟨13506177374913263502587855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144065891999074810694270453 13506177374913263502587855)
    ·
      refine ⟨20259266062369895253881783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13506177374913263502587855 20259266062369895253881783)
      ·
        refine ⟨30388899093554842880822675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20259266062369895253881783 30388899093554842880822675)
        ·
          refine ⟨45583348640332264321234013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30388899093554842880822675 45583348640332264321234013)
          ·
            refine ⟨17093755740124599120462755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45583348640332264321234013 17093755740124599120462755)
            ·
              refine ⟨25640633610186898680694133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17093755740124599120462755 25640633610186898680694133)
              ·
                refine ⟨2403809400955021751315075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25640633610186898680694133 2403809400955021751315075)
                ·
                  refine ⟨3605714101432532626972613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2403809400955021751315075 3605714101432532626972613)
                  ·
                    refine ⟨676071394018599867557365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3605714101432532626972613 676071394018599867557365)
                    ·
                      rfl

theorem cell23_3949933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_3949933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949933 prefixEnd_3949933 := by exact prefixLift 3949933
  have htrace : WordTrace (prefixWord ++ tailWord_3949933) baseStart_3949933 baseEnd_3949933 := by
    simpa [prefixWord, tailWord_3949933, baseEnd_3949933] using wordTrace_append hprefix tailTrace_3949933
  have hstable : (prefixWord ++ tailWord_3949933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949933).length < 2 ^ (prefixWord ++ tailWord_3949933).sum := by decide
  have hdescent : baseEnd_3949933 < baseStart_3949933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949996 : List Nat := [2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 4]
def baseStart_3949996 : Nat := 118140960795 + 3949996 * 2 ^ 59
def prefixEnd_3949996 : Nat := 4983230072969 + 3 ^ 40 * 3949996 * 2
def baseEnd_3949996 : Nat := 2028246531337032856184305

theorem tailTrace_3949996 : CollatzResearch.WordTrace tailWord_3949996 prefixEnd_3949996 2028246531337032856184305 := by
  unfold tailWord_3949996
  simp only [CollatzResearch.WordTrace]
  refine ⟨72034094898923286226906921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96045459865231048302542561 72034094898923286226906921)
  ·
    refine ⟨54025571174192464670180191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72034094898923286226906921 54025571174192464670180191)
    ·
      refine ⟨81038356761288697005270287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54025571174192464670180191 81038356761288697005270287)
      ·
        refine ⟨121557535141933045507905431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81038356761288697005270287 121557535141933045507905431)
        ·
          refine ⟨182336302712899568261858147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121557535141933045507905431 182336302712899568261858147)
          ·
            refine ⟨273504454069349352392787221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182336302712899568261858147 273504454069349352392787221)
            ·
              refine ⟨12820521284500750893411901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 273504454069349352392787221 12820521284500750893411901)
              ·
                refine ⟨4807695481687781585029463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12820521284500750893411901 4807695481687781585029463)
                ·
                  refine ⟨7211543222531672377544195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4807695481687781585029463 7211543222531672377544195)
                  ·
                    refine ⟨10817314833797508566316293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7211543222531672377544195 10817314833797508566316293)
                    ·
                      refine ⟨2028246531337032856184305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10817314833797508566316293 2028246531337032856184305)
                      ·
                        rfl

theorem cell23_3949996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 4].length) (baseStart_3949996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3949996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3949996 prefixEnd_3949996 := by exact prefixLift 3949996
  have htrace : WordTrace (prefixWord ++ tailWord_3949996) baseStart_3949996 baseEnd_3949996 := by
    simpa [prefixWord, tailWord_3949996, baseEnd_3949996] using wordTrace_append hprefix tailTrace_3949996
  have hstable : (prefixWord ++ tailWord_3949996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949996).length < 2 ^ (prefixWord ++ tailWord_3949996).sum := by decide
  have hdescent : baseEnd_3949996 < baseStart_3949996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950063 : List Nat := [1, 1, 2, 1, 4, 1, 3, 4, 2, 1, 3]
def baseStart_3950063 : Nat := 118140960795 + 3950063 * 2 ^ 59
def prefixEnd_3950063 : Nat := 4983230072969 + 3 ^ 40 * 3950063 * 2
def baseEnd_3950063 : Nat := 2028280934540884094046497

theorem tailTrace_3950063 : CollatzResearch.WordTrace tailWord_3950063 prefixEnd_3950063 2028280934540884094046497 := by
  unfold tailWord_3950063
  simp only [CollatzResearch.WordTrace]
  refine ⟨144070633488603842896502843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96047088992402561931001895 144070633488603842896502843)
  ·
    refine ⟨216105950232905764344754265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144070633488603842896502843 216105950232905764344754265)
    ·
      refine ⟨162079462674679323258565699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216105950232905764344754265 162079462674679323258565699)
      ·
        refine ⟨243119194012018984887848549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162079462674679323258565699 243119194012018984887848549)
        ·
          refine ⟨45584848877253559666471603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243119194012018984887848549 45584848877253559666471603)
          ·
            refine ⟨68377273315880339499707405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45584848877253559666471603 68377273315880339499707405)
            ·
              refine ⟨25641477493455127312390277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68377273315880339499707405 25641477493455127312390277)
              ·
                refine ⟨4807777030022836371073177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25641477493455127312390277 4807777030022836371073177)
                ·
                  refine ⟨3605832772517127278304883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4807777030022836371073177 3605832772517127278304883)
                  ·
                    refine ⟨5408749158775690917457325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3605832772517127278304883 5408749158775690917457325)
                    ·
                      refine ⟨2028280934540884094046497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5408749158775690917457325 2028280934540884094046497)
                      ·
                        rfl

theorem cell23_3950063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 1, 3].length) (baseStart_3950063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950063 prefixEnd_3950063 := by exact prefixLift 3950063
  have htrace : WordTrace (prefixWord ++ tailWord_3950063) baseStart_3950063 baseEnd_3950063 := by
    simpa [prefixWord, tailWord_3950063, baseEnd_3950063] using wordTrace_append hprefix tailTrace_3950063
  have hstable : (prefixWord ++ tailWord_3950063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950063).length < 2 ^ (prefixWord ++ tailWord_3950063).sum := by decide
  have hdescent : baseEnd_3950063 < baseStart_3950063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950064 : List Nat := [2, 1, 1, 1, 3, 6, 2, 2, 1, 2, 2]
def baseStart_3950064 : Nat := 118140960795 + 3950064 * 2 ^ 59
def prefixEnd_3950064 : Nat := 4983230072969 + 3 ^ 40 * 3950064 * 2
def baseEnd_3950064 : Nat := 2028281448021538590133993

theorem tailTrace_3950064 : CollatzResearch.WordTrace tailWord_3950064 prefixEnd_3950064 2028281448021538590133993 := by
  unfold tailWord_3950064
  simp only [CollatzResearch.WordTrace]
  refine ⟨72035334980800110033644623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96047113307733480044859497 72035334980800110033644623)
  ·
    refine ⟨108053002471200165050466935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72035334980800110033644623 108053002471200165050466935)
    ·
      refine ⟨162079503706800247575700403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108053002471200165050466935 162079503706800247575700403)
      ·
        refine ⟨243119255560200371363550605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162079503706800247575700403 243119255560200371363550605)
        ·
          refine ⟨91169720835075139261331477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243119255560200371363550605 91169720835075139261331477)
          ·
            refine ⟨4273580664144147152874913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91169720835075139261331477 4273580664144147152874913)
            ·
              refine ⟨3205185498108110364656185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4273580664144147152874913 3205185498108110364656185)
              ·
                refine ⟨2403889123581082773492139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3205185498108110364656185 2403889123581082773492139)
                ·
                  refine ⟨3605833685371624160238209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2403889123581082773492139 3605833685371624160238209)
                  ·
                    refine ⟨2704375264028718120178657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3605833685371624160238209 2704375264028718120178657)
                    ·
                      refine ⟨2028281448021538590133993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2704375264028718120178657 2028281448021538590133993)
                      ·
                        rfl

theorem cell23_3950064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 1, 2, 2].length) (baseStart_3950064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950064 prefixEnd_3950064 := by exact prefixLift 3950064
  have htrace : WordTrace (prefixWord ++ tailWord_3950064) baseStart_3950064 baseEnd_3950064 := by
    simpa [prefixWord, tailWord_3950064, baseEnd_3950064] using wordTrace_append hprefix tailTrace_3950064
  have hstable : (prefixWord ++ tailWord_3950064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950064).length < 2 ^ (prefixWord ++ tailWord_3950064).sum := by decide
  have hdescent : baseEnd_3950064 < baseStart_3950064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950066 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 2, 7]
def baseStart_3950066 : Nat := 118140960795 + 3950066 * 2 ^ 59
def prefixEnd_3950066 : Nat := 4983230072969 + 3 ^ 40 * 3950066 * 2
def baseEnd_3950066 : Nat := 676094158327615860769661

theorem tailTrace_3950066 : CollatzResearch.WordTrace tailWord_3950066 prefixEnd_3950066 676094158327615860769661 := by
  unfold tailWord_3950066
  simp only [CollatzResearch.WordTrace]
  refine ⟨36017685726898243602215513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96047161938395316272574701 36017685726898243602215513)
  ·
    refine ⟨27013264295173682701661635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36017685726898243602215513 27013264295173682701661635)
    ·
      refine ⟨40519896442760524052492453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27013264295173682701661635 40519896442760524052492453)
      ·
        refine ⟨7597480583017598259842335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40519896442760524052492453 7597480583017598259842335)
        ·
          refine ⟨11396220874526397389763503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7597480583017598259842335 11396220874526397389763503)
          ·
            refine ⟨17094331311789596084645255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11396220874526397389763503 17094331311789596084645255)
            ·
              refine ⟨25641496967684394126967883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17094331311789596084645255 25641496967684394126967883)
              ·
                refine ⟨38462245451526591190451825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25641496967684394126967883 38462245451526591190451825)
                ·
                  refine ⟨28846684088644943392838869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38462245451526591190451825 28846684088644943392838869)
                  ·
                    refine ⟨676094158327615860769661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28846684088644943392838869 676094158327615860769661)
                    ·
                      rfl

theorem cell23_3950066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_3950066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950066 prefixEnd_3950066 := by exact prefixLift 3950066
  have htrace : WordTrace (prefixWord ++ tailWord_3950066) baseStart_3950066 baseEnd_3950066 := by
    simpa [prefixWord, tailWord_3950066, baseEnd_3950066] using wordTrace_append hprefix tailTrace_3950066
  have hstable : (prefixWord ++ tailWord_3950066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950066).length < 2 ^ (prefixWord ++ tailWord_3950066).sum := by decide
  have hdescent : baseEnd_3950066 < baseStart_3950066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950156 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 1, 7]
def baseStart_3950156 : Nat := 118140960795 + 3950156 * 2 ^ 59
def prefixEnd_3950156 : Nat := 4983230072969 + 3 ^ 40 * 3950156 * 2
def baseEnd_3950156 : Nat := 676109562747250743394523

theorem tailTrace_3950156 : CollatzResearch.WordTrace tailWord_3950156 prefixEnd_3950156 676109562747250743394523 := by
  unfold tailWord_3950156
  simp only [CollatzResearch.WordTrace]
  refine ⟨72037012738633459889819161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96049350318177946519758881 72037012738633459889819161)
  ·
    refine ⟨54027759553975094917364371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72037012738633459889819161 54027759553975094917364371)
    ·
      refine ⟨81041639330962642376046557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54027759553975094917364371 81041639330962642376046557)
      ·
        refine ⟨30390614749110990891017459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81041639330962642376046557 30390614749110990891017459)
        ·
          refine ⟨45585922123666486336526189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30390614749110990891017459 45585922123666486336526189)
          ·
            refine ⟨17094720796374932376197321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45585922123666486336526189 17094720796374932376197321)
            ·
              refine ⟨12821040597281199282147991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17094720796374932376197321 12821040597281199282147991)
              ·
                refine ⟨19231560895921798923221987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12821040597281199282147991 19231560895921798923221987)
                ·
                  refine ⟨28847341343882698384832981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19231560895921798923221987 28847341343882698384832981)
                  ·
                    refine ⟨676109562747250743394523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28847341343882698384832981 676109562747250743394523)
                    ·
                      rfl

theorem cell23_3950156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_3950156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950156 prefixEnd_3950156 := by exact prefixLift 3950156
  have htrace : WordTrace (prefixWord ++ tailWord_3950156) baseStart_3950156 baseEnd_3950156 := by
    simpa [prefixWord, tailWord_3950156, baseEnd_3950156] using wordTrace_append hprefix tailTrace_3950156
  have hstable : (prefixWord ++ tailWord_3950156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950156).length < 2 ^ (prefixWord ++ tailWord_3950156).sum := by decide
  have hdescent : baseEnd_3950156 < baseStart_3950156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950193 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 2, 4, 2]
def baseStart_3950193 : Nat := 118140960795 + 3950193 * 2 ^ 59
def prefixEnd_3950193 : Nat := 4983230072969 + 3 ^ 40 * 3950193 * 2
def baseEnd_3950193 : Nat := 2028347687025968585420899

theorem tailTrace_3950193 : CollatzResearch.WordTrace tailWord_3950193 prefixEnd_3950193 2028347687025968585420899 := by
  unfold tailWord_3950193
  simp only [CollatzResearch.WordTrace]
  refine ⟨144075374978132875098735233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96050249985421916732490155 144075374978132875098735233)
  ·
    refine ⟨108056531233599656324051425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144075374978132875098735233 108056531233599656324051425)
    ·
      refine ⟨81042398425199742243038569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108056531233599656324051425 81042398425199742243038569)
      ·
        refine ⟨60781798818899806682278927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81042398425199742243038569 60781798818899806682278927)
        ·
          refine ⟨91172698228349710023418391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60781798818899806682278927 91172698228349710023418391)
          ·
            refine ⟨136759047342524565035127587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91172698228349710023418391 136759047342524565035127587)
            ·
              refine ⟨205138571013786847552691381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136759047342524565035127587 205138571013786847552691381)
              ·
                refine ⟨19231741032542516958064817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205138571013786847552691381 19231741032542516958064817)
                ·
                  refine ⟨14423805774406887718548613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19231741032542516958064817 14423805774406887718548613)
                  ·
                    refine ⟨2704463582701291447227865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14423805774406887718548613 2704463582701291447227865)
                    ·
                      refine ⟨2028347687025968585420899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2704463582701291447227865 2028347687025968585420899)
                      ·
                        rfl

theorem cell23_3950193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_3950193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950193 prefixEnd_3950193 := by exact prefixLift 3950193
  have htrace : WordTrace (prefixWord ++ tailWord_3950193) baseStart_3950193 baseEnd_3950193 := by
    simpa [prefixWord, tailWord_3950193, baseEnd_3950193] using wordTrace_append hprefix tailTrace_3950193
  have hstable : (prefixWord ++ tailWord_3950193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950193).length < 2 ^ (prefixWord ++ tailWord_3950193).sum := by decide
  have hdescent : baseEnd_3950193 < baseStart_3950193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950220 : List Nat := [2, 2, 1, 2, 1, 1, 4, 5, 1, 4]
def baseStart_3950220 : Nat := 118140960795 + 3950220 * 2 ^ 59
def prefixEnd_3950220 : Nat := 4983230072969 + 3 ^ 40 * 3950220 * 2
def baseEnd_3950220 : Nat := 676120517001213326594425

theorem tailTrace_3950220 : CollatzResearch.WordTrace tailWord_3950220 prefixEnd_3950220 676120517001213326594425 := by
  unfold tailWord_3950220
  simp only [CollatzResearch.WordTrace]
  refine ⟨72038179874517529354984057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96050906499356705806645409 72038179874517529354984057)
  ·
    refine ⟨54028634905888147016238043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72038179874517529354984057 54028634905888147016238043)
    ·
      refine ⟨81042952358832220524357065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54028634905888147016238043 81042952358832220524357065)
      ·
        refine ⟨60782214269124165393267799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81042952358832220524357065 60782214269124165393267799)
        ·
          refine ⟨91173321403686248089901699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60782214269124165393267799 91173321403686248089901699)
          ·
            refine ⟨136759982105529372134852549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91173321403686248089901699 136759982105529372134852549)
            ·
              refine ⟨25642496644786757275284853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136759982105529372134852549 25642496644786757275284853)
              ·
                refine ⟨2403984060448758494557955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25642496644786757275284853 2403984060448758494557955)
                ·
                  refine ⟨3605976090673137741836933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2403984060448758494557955 3605976090673137741836933)
                  ·
                    refine ⟨676120517001213326594425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3605976090673137741836933 676120517001213326594425)
                    ·
                      rfl

theorem cell23_3950220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 1, 4].length) (baseStart_3950220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950220 prefixEnd_3950220 := by exact prefixLift 3950220
  have htrace : WordTrace (prefixWord ++ tailWord_3950220) baseStart_3950220 baseEnd_3950220 := by
    simpa [prefixWord, tailWord_3950220, baseEnd_3950220] using wordTrace_append hprefix tailTrace_3950220
  have hstable : (prefixWord ++ tailWord_3950220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950220).length < 2 ^ (prefixWord ++ tailWord_3950220).sum := by decide
  have hdescent : baseEnd_3950220 < baseStart_3950220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950263 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 3, 5]
def baseStart_3950263 : Nat := 118140960795 + 3950263 * 2 ^ 59
def prefixEnd_3950263 : Nat := 4983230072969 + 3 ^ 40 * 3950263 * 2
def baseEnd_3950263 : Nat := 676127876890594437181859

theorem tailTrace_3950263 : CollatzResearch.WordTrace tailWord_3950263 prefixEnd_3950263 676127876890594437181859 := by
  unfold tailWord_3950263
  simp only [CollatzResearch.WordTrace]
  refine ⟨144077928087879277053783443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96051952058586184702522295 144077928087879277053783443)
  ·
    refine ⟨216116892131818915580675165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144077928087879277053783443 216116892131818915580675165)
    ·
      refine ⟨81043834549432093342753187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216116892131818915580675165 81043834549432093342753187)
      ·
        refine ⟨121565751824148140014129781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81043834549432093342753187 121565751824148140014129781)
        ·
          refine ⟨11396789233513888126324667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121565751824148140014129781 11396789233513888126324667)
          ·
            refine ⟨17095183850270832189487001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11396789233513888126324667 17095183850270832189487001)
            ·
              refine ⟨12821387887703124142115251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17095183850270832189487001 12821387887703124142115251)
              ·
                refine ⟨19232081831554686213172877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12821387887703124142115251 19232081831554686213172877)
                ·
                  refine ⟨7212030686833007329939829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19232081831554686213172877 7212030686833007329939829)
                  ·
                    refine ⟨676127876890594437181859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7212030686833007329939829 676127876890594437181859)
                    ·
                      rfl

theorem cell23_3950263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_3950263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950263 prefixEnd_3950263 := by exact prefixLift 3950263
  have htrace : WordTrace (prefixWord ++ tailWord_3950263) baseStart_3950263 baseEnd_3950263 := by
    simpa [prefixWord, tailWord_3950263, baseEnd_3950263] using wordTrace_append hprefix tailTrace_3950263
  have hstable : (prefixWord ++ tailWord_3950263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950263).length < 2 ^ (prefixWord ++ tailWord_3950263).sum := by decide
  have hdescent : baseEnd_3950263 < baseStart_3950263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950283 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 1, 8, 2]
def baseStart_3950283 : Nat := 118140960795 + 3950283 * 2 ^ 59
def prefixEnd_3950283 : Nat := 4983230072969 + 3 ^ 40 * 3950283 * 2
def baseEnd_3950283 : Nat := 2028393900284873233295485

theorem tailTrace_3950283 : CollatzResearch.WordTrace tailWord_3950283 prefixEnd_3950283 2028393900284873233295485 := by
  unfold tailWord_3950283
  simp only [CollatzResearch.WordTrace]
  refine ⟨144078657547806820469511503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96052438365204546979674335 144078657547806820469511503)
  ·
    refine ⟨216117986321710230704267255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144078657547806820469511503 216117986321710230704267255)
    ·
      refine ⟨324176979482565346056400883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216117986321710230704267255 324176979482565346056400883)
      ·
        refine ⟨486265469223848019084601325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324176979482565346056400883 486265469223848019084601325)
        ·
          refine ⟨182349550958943007156725497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 486265469223848019084601325 182349550958943007156725497)
          ·
            refine ⟨136762163219207255367544123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182349550958943007156725497 136762163219207255367544123)
            ·
              refine ⟨205143244828810883051316185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136762163219207255367544123 205143244828810883051316185)
              ·
                refine ⟨153857433621608162288487139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205143244828810883051316185 153857433621608162288487139)
                ·
                  refine ⟨230786150432412243432730709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153857433621608162288487139 230786150432412243432730709)
                  ·
                    refine ⟨2704525200379830977727313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 230786150432412243432730709 2704525200379830977727313)
                    ·
                      refine ⟨2028393900284873233295485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2704525200379830977727313 2028393900284873233295485)
                      ·
                        rfl

theorem cell23_3950283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 8, 2].length) (baseStart_3950283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950283 prefixEnd_3950283 := by exact prefixLift 3950283
  have htrace : WordTrace (prefixWord ++ tailWord_3950283) baseStart_3950283 baseEnd_3950283 := by
    simpa [prefixWord, tailWord_3950283, baseEnd_3950283] using wordTrace_append hprefix tailTrace_3950283
  have hstable : (prefixWord ++ tailWord_3950283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950283).length < 2 ^ (prefixWord ++ tailWord_3950283).sum := by decide
  have hdescent : baseEnd_3950283 < baseStart_3950283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950303 : List Nat := [1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 5]
def baseStart_3950303 : Nat := 118140960795 + 3950303 * 2 ^ 59
def prefixEnd_3950303 : Nat := 4983230072969 + 3 ^ 40 * 3950303 * 2
def baseEnd_3950303 : Nat := 2028404169897963155045393

theorem tailTrace_3950303 : CollatzResearch.WordTrace tailWord_3950303 prefixEnd_3950303 2028404169897963155045393 := by
  unfold tailWord_3950303
  simp only [CollatzResearch.WordTrace]
  refine ⟨144079387007734363885239563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96052924671822909256826375 144079387007734363885239563)
  ·
    refine ⟨216119080511601545827859345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144079387007734363885239563 216119080511601545827859345)
    ·
      refine ⟨162089310383701159370894509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216119080511601545827859345 162089310383701159370894509)
      ·
        refine ⟨60783491393887934764085441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162089310383701159370894509 60783491393887934764085441)
        ·
          refine ⟨45587618545415951073064081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60783491393887934764085441 45587618545415951073064081)
          ·
            refine ⟨34190713909061963304798061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45587618545415951073064081 34190713909061963304798061)
            ·
              refine ⟨12821517715898236239299273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34190713909061963304798061 12821517715898236239299273)
              ·
                refine ⟨9616138286923677179474455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12821517715898236239299273 9616138286923677179474455)
                ·
                  refine ⟨14424207430385515769211683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9616138286923677179474455 14424207430385515769211683)
                  ·
                    refine ⟨21636311145578273653817525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14424207430385515769211683 21636311145578273653817525)
                    ·
                      refine ⟨2028404169897963155045393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21636311145578273653817525 2028404169897963155045393)
                      ·
                        rfl

theorem cell23_3950303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_3950303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950303 prefixEnd_3950303 := by exact prefixLift 3950303
  have htrace : WordTrace (prefixWord ++ tailWord_3950303) baseStart_3950303 baseEnd_3950303 := by
    simpa [prefixWord, tailWord_3950303, baseEnd_3950303] using wordTrace_append hprefix tailTrace_3950303
  have hstable : (prefixWord ++ tailWord_3950303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950303).length < 2 ^ (prefixWord ++ tailWord_3950303).sum := by decide
  have hdescent : baseEnd_3950303 < baseStart_3950303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950317 : List Nat := [1, 5, 1, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_3950317 : Nat := 118140960795 + 3950317 * 2 ^ 59
def prefixEnd_3950317 : Nat := 4983230072969 + 3 ^ 40 * 3950317 * 2
def baseEnd_3950317 : Nat := 2028411358627126100270329

theorem tailTrace_3950317 : CollatzResearch.WordTrace tailWord_3950317 prefixEnd_3950317 2028411358627126100270329 := by
  unfold tailWord_3950317
  simp only [CollatzResearch.WordTrace]
  refine ⟨144079897629683644276249205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96053265086455762850832803 144079897629683644276249205)
  ·
    refine ⟨13507490402782841650898363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144079897629683644276249205 13507490402782841650898363)
    ·
      refine ⟨20261235604174262476347545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13507490402782841650898363 20261235604174262476347545)
      ·
        refine ⟨15195926703130696857260659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20261235604174262476347545 15195926703130696857260659)
        ·
          refine ⟨22793890054696045285890989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15195926703130696857260659 22793890054696045285890989)
          ·
            refine ⟨8547708770511016982209121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22793890054696045285890989 8547708770511016982209121)
            ·
              refine ⟨6410781577883262736656841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8547708770511016982209121 6410781577883262736656841)
              ·
                refine ⟨4808086183412447052492631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6410781577883262736656841 4808086183412447052492631)
                ·
                  refine ⟨7212129275118670578738947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4808086183412447052492631 7212129275118670578738947)
                  ·
                    refine ⟨10818193912678005868108421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7212129275118670578738947 10818193912678005868108421)
                    ·
                      refine ⟨2028411358627126100270329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10818193912678005868108421 2028411358627126100270329)
                      ·
                        rfl

theorem cell23_3950317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_3950317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950317 prefixEnd_3950317 := by exact prefixLift 3950317
  have htrace : WordTrace (prefixWord ++ tailWord_3950317) baseStart_3950317 baseEnd_3950317 := by
    simpa [prefixWord, tailWord_3950317, baseEnd_3950317] using wordTrace_append hprefix tailTrace_3950317
  have hstable : (prefixWord ++ tailWord_3950317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950317).length < 2 ^ (prefixWord ++ tailWord_3950317).sum := by decide
  have hdescent : baseEnd_3950317 < baseStart_3950317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950323 : List Nat := [1, 1, 1, 2, 2, 3, 6, 7]
def baseStart_3950323 : Nat := 118140960795 + 3950323 * 2 ^ 59
def prefixEnd_3950323 : Nat := 4983230072969 + 3 ^ 40 * 3950323 * 2
def baseEnd_3950323 : Nat := 75126460722631595436863

theorem tailTrace_3950323 : CollatzResearch.WordTrace tailWord_3950323 prefixEnd_3950323 75126460722631595436863 := by
  unfold tailWord_3950323
  simp only [CollatzResearch.WordTrace]
  refine ⟨144080116467661907300967623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96053410978441271533978415 144080116467661907300967623)
  ·
    refine ⟨216120174701492860951451435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144080116467661907300967623 216120174701492860951451435)
    ·
      refine ⟨324180262052239291427177153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216120174701492860951451435 324180262052239291427177153)
      ·
        refine ⟨243135196539179468570382865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324180262052239291427177153 243135196539179468570382865)
        ·
          refine ⟨182351397404384601427787149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243135196539179468570382865 182351397404384601427787149)
          ·
            refine ⟨68381774026644225535420181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182351397404384601427787149 68381774026644225535420181)
            ·
              refine ⟨3205395657498948071972821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68381774026644225535420181 3205395657498948071972821)
              ·
                refine ⟨75126460722631595436863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3205395657498948071972821 75126460722631595436863)
                ·
                  rfl

theorem cell23_3950323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 7].length) (baseStart_3950323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950323 prefixEnd_3950323 := by exact prefixLift 3950323
  have htrace : WordTrace (prefixWord ++ tailWord_3950323) baseStart_3950323 baseEnd_3950323 := by
    simpa [prefixWord, tailWord_3950323, baseEnd_3950323] using wordTrace_append hprefix tailTrace_3950323
  have hstable : (prefixWord ++ tailWord_3950323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950323).length < 2 ^ (prefixWord ++ tailWord_3950323).sum := by decide
  have hdescent : baseEnd_3950323 < baseStart_3950323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950367 : List Nat := [1, 1, 2, 4, 2, 1, 3, 3, 2, 1, 3]
def baseStart_3950367 : Nat := 118140960795 + 3950367 * 2 ^ 59
def prefixEnd_3950367 : Nat := 4983230072969 + 3 ^ 40 * 3950367 * 2
def baseEnd_3950367 : Nat := 2028437032659850904645099

theorem tailTrace_3950367 : CollatzResearch.WordTrace tailWord_3950367 prefixEnd_3950367 2028437032659850904645099 := by
  unfold tailWord_3950367
  simp only [CollatzResearch.WordTrace]
  refine ⟨144081721279502502815569355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96054480853001668543712903 144081721279502502815569355)
  ·
    refine ⟨216122581919253754223354033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144081721279502502815569355 216122581919253754223354033)
    ·
      refine ⟨162091936439440315667515525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216122581919253754223354033 162091936439440315667515525)
      ·
        refine ⟨30392238082395059187659161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162091936439440315667515525 30392238082395059187659161)
        ·
          refine ⟨22794178561796294390744371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30392238082395059187659161 22794178561796294390744371)
          ·
            refine ⟨34191267842694441586116557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22794178561796294390744371 34191267842694441586116557)
            ·
              refine ⟨12821725441010415594793709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34191267842694441586116557 12821725441010415594793709)
              ·
                refine ⟨4808147040378905848047641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12821725441010415594793709 4808147040378905848047641)
                ·
                  refine ⟨3606110280284179386035731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4808147040378905848047641 3606110280284179386035731)
                  ·
                    refine ⟨5409165420426269079053597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3606110280284179386035731 5409165420426269079053597)
                    ·
                      refine ⟨2028437032659850904645099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5409165420426269079053597 2028437032659850904645099)
                      ·
                        rfl

theorem cell23_3950367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_3950367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950367 prefixEnd_3950367 := by exact prefixLift 3950367
  have htrace : WordTrace (prefixWord ++ tailWord_3950367) baseStart_3950367 baseEnd_3950367 := by
    simpa [prefixWord, tailWord_3950367, baseEnd_3950367] using wordTrace_append hprefix tailTrace_3950367
  have hstable : (prefixWord ++ tailWord_3950367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950367).length < 2 ^ (prefixWord ++ tailWord_3950367).sum := by decide
  have hdescent : baseEnd_3950367 < baseStart_3950367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950407 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 4, 2, 2]
def baseStart_3950407 : Nat := 118140960795 + 3950407 * 2 ^ 59
def prefixEnd_3950407 : Nat := 4983230072969 + 3 ^ 40 * 3950407 * 2
def baseEnd_3950407 : Nat := 2028457571886030748144915

theorem tailTrace_3950407 : CollatzResearch.WordTrace tailWord_3950407 prefixEnd_3950407 2028457571886030748144915 := by
  unfold tailWord_3950407
  simp only [CollatzResearch.WordTrace]
  refine ⟨144083180199357589647025475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96055453466238393098016983 144083180199357589647025475)
  ·
    refine ⟨216124770299036384470538213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144083180199357589647025475 216124770299036384470538213)
    ·
      refine ⟨40523394431069322088225915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216124770299036384470538213 40523394431069322088225915)
      ·
        refine ⟨60785091646603983132338873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40523394431069322088225915 60785091646603983132338873)
        ·
          refine ⟨45588818734952987349254155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60785091646603983132338873 45588818734952987349254155)
          ·
            refine ⟨68383228102429481023881233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45588818734952987349254155 68383228102429481023881233)
            ·
              refine ⟨51287421076822110767910925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68383228102429481023881233 51287421076822110767910925)
              ·
                refine ⟨19232782903808291537966597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51287421076822110767910925 19232782903808291537966597)
                ·
                  refine ⟨3606146794464054663368737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19232782903808291537966597 3606146794464054663368737)
                  ·
                    refine ⟨2704610095848040997526553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3606146794464054663368737 2704610095848040997526553)
                    ·
                      refine ⟨2028457571886030748144915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2704610095848040997526553 2028457571886030748144915)
                      ·
                        rfl

theorem cell23_3950407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_3950407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950407 prefixEnd_3950407 := by exact prefixLift 3950407
  have htrace : WordTrace (prefixWord ++ tailWord_3950407) baseStart_3950407 baseEnd_3950407 := by
    simpa [prefixWord, tailWord_3950407, baseEnd_3950407] using wordTrace_append hprefix tailTrace_3950407
  have hstable : (prefixWord ++ tailWord_3950407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950407).length < 2 ^ (prefixWord ++ tailWord_3950407).sum := by decide
  have hdescent : baseEnd_3950407 < baseStart_3950407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950420 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_3950420 : Nat := 118140960795 + 3950420 * 2 ^ 59
def prefixEnd_3950420 : Nat := 4983230072969 + 3 ^ 40 * 3950420 * 2
def baseEnd_3950420 : Nat := 2028464247134539197282355

theorem tailTrace_3950420 : CollatzResearch.WordTrace tailWord_3950420 prefixEnd_3950420 2028464247134539197282355 := by
  unfold tailWord_3950420
  simp only [CollatzResearch.WordTrace]
  refine ⟨72041827174155246433624357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96055769565540328578165809 72041827174155246433624357)
  ·
    refine ⟨13507842595154108706304567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72041827174155246433624357 13507842595154108706304567)
    ·
      refine ⟨20261763892731163059456851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13507842595154108706304567 20261763892731163059456851)
      ·
        refine ⟨30392645839096744589185277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20261763892731163059456851 30392645839096744589185277)
        ·
          refine ⟨11397242189661279220944479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30392645839096744589185277 11397242189661279220944479)
          ·
            refine ⟨17095863284491918831416719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11397242189661279220944479 17095863284491918831416719)
            ·
              refine ⟨25643794926737878247125079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17095863284491918831416719 25643794926737878247125079)
              ·
                refine ⟨38465692390106817370687619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25643794926737878247125079 38465692390106817370687619)
                ·
                  refine ⟨57698538585160226056031429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38465692390106817370687619 57698538585160226056031429)
                  ·
                    refine ⟨10818475984717542385505893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57698538585160226056031429 10818475984717542385505893)
                    ·
                      refine ⟨2028464247134539197282355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10818475984717542385505893 2028464247134539197282355)
                      ·
                        rfl

theorem cell23_3950420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_3950420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950420 prefixEnd_3950420 := by exact prefixLift 3950420
  have htrace : WordTrace (prefixWord ++ tailWord_3950420) baseStart_3950420 baseEnd_3950420 := by
    simpa [prefixWord, tailWord_3950420, baseEnd_3950420] using wordTrace_append hprefix tailTrace_3950420
  have hstable : (prefixWord ++ tailWord_3950420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950420).length < 2 ^ (prefixWord ++ tailWord_3950420).sum := by decide
  have hdescent : baseEnd_3950420 < baseStart_3950420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950440 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_3950440 : Nat := 118140960795 + 3950440 * 2 ^ 59
def prefixEnd_3950440 : Nat := 4983230072969 + 3 ^ 40 * 3950440 * 2
def baseEnd_3950440 : Nat := 2028474516747629119032263

theorem tailTrace_3950440 : CollatzResearch.WordTrace tailWord_3950440 prefixEnd_3950440 2028474516747629119032263 := by
  unfold tailWord_3950440
  simp only [CollatzResearch.WordTrace]
  refine ⟨72042191904119018141488387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96056255872158690855317849 72042191904119018141488387)
  ·
    refine ⟨108063287856178527212232581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72042191904119018141488387 108063287856178527212232581)
    ·
      refine ⟨20261866473033473852293609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108063287856178527212232581 20261866473033473852293609)
      ·
        refine ⟨15196399854775105389220207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20261866473033473852293609 15196399854775105389220207)
        ·
          refine ⟨22794599782162658083830311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15196399854775105389220207 22794599782162658083830311)
          ·
            refine ⟨34191899673243987125745467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22794599782162658083830311 34191899673243987125745467)
            ·
              refine ⟨51287849509865980688618201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34191899673243987125745467 51287849509865980688618201)
              ·
                refine ⟨38465887132399485516463651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51287849509865980688618201 38465887132399485516463651)
                ·
                  refine ⟨57698830698599228274695477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38465887132399485516463651 57698830698599228274695477)
                  ·
                    refine ⟨5409265377993677650752701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57698830698599228274695477 5409265377993677650752701)
                    ·
                      refine ⟨2028474516747629119032263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5409265377993677650752701 2028474516747629119032263)
                      ·
                        rfl

theorem cell23_3950440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_3950440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950440 prefixEnd_3950440 := by exact prefixLift 3950440
  have htrace : WordTrace (prefixWord ++ tailWord_3950440) baseStart_3950440 baseEnd_3950440 := by
    simpa [prefixWord, tailWord_3950440, baseEnd_3950440] using wordTrace_append hprefix tailTrace_3950440
  have hstable : (prefixWord ++ tailWord_3950440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950440).length < 2 ^ (prefixWord ++ tailWord_3950440).sum := by decide
  have hdescent : baseEnd_3950440 < baseStart_3950440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950483 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 5]
def baseStart_3950483 : Nat := 118140960795 + 3950483 * 2 ^ 59
def prefixEnd_3950483 : Nat := 4983230072969 + 3 ^ 40 * 3950483 * 2
def baseEnd_3950483 : Nat := 2028496596415772450794565

theorem tailTrace_3950483 : CollatzResearch.WordTrace tailWord_3950483 prefixEnd_3950483 2028496596415772450794565 := by
  unfold tailWord_3950483
  simp only [CollatzResearch.WordTrace]
  refine ⟨144085952147082254626792103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96057301431388169751194735 144085952147082254626792103)
  ·
    refine ⟨216128928220623381940188155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144085952147082254626792103 216128928220623381940188155)
    ·
      refine ⟨324193392330935072910282233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216128928220623381940188155 324193392330935072910282233)
      ·
        refine ⟨243145044248201304682711675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324193392330935072910282233 243145044248201304682711675)
        ·
          refine ⟨364717566372301957024067513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243145044248201304682711675 364717566372301957024067513)
          ·
            refine ⟨273538174779226467768050635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364717566372301957024067513 273538174779226467768050635)
            ·
              refine ⟨410307262168839701652075953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273538174779226467768050635 410307262168839701652075953)
              ·
                refine ⟨307730446626629776239056965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410307262168839701652075953 307730446626629776239056965)
                ·
                  refine ⟨57699458742493083044823181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 307730446626629776239056965 57699458742493083044823181)
                  ·
                    refine ⟨21637297028434906141808693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57699458742493083044823181 21637297028434906141808693)
                    ·
                      refine ⟨2028496596415772450794565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21637297028434906141808693 2028496596415772450794565)
                      ·
                        rfl

theorem cell23_3950483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_3950483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950483 prefixEnd_3950483 := by exact prefixLift 3950483
  have htrace : WordTrace (prefixWord ++ tailWord_3950483) baseStart_3950483 baseEnd_3950483 := by
    simpa [prefixWord, tailWord_3950483, baseEnd_3950483] using wordTrace_append hprefix tailTrace_3950483
  have hstable : (prefixWord ++ tailWord_3950483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950483).length < 2 ^ (prefixWord ++ tailWord_3950483).sum := by decide
  have hdescent : baseEnd_3950483 < baseStart_3950483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950517 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_3950517 : Nat := 118140960795 + 3950517 * 2 ^ 59
def prefixEnd_3950517 : Nat := 4983230072969 + 3 ^ 40 * 3950517 * 2
def baseEnd_3950517 : Nat := 2028514054758025317769409

theorem tailTrace_3950517 : CollatzResearch.WordTrace tailWord_3950517 prefixEnd_3950517 2028514054758025317769409 := by
  unfold tailWord_3950517
  simp only [CollatzResearch.WordTrace]
  refine ⟨144087192228959078433529805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96058128152639385622353203 144087192228959078433529805)
  ·
    refine ⟨54032697085859654412573677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144087192228959078433529805 54032697085859654412573677)
    ·
      refine ⟨20262261407197370404715129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54032697085859654412573677 20262261407197370404715129)
      ·
        refine ⟨15196696055398027803536347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20262261407197370404715129 15196696055398027803536347)
        ·
          refine ⟨22795044083097041705304521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15196696055398027803536347 22795044083097041705304521)
          ·
            refine ⟨17096283062322781278978391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22795044083097041705304521 17096283062322781278978391)
            ·
              refine ⟨25644424593484171918467587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17096283062322781278978391 25644424593484171918467587)
              ·
                refine ⟨38466636890226257877701381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25644424593484171918467587 38466636890226257877701381)
                ·
                  refine ⟨7212494416917423352069009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38466636890226257877701381 7212494416917423352069009)
                  ·
                    refine ⟨5409370812688067514051757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7212494416917423352069009 5409370812688067514051757)
                    ·
                      refine ⟨2028514054758025317769409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5409370812688067514051757 2028514054758025317769409)
                      ·
                        rfl

theorem cell23_3950517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_3950517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950517 prefixEnd_3950517 := by exact prefixLift 3950517
  have htrace : WordTrace (prefixWord ++ tailWord_3950517) baseStart_3950517 baseEnd_3950517 := by
    simpa [prefixWord, tailWord_3950517, baseEnd_3950517] using wordTrace_append hprefix tailTrace_3950517
  have hstable : (prefixWord ++ tailWord_3950517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950517).length < 2 ^ (prefixWord ++ tailWord_3950517).sum := by decide
  have hdescent : baseEnd_3950517 < baseStart_3950517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950520 : List Nat := [2, 1, 2, 1, 2, 3, 2, 4, 6]
def baseStart_3950520 : Nat := 118140960795 + 3950520 * 2 ^ 59
def prefixEnd_3950520 : Nat := 4983230072969 + 3 ^ 40 * 3950520 * 2
def baseEnd_3950520 : Nat := 225390621688887645114655

theorem tailTrace_3950520 : CollatzResearch.WordTrace tailWord_3950520 prefixEnd_3950520 225390621688887645114655 := by
  unfold tailWord_3950520
  simp only [CollatzResearch.WordTrace]
  refine ⟨72043650823974104972944507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96058201098632139963926009 72043650823974104972944507)
  ·
    refine ⟨108065476235961157459416761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72043650823974104972944507 108065476235961157459416761)
    ·
      refine ⟨81049107176970868094562571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108065476235961157459416761 81049107176970868094562571)
      ·
        refine ⟨121573660765456302141843857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81049107176970868094562571 121573660765456302141843857)
        ·
          refine ⟨91180245574092226606382893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121573660765456302141843857 91180245574092226606382893)
          ·
            refine ⟨34192592090284584977393585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91180245574092226606382893 34192592090284584977393585)
            ·
              refine ⟨25644444067713438733045189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34192592090284584977393585 25644444067713438733045189)
              ·
                refine ⟨4808333262696269762445973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25644444067713438733045189 4808333262696269762445973)
                ·
                  refine ⟨225390621688887645114655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4808333262696269762445973 225390621688887645114655)
                  ·
                    rfl

theorem cell23_3950520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 6].length) (baseStart_3950520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950520 prefixEnd_3950520 := by exact prefixLift 3950520
  have htrace : WordTrace (prefixWord ++ tailWord_3950520) baseStart_3950520 baseEnd_3950520 := by
    simpa [prefixWord, tailWord_3950520, baseEnd_3950520] using wordTrace_append hprefix tailTrace_3950520
  have hstable : (prefixWord ++ tailWord_3950520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950520).length < 2 ^ (prefixWord ++ tailWord_3950520).sum := by decide
  have hdescent : baseEnd_3950520 < baseStart_3950520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950597 : List Nat := [1, 3, 1, 1, 2, 5, 2, 1, 1, 6]
def baseStart_3950597 : Nat := 118140960795 + 3950597 * 2 ^ 59
def prefixEnd_3950597 : Nat := 4983230072969 + 3 ^ 40 * 3950597 * 2
def baseEnd_3950597 : Nat := 676185044403461668256347

theorem tailTrace_3950597 : CollatzResearch.WordTrace tailWord_3950597 prefixEnd_3950597 676185044403461668256347 := by
  unfold tailWord_3950597
  simp only [CollatzResearch.WordTrace]
  refine ⟨144090110068669252096442045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96060073379112834730961363 144090110068669252096442045)
  ·
    refine ⟨54033791275750969536165767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144090110068669252096442045 54033791275750969536165767)
    ·
      refine ⟨81050686913626454304248651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54033791275750969536165767 81050686913626454304248651)
      ·
        refine ⟨121576030370439681456372977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81050686913626454304248651 121576030370439681456372977)
        ·
          refine ⟨91182022777829761092279733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121576030370439681456372977 91182022777829761092279733)
          ·
            refine ⟨8548314635421540102401225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91182022777829761092279733 8548314635421540102401225)
            ·
              refine ⟨6411235976566155076800919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8548314635421540102401225 6411235976566155076800919)
              ·
                refine ⟨9616853964849232615201379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6411235976566155076800919 9616853964849232615201379)
                ·
                  refine ⟨14425280947273848922802069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9616853964849232615201379 14425280947273848922802069)
                  ·
                    refine ⟨676185044403461668256347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14425280947273848922802069 676185044403461668256347)
                    ·
                      rfl

theorem cell23_3950597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_3950597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950597 prefixEnd_3950597 := by exact prefixLift 3950597
  have htrace : WordTrace (prefixWord ++ tailWord_3950597) baseStart_3950597 baseEnd_3950597 := by
    simpa [prefixWord, tailWord_3950597, baseEnd_3950597] using wordTrace_append hprefix tailTrace_3950597
  have hstable : (prefixWord ++ tailWord_3950597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950597).length < 2 ^ (prefixWord ++ tailWord_3950597).sum := by decide
  have hdescent : baseEnd_3950597 < baseStart_3950597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950621 : List Nat := [1, 4, 2, 2, 2, 1, 4, 1, 1, 1, 4]
def baseStart_3950621 : Nat := 118140960795 + 3950621 * 2 ^ 59
def prefixEnd_3950621 : Nat := 4983230072969 + 3 ^ 40 * 3950621 * 2
def baseEnd_3950621 : Nat := 2028567456746092910868931

theorem tailTrace_3950621 : CollatzResearch.WordTrace tailWord_3950621 prefixEnd_3950621 2028567456746092910868931 := by
  unfold tailWord_3950621
  simp only [CollatzResearch.WordTrace]
  refine ⟨144090985420582304195315717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96060656947054869463543811 144090985420582304195315717)
  ·
    refine ⟨27017059766359182036621697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144090985420582304195315717 27017059766359182036621697)
    ·
      refine ⟨20262794824769386527466273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27017059766359182036621697 20262794824769386527466273)
      ·
        refine ⟨15197096118577039895599705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20262794824769386527466273 15197096118577039895599705)
        ·
          refine ⟨11397822088932779921699779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15197096118577039895599705 11397822088932779921699779)
          ·
            refine ⟨17096733133399169882549669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11397822088932779921699779 17096733133399169882549669)
            ·
              refine ⟨3205637462512344352978063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17096733133399169882549669 3205637462512344352978063)
              ·
                refine ⟨4808456193768516529467095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3205637462512344352978063 4808456193768516529467095)
                ·
                  refine ⟨7212684290652774794200643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4808456193768516529467095 7212684290652774794200643)
                  ·
                    refine ⟨10819026435979162191300965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7212684290652774794200643 10819026435979162191300965)
                    ·
                      refine ⟨2028567456746092910868931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10819026435979162191300965 2028567456746092910868931)
                      ·
                        rfl

theorem cell23_3950621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_3950621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950621 prefixEnd_3950621 := by exact prefixLift 3950621
  have htrace : WordTrace (prefixWord ++ tailWord_3950621) baseStart_3950621 baseEnd_3950621 := by
    simpa [prefixWord, tailWord_3950621, baseEnd_3950621] using wordTrace_append hprefix tailTrace_3950621
  have hstable : (prefixWord ++ tailWord_3950621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950621).length < 2 ^ (prefixWord ++ tailWord_3950621).sum := by decide
  have hdescent : baseEnd_3950621 < baseStart_3950621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950631 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 4, 4]
def baseStart_3950631 : Nat := 118140960795 + 3950631 * 2 ^ 59
def prefixEnd_3950631 : Nat := 4983230072969 + 3 ^ 40 * 3950631 * 2
def baseEnd_3950631 : Nat := 676190863850879290581295

theorem tailTrace_3950631 : CollatzResearch.WordTrace tailWord_3950631 prefixEnd_3950631 676190863850879290581295 := by
  unfold tailWord_3950631
  simp only [CollatzResearch.WordTrace]
  refine ⟨144091350150546075903179747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96060900100364050602119831 144091350150546075903179747)
  ·
    refine ⟨216137025225819113854769621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144091350150546075903179747 216137025225819113854769621)
    ·
      refine ⟨5065711528730135480971163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 216137025225819113854769621 5065711528730135480971163)
      ·
        refine ⟨7598567293095203221456745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5065711528730135480971163 7598567293095203221456745)
        ·
          refine ⟨5698925469821402416092559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7598567293095203221456745 5698925469821402416092559)
          ·
            refine ⟨8548388204732103624138839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5698925469821402416092559 8548388204732103624138839)
            ·
              refine ⟨12822582307098155436208259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8548388204732103624138839 12822582307098155436208259)
              ·
                refine ⟨19233873460647233154312389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12822582307098155436208259 19233873460647233154312389)
                ·
                  refine ⟨3606351273871356216433573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19233873460647233154312389 3606351273871356216433573)
                  ·
                    refine ⟨676190863850879290581295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3606351273871356216433573 676190863850879290581295)
                    ·
                      rfl

theorem cell23_3950631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_3950631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950631 prefixEnd_3950631 := by exact prefixLift 3950631
  have htrace : WordTrace (prefixWord ++ tailWord_3950631) baseStart_3950631 baseEnd_3950631 := by
    simpa [prefixWord, tailWord_3950631, baseEnd_3950631] using wordTrace_append hprefix tailTrace_3950631
  have hstable : (prefixWord ++ tailWord_3950631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950631).length < 2 ^ (prefixWord ++ tailWord_3950631).sum := by decide
  have hdescent : baseEnd_3950631 < baseStart_3950631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950638 : List Nat := [4, 1, 3, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_3950638 : Nat := 118140960795 + 3950638 * 2 ^ 59
def prefixEnd_3950638 : Nat := 4983230072969 + 3 ^ 40 * 3950638 * 2
def baseEnd_3950638 : Nat := 2028576185917219344356353

theorem tailTrace_3950638 : CollatzResearch.WordTrace tailWord_3950638 prefixEnd_3950638 2028576185917219344356353 := by
  unfold tailWord_3950638
  simp only [CollatzResearch.WordTrace]
  refine ⟨18011450682690089512335571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96061070307680477399123045 18011450682690089512335571)
  ·
    refine ⟨27017176024035134268503357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18011450682690089512335571 27017176024035134268503357)
    ·
      refine ⟨10131441009013175350688759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27017176024035134268503357 10131441009013175350688759)
      ·
        refine ⟨15197161513519763026033139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10131441009013175350688759 15197161513519763026033139)
        ·
          refine ⟨22795742270279644539049709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15197161513519763026033139 22795742270279644539049709)
          ·
            refine ⟨8548403351354866702143641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22795742270279644539049709 8548403351354866702143641)
            ·
              refine ⟨6411302513516150026607731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8548403351354866702143641 6411302513516150026607731)
              ·
                refine ⟨9616953770274225039911597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6411302513516150026607731 9616953770274225039911597)
                ·
                  refine ⟨3606357663852834389966849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9616953770274225039911597 3606357663852834389966849)
                  ·
                    refine ⟨2704768247889625792475137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3606357663852834389966849 2704768247889625792475137)
                    ·
                      refine ⟨2028576185917219344356353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2704768247889625792475137 2028576185917219344356353)
                      ·
                        rfl

theorem cell23_3950638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_3950638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950638 prefixEnd_3950638 := by exact prefixLift 3950638
  have htrace : WordTrace (prefixWord ++ tailWord_3950638) baseStart_3950638 baseEnd_3950638 := by
    simpa [prefixWord, tailWord_3950638, baseEnd_3950638] using wordTrace_append hprefix tailTrace_3950638
  have hstable : (prefixWord ++ tailWord_3950638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950638).length < 2 ^ (prefixWord ++ tailWord_3950638).sum := by decide
  have hdescent : baseEnd_3950638 < baseStart_3950638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950697 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 2, 4, 3]
def baseStart_3950697 : Nat := 118140960795 + 3950697 * 2 ^ 59
def prefixEnd_3950697 : Nat := 4983230072969 + 3 ^ 40 * 3950697 * 2
def baseEnd_3950697 : Nat := 2028606481275834613518581

theorem tailTrace_3950697 : CollatzResearch.WordTrace tailWord_3950697 prefixEnd_3950697 2028606481275834613518581 := by
  unfold tailWord_3950697
  simp only [CollatzResearch.WordTrace]
  refine ⟨144093757368306969175082345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96062504912204646116721563 144093757368306969175082345)
  ·
    refine ⟨108070318026230226881311759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144093757368306969175082345 108070318026230226881311759)
    ·
      refine ⟨162105477039345340321967639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108070318026230226881311759 162105477039345340321967639)
      ·
        refine ⟨243158215559018010482951459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162105477039345340321967639 243158215559018010482951459)
        ·
          refine ⟨364737323338527015724427189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243158215559018010482951459 364737323338527015724427189)
          ·
            refine ⟨34194124062986907724165049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 364737323338527015724427189 34194124062986907724165049)
            ·
              refine ⟨25645593047240180793123787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34194124062986907724165049 25645593047240180793123787)
              ·
                refine ⟨38468389570860271189685681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25645593047240180793123787 38468389570860271189685681)
                ·
                  refine ⟨28851292178145203392264261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38468389570860271189685681 28851292178145203392264261)
                  ·
                    refine ⟨5409617283402225636049549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28851292178145203392264261 5409617283402225636049549)
                    ·
                      refine ⟨2028606481275834613518581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5409617283402225636049549 2028606481275834613518581)
                      ·
                        rfl

theorem cell23_3950697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 4, 3].length) (baseStart_3950697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950697 prefixEnd_3950697 := by exact prefixLift 3950697
  have htrace : WordTrace (prefixWord ++ tailWord_3950697) baseStart_3950697 baseEnd_3950697 := by
    simpa [prefixWord, tailWord_3950697, baseEnd_3950697] using wordTrace_append hprefix tailTrace_3950697
  have hstable : (prefixWord ++ tailWord_3950697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950697).length < 2 ^ (prefixWord ++ tailWord_3950697).sum := by decide
  have hdescent : baseEnd_3950697 < baseStart_3950697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950747 : List Nat := [1, 1, 1, 1, 1, 1, 2, 8, 2, 5]
def baseStart_3950747 : Nat := 118140960795 + 3950747 * 2 ^ 59
def prefixEnd_3950747 : Nat := 4983230072969 + 3 ^ 40 * 3950747 * 2
def baseEnd_3950747 : Nat := 676210718436186472631117

theorem tailTrace_3950747 : CollatzResearch.WordTrace tailWord_3950747 prefixEnd_3950747 676210718436186472631117 := by
  unfold tailWord_3950747
  simp only [CollatzResearch.WordTrace]
  refine ⟨144095581018125827714402495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96063720678750551809601663 144095581018125827714402495)
  ·
    refine ⟨216143371527188741571603743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144095581018125827714402495 216143371527188741571603743)
    ·
      refine ⟨324215057290783112357405615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216143371527188741571603743 324215057290783112357405615)
      ·
        refine ⟨486322585936174668536108423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324215057290783112357405615 486322585936174668536108423)
        ·
          refine ⟨729483878904262002804162635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486322585936174668536108423 729483878904262002804162635)
          ·
            refine ⟨1094225818356393004206243953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729483878904262002804162635 1094225818356393004206243953)
            ·
              refine ⟨820669363767294753154682965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1094225818356393004206243953 820669363767294753154682965)
              ·
                refine ⟨9617219106647985388531441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 820669363767294753154682965 9617219106647985388531441)
                ·
                  refine ⟨7212914329985989041398581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9617219106647985388531441 7212914329985989041398581)
                  ·
                    refine ⟨676210718436186472631117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7212914329985989041398581 676210718436186472631117)
                    ·
                      rfl

theorem cell23_3950747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 5].length) (baseStart_3950747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950747 prefixEnd_3950747 := by exact prefixLift 3950747
  have htrace : WordTrace (prefixWord ++ tailWord_3950747) baseStart_3950747 baseEnd_3950747 := by
    simpa [prefixWord, tailWord_3950747, baseEnd_3950747] using wordTrace_append hprefix tailTrace_3950747
  have hstable : (prefixWord ++ tailWord_3950747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950747).length < 2 ^ (prefixWord ++ tailWord_3950747).sum := by decide
  have hdescent : baseEnd_3950747 < baseStart_3950747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950751 : List Nat := [1, 1, 2, 6, 1, 2, 1, 4, 5]
def baseStart_3950751 : Nat := 118140960795 + 3950751 * 2 ^ 59
def prefixEnd_3950751 : Nat := 4983230072969 + 3 ^ 40 * 3950751 * 2
def baseEnd_3950751 : Nat := 225403801025686378027037

theorem tailTrace_3950751 : CollatzResearch.WordTrace tailWord_3950751 prefixEnd_3950751 225403801025686378027037 := by
  unfold tailWord_3950751
  simp only [CollatzResearch.WordTrace]
  refine ⟨144095726910111336397548107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96063817940074224265032071 144095726910111336397548107)
  ·
    refine ⟨216143590365167004596322161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144095726910111336397548107 216143590365167004596322161)
    ·
      refine ⟨162107692773875253447241621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216143590365167004596322161 162107692773875253447241621)
      ·
        refine ⟨7598798098775402505339451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 162107692773875253447241621 7598798098775402505339451)
        ·
          refine ⟨11398197148163103758009177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7598798098775402505339451 11398197148163103758009177)
          ·
            refine ⟨8548647861122327818506883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11398197148163103758009177 8548647861122327818506883)
            ·
              refine ⟨12822971791683491727760325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8548647861122327818506883 12822971791683491727760325)
              ·
                refine ⟨2404307210940654698955061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12822971791683491727760325 2404307210940654698955061)
                ·
                  refine ⟨225403801025686378027037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2404307210940654698955061 225403801025686378027037)
                  ·
                    rfl

theorem cell23_3950751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 5].length) (baseStart_3950751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950751 prefixEnd_3950751 := by exact prefixLift 3950751
  have htrace : WordTrace (prefixWord ++ tailWord_3950751) baseStart_3950751 baseEnd_3950751 := by
    simpa [prefixWord, tailWord_3950751, baseEnd_3950751] using wordTrace_append hprefix tailTrace_3950751
  have hstable : (prefixWord ++ tailWord_3950751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950751).length < 2 ^ (prefixWord ++ tailWord_3950751).sum := by decide
  have hdescent : baseEnd_3950751 < baseStart_3950751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950757 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 5]
def baseStart_3950757 : Nat := 118140960795 + 3950757 * 2 ^ 59
def prefixEnd_3950757 : Nat := 4983230072969 + 3 ^ 40 * 3950757 * 2
def baseEnd_3950757 : Nat := 2028637290115104378768305

theorem tailTrace_3950757 : CollatzResearch.WordTrace tailWord_3950757 prefixEnd_3950757 2028637290115104378768305 := by
  unfold tailWord_3950757
  simp only [CollatzResearch.WordTrace]
  refine ⟨144095945748089599422266525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96063963832059732948177683 144095945748089599422266525)
  ·
    refine ⟨54035979655533599783349947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144095945748089599422266525 54035979655533599783349947)
    ·
      refine ⟨81053969483300399675024921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54035979655533599783349947 81053969483300399675024921)
      ·
        refine ⟨60790477112475299756268691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81053969483300399675024921 60790477112475299756268691)
        ·
          refine ⟨91185715668712949634403037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60790477112475299756268691 91185715668712949634403037)
          ·
            refine ⟨34194643375767356112901139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91185715668712949634403037 34194643375767356112901139)
            ·
              refine ⟨51291965063651034169351709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34194643375767356112901139 51291965063651034169351709)
              ·
                refine ⟨19234486898869137813506891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51291965063651034169351709 19234486898869137813506891)
                ·
                  refine ⟨28851730348303706720260337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19234486898869137813506891 28851730348303706720260337)
                  ·
                    refine ⟨21638797761227780040195253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28851730348303706720260337 21638797761227780040195253)
                    ·
                      refine ⟨2028637290115104378768305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21638797761227780040195253 2028637290115104378768305)
                      ·
                        rfl

theorem cell23_3950757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_3950757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950757 prefixEnd_3950757 := by exact prefixLift 3950757
  have htrace : WordTrace (prefixWord ++ tailWord_3950757) baseStart_3950757 baseEnd_3950757 := by
    simpa [prefixWord, tailWord_3950757, baseEnd_3950757] using wordTrace_append hprefix tailTrace_3950757
  have hstable : (prefixWord ++ tailWord_3950757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950757).length < 2 ^ (prefixWord ++ tailWord_3950757).sum := by decide
  have hdescent : baseEnd_3950757 < baseStart_3950757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950767 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 4]
def baseStart_3950767 : Nat := 118140960795 + 3950767 * 2 ^ 59
def prefixEnd_3950767 : Nat := 4983230072969 + 3 ^ 40 * 3950767 * 2
def baseEnd_3950767 : Nat := 2028642424921649339643259

theorem tailTrace_3950767 : CollatzResearch.WordTrace tailWord_3950767 prefixEnd_3950767 2028642424921649339643259 := by
  unfold tailWord_3950767
  simp only [CollatzResearch.WordTrace]
  refine ⟨144096310478053371130130555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96064206985368914086753703 144096310478053371130130555)
  ·
    refine ⟨216144465717080056695195833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144096310478053371130130555 216144465717080056695195833)
    ·
      refine ⟨162108349287810042521396875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216144465717080056695195833 162108349287810042521396875)
      ·
        refine ⟨243162523931715063782095313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162108349287810042521396875 243162523931715063782095313)
        ·
          refine ⟨182371892948786297836571485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243162523931715063782095313 182371892948786297836571485)
          ·
            refine ⟨68389459855794861688714307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182371892948786297836571485 68389459855794861688714307)
            ·
              refine ⟨102584189783692292533071461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68389459855794861688714307 102584189783692292533071461)
              ·
                refine ⟨19234535584442304849950899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102584189783692292533071461 19234535584442304849950899)
                ·
                  refine ⟨28851803376663457274926349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19234535584442304849950899 28851803376663457274926349)
                  ·
                    refine ⟨10819426266248796478097381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28851803376663457274926349 10819426266248796478097381)
                    ·
                      refine ⟨2028642424921649339643259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10819426266248796478097381 2028642424921649339643259)
                      ·
                        rfl

theorem cell23_3950767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_3950767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950767 prefixEnd_3950767 := by exact prefixLift 3950767
  have htrace : WordTrace (prefixWord ++ tailWord_3950767) baseStart_3950767 baseEnd_3950767 := by
    simpa [prefixWord, tailWord_3950767, baseEnd_3950767] using wordTrace_append hprefix tailTrace_3950767
  have hstable : (prefixWord ++ tailWord_3950767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950767).length < 2 ^ (prefixWord ++ tailWord_3950767).sum := by decide
  have hdescent : baseEnd_3950767 < baseStart_3950767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950784 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 4]
def baseStart_3950784 : Nat := 118140960795 + 3950784 * 2 ^ 59
def prefixEnd_3950784 : Nat := 4983230072969 + 3 ^ 40 * 3950784 * 2
def baseEnd_3950784 : Nat := 2028651154092775773130681

theorem tailTrace_3950784 : CollatzResearch.WordTrace tailWord_3950784 prefixEnd_3950784 2028651154092775773130681 := by
  unfold tailWord_3950784
  simp only [CollatzResearch.WordTrace]
  refine ⟨72048465259495891516749703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96064620345994522022332937 72048465259495891516749703)
  ·
    refine ⟨108072697889243837275124555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72048465259495891516749703 108072697889243837275124555)
    ·
      refine ⟨162109046833865755912686833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108072697889243837275124555 162109046833865755912686833)
      ·
        refine ⟨121581785125399316934515125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162109046833865755912686833 121581785125399316934515125)
        ·
          refine ⟨11398292355506185962610793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121581785125399316934515125 11398292355506185962610793)
          ·
            refine ⟨8548719266629639471958095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11398292355506185962610793 8548719266629639471958095)
            ·
              refine ⟨12823078899944459207937143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8548719266629639471958095 12823078899944459207937143)
              ·
                refine ⟨19234618349916688811905715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12823078899944459207937143 19234618349916688811905715)
                ·
                  refine ⟨28851927524875033217858573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19234618349916688811905715 28851927524875033217858573)
                  ·
                    refine ⟨10819472821828137456696965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28851927524875033217858573 10819472821828137456696965)
                    ·
                      refine ⟨2028651154092775773130681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10819472821828137456696965 2028651154092775773130681)
                      ·
                        rfl

theorem cell23_3950784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_3950784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950784 prefixEnd_3950784 := by exact prefixLift 3950784
  have htrace : WordTrace (prefixWord ++ tailWord_3950784) baseStart_3950784 baseEnd_3950784 := by
    simpa [prefixWord, tailWord_3950784, baseEnd_3950784] using wordTrace_append hprefix tailTrace_3950784
  have hstable : (prefixWord ++ tailWord_3950784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950784).length < 2 ^ (prefixWord ++ tailWord_3950784).sum := by decide
  have hdescent : baseEnd_3950784 < baseStart_3950784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950794 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 5, 4]
def baseStart_3950794 : Nat := 118140960795 + 3950794 * 2 ^ 59
def prefixEnd_3950794 : Nat := 4983230072969 + 3 ^ 40 * 3950794 * 2
def baseEnd_3950794 : Nat := 676218762966440244668545

theorem tailTrace_3950794 : CollatzResearch.WordTrace tailWord_3950794 prefixEnd_3950794 676218762966440244668545 := by
  unfold tailWord_3950794
  simp only [CollatzResearch.WordTrace]
  refine ⟨36024323812238888685340859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96064863499303703160908957 36024323812238888685340859)
  ·
    refine ⟨54036485718358333028011289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36024323812238888685340859 54036485718358333028011289)
    ·
      refine ⟨40527364288768749771008467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54036485718358333028011289 40527364288768749771008467)
      ·
        refine ⟨60791046433153124656512701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40527364288768749771008467 60791046433153124656512701)
        ·
          refine ⟨22796642412432421746192263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60791046433153124656512701 22796642412432421746192263)
          ·
            refine ⟨34194963618648632619288395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22796642412432421746192263 34194963618648632619288395)
            ·
              refine ⟨51292445427972948928932593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34194963618648632619288395 51292445427972948928932593)
              ·
                refine ⟨38469334070979711696699445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51292445427972948928932593 38469334070979711696699445)
                ·
                  refine ⟨3606500069154347971565573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38469334070979711696699445 3606500069154347971565573)
                  ·
                    refine ⟨676218762966440244668545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3606500069154347971565573 676218762966440244668545)
                    ·
                      rfl

theorem cell23_3950794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_3950794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950794 prefixEnd_3950794 := by exact prefixLift 3950794
  have htrace : WordTrace (prefixWord ++ tailWord_3950794) baseStart_3950794 baseEnd_3950794 := by
    simpa [prefixWord, tailWord_3950794, baseEnd_3950794] using wordTrace_append hprefix tailTrace_3950794
  have hstable : (prefixWord ++ tailWord_3950794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950794).length < 2 ^ (prefixWord ++ tailWord_3950794).sum := by decide
  have hdescent : baseEnd_3950794 < baseStart_3950794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950827 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 6]
def baseStart_3950827 : Nat := 118140960795 + 3950827 * 2 ^ 59
def prefixEnd_3950827 : Nat := 4983230072969 + 3 ^ 40 * 3950827 * 2
def baseEnd_3950827 : Nat := 2028673233760919104892983

theorem tailTrace_3950827 : CollatzResearch.WordTrace tailWord_3950827 prefixEnd_3950827 2028673233760919104892983 := by
  unfold tailWord_3950827
  simp only [CollatzResearch.WordTrace]
  refine ⟨144098498857836001377314735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96065665905224000918209823 144098498857836001377314735)
  ·
    refine ⟨216147748286754002065972103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144098498857836001377314735 216147748286754002065972103)
    ·
      refine ⟨324221622430131003098958155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216147748286754002065972103 324221622430131003098958155)
      ·
        refine ⟨486332433645196504648437233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324221622430131003098958155 486332433645196504648437233)
        ·
          refine ⟨364749325233897378486327925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486332433645196504648437233 364749325233897378486327925)
          ·
            refine ⟨34195249240677879233093243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 364749325233897378486327925 34195249240677879233093243)
            ·
              refine ⟨51292873861016818849639865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34195249240677879233093243 51292873861016818849639865)
              ·
                refine ⟨38469655395762614137229899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51292873861016818849639865 38469655395762614137229899)
                ·
                  refine ⟨57704483093643921205844849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38469655395762614137229899 57704483093643921205844849)
                  ·
                    refine ⟨43278362320232940904383637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57704483093643921205844849 43278362320232940904383637)
                    ·
                      refine ⟨2028673233760919104892983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43278362320232940904383637 2028673233760919104892983)
                      ·
                        rfl

theorem cell23_3950827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 6].length) (baseStart_3950827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950827 prefixEnd_3950827 := by exact prefixLift 3950827
  have htrace : WordTrace (prefixWord ++ tailWord_3950827) baseStart_3950827 baseEnd_3950827 := by
    simpa [prefixWord, tailWord_3950827, baseEnd_3950827] using wordTrace_append hprefix tailTrace_3950827
  have hstable : (prefixWord ++ tailWord_3950827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950827).length < 2 ^ (prefixWord ++ tailWord_3950827).sum := by decide
  have hdescent : baseEnd_3950827 < baseStart_3950827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950904 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 3, 2, 4]
def baseStart_3950904 : Nat := 118140960795 + 3950904 * 2 ^ 59
def prefixEnd_3950904 : Nat := 4983230072969 + 3 ^ 40 * 3950904 * 2
def baseEnd_3950904 : Nat := 2028712771771315303630129

theorem tailTrace_3950904 : CollatzResearch.WordTrace tailWord_3950904 prefixEnd_3950904 2028712771771315303630129 := by
  unfold tailWord_3950904
  simp only [CollatzResearch.WordTrace]
  refine ⟨72050653639278521763933883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96067538185704695685245177 72050653639278521763933883)
  ·
    refine ⟨108075980458917782645900825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72050653639278521763933883 108075980458917782645900825)
    ·
      refine ⟨81056985344188336984425619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108075980458917782645900825 81056985344188336984425619)
      ·
        refine ⟨121585478016282505476638429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81056985344188336984425619 121585478016282505476638429)
        ·
          refine ⟨45594554256105939553739411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121585478016282505476638429 45594554256105939553739411)
          ·
            refine ⟨68391831384158909330609117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45594554256105939553739411 68391831384158909330609117)
            ·
              refine ⟨25646936769059590998978419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68391831384158909330609117 25646936769059590998978419)
              ·
                refine ⟨38470405153589386498467629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25646936769059590998978419 38470405153589386498467629)
                ·
                  refine ⟨14426401932596019936925361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38470405153589386498467629 14426401932596019936925361)
                  ·
                    refine ⟨10819801449447014952694021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14426401932596019936925361 10819801449447014952694021)
                    ·
                      refine ⟨2028712771771315303630129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10819801449447014952694021 2028712771771315303630129)
                      ·
                        rfl

theorem cell23_3950904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_3950904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950904 prefixEnd_3950904 := by exact prefixLift 3950904
  have htrace : WordTrace (prefixWord ++ tailWord_3950904) baseStart_3950904 baseEnd_3950904 := by
    simpa [prefixWord, tailWord_3950904, baseEnd_3950904] using wordTrace_append hprefix tailTrace_3950904
  have hstable : (prefixWord ++ tailWord_3950904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950904).length < 2 ^ (prefixWord ++ tailWord_3950904).sum := by decide
  have hdescent : baseEnd_3950904 < baseStart_3950904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950908 : List Nat := [2, 2, 2, 2, 1, 2, 5, 1, 1, 1, 4]
def baseStart_3950908 : Nat := 118140960795 + 3950908 * 2 ^ 59
def prefixEnd_3950908 : Nat := 4983230072969 + 3 ^ 40 * 3950908 * 2
def baseEnd_3950908 : Nat := 2028714825693933287980111

theorem tailTrace_3950908 : CollatzResearch.WordTrace tailWord_3950908 prefixEnd_3950908 2028714825693933287980111 := by
  unfold tailWord_3950908
  simp only [CollatzResearch.WordTrace]
  refine ⟨72050726585271276105506689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96067635447028368140675585 72050726585271276105506689)
  ·
    refine ⟨54038044938953457079130017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72050726585271276105506689 54038044938953457079130017)
    ·
      refine ⟨40528533704215092809347513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54038044938953457079130017 40528533704215092809347513)
      ·
        refine ⟨30396400278161319607010635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40528533704215092809347513 30396400278161319607010635)
        ·
          refine ⟨45594600417241979410515953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30396400278161319607010635 45594600417241979410515953)
          ·
            refine ⟨34195950312931484557886965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45594600417241979410515953 34195950312931484557886965)
            ·
              refine ⟨3205870341837326677301903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34195950312931484557886965 3205870341837326677301903)
              ·
                refine ⟨4808805512755990015952855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3205870341837326677301903 4808805512755990015952855)
                ·
                  refine ⟨7213208269133985023929283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4808805512755990015952855 7213208269133985023929283)
                  ·
                    refine ⟨10819812403700977535893925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7213208269133985023929283 10819812403700977535893925)
                    ·
                      refine ⟨2028714825693933287980111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10819812403700977535893925 2028714825693933287980111)
                      ·
                        rfl

theorem cell23_3950908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_3950908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3950908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3950908 prefixEnd_3950908 := by exact prefixLift 3950908
  have htrace : WordTrace (prefixWord ++ tailWord_3950908) baseStart_3950908 baseEnd_3950908 := by
    simpa [prefixWord, tailWord_3950908, baseEnd_3950908] using wordTrace_append hprefix tailTrace_3950908
  have hstable : (prefixWord ++ tailWord_3950908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950908).length < 2 ^ (prefixWord ++ tailWord_3950908).sum := by decide
  have hdescent : baseEnd_3950908 < baseStart_3950908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951015 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_3951015 : Nat := 118140960795 + 3951015 * 2 ^ 59
def prefixEnd_3951015 : Nat := 4983230072969 + 3 ^ 40 * 3951015 * 2
def baseEnd_3951015 : Nat := 2028769768123964369342119

theorem tailTrace_3951015 : CollatzResearch.WordTrace tailWord_3951015 prefixEnd_3951015 2028769768123964369342119 := by
  unfold tailWord_3951015
  simp only [CollatzResearch.WordTrace]
  refine ⟨144105355781154909485158499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96070237187436606323438999 144105355781154909485158499)
  ·
    refine ⟨216158033671732364227737749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144105355781154909485158499 216158033671732364227737749)
    ·
      refine ⟨10132407828362454573175207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 216158033671732364227737749 10132407828362454573175207)
      ·
        refine ⟨15198611742543681859762811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10132407828362454573175207 15198611742543681859762811)
        ·
          refine ⟨22797917613815522789644217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15198611742543681859762811 22797917613815522789644217)
          ·
            refine ⟨17098438210361642092233163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22797917613815522789644217 17098438210361642092233163)
            ·
              refine ⟨25647657315542463138349745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17098438210361642092233163 25647657315542463138349745)
              ·
                refine ⟨19235742986656847353762309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25647657315542463138349745 19235742986656847353762309)
                ·
                  refine ⟨3606701809998158878830433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19235742986656847353762309 3606701809998158878830433)
                  ·
                    refine ⟨2705026357498619159122825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3606701809998158878830433 2705026357498619159122825)
                    ·
                      refine ⟨2028769768123964369342119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2705026357498619159122825 2028769768123964369342119)
                      ·
                        rfl

theorem cell23_3951015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_3951015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951015 prefixEnd_3951015 := by exact prefixLift 3951015
  have htrace : WordTrace (prefixWord ++ tailWord_3951015) baseStart_3951015 baseEnd_3951015 := by
    simpa [prefixWord, tailWord_3951015, baseEnd_3951015] using wordTrace_append hprefix tailTrace_3951015
  have hstable : (prefixWord ++ tailWord_3951015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951015).length < 2 ^ (prefixWord ++ tailWord_3951015).sum := by decide
  have hdescent : baseEnd_3951015 < baseStart_3951015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951038 : List Nat := [4, 2, 1, 1, 1, 1, 2, 6, 5]
def baseStart_3951038 : Nat := 118140960795 + 3951038 * 2 ^ 59
def prefixEnd_3951038 : Nat := 4983230072969 + 3 ^ 40 * 3951038 * 2
def baseEnd_3951038 : Nat := 225420175353224197706057

theorem tailTrace_3951038 : CollatzResearch.WordTrace tailWord_3951038 prefixEnd_3951038 225420175353224197706057 := by
  unfold tailWord_3951038
  simp only [CollatzResearch.WordTrace]
  refine ⟨18013274332508948051655721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96070796440047722942163845 18013274332508948051655721)
  ·
    refine ⟨13509955749381711038741791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18013274332508948051655721 13509955749381711038741791)
    ·
      refine ⟨20264933624072566558112687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13509955749381711038741791 20264933624072566558112687)
      ·
        refine ⟨30397400436108849837169031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20264933624072566558112687 30397400436108849837169031)
        ·
          refine ⟨45596100654163274755753547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30397400436108849837169031 45596100654163274755753547)
          ·
            refine ⟨68394150981244912133630321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45596100654163274755753547 68394150981244912133630321)
            ·
              refine ⟨51295613235933684100222741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68394150981244912133630321 51295613235933684100222741)
              ·
                refine ⟨2404481870434391442197941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51295613235933684100222741 2404481870434391442197941)
                ·
                  refine ⟨225420175353224197706057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2404481870434391442197941 225420175353224197706057)
                  ·
                    rfl

theorem cell23_3951038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_3951038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951038 prefixEnd_3951038 := by exact prefixLift 3951038
  have htrace : WordTrace (prefixWord ++ tailWord_3951038) baseStart_3951038 baseEnd_3951038 := by
    simpa [prefixWord, tailWord_3951038, baseEnd_3951038] using wordTrace_append hprefix tailTrace_3951038
  have hstable : (prefixWord ++ tailWord_3951038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951038).length < 2 ^ (prefixWord ++ tailWord_3951038).sum := by decide
  have hdescent : baseEnd_3951038 < baseStart_3951038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951081 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 7, 4]
def baseStart_3951081 : Nat := 118140960795 + 3951081 * 2 ^ 59
def prefixEnd_3951081 : Nat := 4983230072969 + 3 ^ 40 * 3951081 * 2
def baseEnd_3951081 : Nat := 676267885949053703705605

theorem tailTrace_3951081 : CollatzResearch.WordTrace tailWord_3951081 prefixEnd_3951081 676267885949053703705605 := by
  unfold tailWord_3951081
  simp only [CollatzResearch.WordTrace]
  refine ⟨144107762998915802757061097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96071841999277201838040731 144107762998915802757061097)
  ·
    refine ⟨108080822249186852067795823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144107762998915802757061097 108080822249186852067795823)
    ·
      refine ⟨162121233373780278101693735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108080822249186852067795823 162121233373780278101693735)
      ·
        refine ⟨243181850060670417152540603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162121233373780278101693735 243181850060670417152540603)
        ·
          refine ⟨364772775091005625728810905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243181850060670417152540603 364772775091005625728810905)
          ·
            refine ⟨273579581318254219296608179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364772775091005625728810905 273579581318254219296608179)
            ·
              refine ⟨410369371977381328944912269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273579581318254219296608179 410369371977381328944912269)
              ·
                refine ⟨153888514491517998354342101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410369371977381328944912269 153888514491517998354342101)
                ·
                  refine ⟨3606762058394953086429893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 153888514491517998354342101 3606762058394953086429893)
                  ·
                    refine ⟨676267885949053703705605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3606762058394953086429893 676267885949053703705605)
                    ·
                      rfl

theorem cell23_3951081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 4].length) (baseStart_3951081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951081 prefixEnd_3951081 := by exact prefixLift 3951081
  have htrace : WordTrace (prefixWord ++ tailWord_3951081) baseStart_3951081 baseEnd_3951081 := by
    simpa [prefixWord, tailWord_3951081, baseEnd_3951081] using wordTrace_append hprefix tailTrace_3951081
  have hstable : (prefixWord ++ tailWord_3951081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951081).length < 2 ^ (prefixWord ++ tailWord_3951081).sum := by decide
  have hdescent : baseEnd_3951081 < baseStart_3951081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951088 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 2, 4, 2]
def baseStart_3951088 : Nat := 118140960795 + 3951088 * 2 ^ 59
def prefixEnd_3951088 : Nat := 4983230072969 + 3 ^ 40 * 3951088 * 2
def baseEnd_3951088 : Nat := 2028807252211742583729283

theorem tailTrace_3951088 : CollatzResearch.WordTrace tailWord_3951088 prefixEnd_3951088 2028807252211742583729283 := by
  unfold tailWord_3951088
  simp only [CollatzResearch.WordTrace]
  refine ⟨72054009154945221476282959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96072012206593628635043945 72054009154945221476282959)
  ·
    refine ⟨108081013732417832214424439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72054009154945221476282959 108081013732417832214424439)
    ·
      refine ⟨162121520598626748321636659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108081013732417832214424439 162121520598626748321636659)
      ·
        refine ⟨243182280897940122482454989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162121520598626748321636659 243182280897940122482454989)
        ·
          refine ⟨91193355336727545930920621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243182280897940122482454989 91193355336727545930920621)
          ·
            refine ⟨34197508251272829724095233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91193355336727545930920621 34197508251272829724095233)
            ·
              refine ⟨25648131188454622293071425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34197508251272829724095233 25648131188454622293071425)
              ·
                refine ⟨19236098391340966719803569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25648131188454622293071425 19236098391340966719803569)
                ·
                  refine ⟨14427073793505725039852677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19236098391340966719803569 14427073793505725039852677)
                  ·
                    refine ⟨2705076336282323444972377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14427073793505725039852677 2705076336282323444972377)
                    ·
                      refine ⟨2028807252211742583729283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2705076336282323444972377 2028807252211742583729283)
                      ·
                        rfl

theorem cell23_3951088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 4, 2].length) (baseStart_3951088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951088 prefixEnd_3951088 := by exact prefixLift 3951088
  have htrace : WordTrace (prefixWord ++ tailWord_3951088) baseStart_3951088 baseEnd_3951088 := by
    simpa [prefixWord, tailWord_3951088, baseEnd_3951088] using wordTrace_append hprefix tailTrace_3951088
  have hstable : (prefixWord ++ tailWord_3951088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951088).length < 2 ^ (prefixWord ++ tailWord_3951088).sum := by decide
  have hdescent : baseEnd_3951088 < baseStart_3951088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951105 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 2, 4, 2]
def baseStart_3951105 : Nat := 118140960795 + 3951105 * 2 ^ 59
def prefixEnd_3951105 : Nat := 4983230072969 + 3 ^ 40 * 3951105 * 2
def baseEnd_3951105 : Nat := 2028815981382869017216705

theorem tailTrace_3951105 : CollatzResearch.WordTrace tailWord_3951105 prefixEnd_3951105 2028815981382869017216705 := by
  unfold tailWord_3951105
  simp only [CollatzResearch.WordTrace]
  refine ⟨144108638350828854855934769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96072425567219236570623179 144108638350828854855934769)
  ·
    refine ⟨108081478763121641141951077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144108638350828854855934769 108081478763121641141951077)
    ·
      refine ⟨20265277268085307714115827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108081478763121641141951077 20265277268085307714115827)
      ·
        refine ⟨30397915902127961571173741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20265277268085307714115827 30397915902127961571173741)
        ·
          refine ⟨11399218463297985589190153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30397915902127961571173741 11399218463297985589190153)
          ·
            refine ⟨8549413847473489191892615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11399218463297985589190153 8549413847473489191892615)
            ·
              refine ⟨12824120771210233787838923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8549413847473489191892615 12824120771210233787838923)
              ·
                refine ⟨19236181156815350681758385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12824120771210233787838923 19236181156815350681758385)
                ·
                  refine ⟨14427135867611513011318789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19236181156815350681758385 14427135867611513011318789)
                  ·
                    refine ⟨2705087975177158689622273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14427135867611513011318789 2705087975177158689622273)
                    ·
                      refine ⟨2028815981382869017216705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2705087975177158689622273 2028815981382869017216705)
                      ·
                        rfl

theorem cell23_3951105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_3951105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951105 prefixEnd_3951105 := by exact prefixLift 3951105
  have htrace : WordTrace (prefixWord ++ tailWord_3951105) baseStart_3951105 baseEnd_3951105 := by
    simpa [prefixWord, tailWord_3951105, baseEnd_3951105] using wordTrace_append hprefix tailTrace_3951105
  have hstable : (prefixWord ++ tailWord_3951105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951105).length < 2 ^ (prefixWord ++ tailWord_3951105).sum := by decide
  have hdescent : baseEnd_3951105 < baseStart_3951105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951121 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 3]
def baseStart_3951121 : Nat := 118140960795 + 3951121 * 2 ^ 59
def prefixEnd_3951121 : Nat := 4983230072969 + 3 ^ 40 * 3951121 * 2
def baseEnd_3951121 : Nat := 2028824197073340954616631

theorem tailTrace_3951121 : CollatzResearch.WordTrace tailWord_3951121 prefixEnd_3951121 2028824197073340954616631 := by
  unfold tailWord_3951121
  simp only [CollatzResearch.WordTrace]
  refine ⟨144109221918770889588517217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96072814612513926392344811 144109221918770889588517217)
  ·
    refine ⟨108081916439078167191387913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144109221918770889588517217 108081916439078167191387913)
    ·
      refine ⟨81061437329308625393540935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108081916439078167191387913 81061437329308625393540935)
      ·
        refine ⟨121592155993962938090311403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81061437329308625393540935 121592155993962938090311403)
        ·
          refine ⟨182388233990944407135467105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121592155993962938090311403 182388233990944407135467105)
          ·
            refine ⟨136791175493208305351600329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182388233990944407135467105 136791175493208305351600329)
            ·
              refine ⟨102593381619906229013700247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136791175493208305351600329 102593381619906229013700247)
              ·
                refine ⟨153890072429859343520550371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102593381619906229013700247 153890072429859343520550371)
                ·
                  refine ⟨230835108644789015280825557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153890072429859343520550371 230835108644789015280825557)
                  ·
                    refine ⟨5410197858862242545644349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 230835108644789015280825557 5410197858862242545644349)
                    ·
                      refine ⟨2028824197073340954616631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5410197858862242545644349 2028824197073340954616631)
                      ·
                        rfl

theorem cell23_3951121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_3951121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951121 prefixEnd_3951121 := by exact prefixLift 3951121
  have htrace : WordTrace (prefixWord ++ tailWord_3951121) baseStart_3951121 baseEnd_3951121 := by
    simpa [prefixWord, tailWord_3951121, baseEnd_3951121] using wordTrace_append hprefix tailTrace_3951121
  have hstable : (prefixWord ++ tailWord_3951121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951121).length < 2 ^ (prefixWord ++ tailWord_3951121).sum := by decide
  have hdescent : baseEnd_3951121 < baseStart_3951121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951132 : List Nat := [2, 2, 3, 1, 2, 3, 2, 3, 1, 4]
def baseStart_3951132 : Nat := 118140960795 + 3951132 * 2 ^ 59
def prefixEnd_3951132 : Nat := 4983230072969 + 3 ^ 40 * 3951132 * 2
def baseEnd_3951132 : Nat := 676276615120180137193027

theorem tailTrace_3951132 : CollatzResearch.WordTrace tailWord_3951132 prefixEnd_3951132 676276615120180137193027 := by
  unfold tailWord_3951132
  simp only [CollatzResearch.WordTrace]
  refine ⟨72054811560865519233583825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96073082081154025644778433 72054811560865519233583825)
  ·
    refine ⟨54041108670649139425187869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72054811560865519233583825 54041108670649139425187869)
    ·
      refine ⟨20265415751493427284445451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54041108670649139425187869 20265415751493427284445451)
      ·
        refine ⟨30398123627240140926668177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20265415751493427284445451 30398123627240140926668177)
        ·
          refine ⟨22798592720430105695001133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30398123627240140926668177 22798592720430105695001133)
          ·
            refine ⟨8549472270161289635625425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22798592720430105695001133 8549472270161289635625425)
            ·
              refine ⟨6412104202620967226719069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8549472270161289635625425 6412104202620967226719069)
              ·
                refine ⟨2404539075982862710019651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6412104202620967226719069 2404539075982862710019651)
                ·
                  refine ⟨3606808613974294065029477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2404539075982862710019651 3606808613974294065029477)
                  ·
                    refine ⟨676276615120180137193027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3606808613974294065029477 676276615120180137193027)
                    ·
                      rfl

theorem cell23_3951132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_3951132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951132 prefixEnd_3951132 := by exact prefixLift 3951132
  have htrace : WordTrace (prefixWord ++ tailWord_3951132) baseStart_3951132 baseEnd_3951132 := by
    simpa [prefixWord, tailWord_3951132, baseEnd_3951132] using wordTrace_append hprefix tailTrace_3951132
  have hstable : (prefixWord ++ tailWord_3951132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951132).length < 2 ^ (prefixWord ++ tailWord_3951132).sum := by decide
  have hdescent : baseEnd_3951132 < baseStart_3951132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951155 : List Nat := [1, 1, 1, 2, 4, 2, 4, 1, 3, 1, 3]
def baseStart_3951155 : Nat := 118140960795 + 3951155 * 2 ^ 59
def prefixEnd_3951155 : Nat := 4983230072969 + 3 ^ 40 * 3951155 * 2
def baseEnd_3951155 : Nat := 2028841655415593821591475

theorem tailTrace_3951155 : CollatzResearch.WordTrace tailWord_3951155 prefixEnd_3951155 2028841655415593821591475 := by
  unfold tailWord_3951155
  simp only [CollatzResearch.WordTrace]
  refine ⟨144110462000647713395254919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96073641333765142263503279 144110462000647713395254919)
  ·
    refine ⟨216165693000971570092882379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144110462000647713395254919 216165693000971570092882379)
    ·
      refine ⟨324248539501457355139323569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216165693000971570092882379 324248539501457355139323569)
      ·
        refine ⟨243186404626093016354492677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324248539501457355139323569 243186404626093016354492677)
        ·
          refine ⟨45597450867392440566467377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243186404626093016354492677 45597450867392440566467377)
          ·
            refine ⟨34198088150544330424850533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45597450867392440566467377 34198088150544330424850533)
            ·
              refine ⟨6412141528227061954659475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34198088150544330424850533 6412141528227061954659475)
              ·
                refine ⟨9618212292340592931989213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6412141528227061954659475 9618212292340592931989213)
                ·
                  refine ⟨3606829609627722349495955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9618212292340592931989213 3606829609627722349495955)
                  ·
                    refine ⟨5410244414441583524243933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3606829609627722349495955 5410244414441583524243933)
                    ·
                      refine ⟨2028841655415593821591475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5410244414441583524243933 2028841655415593821591475)
                      ·
                        rfl

theorem cell23_3951155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 1, 3].length) (baseStart_3951155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951155 prefixEnd_3951155 := by exact prefixLift 3951155
  have htrace : WordTrace (prefixWord ++ tailWord_3951155) baseStart_3951155 baseEnd_3951155 := by
    simpa [prefixWord, tailWord_3951155, baseEnd_3951155] using wordTrace_append hprefix tailTrace_3951155
  have hstable : (prefixWord ++ tailWord_3951155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951155).length < 2 ^ (prefixWord ++ tailWord_3951155).sum := by decide
  have hdescent : baseEnd_3951155 < baseStart_3951155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951165 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 1, 5, 2]
def baseStart_3951165 : Nat := 118140960795 + 3951165 * 2 ^ 59
def prefixEnd_3951165 : Nat := 4983230072969 + 3 ^ 40 * 3951165 * 2
def baseEnd_3951165 : Nat := 2028846790222138782466429

theorem tailTrace_3951165 : CollatzResearch.WordTrace tailWord_3951165 prefixEnd_3951165 2028846790222138782466429 := by
  unfold tailWord_3951165
  simp only [CollatzResearch.WordTrace]
  refine ⟨144110826730611485103118949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96073884487074323402079299 144110826730611485103118949)
  ·
    refine ⟨27020780011989653456834803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144110826730611485103118949 27020780011989653456834803)
    ·
      refine ⟨40531170017984480185252205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27020780011989653456834803 40531170017984480185252205)
      ·
        refine ⟨15199188756744180069469577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40531170017984480185252205 15199188756744180069469577)
        ·
          refine ⟨11399391567558135052102183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15199188756744180069469577 11399391567558135052102183)
          ·
            refine ⟨17099087351337202578153275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11399391567558135052102183 17099087351337202578153275)
            ·
              refine ⟨25648631027005803867229913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17099087351337202578153275 25648631027005803867229913)
              ·
                refine ⟨19236473270254352900422435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25648631027005803867229913 19236473270254352900422435)
                ·
                  refine ⟨28854709905381529350633653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19236473270254352900422435 28854709905381529350633653)
                  ·
                    refine ⟨2705129053629518376621905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28854709905381529350633653 2705129053629518376621905)
                    ·
                      refine ⟨2028846790222138782466429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2705129053629518376621905 2028846790222138782466429)
                      ·
                        rfl

theorem cell23_3951165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_3951165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951165 prefixEnd_3951165 := by exact prefixLift 3951165
  have htrace : WordTrace (prefixWord ++ tailWord_3951165) baseStart_3951165 baseEnd_3951165 := by
    simpa [prefixWord, tailWord_3951165, baseEnd_3951165] using wordTrace_append hprefix tailTrace_3951165
  have hstable : (prefixWord ++ tailWord_3951165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951165).length < 2 ^ (prefixWord ++ tailWord_3951165).sum := by decide
  have hdescent : baseEnd_3951165 < baseStart_3951165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951175 : List Nat := [1, 1, 4, 1, 4, 2, 2, 2, 1, 5]
def baseStart_3951175 : Nat := 118140960795 + 3951175 * 2 ^ 59
def prefixEnd_3951175 : Nat := 4983230072969 + 3 ^ 40 * 3951175 * 2
def baseEnd_3951175 : Nat := 676283975009561247780461

theorem tailTrace_3951175 : CollatzResearch.WordTrace tailWord_3951175 prefixEnd_3951175 676283975009561247780461 := by
  unfold tailWord_3951175
  simp only [CollatzResearch.WordTrace]
  refine ⟨144111191460575256810982979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96074127640383504540655319 144111191460575256810982979)
  ·
    refine ⟨216166787190862885216474469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144111191460575256810982979 216166787190862885216474469)
    ·
      refine ⟨40531272598286790978088963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216166787190862885216474469 40531272598286790978088963)
      ·
        refine ⟨60796908897430186467133445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40531272598286790978088963 60796908897430186467133445)
        ·
          refine ⟨11399420418268159962587521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60796908897430186467133445 11399420418268159962587521)
          ·
            refine ⟨8549565313701119971940641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11399420418268159962587521 8549565313701119971940641)
            ·
              refine ⟨6412173985275839978955481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8549565313701119971940641 6412173985275839978955481)
              ·
                refine ⟨4809130488956879984216611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6412173985275839978955481 4809130488956879984216611)
                ·
                  refine ⟨7213695733435319976324917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4809130488956879984216611 7213695733435319976324917)
                  ·
                    refine ⟨676283975009561247780461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7213695733435319976324917 676283975009561247780461)
                    ·
                      rfl

theorem cell23_3951175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_3951175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951175 prefixEnd_3951175 := by exact prefixLift 3951175
  have htrace : WordTrace (prefixWord ++ tailWord_3951175) baseStart_3951175 baseEnd_3951175 := by
    simpa [prefixWord, tailWord_3951175, baseEnd_3951175] using wordTrace_append hprefix tailTrace_3951175
  have hstable : (prefixWord ++ tailWord_3951175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951175).length < 2 ^ (prefixWord ++ tailWord_3951175).sum := by decide
  have hdescent : baseEnd_3951175 < baseStart_3951175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951201 : List Nat := [1, 2, 3, 1, 1, 4, 11]
def baseStart_3951201 : Nat := 118140960795 + 3951201 * 2 ^ 59
def prefixEnd_3951201 : Nat := 4983230072969 + 3 ^ 40 * 3951201 * 2
def baseEnd_3951201 : Nat := 25047719450934575822423

theorem tailTrace_3951201 : CollatzResearch.WordTrace tailWord_3951201 prefixEnd_3951201 25047719450934575822423 := by
  unfold tailWord_3951201
  simp only [CollatzResearch.WordTrace]
  refine ⟨144112139758481063251429457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96074759838987375500952971 144112139758481063251429457)
  ·
    refine ⟨108084104818860797438572093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144112139758481063251429457 108084104818860797438572093)
    ·
      refine ⟨40531539307072799039464535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108084104818860797438572093 40531539307072799039464535)
      ·
        refine ⟨60797308960609198559196803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40531539307072799039464535 60797308960609198559196803)
        ·
          refine ⟨91195963440913797838795205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60797308960609198559196803 91195963440913797838795205)
          ·
            refine ⟨17099243145171337094774101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91195963440913797838795205 17099243145171337094774101)
            ·
              refine ⟨25047719450934575822423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17099243145171337094774101 25047719450934575822423)
              ·
                rfl

theorem cell23_3951201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 11].length) (baseStart_3951201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951201 prefixEnd_3951201 := by exact prefixLift 3951201
  have htrace : WordTrace (prefixWord ++ tailWord_3951201) baseStart_3951201 baseEnd_3951201 := by
    simpa [prefixWord, tailWord_3951201, baseEnd_3951201] using wordTrace_append hprefix tailTrace_3951201
  have hstable : (prefixWord ++ tailWord_3951201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951201).length < 2 ^ (prefixWord ++ tailWord_3951201).sum := by decide
  have hdescent : baseEnd_3951201 < baseStart_3951201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951212 : List Nat := [2, 2, 1, 1, 3, 1, 5, 1, 3, 2, 2]
def baseStart_3951212 : Nat := 118140960795 + 3951212 * 2 ^ 59
def prefixEnd_3951212 : Nat := 4983230072969 + 3 ^ 40 * 3951212 * 2
def baseEnd_3951212 : Nat := 2028870923812900098578713

theorem tailTrace_3951212 : CollatzResearch.WordTrace tailWord_3951212 prefixEnd_3951212 2028870923812900098578713 := by
  unfold tailWord_3951212
  simp only [CollatzResearch.WordTrace]
  refine ⟨72056270480720606065039945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96075027307627474753386593 72056270480720606065039945)
  ·
    refine ⟨54042202860540454548779959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72056270480720606065039945 54042202860540454548779959)
    ·
      refine ⟨81063304290810681823169939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54042202860540454548779959 81063304290810681823169939)
      ·
        refine ⟨121594956436216022734754909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81063304290810681823169939 121594956436216022734754909)
        ·
          refine ⟨45598108663581008525533091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121594956436216022734754909 45598108663581008525533091)
          ·
            refine ⟨68397162995371512788299637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45598108663581008525533091 68397162995371512788299637)
            ·
              refine ⟨6412234030816079323903091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68397162995371512788299637 6412234030816079323903091)
              ·
                refine ⟨9618351046224118985854637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6412234030816079323903091 9618351046224118985854637)
                ·
                  refine ⟨3606881642334044619695489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9618351046224118985854637 3606881642334044619695489)
                  ·
                    refine ⟨2705161231750533464771617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3606881642334044619695489 2705161231750533464771617)
                    ·
                      refine ⟨2028870923812900098578713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2705161231750533464771617 2028870923812900098578713)
                      ·
                        rfl

theorem cell23_3951212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 2, 2].length) (baseStart_3951212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951212 prefixEnd_3951212 := by exact prefixLift 3951212
  have htrace : WordTrace (prefixWord ++ tailWord_3951212) baseStart_3951212 baseEnd_3951212 := by
    simpa [prefixWord, tailWord_3951212, baseEnd_3951212] using wordTrace_append hprefix tailTrace_3951212
  have hstable : (prefixWord ++ tailWord_3951212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951212).length < 2 ^ (prefixWord ++ tailWord_3951212).sum := by decide
  have hdescent : baseEnd_3951212 < baseStart_3951212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951229 : List Nat := [1, 4, 1, 1, 6, 1, 1, 2, 1, 1, 4]
def baseStart_3951229 : Nat := 118140960795 + 3951229 * 2 ^ 59
def prefixEnd_3951229 : Nat := 4983230072969 + 3 ^ 40 * 3951229 * 2
def baseEnd_3951229 : Nat := 2028879652984026532066135

theorem tailTrace_3951229 : CollatzResearch.WordTrace tailWord_3951229 prefixEnd_3951229 2028879652984026532066135 := by
  unfold tailWord_3951229
  simp only [CollatzResearch.WordTrace]
  refine ⟨144113161002379624033448741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96075440668253082688965827 144113161002379624033448741)
  ·
    refine ⟨27021217687946179506271639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144113161002379624033448741 27021217687946179506271639)
    ·
      refine ⟨40531826531919269259407459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27021217687946179506271639 40531826531919269259407459)
      ·
        refine ⟨60797739797878903889111189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40531826531919269259407459 60797739797878903889111189)
        ·
          refine ⟨2849894053025573619802087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60797739797878903889111189 2849894053025573619802087)
          ·
            refine ⟨4274841079538360429703131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2849894053025573619802087 4274841079538360429703131)
            ·
              refine ⟨6412261619307540644554697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4274841079538360429703131 6412261619307540644554697)
              ·
                refine ⟨4809196214480655483416023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6412261619307540644554697 4809196214480655483416023)
                ·
                  refine ⟨7213794321720983225124035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4809196214480655483416023 7213794321720983225124035)
                  ·
                    refine ⟨10820691482581474837686053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7213794321720983225124035 10820691482581474837686053)
                    ·
                      refine ⟨2028879652984026532066135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10820691482581474837686053 2028879652984026532066135)
                      ·
                        rfl

theorem cell23_3951229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_3951229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951229 prefixEnd_3951229 := by exact prefixLift 3951229
  have htrace : WordTrace (prefixWord ++ tailWord_3951229) baseStart_3951229 baseEnd_3951229 := by
    simpa [prefixWord, tailWord_3951229, baseEnd_3951229] using wordTrace_append hprefix tailTrace_3951229
  have hstable : (prefixWord ++ tailWord_3951229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951229).length < 2 ^ (prefixWord ++ tailWord_3951229).sum := by decide
  have hdescent : baseEnd_3951229 < baseStart_3951229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951231 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 4, 7]
def baseStart_3951231 : Nat := 118140960795 + 3951231 * 2 ^ 59
def prefixEnd_3951231 : Nat := 4983230072969 + 3 ^ 40 * 3951231 * 2
def baseEnd_3951231 : Nat := 676293559981778508080375

theorem tailTrace_3951231 : CollatzResearch.WordTrace tailWord_3951231 prefixEnd_3951231 676293559981778508080375 := by
  unfold tailWord_3951231
  simp only [CollatzResearch.WordTrace]
  refine ⟨144113233948372378375021547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96075489298914918916681031 144113233948372378375021547)
  ·
    refine ⟨216169850922558567562532321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144113233948372378375021547 216169850922558567562532321)
    ·
      refine ⟨162127388191918925671899241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216169850922558567562532321 162127388191918925671899241)
      ·
        refine ⟨121595541143939194253924431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162127388191918925671899241 121595541143939194253924431)
        ·
          refine ⟨182393311715908791380886647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121595541143939194253924431 182393311715908791380886647)
          ·
            refine ⟨273589967573863187071329971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182393311715908791380886647 273589967573863187071329971)
            ·
              refine ⟨410384951360794780606994957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273589967573863187071329971 410384951360794780606994957)
              ·
                refine ⟨153894356760298042727623109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410384951360794780606994957 153894356760298042727623109)
                ·
                  refine ⟨28855191892555883011429333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153894356760298042727623109 28855191892555883011429333)
                  ·
                    refine ⟨676293559981778508080375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28855191892555883011429333 676293559981778508080375)
                    ·
                      rfl

theorem cell23_3951231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 7].length) (baseStart_3951231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951231 prefixEnd_3951231 := by exact prefixLift 3951231
  have htrace : WordTrace (prefixWord ++ tailWord_3951231) baseStart_3951231 baseEnd_3951231 := by
    simpa [prefixWord, tailWord_3951231, baseEnd_3951231] using wordTrace_append hprefix tailTrace_3951231
  have hstable : (prefixWord ++ tailWord_3951231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951231).length < 2 ^ (prefixWord ++ tailWord_3951231).sum := by decide
  have hdescent : baseEnd_3951231 < baseStart_3951231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951232 : List Nat := [2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 3]
def baseStart_3951232 : Nat := 118140960795 + 3951232 * 2 ^ 59
def prefixEnd_3951232 : Nat := 4983230072969 + 3 ^ 40 * 3951232 * 2
def baseEnd_3951232 : Nat := 2028881193425990020328621

theorem tailTrace_3951232 : CollatzResearch.WordTrace tailWord_3951232 prefixEnd_3951232 2028881193425990020328621 := by
  unfold tailWord_3951232
  simp only [CollatzResearch.WordTrace]
  refine ⟨72056635210684377772903975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96075513614245837030538633 72056635210684377772903975)
  ·
    refine ⟨108084952816026566659355963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72056635210684377772903975 108084952816026566659355963)
    ·
      refine ⟨162127429224039849989033945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108084952816026566659355963 162127429224039849989033945)
      ·
        refine ⟨121595571918029887491775459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162127429224039849989033945 121595571918029887491775459)
        ·
          refine ⟨182393357877044831237663189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121595571918029887491775459 182393357877044831237663189)
          ·
            refine ⟨4274844325243238232132731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 182393357877044831237663189 4274844325243238232132731)
            ·
              refine ⟨6412266487864857348199097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4274844325243238232132731 6412266487864857348199097)
              ·
                refine ⟨4809199865898643011149323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6412266487864857348199097 4809199865898643011149323)
                ·
                  refine ⟨7213799798847964516723985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4809199865898643011149323 7213799798847964516723985)
                  ·
                    refine ⟨5410349849135973387542989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7213799798847964516723985 5410349849135973387542989)
                    ·
                      refine ⟨2028881193425990020328621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5410349849135973387542989 2028881193425990020328621)
                      ·
                        rfl

theorem cell23_3951232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 3].length) (baseStart_3951232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951232 prefixEnd_3951232 := by exact prefixLift 3951232
  have htrace : WordTrace (prefixWord ++ tailWord_3951232) baseStart_3951232 baseEnd_3951232 := by
    simpa [prefixWord, tailWord_3951232, baseEnd_3951232] using wordTrace_append hprefix tailTrace_3951232
  have hstable : (prefixWord ++ tailWord_3951232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951232).length < 2 ^ (prefixWord ++ tailWord_3951232).sum := by decide
  have hdescent : baseEnd_3951232 < baseStart_3951232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951251 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 8]
def baseStart_3951251 : Nat := 118140960795 + 3951251 * 2 ^ 59
def prefixEnd_3951251 : Nat := 4983230072969 + 3 ^ 40 * 3951251 * 2
def baseEnd_3951251 : Nat := 2028890949558425445991033

theorem tailTrace_3951251 : CollatzResearch.WordTrace tailWord_3951251 prefixEnd_3951251 2028890949558425445991033 := by
  unfold tailWord_3951251
  simp only [CollatzResearch.WordTrace]
  refine ⟨144113963408299921790749607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96075975605533281193833071 144113963408299921790749607)
  ·
    refine ⟨216170945112449882686124411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144113963408299921790749607 216170945112449882686124411)
    ·
      refine ⟨324256417668674824029186617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216170945112449882686124411 324256417668674824029186617)
      ·
        refine ⟨243192313251506118021889963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324256417668674824029186617 243192313251506118021889963)
        ·
          refine ⟨364788469877259177032834945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243192313251506118021889963 364788469877259177032834945)
          ·
            refine ⟨273591352407944382774626209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364788469877259177032834945 273591352407944382774626209)
            ·
              refine ⟨205193514305958287080969657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273591352407944382774626209 205193514305958287080969657)
              ·
                refine ⟨153895135729468715310727243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205193514305958287080969657 153895135729468715310727243)
                ·
                  refine ⟨230842703594203072966090865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153895135729468715310727243 230842703594203072966090865)
                  ·
                    refine ⟨173132027695652304724568149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 230842703594203072966090865 173132027695652304724568149)
                    ·
                      refine ⟨2028890949558425445991033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 173132027695652304724568149 2028890949558425445991033)
                      ·
                        rfl

theorem cell23_3951251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_3951251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951251 prefixEnd_3951251 := by exact prefixLift 3951251
  have htrace : WordTrace (prefixWord ++ tailWord_3951251) baseStart_3951251 baseEnd_3951251 := by
    simpa [prefixWord, tailWord_3951251, baseEnd_3951251] using wordTrace_append hprefix tailTrace_3951251
  have hstable : (prefixWord ++ tailWord_3951251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951251).length < 2 ^ (prefixWord ++ tailWord_3951251).sum := by decide
  have hdescent : baseEnd_3951251 < baseStart_3951251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951268 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_3951268 : Nat := 118140960795 + 3951268 * 2 ^ 59
def prefixEnd_3951268 : Nat := 4983230072969 + 3 ^ 40 * 3951268 * 2
def baseEnd_3951268 : Nat := 2028899678729551879478455

theorem tailTrace_3951268 : CollatzResearch.WordTrace tailWord_3951268 prefixEnd_3951268 2028899678729551879478455 := by
  unfold tailWord_3951268
  simp only [CollatzResearch.WordTrace]
  refine ⟨72057291724619166847059229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96076388966158889129412305 72057291724619166847059229)
  ·
    refine ⟨27021484396732187567647211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72057291724619166847059229 27021484396732187567647211)
    ·
      refine ⟨40532226595098281351470817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27021484396732187567647211 40532226595098281351470817)
      ·
        refine ⟨30399169946323711013603113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40532226595098281351470817 30399169946323711013603113)
        ·
          refine ⟨22799377459742783260202335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30399169946323711013603113 22799377459742783260202335)
          ·
            refine ⟨34199066189614174890303503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22799377459742783260202335 34199066189614174890303503)
            ·
              refine ⟨51298599284421262335455255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34199066189614174890303503 51298599284421262335455255)
              ·
                refine ⟨76947898926631893503182883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51298599284421262335455255 76947898926631893503182883)
                ·
                  refine ⟨115421848389947840254774325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76947898926631893503182883 115421848389947840254774325)
                  ·
                    refine ⟨10820798286557610023885093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115421848389947840254774325 10820798286557610023885093)
                    ·
                      refine ⟨2028899678729551879478455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10820798286557610023885093 2028899678729551879478455)
                      ·
                        rfl

theorem cell23_3951268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_3951268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951268 prefixEnd_3951268 := by exact prefixLift 3951268
  have htrace : WordTrace (prefixWord ++ tailWord_3951268) baseStart_3951268 baseEnd_3951268 := by
    simpa [prefixWord, tailWord_3951268, baseEnd_3951268] using wordTrace_append hprefix tailTrace_3951268
  have hstable : (prefixWord ++ tailWord_3951268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951268).length < 2 ^ (prefixWord ++ tailWord_3951268).sum := by decide
  have hdescent : baseEnd_3951268 < baseStart_3951268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951306 : List Nat := [3, 1, 2, 1, 4, 3, 2, 1, 1, 3, 2]
def baseStart_3951306 : Nat := 118140960795 + 3951306 * 2 ^ 59
def prefixEnd_3951306 : Nat := 4983230072969 + 3 ^ 40 * 3951306 * 2
def baseEnd_3951306 : Nat := 2028919190994422730803281

theorem tailTrace_3951306 : CollatzResearch.WordTrace tailWord_3951306 prefixEnd_3951306 2028919190994422730803281 := by
  unfold tailWord_3951306
  simp only [CollatzResearch.WordTrace]
  refine ⟨36028992355775166546000443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96077312948733777456001181 36028992355775166546000443)
  ·
    refine ⟨54043488533662749819000665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36028992355775166546000443 54043488533662749819000665)
    ·
      refine ⟨40532616400247062364250499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54043488533662749819000665 40532616400247062364250499)
      ·
        refine ⟨60798924600370593546375749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40532616400247062364250499 60798924600370593546375749)
        ·
          refine ⟨11399798362569486289945453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60798924600370593546375749 11399798362569486289945453)
          ·
            refine ⟨4274924385963557358729545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11399798362569486289945453 4274924385963557358729545)
            ·
              refine ⟨3206193289472668019047159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4274924385963557358729545 3206193289472668019047159)
              ·
                refine ⟨4809289934209002028570739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3206193289472668019047159 4809289934209002028570739)
                ·
                  refine ⟨7213934901313503042856109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4809289934209002028570739 7213934901313503042856109)
                  ·
                    refine ⟨2705225587992563641071041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7213934901313503042856109 2705225587992563641071041)
                    ·
                      refine ⟨2028919190994422730803281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2705225587992563641071041 2028919190994422730803281)
                      ·
                        rfl

theorem cell23_3951306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_3951306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951306 prefixEnd_3951306 := by exact prefixLift 3951306
  have htrace : WordTrace (prefixWord ++ tailWord_3951306) baseStart_3951306 baseEnd_3951306 := by
    simpa [prefixWord, tailWord_3951306, baseEnd_3951306] using wordTrace_append hprefix tailTrace_3951306
  have hstable : (prefixWord ++ tailWord_3951306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951306).length < 2 ^ (prefixWord ++ tailWord_3951306).sum := by decide
  have hdescent : baseEnd_3951306 < baseStart_3951306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951319 : List Nat := [1, 1, 3, 2, 1, 4, 3, 2, 2, 2, 2]
def baseStart_3951319 : Nat := 118140960795 + 3951319 * 2 ^ 59
def prefixEnd_3951319 : Nat := 4983230072969 + 3 ^ 40 * 3951319 * 2
def baseEnd_3951319 : Nat := 2028925866242931179940721

theorem tailTrace_3951319 : CollatzResearch.WordTrace tailWord_3951319 prefixEnd_3951319 2028925866242931179940721 := by
  unfold tailWord_3951319
  simp only [CollatzResearch.WordTrace]
  refine ⟨144116443572053569404225011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96077629048035712936150007 144116443572053569404225011)
  ·
    refine ⟨216174665358080354106337517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144116443572053569404225011 216174665358080354106337517)
    ·
      refine ⟨81065499509280132789876569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216174665358080354106337517 81065499509280132789876569)
      ·
        refine ⟨60799124631960099592407427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81065499509280132789876569 60799124631960099592407427)
        ·
          refine ⟨91198686947940149388611141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60799124631960099592407427 91198686947940149388611141)
          ·
            refine ⟨17099753802738778010364589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91198686947940149388611141 17099753802738778010364589)
            ·
              refine ⟨6412407676027041753886721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17099753802738778010364589 6412407676027041753886721)
              ·
                refine ⟨4809305757020281315415041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6412407676027041753886721 4809305757020281315415041)
                ·
                  refine ⟨3606979317765210986561281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4809305757020281315415041 3606979317765210986561281)
                  ·
                    refine ⟨2705234488323908239920961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3606979317765210986561281 2705234488323908239920961)
                    ·
                      refine ⟨2028925866242931179940721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2705234488323908239920961 2028925866242931179940721)
                      ·
                        rfl

theorem cell23_3951319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_3951319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951319 prefixEnd_3951319 := by exact prefixLift 3951319
  have htrace : WordTrace (prefixWord ++ tailWord_3951319) baseStart_3951319 baseEnd_3951319 := by
    simpa [prefixWord, tailWord_3951319, baseEnd_3951319] using wordTrace_append hprefix tailTrace_3951319
  have hstable : (prefixWord ++ tailWord_3951319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951319).length < 2 ^ (prefixWord ++ tailWord_3951319).sum := by decide
  have hdescent : baseEnd_3951319 < baseStart_3951319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951336 : List Nat := [2, 1, 4, 1, 5, 1, 1, 1, 1, 4, 2]
def baseStart_3951336 : Nat := 118140960795 + 3951336 * 2 ^ 59
def prefixEnd_3951336 : Nat := 4983230072969 + 3 ^ 40 * 3951336 * 2
def baseEnd_3951336 : Nat := 2028934595414057613428143

theorem tailTrace_3951336 : CollatzResearch.WordTrace tailWord_3951336 prefixEnd_3951336 2028934595414057613428143 := by
  unfold tailWord_3951336
  simp only [CollatzResearch.WordTrace]
  refine ⟨72058531806495990653796931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96078042408661320871729241 72058531806495990653796931)
  ·
    refine ⟨108087797709743985980695397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72058531806495990653796931 108087797709743985980695397)
    ·
      refine ⟨20266462070576997371380387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108087797709743985980695397 20266462070576997371380387)
      ·
        refine ⟨30399693105865496057070581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20266462070576997371380387 30399693105865496057070581)
        ·
          refine ⟨2849971228674890255350367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30399693105865496057070581 2849971228674890255350367)
          ·
            refine ⟨4274956843012335383025551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2849971228674890255350367 4274956843012335383025551)
            ·
              refine ⟨6412435264518503074538327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4274956843012335383025551 6412435264518503074538327)
              ·
                refine ⟨9618652896777754611807491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6412435264518503074538327 9618652896777754611807491)
                ·
                  refine ⟨14427979345166631917711237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9618652896777754611807491 14427979345166631917711237)
                  ·
                    refine ⟨2705246127218743484570857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14427979345166631917711237 2705246127218743484570857)
                    ·
                      refine ⟨2028934595414057613428143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2705246127218743484570857 2028934595414057613428143)
                      ·
                        rfl

theorem cell23_3951336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_3951336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951336 prefixEnd_3951336 := by exact prefixLift 3951336
  have htrace : WordTrace (prefixWord ++ tailWord_3951336) baseStart_3951336 baseEnd_3951336 := by
    simpa [prefixWord, tailWord_3951336, baseEnd_3951336] using wordTrace_append hprefix tailTrace_3951336
  have hstable : (prefixWord ++ tailWord_3951336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951336).length < 2 ^ (prefixWord ++ tailWord_3951336).sum := by decide
  have hdescent : baseEnd_3951336 < baseStart_3951336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951375 : List Nat := [1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 4]
def baseStart_3951375 : Nat := 118140960795 + 3951375 * 2 ^ 59
def prefixEnd_3951375 : Nat := 4983230072969 + 3 ^ 40 * 3951375 * 2
def baseEnd_3951375 : Nat := 2028954621159582960840463

theorem tailTrace_3951375 : CollatzResearch.WordTrace tailWord_3951375 prefixEnd_3951375 2028954621159582960840463 := by
  unfold tailWord_3951375
  simp only [CollatzResearch.WordTrace]
  refine ⟨144118486059850690968263579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96078990706567127312175719 144118486059850690968263579)
  ·
    refine ⟨216177729089776036452395369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144118486059850690968263579 216177729089776036452395369)
    ·
      refine ⟨162133296817332027339296527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216177729089776036452395369 162133296817332027339296527)
      ·
        refine ⟨243199945225998041008944791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162133296817332027339296527 243199945225998041008944791)
        ·
          refine ⟨364799917838997061513417187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243199945225998041008944791 364799917838997061513417187)
          ·
            refine ⟨547199876758495592270125781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364799917838997061513417187 547199876758495592270125781)
            ·
              refine ⟨12824997111527240443831073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 547199876758495592270125781 12824997111527240443831073)
              ·
                refine ⟨9618747833645430332873305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12824997111527240443831073 9618747833645430332873305)
                ·
                  refine ⟨7214060875234072749654979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9618747833645430332873305 7214060875234072749654979)
                  ·
                    refine ⟨10821091312851109124482469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7214060875234072749654979 10821091312851109124482469)
                    ·
                      refine ⟨2028954621159582960840463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10821091312851109124482469 2028954621159582960840463)
                      ·
                        rfl

theorem cell23_3951375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 4].length) (baseStart_3951375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951375 prefixEnd_3951375 := by exact prefixLift 3951375
  have htrace : WordTrace (prefixWord ++ tailWord_3951375) baseStart_3951375 baseEnd_3951375 := by
    simpa [prefixWord, tailWord_3951375, baseEnd_3951375] using wordTrace_append hprefix tailTrace_3951375
  have hstable : (prefixWord ++ tailWord_3951375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951375).length < 2 ^ (prefixWord ++ tailWord_3951375).sum := by decide
  have hdescent : baseEnd_3951375 < baseStart_3951375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951385 : List Nat := [1, 2, 1, 2, 1, 1, 1, 7, 3, 4]
def baseStart_3951385 : Nat := 118140960795 + 3951385 * 2 ^ 59
def prefixEnd_3951385 : Nat := 4983230072969 + 3 ^ 40 * 3951385 * 2
def baseEnd_3951385 : Nat := 676319918655375973905139

theorem tailTrace_3951385 : CollatzResearch.WordTrace tailWord_3951385 prefixEnd_3951385 676319918655375973905139 := by
  unfold tailWord_3951385
  simp only [CollatzResearch.WordTrace]
  refine ⟨144118850789814462676127609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96079233859876308450751739 144118850789814462676127609)
  ·
    refine ⟨108089138092360847007095707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144118850789814462676127609 108089138092360847007095707)
    ·
      refine ⟨162133707138541270510643561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108089138092360847007095707 162133707138541270510643561)
      ·
        refine ⟨121600280353905952882982671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162133707138541270510643561 121600280353905952882982671)
        ·
          refine ⟨182400420530858929324474007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121600280353905952882982671 182400420530858929324474007)
          ·
            refine ⟨273600630796288393986711011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182400420530858929324474007 273600630796288393986711011)
            ·
              refine ⟨410400946194432590980066517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273600630796288393986711011 410400946194432590980066517)
              ·
                refine ⟨9618772176432013851095309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 410400946194432590980066517 9618772176432013851095309)
                ·
                  refine ⟨3607039566162005194160741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9618772176432013851095309 3607039566162005194160741)
                  ·
                    refine ⟨676319918655375973905139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3607039566162005194160741 676319918655375973905139)
                    ·
                      rfl

theorem cell23_3951385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 4].length) (baseStart_3951385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951385 prefixEnd_3951385 := by exact prefixLift 3951385
  have htrace : WordTrace (prefixWord ++ tailWord_3951385) baseStart_3951385 baseEnd_3951385 := by
    simpa [prefixWord, tailWord_3951385, baseEnd_3951385] using wordTrace_append hprefix tailTrace_3951385
  have hstable : (prefixWord ++ tailWord_3951385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951385).length < 2 ^ (prefixWord ++ tailWord_3951385).sum := by decide
  have hdescent : baseEnd_3951385 < baseStart_3951385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951395 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 3]
def baseStart_3951395 : Nat := 118140960795 + 3951395 * 2 ^ 59
def prefixEnd_3951395 : Nat := 4983230072969 + 3 ^ 40 * 3951395 * 2
def baseEnd_3951395 : Nat := 2028964890772672882590371

theorem tailTrace_3951395 : CollatzResearch.WordTrace tailWord_3951395 prefixEnd_3951395 2028964890772672882590371 := by
  unfold tailWord_3951395
  simp only [CollatzResearch.WordTrace]
  refine ⟨144119215519778234383991639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96079477013185489589327759 144119215519778234383991639)
  ·
    refine ⟨216178823279667351575987459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144119215519778234383991639 216178823279667351575987459)
    ·
      refine ⟨324268234919501027363981189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216178823279667351575987459 324268234919501027363981189)
      ·
        refine ⟨60800294047406442630746473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324268234919501027363981189 60800294047406442630746473)
        ·
          refine ⟨45600220535554831973059855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60800294047406442630746473 45600220535554831973059855)
          ·
            refine ⟨68400330803332247959589783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45600220535554831973059855 68400330803332247959589783)
            ·
              refine ⟨102600496204998371939384675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68400330803332247959589783 102600496204998371939384675)
              ·
                refine ⟨153900744307497557909077013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102600496204998371939384675 153900744307497557909077013)
                ·
                  refine ⟨7214097389413948026987985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153900744307497557909077013 7214097389413948026987985)
                  ·
                    refine ⟨5410573042060461020240989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7214097389413948026987985 5410573042060461020240989)
                    ·
                      refine ⟨2028964890772672882590371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5410573042060461020240989 2028964890772672882590371)
                      ·
                        rfl

theorem cell23_3951395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_3951395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951395 prefixEnd_3951395 := by exact prefixLift 3951395
  have htrace : WordTrace (prefixWord ++ tailWord_3951395) baseStart_3951395 baseEnd_3951395 := by
    simpa [prefixWord, tailWord_3951395, baseEnd_3951395] using wordTrace_append hprefix tailTrace_3951395
  have hstable : (prefixWord ++ tailWord_3951395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951395).length < 2 ^ (prefixWord ++ tailWord_3951395).sum := by decide
  have hdescent : baseEnd_3951395 < baseStart_3951395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951436 : List Nat := [2, 2, 1, 3, 3, 1, 4, 2, 1, 4]
def baseStart_3951436 : Nat := 118140960795 + 3951436 * 2 ^ 59
def prefixEnd_3951436 : Nat := 4983230072969 + 3 ^ 40 * 3951436 * 2
def baseEnd_3951436 : Nat := 676328647826502407392561

theorem tailTrace_3951436 : CollatzResearch.WordTrace tailWord_3951436 prefixEnd_3951436 676328647826502407392561 := by
  unfold tailWord_3951436
  simp only [CollatzResearch.WordTrace]
  refine ⟨72060355456314849193117081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96080473941753132257489441 72060355456314849193117081)
  ·
    refine ⟨54045266592236136894837811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72060355456314849193117081 54045266592236136894837811)
    ·
      refine ⟨81067899888354205342256717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54045266592236136894837811 81067899888354205342256717)
      ·
        refine ⟨30400462458132827003346269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81067899888354205342256717 30400462458132827003346269)
        ·
          refine ⟨11400173421799810126254851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30400462458132827003346269 11400173421799810126254851)
          ·
            refine ⟨17100260132699715189382277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11400173421799810126254851 17100260132699715189382277)
            ·
              refine ⟨3206298774881196598009177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17100260132699715189382277 3206298774881196598009177)
              ·
                refine ⟨2404724081160897448506883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3206298774881196598009177 2404724081160897448506883)
                ·
                  refine ⟨3607086121741346172760325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2404724081160897448506883 3607086121741346172760325)
                  ·
                    refine ⟨676328647826502407392561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3607086121741346172760325 676328647826502407392561)
                    ·
                      rfl

theorem cell23_3951436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 1, 4].length) (baseStart_3951436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951436 prefixEnd_3951436 := by exact prefixLift 3951436
  have htrace : WordTrace (prefixWord ++ tailWord_3951436) baseStart_3951436 baseEnd_3951436 := by
    simpa [prefixWord, tailWord_3951436, baseEnd_3951436] using wordTrace_append hprefix tailTrace_3951436
  have hstable : (prefixWord ++ tailWord_3951436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951436).length < 2 ^ (prefixWord ++ tailWord_3951436).sum := by decide
  have hdescent : baseEnd_3951436 < baseStart_3951436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951445 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 5, 5]
def baseStart_3951445 : Nat := 118140960795 + 3951445 * 2 ^ 59
def prefixEnd_3951445 : Nat := 4983230072969 + 3 ^ 40 * 3951445 * 2
def baseEnd_3951445 : Nat := 676330188268465895655047

theorem tailTrace_3951445 : CollatzResearch.WordTrace tailWord_3951445 prefixEnd_3951445 676330188268465895655047 := by
  unfold tailWord_3951445
  simp only [CollatzResearch.WordTrace]
  refine ⟨144121039169597092923311789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96080692779731395282207859 144121039169597092923311789)
  ·
    refine ⟨54045389688598909846241921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144121039169597092923311789 54045389688598909846241921)
    ·
      refine ⟨40534042266449182384681441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54045389688598909846241921 40534042266449182384681441)
      ·
        refine ⟨30400531699836886788511081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40534042266449182384681441 30400531699836886788511081)
        ·
          refine ⟨22800398774877665091383311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30400531699836886788511081 22800398774877665091383311)
          ·
            refine ⟨34200598162316497637074967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22800398774877665091383311 34200598162316497637074967)
            ·
              refine ⟨51300897243474746455612451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34200598162316497637074967 51300897243474746455612451)
              ·
                refine ⟨76951345865212119683418677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51300897243474746455612451 76951345865212119683418677)
                ·
                  refine ⟨7214188674863636220320501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76951345865212119683418677 7214188674863636220320501)
                  ·
                    refine ⟨676330188268465895655047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7214188674863636220320501 676330188268465895655047)
                    ·
                      rfl

theorem cell23_3951445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_3951445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951445 prefixEnd_3951445 := by exact prefixLift 3951445
  have htrace : WordTrace (prefixWord ++ tailWord_3951445) baseStart_3951445 baseEnd_3951445 := by
    simpa [prefixWord, tailWord_3951445, baseEnd_3951445] using wordTrace_append hprefix tailTrace_3951445
  have hstable : (prefixWord ++ tailWord_3951445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951445).length < 2 ^ (prefixWord ++ tailWord_3951445).sum := by decide
  have hdescent : baseEnd_3951445 < baseStart_3951445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951459 : List Nat := [1, 1, 1, 5, 3, 2, 1, 2, 3, 1, 3]
def baseStart_3951459 : Nat := 118140960795 + 3951459 * 2 ^ 59
def prefixEnd_3951459 : Nat := 4983230072969 + 3 ^ 40 * 3951459 * 2
def baseEnd_3951459 : Nat := 2028997753534560632190077

theorem tailTrace_3951459 : CollatzResearch.WordTrace tailWord_3951459 prefixEnd_3951459 2028997753534560632190077 := by
  unfold tailWord_3951459
  simp only [CollatzResearch.WordTrace]
  refine ⟨144121549791546373314321431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96081033194364248876214287 144121549791546373314321431)
  ·
    refine ⟨216182324687319559971482147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144121549791546373314321431 216182324687319559971482147)
    ·
      refine ⟨324273487030979339957223221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216182324687319559971482147 324273487030979339957223221)
      ·
        refine ⟨30400639409154313120989677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 324273487030979339957223221 30400639409154313120989677)
        ·
          refine ⟨11400239778432867420371129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30400639409154313120989677 11400239778432867420371129)
          ·
            refine ⟨8550179833824650565278347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11400239778432867420371129 8550179833824650565278347)
            ·
              refine ⟨12825269750736975847917521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8550179833824650565278347 12825269750736975847917521)
              ·
                refine ⟨9618952313052731885938141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12825269750736975847917521 9618952313052731885938141)
                ·
                  refine ⟨3607107117394774457226803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9618952313052731885938141 3607107117394774457226803)
                  ·
                    refine ⟨5410660676092161685840205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3607107117394774457226803 5410660676092161685840205)
                    ·
                      refine ⟨2028997753534560632190077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5410660676092161685840205 2028997753534560632190077)
                      ·
                        rfl

theorem cell23_3951459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_3951459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951459 prefixEnd_3951459 := by exact prefixLift 3951459
  have htrace : WordTrace (prefixWord ++ tailWord_3951459) baseStart_3951459 baseEnd_3951459 := by
    simpa [prefixWord, tailWord_3951459, baseEnd_3951459] using wordTrace_append hprefix tailTrace_3951459
  have hstable : (prefixWord ++ tailWord_3951459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951459).length < 2 ^ (prefixWord ++ tailWord_3951459).sum := by decide
  have hdescent : baseEnd_3951459 < baseStart_3951459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951475 : List Nat := [1, 1, 1, 2, 2, 1, 6, 2, 1, 6]
def baseStart_3951475 : Nat := 118140960795 + 3951475 * 2 ^ 59
def prefixEnd_3951475 : Nat := 4983230072969 + 3 ^ 40 * 3951475 * 2
def baseEnd_3951475 : Nat := 676335323075010856530001

theorem tailTrace_3951475 : CollatzResearch.WordTrace tailWord_3951475 prefixEnd_3951475 676335323075010856530001 := by
  unfold tailWord_3951475
  simp only [CollatzResearch.WordTrace]
  refine ⟨144122133359488408046903879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96081422239658938697935919 144122133359488408046903879)
  ·
    refine ⟨216183200039232612070355819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144122133359488408046903879 216183200039232612070355819)
    ·
      refine ⟨324274800058848918105533729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216183200039232612070355819 324274800058848918105533729)
      ·
        refine ⟨243206100044136688579150297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324274800058848918105533729 243206100044136688579150297)
        ·
          refine ⟨182404575033102516434362723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243206100044136688579150297 182404575033102516434362723)
          ·
            refine ⟨273606862549653774651544085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182404575033102516434362723 273606862549653774651544085)
            ·
              refine ⟨12825321682015020686791129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 273606862549653774651544085 12825321682015020686791129)
              ·
                refine ⟨9618991261511265515093347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12825321682015020686791129 9618991261511265515093347)
                ·
                  refine ⟨14428486892266898272640021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9618991261511265515093347 14428486892266898272640021)
                  ·
                    refine ⟨676335323075010856530001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14428486892266898272640021 676335323075010856530001)
                    ·
                      rfl

theorem cell23_3951475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 6].length) (baseStart_3951475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951475 prefixEnd_3951475 := by exact prefixLift 3951475
  have htrace : WordTrace (prefixWord ++ tailWord_3951475) baseStart_3951475 baseEnd_3951475 := by
    simpa [prefixWord, tailWord_3951475, baseEnd_3951475] using wordTrace_append hprefix tailTrace_3951475
  have hstable : (prefixWord ++ tailWord_3951475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951475).length < 2 ^ (prefixWord ++ tailWord_3951475).sum := by decide
  have hdescent : baseEnd_3951475 < baseStart_3951475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951499 : List Nat := [1, 1, 1, 1, 4, 2, 3, 3, 3, 2, 2]
def baseStart_3951499 : Nat := 118140960795 + 3951499 * 2 ^ 59
def prefixEnd_3951499 : Nat := 4983230072969 + 3 ^ 40 * 3951499 * 2
def baseEnd_3951499 : Nat := 2029018292760740475689893

theorem tailTrace_3951499 : CollatzResearch.WordTrace tailWord_3951499 prefixEnd_3951499 2029018292760740475689893 := by
  unfold tailWord_3951499
  simp only [CollatzResearch.WordTrace]
  refine ⟨144123008711401460145777551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96082005807600973430518367 144123008711401460145777551)
  ·
    refine ⟨216184513067102190218666327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144123008711401460145777551 216184513067102190218666327)
    ·
      refine ⟨324276769600653285327999491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216184513067102190218666327 324276769600653285327999491)
      ·
        refine ⟨486415154400979927991999237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324276769600653285327999491 486415154400979927991999237)
        ·
          refine ⟨91202841450183736498499857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 486415154400979927991999237 91202841450183736498499857)
          ·
            refine ⟨68402131087637802373874893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91202841450183736498499857 68402131087637802373874893)
            ·
              refine ⟨25650799157864175890203085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68402131087637802373874893 25650799157864175890203085)
              ·
                refine ⟨9619049684199065958826157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25650799157864175890203085 9619049684199065958826157)
                ·
                  refine ⟨3607143631574649734559809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9619049684199065958826157 3607143631574649734559809)
                  ·
                    refine ⟨2705357723680987300919857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3607143631574649734559809 2705357723680987300919857)
                    ·
                      refine ⟨2029018292760740475689893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2705357723680987300919857 2029018292760740475689893)
                      ·
                        rfl

theorem cell23_3951499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 2, 2].length) (baseStart_3951499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951499 prefixEnd_3951499 := by exact prefixLift 3951499
  have htrace : WordTrace (prefixWord ++ tailWord_3951499) baseStart_3951499 baseEnd_3951499 := by
    simpa [prefixWord, tailWord_3951499, baseEnd_3951499] using wordTrace_append hprefix tailTrace_3951499
  have hstable : (prefixWord ++ tailWord_3951499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951499).length < 2 ^ (prefixWord ++ tailWord_3951499).sum := by decide
  have hdescent : baseEnd_3951499 < baseStart_3951499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951516 : List Nat := [2, 2, 3, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3951516 : Nat := 118140960795 + 3951516 * 2 ^ 59
def prefixEnd_3951516 : Nat := 4983230072969 + 3 ^ 40 * 3951516 * 2
def baseEnd_3951516 : Nat := 2029027021931866909177315

theorem tailTrace_3951516 : CollatzResearch.WordTrace tailWord_3951516 prefixEnd_3951516 2029027021931866909177315 := by
  unfold tailWord_3951516
  simp only [CollatzResearch.WordTrace]
  refine ⟨72061814376169936024573201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96082419168226581366097601 72061814376169936024573201)
  ·
    refine ⟨54046360782127452018429901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72061814376169936024573201 54046360782127452018429901)
    ·
      refine ⟨20267385293297794506911213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54046360782127452018429901 20267385293297794506911213)
      ·
        refine ⟨7600269484986672940091705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20267385293297794506911213 7600269484986672940091705)
        ·
          refine ⟨5700202113740004705068779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7600269484986672940091705 5700202113740004705068779)
          ·
            refine ⟨8550303170610007057603169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5700202113740004705068779 8550303170610007057603169)
            ·
              refine ⟨6412727377957505293202377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8550303170610007057603169 6412727377957505293202377)
              ·
                refine ⟨4809545533468128969901783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6412727377957505293202377 4809545533468128969901783)
                ·
                  refine ⟨7214318300202193454852675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4809545533468128969901783 7214318300202193454852675)
                  ·
                    refine ⟨10821477450303290182279013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7214318300202193454852675 10821477450303290182279013)
                    ·
                      refine ⟨2029027021931866909177315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10821477450303290182279013 2029027021931866909177315)
                      ·
                        rfl

theorem cell23_3951516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3951516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951516 prefixEnd_3951516 := by exact prefixLift 3951516
  have htrace : WordTrace (prefixWord ++ tailWord_3951516) baseStart_3951516 baseEnd_3951516 := by
    simpa [prefixWord, tailWord_3951516, baseEnd_3951516] using wordTrace_append hprefix tailTrace_3951516
  have hstable : (prefixWord ++ tailWord_3951516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951516).length < 2 ^ (prefixWord ++ tailWord_3951516).sum := by decide
  have hdescent : baseEnd_3951516 < baseStart_3951516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951519 : List Nat := [1, 1, 2, 5, 2, 1, 1, 4, 1, 2, 3]
def baseStart_3951519 : Nat := 118140960795 + 3951519 * 2 ^ 59
def prefixEnd_3951519 : Nat := 4983230072969 + 3 ^ 40 * 3951519 * 2
def baseEnd_3951519 : Nat := 2029028562373830397439801

theorem tailTrace_3951519 : CollatzResearch.WordTrace tailWord_3951519 prefixEnd_3951519 2029028562373830397439801 := by
  unfold tailWord_3951519
  simp only [CollatzResearch.WordTrace]
  refine ⟨144123738171329003561505611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96082492114219335707670407 144123738171329003561505611)
  ·
    refine ⟨216185607256993505342258417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144123738171329003561505611 216185607256993505342258417)
    ·
      refine ⟨162139205442745129006693813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216185607256993505342258417 162139205442745129006693813)
      ·
        refine ⟨15200550510257355844377545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162139205442745129006693813 15200550510257355844377545)
        ·
          refine ⟨11400412882693016883283159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15200550510257355844377545 11400412882693016883283159)
          ·
            refine ⟨17100619324039525324924739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11400412882693016883283159 17100619324039525324924739)
            ·
              refine ⟨25650928986059287987387109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17100619324039525324924739 25650928986059287987387109)
              ·
                refine ⟨4809549184886116497635083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25650928986059287987387109 4809549184886116497635083)
                ·
                  refine ⟨7214323777329174746452625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4809549184886116497635083 7214323777329174746452625)
                  ·
                    refine ⟨5410742832996881059839469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7214323777329174746452625 5410742832996881059839469)
                    ·
                      refine ⟨2029028562373830397439801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5410742832996881059839469 2029028562373830397439801)
                      ·
                        rfl

theorem cell23_3951519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_3951519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951519 prefixEnd_3951519 := by exact prefixLift 3951519
  have htrace : WordTrace (prefixWord ++ tailWord_3951519) baseStart_3951519 baseEnd_3951519 := by
    simpa [prefixWord, tailWord_3951519, baseEnd_3951519] using wordTrace_append hprefix tailTrace_3951519
  have hstable : (prefixWord ++ tailWord_3951519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951519).length < 2 ^ (prefixWord ++ tailWord_3951519).sum := by decide
  have hdescent : baseEnd_3951519 < baseStart_3951519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951522 : List Nat := [3, 3, 1, 2, 2, 2, 1, 9]
def baseStart_3951522 : Nat := 118140960795 + 3951522 * 2 ^ 59
def prefixEnd_3951522 : Nat := 4983230072969 + 3 ^ 40 * 3951522 * 2
def baseEnd_3951522 : Nat := 75149263067251625396381

theorem tailTrace_3951522 : CollatzResearch.WordTrace tailWord_3951522 prefixEnd_3951522 75149263067251625396381 := by
  unfold tailWord_3951522
  simp only [CollatzResearch.WordTrace]
  refine ⟨36030961897579533768466205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96082565060212090049243213 36030961897579533768466205)
  ·
    refine ⟨13511610711592325163174827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36030961897579533768466205 13511610711592325163174827)
    ·
      refine ⟨20267416067388487744762241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13511610711592325163174827 20267416067388487744762241)
      ·
        refine ⟨15200562050541365808571681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20267416067388487744762241 15200562050541365808571681)
        ·
          refine ⟨11400421537906024356428761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15200562050541365808571681 11400421537906024356428761)
          ·
            refine ⟨8550316153429518267321571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11400421537906024356428761 8550316153429518267321571)
            ·
              refine ⟨12825474230144277400982357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8550316153429518267321571 12825474230144277400982357)
              ·
                refine ⟨75149263067251625396381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12825474230144277400982357 75149263067251625396381)
                ·
                  rfl

theorem cell23_3951522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 9].length) (baseStart_3951522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951522 prefixEnd_3951522 := by exact prefixLift 3951522
  have htrace : WordTrace (prefixWord ++ tailWord_3951522) baseStart_3951522 baseEnd_3951522 := by
    simpa [prefixWord, tailWord_3951522, baseEnd_3951522] using wordTrace_append hprefix tailTrace_3951522
  have hstable : (prefixWord ++ tailWord_3951522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951522).length < 2 ^ (prefixWord ++ tailWord_3951522).sum := by decide
  have hdescent : baseEnd_3951522 < baseStart_3951522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951550 : List Nat := [4, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2]
def baseStart_3951550 : Nat := 118140960795 + 3951550 * 2 ^ 59
def prefixEnd_3951550 : Nat := 4983230072969 + 3 ^ 40 * 3951550 * 2
def baseEnd_3951550 : Nat := 2029044480274119776152159

theorem tailTrace_3951550 : CollatzResearch.WordTrace tailWord_3951550 prefixEnd_3951550 2029044480274119776152159 := by
  unfold tailWord_3951550
  simp only [CollatzResearch.WordTrace]
  refine ⟨18015608604277086981985513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96083245889477797237256069 18015608604277086981985513)
  ·
    refine ⟨13511706453207815236489135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18015608604277086981985513 13511706453207815236489135)
    ·
      refine ⟨20267559679811722854733703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13511706453207815236489135 20267559679811722854733703)
      ·
        refine ⟨30401339519717584282100555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20267559679811722854733703 30401339519717584282100555)
        ·
          refine ⟨45602009279576376423150833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30401339519717584282100555 45602009279576376423150833)
          ·
            refine ⟨34201506959682282317363125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45602009279576376423150833 34201506959682282317363125)
            ·
              refine ⟨3206391277470213967252793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34201506959682282317363125 3206391277470213967252793)
              ·
                refine ⟨2404793458102660475439595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3206391277470213967252793 2404793458102660475439595)
                ·
                  refine ⟨3607190187153990713159393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2404793458102660475439595 3607190187153990713159393)
                  ·
                    refine ⟨2705392640365493034869545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3607190187153990713159393 2705392640365493034869545)
                    ·
                      refine ⟨2029044480274119776152159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2705392640365493034869545 2029044480274119776152159)
                      ·
                        rfl

theorem cell23_3951550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_3951550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951550 prefixEnd_3951550 := by exact prefixLift 3951550
  have htrace : WordTrace (prefixWord ++ tailWord_3951550) baseStart_3951550 baseEnd_3951550 := by
    simpa [prefixWord, tailWord_3951550, baseEnd_3951550] using wordTrace_append hprefix tailTrace_3951550
  have hstable : (prefixWord ++ tailWord_3951550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951550).length < 2 ^ (prefixWord ++ tailWord_3951550).sum := by decide
  have hdescent : baseEnd_3951550 < baseStart_3951550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951555 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 4]
def baseStart_3951555 : Nat := 118140960795 + 3951555 * 2 ^ 59
def prefixEnd_3951555 : Nat := 4983230072969 + 3 ^ 40 * 3951555 * 2
def baseEnd_3951555 : Nat := 2029047047677392256589635

theorem tailTrace_3951555 : CollatzResearch.WordTrace tailWord_3951555 prefixEnd_3951555 2029047047677392256589635 := by
  unfold tailWord_3951555
  simp only [CollatzResearch.WordTrace]
  refine ⟨144125051199198581709816119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96083367466132387806544079 144125051199198581709816119)
  ·
    refine ⟨216187576798797872564724179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144125051199198581709816119 216187576798797872564724179)
    ·
      refine ⟨324281365198196808847086269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216187576798797872564724179 324281365198196808847086269)
      ·
        refine ⟨121605511949323803317657351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324281365198196808847086269 121605511949323803317657351)
        ·
          refine ⟨182408267923985704976486027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121605511949323803317657351 182408267923985704976486027)
          ·
            refine ⟨273612401885978557464729041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182408267923985704976486027 273612401885978557464729041)
            ·
              refine ⟨205209301414483918098546781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273612401885978557464729041 205209301414483918098546781)
              ·
                refine ⟨76953488030431469286955043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205209301414483918098546781 76953488030431469286955043)
                ·
                  refine ⟨115430232045647203930432565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76953488030431469286955043 115430232045647203930432565)
                  ·
                    refine ⟨10821584254279425368478053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115430232045647203930432565 10821584254279425368478053)
                    ·
                      refine ⟨2029047047677392256589635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10821584254279425368478053 2029047047677392256589635)
                      ·
                        rfl

theorem cell23_3951555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_3951555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951555 prefixEnd_3951555 := by exact prefixLift 3951555
  have htrace : WordTrace (prefixWord ++ tailWord_3951555) baseStart_3951555 baseEnd_3951555 := by
    simpa [prefixWord, tailWord_3951555, baseEnd_3951555] using wordTrace_append hprefix tailTrace_3951555
  have hstable : (prefixWord ++ tailWord_3951555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951555).length < 2 ^ (prefixWord ++ tailWord_3951555).sum := by decide
  have hdescent : baseEnd_3951555 < baseStart_3951555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951566 : List Nat := [4, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3]
def baseStart_3951566 : Nat := 118140960795 + 3951566 * 2 ^ 59
def prefixEnd_3951566 : Nat := 4983230072969 + 3 ^ 40 * 3951566 * 2
def baseEnd_3951566 : Nat := 2029052695964591713552085

theorem tailTrace_3951566 : CollatzResearch.WordTrace tailWord_3951566 prefixEnd_3951566 2029052695964591713552085 := by
  unfold tailWord_3951566
  simp only [CollatzResearch.WordTrace]
  refine ⟨18015681550269841323558319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96083634934772487058977701 18015681550269841323558319)
  ·
    refine ⟨27023522325404761985337479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18015681550269841323558319 27023522325404761985337479)
    ·
      refine ⟨40535283488107142978006219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27023522325404761985337479 40535283488107142978006219)
      ·
        refine ⟨60802925232160714467009329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40535283488107142978006219 60802925232160714467009329)
        ·
          refine ⟨45602193924120535850256997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60802925232160714467009329 45602193924120535850256997)
          ·
            refine ⟨8550411360772600471923187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45602193924120535850256997 8550411360772600471923187)
            ·
              refine ⟨12825617041158900707884781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8550411360772600471923187 12825617041158900707884781)
              ·
                refine ⟨4809606390434587765456793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12825617041158900707884781 4809606390434587765456793)
                ·
                  refine ⟨3607204792825940824092595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4809606390434587765456793 3607204792825940824092595)
                  ·
                    refine ⟨5410807189238911236138893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3607204792825940824092595 5410807189238911236138893)
                    ·
                      refine ⟨2029052695964591713552085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5410807189238911236138893 2029052695964591713552085)
                      ·
                        rfl

theorem cell23_3951566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_3951566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951566 prefixEnd_3951566 := by exact prefixLift 3951566
  have htrace : WordTrace (prefixWord ++ tailWord_3951566) baseStart_3951566 baseEnd_3951566 := by
    simpa [prefixWord, tailWord_3951566, baseEnd_3951566] using wordTrace_append hprefix tailTrace_3951566
  have hstable : (prefixWord ++ tailWord_3951566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951566).length < 2 ^ (prefixWord ++ tailWord_3951566).sum := by decide
  have hdescent : baseEnd_3951566 < baseStart_3951566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951576 : List Nat := [2, 1, 2, 2, 2, 3, 3, 2, 1, 3, 2]
def baseStart_3951576 : Nat := 118140960795 + 3951576 * 2 ^ 59
def prefixEnd_3951576 : Nat := 4983230072969 + 3 ^ 40 * 3951576 * 2
def baseEnd_3951576 : Nat := 2029057830771136674427039

theorem tailTrace_3951576 : CollatzResearch.WordTrace tailWord_3951576 prefixEnd_3951576 2029057830771136674427039 := by
  unfold tailWord_3951576
  simp only [CollatzResearch.WordTrace]
  refine ⟨72062908566061251148165291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96083878088081668197553721 72062908566061251148165291)
  ·
    refine ⟨108094362849091876722247937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72062908566061251148165291 108094362849091876722247937)
    ·
      refine ⟨81070772136818907541685953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108094362849091876722247937 81070772136818907541685953)
      ·
        refine ⟨60803079102614180656264465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81070772136818907541685953 60803079102614180656264465)
        ·
          refine ⟨45602309326960635492198349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60803079102614180656264465 45602309326960635492198349)
          ·
            refine ⟨17100865997610238309574381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45602309326960635492198349 17100865997610238309574381)
            ·
              refine ⟨6412824749103839366090393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17100865997610238309574381 6412824749103839366090393)
              ·
                refine ⟨4809618561827879524567795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6412824749103839366090393 4809618561827879524567795)
                ·
                  refine ⟨7214427842741819286851693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4809618561827879524567795 7214427842741819286851693)
                  ·
                    refine ⟨2705410441028182232569385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7214427842741819286851693 2705410441028182232569385)
                    ·
                      refine ⟨2029057830771136674427039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2705410441028182232569385 2029057830771136674427039)
                      ·
                        rfl

theorem cell23_3951576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_3951576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951576 prefixEnd_3951576 := by exact prefixLift 3951576
  have htrace : WordTrace (prefixWord ++ tailWord_3951576) baseStart_3951576 baseEnd_3951576 := by
    simpa [prefixWord, tailWord_3951576, baseEnd_3951576] using wordTrace_append hprefix tailTrace_3951576
  have hstable : (prefixWord ++ tailWord_3951576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951576).length < 2 ^ (prefixWord ++ tailWord_3951576).sum := by decide
  have hdescent : baseEnd_3951576 < baseStart_3951576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951592 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_3951592 : Nat := 118140960795 + 3951592 * 2 ^ 59
def prefixEnd_3951592 : Nat := 4983230072969 + 3 ^ 40 * 3951592 * 2
def baseEnd_3951592 : Nat := 2029066046461608611826965

theorem tailTrace_3951592 : CollatzResearch.WordTrace tailWord_3951592 prefixEnd_3951592 2029066046461608611826965 := by
  unfold tailWord_3951592
  simp only [CollatzResearch.WordTrace]
  refine ⟨72063200350032268514456515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96084267133376358019275353 72063200350032268514456515)
  ·
    refine ⟨108094800525048402771684773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72063200350032268514456515 108094800525048402771684773)
    ·
      refine ⟨20267775098446575519690895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108094800525048402771684773 20267775098446575519690895)
      ·
        refine ⟨30401662647669863279536343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20267775098446575519690895 30401662647669863279536343)
        ·
          refine ⟨45602493971504794919304515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30401662647669863279536343 45602493971504794919304515)
          ·
            refine ⟨68403740957257192378956773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45602493971504794919304515 68403740957257192378956773)
            ·
              refine ⟨12825701429485723571054395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68403740957257192378956773 12825701429485723571054395)
              ·
                refine ⟨19238552144228585356581593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12825701429485723571054395 19238552144228585356581593)
                ·
                  refine ⟨14428914108171439017436195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19238552144228585356581593 14428914108171439017436195)
                  ·
                    refine ⟨21643371162257158526154293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14428914108171439017436195 21643371162257158526154293)
                    ·
                      refine ⟨2029066046461608611826965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21643371162257158526154293 2029066046461608611826965)
                      ·
                        rfl

theorem cell23_3951592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_3951592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951592 prefixEnd_3951592 := by exact prefixLift 3951592
  have htrace : WordTrace (prefixWord ++ tailWord_3951592) baseStart_3951592 baseEnd_3951592 := by
    simpa [prefixWord, tailWord_3951592, baseEnd_3951592] using wordTrace_append hprefix tailTrace_3951592
  have hstable : (prefixWord ++ tailWord_3951592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951592).length < 2 ^ (prefixWord ++ tailWord_3951592).sum := by decide
  have hdescent : baseEnd_3951592 < baseStart_3951592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951615 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 8]
def baseStart_3951615 : Nat := 118140960795 + 3951615 * 2 ^ 59
def prefixEnd_3951615 : Nat := 4983230072969 + 3 ^ 40 * 3951615 * 2
def baseEnd_3951615 : Nat := 2029077856516662021839359

theorem tailTrace_3951615 : CollatzResearch.WordTrace tailWord_3951615 prefixEnd_3951615 2029077856516662021839359 := by
  unfold tailWord_3951615
  simp only [CollatzResearch.WordTrace]
  refine ⟨144127239578981211957000299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96084826385987474638000199 144127239578981211957000299)
  ·
    refine ⟨216190859368471817935500449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144127239578981211957000299 216190859368471817935500449)
    ·
      refine ⟨162143144526353863451625337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216190859368471817935500449 162143144526353863451625337)
      ·
        refine ⟨121607358394765397588719003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162143144526353863451625337 121607358394765397588719003)
        ·
          refine ⟨182411037592148096383078505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121607358394765397588719003 182411037592148096383078505)
          ·
            refine ⟨136808278194111072287308879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182411037592148096383078505 136808278194111072287308879)
            ·
              refine ⟨205212417291166608430963319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136808278194111072287308879 205212417291166608430963319)
              ·
                refine ⟨307818625936749912646444979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205212417291166608430963319 307818625936749912646444979)
                ·
                  refine ⟨461727938905124868969667469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307818625936749912646444979 461727938905124868969667469)
                  ·
                    refine ⟨173147977089421825863625301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 461727938905124868969667469 173147977089421825863625301)
                    ·
                      refine ⟨2029077856516662021839359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 173147977089421825863625301 2029077856516662021839359)
                      ·
                        rfl

theorem cell23_3951615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_3951615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951615 prefixEnd_3951615 := by exact prefixLift 3951615
  have htrace : WordTrace (prefixWord ++ tailWord_3951615) baseStart_3951615 baseEnd_3951615 := by
    simpa [prefixWord, tailWord_3951615, baseEnd_3951615] using wordTrace_append hprefix tailTrace_3951615
  have hstable : (prefixWord ++ tailWord_3951615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951615).length < 2 ^ (prefixWord ++ tailWord_3951615).sum := by decide
  have hdescent : baseEnd_3951615 < baseStart_3951615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951642 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 1, 7]
def baseStart_3951642 : Nat := 118140960795 + 3951642 * 2 ^ 59
def prefixEnd_3951642 : Nat := 4983230072969 + 3 ^ 40 * 3951642 * 2
def baseEnd_3951642 : Nat := 676363906831444472067245

theorem tailTrace_3951642 : CollatzResearch.WordTrace tailWord_3951642 prefixEnd_3951642 676363906831444472067245 := by
  unfold tailWord_3951642
  simp only [CollatzResearch.WordTrace]
  refine ⟨36032056087470848892058295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96085482899922263712155453 36032056087470848892058295)
  ·
    refine ⟨54048084131206273338087443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36032056087470848892058295 54048084131206273338087443)
    ·
      refine ⟨81072126196809410007131165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54048084131206273338087443 81072126196809410007131165)
      ·
        refine ⟨30402047323803528752674187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81072126196809410007131165 30402047323803528752674187)
        ·
          refine ⟨45603070985705293129011281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30402047323803528752674187 45603070985705293129011281)
          ·
            refine ⟨34202303239278969846758461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45603070985705293129011281 34202303239278969846758461)
            ·
              refine ⟨12825863714729613692534423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34202303239278969846758461 12825863714729613692534423)
              ·
                refine ⟨19238795572094420538801635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12825863714729613692534423 19238795572094420538801635)
                ·
                  refine ⟨28858193358141630808202453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19238795572094420538801635 28858193358141630808202453)
                  ·
                    refine ⟨676363906831444472067245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28858193358141630808202453 676363906831444472067245)
                    ·
                      rfl

theorem cell23_3951642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_3951642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951642 prefixEnd_3951642 := by exact prefixLift 3951642
  have htrace : WordTrace (prefixWord ++ tailWord_3951642) baseStart_3951642 baseEnd_3951642 := by
    simpa [prefixWord, tailWord_3951642, baseEnd_3951642] using wordTrace_append hprefix tailTrace_3951642
  have hstable : (prefixWord ++ tailWord_3951642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951642).length < 2 ^ (prefixWord ++ tailWord_3951642).sum := by decide
  have hdescent : baseEnd_3951642 < baseStart_3951642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951692 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 1, 6, 4]
def baseStart_3951692 : Nat := 118140960795 + 3951692 * 2 ^ 59
def prefixEnd_3951692 : Nat := 4983230072969 + 3 ^ 40 * 3951692 * 2
def baseEnd_3951692 : Nat := 2029117394527058220576505

theorem tailTrace_3951692 : CollatzResearch.WordTrace tailWord_3951692 prefixEnd_3951692 2029117394527058220576505 := by
  unfold tailWord_3951692
  simp only [CollatzResearch.WordTrace]
  refine ⟨72065023999851127053776665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96086698666468169405035553 72065023999851127053776665)
  ·
    refine ⟨54048767999888345290332499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72065023999851127053776665 54048767999888345290332499)
    ·
      refine ⟨81073151999832517935498749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54048767999888345290332499 81073151999832517935498749)
      ·
        refine ⟨30402431999937194225812031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81073151999832517935498749 30402431999937194225812031)
        ·
          refine ⟨45603647999905791338718047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30402431999937194225812031 45603647999905791338718047)
          ·
            refine ⟨68405471999858687008077071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45603647999905791338718047 68405471999858687008077071)
            ·
              refine ⟨102608207999788030512115607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68405471999858687008077071 102608207999788030512115607)
              ·
                refine ⟨153912311999682045768173411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102608207999788030512115607 153912311999682045768173411)
                ·
                  refine ⟨230868467999523068652260117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153912311999682045768173411 230868467999523068652260117)
                  ·
                    refine ⟨10821959437477643843074693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 230868467999523068652260117 10821959437477643843074693)
                    ·
                      refine ⟨2029117394527058220576505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10821959437477643843074693 2029117394527058220576505)
                      ·
                        rfl

theorem cell23_3951692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_3951692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951692 prefixEnd_3951692 := by exact prefixLift 3951692
  have htrace : WordTrace (prefixWord ++ tailWord_3951692) baseStart_3951692 baseEnd_3951692 := by
    simpa [prefixWord, tailWord_3951692, baseEnd_3951692] using wordTrace_append hprefix tailTrace_3951692
  have hstable : (prefixWord ++ tailWord_3951692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951692).length < 2 ^ (prefixWord ++ tailWord_3951692).sum := by decide
  have hdescent : baseEnd_3951692 < baseStart_3951692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951706 : List Nat := [3, 1, 1, 2, 1, 1, 2, 7, 1, 4]
def baseStart_3951706 : Nat := 118140960795 + 3951706 * 2 ^ 59
def prefixEnd_3951706 : Nat := 4983230072969 + 3 ^ 40 * 3951706 * 2
def baseEnd_3951706 : Nat := 676374861085407055267147

theorem tailTrace_3951706 : CollatzResearch.WordTrace tailWord_3951706 prefixEnd_3951706 676374861085407055267147 := by
  unfold tailWord_3951706
  simp only [CollatzResearch.WordTrace]
  refine ⟨36032639655412883624640743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96087039081101022999041981 36032639655412883624640743)
  ·
    refine ⟨54048959483119325436961115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36032639655412883624640743 54048959483119325436961115)
    ·
      refine ⟨81073439224678988155441673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54048959483119325436961115 81073439224678988155441673)
      ·
        refine ⟨60805079418509241116581255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81073439224678988155441673 60805079418509241116581255)
        ·
          refine ⟨91207619127763861674871883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60805079418509241116581255 91207619127763861674871883)
          ·
            refine ⟨136811428691645792512307825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91207619127763861674871883 136811428691645792512307825)
            ·
              refine ⟨102608571518734344384230869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136811428691645792512307825 102608571518734344384230869)
              ·
                refine ⟨2404888394970336196505411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 102608571518734344384230869 2404888394970336196505411)
                ·
                  refine ⟨3607332592455504294758117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2404888394970336196505411 3607332592455504294758117)
                  ·
                    refine ⟨676374861085407055267147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3607332592455504294758117 676374861085407055267147)
                    ·
                      rfl

theorem cell23_3951706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 1, 4].length) (baseStart_3951706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951706 prefixEnd_3951706 := by exact prefixLift 3951706
  have htrace : WordTrace (prefixWord ++ tailWord_3951706) baseStart_3951706 baseEnd_3951706 := by
    simpa [prefixWord, tailWord_3951706, baseEnd_3951706] using wordTrace_append hprefix tailTrace_3951706
  have hstable : (prefixWord ++ tailWord_3951706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951706).length < 2 ^ (prefixWord ++ tailWord_3951706).sum := by decide
  have hdescent : baseEnd_3951706 < baseStart_3951706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951739 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 3, 5, 2]
def baseStart_3951739 : Nat := 118140960795 + 3951739 * 2 ^ 59
def prefixEnd_3951739 : Nat := 4983230072969 + 3 ^ 40 * 3951739 * 2
def baseEnd_3951739 : Nat := 2029141528117819536688789

theorem tailTrace_3951739 : CollatzResearch.WordTrace tailWord_3951739 prefixEnd_3951739 2029141528117819536688789 := by
  unfold tailWord_3951739
  simp only [CollatzResearch.WordTrace]
  refine ⟨144131762230531981134514271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96087841487021320756342847 144131762230531981134514271)
  ·
    refine ⟨216197643345797971701771407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144131762230531981134514271 216197643345797971701771407)
    ·
      refine ⟨324296465018696957552657111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216197643345797971701771407 324296465018696957552657111)
      ·
        refine ⟨486444697528045436328985667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324296465018696957552657111 486444697528045436328985667)
        ·
          refine ⟨729667046292068154493478501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486444697528045436328985667 729667046292068154493478501)
          ·
            refine ⟨136812571179762778967527219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 729667046292068154493478501 136812571179762778967527219)
            ·
              refine ⟨205218856769644168451290829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136812571179762778967527219 205218856769644168451290829)
              ·
                refine ⟨76957071288616563169234061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205218856769644168451290829 76957071288616563169234061)
                ·
                  refine ⟨28858901733231211188462773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76957071288616563169234061 28858901733231211188462773)
                  ·
                    refine ⟨2705522037490426048918385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28858901733231211188462773 2705522037490426048918385)
                    ·
                      refine ⟨2029141528117819536688789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2705522037490426048918385 2029141528117819536688789)
                      ·
                        rfl

theorem cell23_3951739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 5, 2].length) (baseStart_3951739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951739 prefixEnd_3951739 := by exact prefixLift 3951739
  have htrace : WordTrace (prefixWord ++ tailWord_3951739) baseStart_3951739 baseEnd_3951739 := by
    simpa [prefixWord, tailWord_3951739, baseEnd_3951739] using wordTrace_append hprefix tailTrace_3951739
  have hstable : (prefixWord ++ tailWord_3951739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951739).length < 2 ^ (prefixWord ++ tailWord_3951739).sum := by decide
  have hdescent : baseEnd_3951739 < baseStart_3951739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951779 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 4, 4]
def baseStart_3951779 : Nat := 118140960795 + 3951779 * 2 ^ 59
def prefixEnd_3951779 : Nat := 4983230072969 + 3 ^ 40 * 3951779 * 2
def baseEnd_3951779 : Nat := 676387355781333126729535

theorem tailTrace_3951779 : CollatzResearch.WordTrace tailWord_3951779 prefixEnd_3951779 676387355781333126729535 := by
  unfold tailWord_3951779
  simp only [CollatzResearch.WordTrace]
  refine ⟨144133221150387067965970391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96088814100258045310646927 144133221150387067965970391)
  ·
    refine ⟨216199831725580601948955587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144133221150387067965970391 216199831725580601948955587)
    ·
      refine ⟨324299747588370902923433381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216199831725580601948955587 324299747588370902923433381)
      ·
        refine ⟨60806202672819544298143759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324299747588370902923433381 60806202672819544298143759)
        ·
          refine ⟨91209304009229316447215639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60806202672819544298143759 91209304009229316447215639)
          ·
            refine ⟨136813956013843974670823459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91209304009229316447215639 136813956013843974670823459)
            ·
              refine ⟨205220934020765962006235189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136813956013843974670823459 205220934020765962006235189)
              ·
                refine ⟨19239462564446808938084549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205220934020765962006235189 19239462564446808938084549)
                ·
                  refine ⟨3607399230833776675890853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19239462564446808938084549 3607399230833776675890853)
                  ·
                    refine ⟨676387355781333126729535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3607399230833776675890853 676387355781333126729535)
                    ·
                      rfl

theorem cell23_3951779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 4].length) (baseStart_3951779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951779 prefixEnd_3951779 := by exact prefixLift 3951779
  have htrace : WordTrace (prefixWord ++ tailWord_3951779) baseStart_3951779 baseEnd_3951779 := by
    simpa [prefixWord, tailWord_3951779, baseEnd_3951779] using wordTrace_append hprefix tailTrace_3951779
  have hstable : (prefixWord ++ tailWord_3951779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951779).length < 2 ^ (prefixWord ++ tailWord_3951779).sum := by decide
  have hdescent : baseEnd_3951779 < baseStart_3951779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951780 : List Nat := [2, 3, 1, 2, 3, 2, 1, 4, 1, 1, 3]
def baseStart_3951780 : Nat := 118140960795 + 3951780 * 2 ^ 59
def prefixEnd_3951780 : Nat := 4983230072969 + 3 ^ 40 * 3951780 * 2
def baseEnd_3951780 : Nat := 2029162580824653876276101

theorem tailTrace_3951780 : CollatzResearch.WordTrace tailWord_3951780 prefixEnd_3951780 2029162580824653876276101 := by
  unfold tailWord_3951780
  simp only [CollatzResearch.WordTrace]
  refine ⟨72066628811691722568378397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96088838415588963424504529 72066628811691722568378397)
  ·
    refine ⟨27024985804384395963141899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72066628811691722568378397 27024985804384395963141899)
    ·
      refine ⟨40537478706576593944712849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27024985804384395963141899 40537478706576593944712849)
      ·
        refine ⟨30403109029932445458534637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40537478706576593944712849 30403109029932445458534637)
        ·
          refine ⟨11401165886224667046950489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30403109029932445458534637 11401165886224667046950489)
          ·
            refine ⟨8550874414668500285212867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11401165886224667046950489 8550874414668500285212867)
            ·
              refine ⟨12826311622002750427819301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8550874414668500285212867 12826311622002750427819301)
              ·
                refine ⟨2404933429125515705216119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12826311622002750427819301 2404933429125515705216119)
                ·
                  refine ⟨3607400143688273557824179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2404933429125515705216119 3607400143688273557824179)
                  ·
                    refine ⟨5411100215532410336736269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3607400143688273557824179 5411100215532410336736269)
                    ·
                      refine ⟨2029162580824653876276101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5411100215532410336736269 2029162580824653876276101)
                      ·
                        rfl

theorem cell23_3951780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_3951780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951780 prefixEnd_3951780 := by exact prefixLift 3951780
  have htrace : WordTrace (prefixWord ++ tailWord_3951780) baseStart_3951780 baseEnd_3951780 := by
    simpa [prefixWord, tailWord_3951780, baseEnd_3951780] using wordTrace_append hprefix tailTrace_3951780
  have hstable : (prefixWord ++ tailWord_3951780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951780).length < 2 ^ (prefixWord ++ tailWord_3951780).sum := by decide
  have hdescent : baseEnd_3951780 < baseStart_3951780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951819 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 3]
def baseStart_3951819 : Nat := 118140960795 + 3951819 * 2 ^ 59
def prefixEnd_3951819 : Nat := 4983230072969 + 3 ^ 40 * 3951819 * 2
def baseEnd_3951819 : Nat := 2029182606570179223688421

theorem tailTrace_3951819 : CollatzResearch.WordTrace tailWord_3951819 prefixEnd_3951819 2029182606570179223688421 := by
  unfold tailWord_3951819
  simp only [CollatzResearch.WordTrace]
  refine ⟨144134680070242154797426511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96089786713494769864951007 144134680070242154797426511)
  ·
    refine ⟨216202020105363232196139767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144134680070242154797426511 216202020105363232196139767)
    ·
      refine ⟨324303030158044848294209651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216202020105363232196139767 324303030158044848294209651)
      ·
        refine ⟨486454545237067272441314477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324303030158044848294209651 486454545237067272441314477)
        ·
          refine ⟨182420454463900227165492929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 486454545237067272441314477 182420454463900227165492929)
          ·
            refine ⟨136815340847925170374119697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182420454463900227165492929 136815340847925170374119697)
            ·
              refine ⟨102611505635943877780589773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136815340847925170374119697 102611505635943877780589773)
              ·
                refine ⟨38479314613478954167721165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102611505635943877780589773 38479314613478954167721165)
                ·
                  refine ⟨14429742980054607812895437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38479314613478954167721165 14429742980054607812895437)
                  ·
                    refine ⟨5411153617520477929835789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14429742980054607812895437 5411153617520477929835789)
                    ·
                      refine ⟨2029182606570179223688421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5411153617520477929835789 2029182606570179223688421)
                      ·
                        rfl

theorem cell23_3951819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 3].length) (baseStart_3951819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951819 prefixEnd_3951819 := by exact prefixLift 3951819
  have htrace : WordTrace (prefixWord ++ tailWord_3951819) baseStart_3951819 baseEnd_3951819 := by
    simpa [prefixWord, tailWord_3951819, baseEnd_3951819] using wordTrace_append hprefix tailTrace_3951819
  have hstable : (prefixWord ++ tailWord_3951819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951819).length < 2 ^ (prefixWord ++ tailWord_3951819).sum := by decide
  have hdescent : baseEnd_3951819 < baseStart_3951819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951830 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_3951830 : Nat := 118140960795 + 3951830 * 2 ^ 59
def prefixEnd_3951830 : Nat := 4983230072969 + 3 ^ 40 * 3951830 * 2
def baseEnd_3951830 : Nat := 676396084952459560216957

theorem tailTrace_3951830 : CollatzResearch.WordTrace tailWord_3951830 prefixEnd_3951830 676396084952459560216957 := by
  unfold tailWord_3951830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9008442579575143979754809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96090054182134869117384629 9008442579575143979754809)
  ·
    refine ⟨6756331934681357984816107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9008442579575143979754809 6756331934681357984816107)
    ·
      refine ⟨10134497902022036977224161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6756331934681357984816107 10134497902022036977224161)
      ·
        refine ⟨7600873426516527732918121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10134497902022036977224161 7600873426516527732918121)
        ·
          refine ⟨5700655069887395799688591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7600873426516527732918121 5700655069887395799688591)
          ·
            refine ⟨8550982604831093699532887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5700655069887395799688591 8550982604831093699532887)
            ·
              refine ⟨12826473907246640549299331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8550982604831093699532887 12826473907246640549299331)
              ·
                refine ⟨19239710860869960823948997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12826473907246640549299331 19239710860869960823948997)
                ·
                  refine ⟨3607445786413117654490437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19239710860869960823948997 3607445786413117654490437)
                  ·
                    refine ⟨676396084952459560216957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3607445786413117654490437 676396084952459560216957)
                    ·
                      rfl

theorem cell23_3951830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_3951830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951830 prefixEnd_3951830 := by exact prefixLift 3951830
  have htrace : WordTrace (prefixWord ++ tailWord_3951830) baseStart_3951830 baseEnd_3951830 := by
    simpa [prefixWord, tailWord_3951830, baseEnd_3951830] using wordTrace_append hprefix tailTrace_3951830
  have hstable : (prefixWord ++ tailWord_3951830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951830).length < 2 ^ (prefixWord ++ tailWord_3951830).sum := by decide
  have hdescent : baseEnd_3951830 < baseStart_3951830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951837 : List Nat := [1, 4, 3, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_3951837 : Nat := 118140960795 + 3951837 * 2 ^ 59
def prefixEnd_3951837 : Nat := 4983230072969 + 3 ^ 40 * 3951837 * 2
def baseEnd_3951837 : Nat := 2029191849221960153263339

theorem tailTrace_3951837 : CollatzResearch.WordTrace tailWord_3951837 prefixEnd_3951837 2029191849221960153263339 := by
  unfold tailWord_3951837
  simp only [CollatzResearch.WordTrace]
  refine ⟨144135336584176943871581765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96090224389451295914387843 144135336584176943871581765)
  ·
    refine ⟨27025375609533176975921581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144135336584176943871581765 27025375609533176975921581)
    ·
      refine ⟨10134515853574941365970593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27025375609533176975921581 10134515853574941365970593)
      ·
        refine ⟨7600886890181206024477945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10134515853574941365970593 7600886890181206024477945)
        ·
          refine ⟨5700665167635904518358459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7600886890181206024477945 5700665167635904518358459)
          ·
            refine ⟨8550997751453856777537689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5700665167635904518358459 8550997751453856777537689)
            ·
              refine ⟨6413248313590392583153267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8550997751453856777537689 6413248313590392583153267)
              ·
                refine ⟨9619872470385588874729901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6413248313590392583153267 9619872470385588874729901)
                ·
                  refine ⟨3607452176394595828023713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9619872470385588874729901 3607452176394595828023713)
                  ·
                    refine ⟨2705589132295946871017785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3607452176394595828023713 2705589132295946871017785)
                    ·
                      refine ⟨2029191849221960153263339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2705589132295946871017785 2029191849221960153263339)
                      ·
                        rfl

theorem cell23_3951837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_3951837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951837 prefixEnd_3951837 := by exact prefixLift 3951837
  have htrace : WordTrace (prefixWord ++ tailWord_3951837) baseStart_3951837 baseEnd_3951837 := by
    simpa [prefixWord, tailWord_3951837, baseEnd_3951837] using wordTrace_append hprefix tailTrace_3951837
  have hstable : (prefixWord ++ tailWord_3951837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951837).length < 2 ^ (prefixWord ++ tailWord_3951837).sum := by decide
  have hdescent : baseEnd_3951837 < baseStart_3951837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951853 : List Nat := [1, 5, 1, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_3951853 : Nat := 118140960795 + 3951853 * 2 ^ 59
def prefixEnd_3951853 : Nat := 4983230072969 + 3 ^ 40 * 3951853 * 2
def baseEnd_3951853 : Nat := 2029200064912432090663265

theorem tailTrace_3951853 : CollatzResearch.WordTrace tailWord_3951853 prefixEnd_3951853 2029200064912432090663265 := by
  unfold tailWord_3951853
  simp only [CollatzResearch.WordTrace]
  refine ⟨144135920152118978604164213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96090613434745985736109475 144135920152118978604164213)
  ·
    refine ⟨13512742514261154244140395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144135920152118978604164213 13512742514261154244140395)
    ·
      refine ⟨20269113771391731366210593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13512742514261154244140395 20269113771391731366210593)
      ·
        refine ⟨15201835328543798524657945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20269113771391731366210593 15201835328543798524657945)
        ·
          refine ⟨11401376496407848893493459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15201835328543798524657945 11401376496407848893493459)
          ·
            refine ⟨17102064744611773340240189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11401376496407848893493459 17102064744611773340240189)
            ·
              refine ⟨6413274279229415002590071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17102064744611773340240189 6413274279229415002590071)
              ·
                refine ⟨9619911418844122503885107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6413274279229415002590071 9619911418844122503885107)
                ·
                  refine ⟨14429867128266183755827661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9619911418844122503885107 14429867128266183755827661)
                  ·
                    refine ⟨5411200173099818908435373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14429867128266183755827661 5411200173099818908435373)
                    ·
                      refine ⟨2029200064912432090663265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5411200173099818908435373 2029200064912432090663265)
                      ·
                        rfl

theorem cell23_3951853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_3951853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951853 prefixEnd_3951853 := by exact prefixLift 3951853
  have htrace : WordTrace (prefixWord ++ tailWord_3951853) baseStart_3951853 baseEnd_3951853 := by
    simpa [prefixWord, tailWord_3951853, baseEnd_3951853] using wordTrace_append hprefix tailTrace_3951853
  have hstable : (prefixWord ++ tailWord_3951853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951853).length < 2 ^ (prefixWord ++ tailWord_3951853).sum := by decide
  have hdescent : baseEnd_3951853 < baseStart_3951853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951860 : List Nat := [2, 6, 1, 2, 1, 1, 1, 9]
def baseStart_3951860 : Nat := 118140960795 + 3951860 * 2 ^ 59
def prefixEnd_3951860 : Nat := 4983230072969 + 3 ^ 40 * 3951860 * 2
def baseEnd_3951860 : Nat := 75155691084333835676879

theorem tailTrace_3951860 : CollatzResearch.WordTrace tailWord_3951860 prefixEnd_3951860 75155691084333835676879 := by
  unfold tailWord_3951860
  simp only [CollatzResearch.WordTrace]
  refine ⟨72068087731546809399834517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96090783642062412533112689 72068087731546809399834517)
  ·
    refine ⟨3378191612416256690617243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72068087731546809399834517 3378191612416256690617243)
    ·
      refine ⟨5067287418624385035925865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3378191612416256690617243 5067287418624385035925865)
      ·
        refine ⟨3800465563968288776944399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5067287418624385035925865 3800465563968288776944399)
        ·
          refine ⟨5700698345952433165416599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3800465563968288776944399 5700698345952433165416599)
          ·
            refine ⟨8551047518928649748124899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5700698345952433165416599 8551047518928649748124899)
            ·
              refine ⟨12826571278392974622187349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8551047518928649748124899 12826571278392974622187349)
              ·
                refine ⟨75155691084333835676879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12826571278392974622187349 75155691084333835676879)
                ·
                  rfl

theorem cell23_3951860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 9].length) (baseStart_3951860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951860 prefixEnd_3951860 := by exact prefixLift 3951860
  have htrace : WordTrace (prefixWord ++ tailWord_3951860) baseStart_3951860 baseEnd_3951860 := by
    simpa [prefixWord, tailWord_3951860, baseEnd_3951860] using wordTrace_append hprefix tailTrace_3951860
  have hstable : (prefixWord ++ tailWord_3951860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951860).length < 2 ^ (prefixWord ++ tailWord_3951860).sum := by decide
  have hdescent : baseEnd_3951860 < baseStart_3951860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951904 : List Nat := [2, 1, 1, 5, 4, 1, 2, 1, 2, 1, 3]
def baseStart_3951904 : Nat := 118140960795 + 3951904 * 2 ^ 59
def prefixEnd_3951904 : Nat := 4983230072969 + 3 ^ 40 * 3951904 * 2
def baseEnd_3951904 : Nat := 2029226252425811391125531

theorem tailTrace_3951904 : CollatzResearch.WordTrace tailWord_3951904 prefixEnd_3951904 2029226252425811391125531 := by
  unfold tailWord_3951904
  simp only [CollatzResearch.WordTrace]
  refine ⟨72068890137467107157135383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96091853516622809542847177 72068890137467107157135383)
  ·
    refine ⟨108103335206200660735703075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72068890137467107157135383 108103335206200660735703075)
    ·
      refine ⟨162155002809300991103554613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108103335206200660735703075 162155002809300991103554613)
      ·
        refine ⟨15202031513371967915958245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162155002809300991103554613 15202031513371967915958245)
        ·
          refine ⟨2850380908757243984242171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15202031513371967915958245 2850380908757243984242171)
          ·
            refine ⟨4275571363135865976363257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2850380908757243984242171 4275571363135865976363257)
            ·
              refine ⟨3206678522351899482272443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4275571363135865976363257 3206678522351899482272443)
              ·
                refine ⟨4810017783527849223408665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3206678522351899482272443 4810017783527849223408665)
                ·
                  refine ⟨3607513337645886917556499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4810017783527849223408665 3607513337645886917556499)
                  ·
                    refine ⟨5411270006468830376334749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3607513337645886917556499 5411270006468830376334749)
                    ·
                      refine ⟨2029226252425811391125531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5411270006468830376334749 2029226252425811391125531)
                      ·
                        rfl

theorem cell23_3951904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_3951904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951904 prefixEnd_3951904 := by exact prefixLift 3951904
  have htrace : WordTrace (prefixWord ++ tailWord_3951904) baseStart_3951904 baseEnd_3951904 := by
    simpa [prefixWord, tailWord_3951904, baseEnd_3951904] using wordTrace_append hprefix tailTrace_3951904
  have hstable : (prefixWord ++ tailWord_3951904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951904).length < 2 ^ (prefixWord ++ tailWord_3951904).sum := by decide
  have hdescent : baseEnd_3951904 < baseStart_3951904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951956 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_3951956 : Nat := 118140960795 + 3951956 * 2 ^ 59
def prefixEnd_3951956 : Nat := 4983230072969 + 3 ^ 40 * 3951956 * 2
def baseEnd_3951956 : Nat := 2029252953419845187675291

theorem tailTrace_3951956 : CollatzResearch.WordTrace tailWord_3951956 prefixEnd_3951956 2029252953419845187675291 := by
  unfold tailWord_3951956
  simp only [CollatzResearch.WordTrace]
  refine ⟨72069838435372913597581861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96093117913830551463442481 72069838435372913597581861)
  ·
    refine ⟨13513094706632421299546599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72069838435372913597581861 13513094706632421299546599)
    ·
      refine ⟨20269642059948631949319899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13513094706632421299546599 20269642059948631949319899)
      ·
        refine ⟨30404463089922947923979849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20269642059948631949319899 30404463089922947923979849)
        ·
          refine ⟨22803347317442210942984887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30404463089922947923979849 22803347317442210942984887)
          ·
            refine ⟨34205020976163316414477331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22803347317442210942984887 34205020976163316414477331)
            ·
              refine ⟨51307531464244974621715997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34205020976163316414477331 51307531464244974621715997)
              ·
                refine ⟨19240324299091865483143499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51307531464244974621715997 19240324299091865483143499)
                ·
                  refine ⟨28860486448637798224715249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19240324299091865483143499 28860486448637798224715249)
                  ·
                    refine ⟨21645364836478348668536437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28860486448637798224715249 21645364836478348668536437)
                    ·
                      refine ⟨2029252953419845187675291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21645364836478348668536437 2029252953419845187675291)
                      ·
                        rfl

theorem cell23_3951956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_3951956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951956 prefixEnd_3951956 := by exact prefixLift 3951956
  have htrace : WordTrace (prefixWord ++ tailWord_3951956) baseStart_3951956 baseEnd_3951956 := by
    simpa [prefixWord, tailWord_3951956, baseEnd_3951956] using wordTrace_append hprefix tailTrace_3951956
  have hstable : (prefixWord ++ tailWord_3951956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951956).length < 2 ^ (prefixWord ++ tailWord_3951956).sum := by decide
  have hdescent : baseEnd_3951956 < baseStart_3951956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951979 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 6]
def baseStart_3951979 : Nat := 118140960795 + 3951979 * 2 ^ 59
def prefixEnd_3951979 : Nat := 4983230072969 + 3 ^ 40 * 3951979 * 2
def baseEnd_3951979 : Nat := 2029264763474898597687685

theorem tailTrace_3951979 : CollatzResearch.WordTrace tailWord_3951979 prefixEnd_3951979 2029264763474898597687685 := by
  unfold tailWord_3951979
  simp only [CollatzResearch.WordTrace]
  refine ⟨144140515749662502123250991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96093677166441668082167327 144140515749662502123250991)
  ·
    refine ⟨216210773624493753184876487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144140515749662502123250991 216210773624493753184876487)
    ·
      refine ⟨324316160436740629777314731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216210773624493753184876487 324316160436740629777314731)
      ·
        refine ⟨486474240655110944665972097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324316160436740629777314731 486474240655110944665972097)
        ·
          refine ⟨364855680491333208499479073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486474240655110944665972097 364855680491333208499479073)
          ·
            refine ⟨273641760368499906374609305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364855680491333208499479073 273641760368499906374609305)
            ·
              refine ⟨205231320276374929780956979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273641760368499906374609305 205231320276374929780956979)
              ·
                refine ⟨307846980414562394671435469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205231320276374929780956979 307846980414562394671435469)
                ·
                  refine ⟨115442617655460898001788301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307846980414562394671435469 115442617655460898001788301)
                  ·
                    refine ⟨43290981620797836750670613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115442617655460898001788301 43290981620797836750670613)
                    ·
                      refine ⟨2029264763474898597687685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43290981620797836750670613 2029264763474898597687685)
                      ·
                        rfl

theorem cell23_3951979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 6].length) (baseStart_3951979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3951979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3951979 prefixEnd_3951979 := by exact prefixLift 3951979
  have htrace : WordTrace (prefixWord ++ tailWord_3951979) baseStart_3951979 baseEnd_3951979 := by
    simpa [prefixWord, tailWord_3951979, baseEnd_3951979] using wordTrace_append hprefix tailTrace_3951979
  have hstable : (prefixWord ++ tailWord_3951979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951979).length < 2 ^ (prefixWord ++ tailWord_3951979).sum := by decide
  have hdescent : baseEnd_3951979 < baseStart_3951979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952026 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6]
def baseStart_3952026 : Nat := 118140960795 + 3952026 * 2 ^ 59
def prefixEnd_3952026 : Nat := 4983230072969 + 3 ^ 40 * 3952026 * 2
def baseEnd_3952026 : Nat := 2029288897065659913799969

theorem tailTrace_3952026 : CollatzResearch.WordTrace tailWord_3952026 prefixEnd_3952026 2029288897065659913799969 := by
  unfold tailWord_3952026
  simp only [CollatzResearch.WordTrace]
  refine ⟨36035557495123057287552983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96094819986994819433474621 36035557495123057287552983)
  ·
    refine ⟨54053336242684585931329475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36035557495123057287552983 54053336242684585931329475)
    ·
      refine ⟨81080004364026878896994213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54053336242684585931329475 81080004364026878896994213)
      ·
        refine ⟨15202500818255039793186415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81080004364026878896994213 15202500818255039793186415)
        ·
          refine ⟨22803751227382559689779623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15202500818255039793186415 22803751227382559689779623)
          ·
            refine ⟨34205626841073839534669435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22803751227382559689779623 34205626841073839534669435)
            ·
              refine ⟨51308440261610759302004153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34205626841073839534669435 51308440261610759302004153)
              ·
                refine ⟨38481330196208069476503115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51308440261610759302004153 38481330196208069476503115)
                ·
                  refine ⟨57721995294312104214754673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38481330196208069476503115 57721995294312104214754673)
                  ·
                    refine ⟨43291496470734078161066005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57721995294312104214754673 43291496470734078161066005)
                    ·
                      refine ⟨2029288897065659913799969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43291496470734078161066005 2029288897065659913799969)
                      ·
                        rfl

theorem cell23_3952026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_3952026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952026 prefixEnd_3952026 := by exact prefixLift 3952026
  have htrace : WordTrace (prefixWord ++ tailWord_3952026) baseStart_3952026 baseEnd_3952026 := by
    simpa [prefixWord, tailWord_3952026, baseEnd_3952026] using wordTrace_append hprefix tailTrace_3952026
  have hstable : (prefixWord ++ tailWord_3952026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952026).length < 2 ^ (prefixWord ++ tailWord_3952026).sum := by decide
  have hdescent : baseEnd_3952026 < baseStart_3952026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952090 : List Nat := [3, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4]
def baseStart_3952090 : Nat := 118140960795 + 3952090 * 2 ^ 59
def prefixEnd_3952090 : Nat := 4983230072969 + 3 ^ 40 * 3952090 * 2
def baseEnd_3952090 : Nat := 2029321759827547663399675

theorem tailTrace_3952090 : CollatzResearch.WordTrace tailWord_3952090 prefixEnd_3952090 2029321759827547663399675 := by
  unfold tailWord_3952090
  simp only [CollatzResearch.WordTrace]
  refine ⟨36036141063065092020135431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96096376168173578720361149 36036141063065092020135431)
  ·
    refine ⟨54054211594597638030203147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36036141063065092020135431 54054211594597638030203147)
    ·
      refine ⟨81081317391896457045304721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54054211594597638030203147 81081317391896457045304721)
      ·
        refine ⟨60810988043922342783978541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81081317391896457045304721 60810988043922342783978541)
        ·
          refine ⟨22804120516470878543991953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60810988043922342783978541 22804120516470878543991953)
          ·
            refine ⟨17103090387353158907993965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22804120516470878543991953 17103090387353158907993965)
            ·
              refine ⟨6413658895257434590497737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17103090387353158907993965 6413658895257434590497737)
              ·
                refine ⟨4810244171443075942873303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6413658895257434590497737 4810244171443075942873303)
                ·
                  refine ⟨7215366257164613914309955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4810244171443075942873303 7215366257164613914309955)
                  ·
                    refine ⟨10823049385746920871464933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7215366257164613914309955 10823049385746920871464933)
                    ·
                      refine ⟨2029321759827547663399675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10823049385746920871464933 2029321759827547663399675)
                      ·
                        rfl

theorem cell23_3952090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_3952090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952090 prefixEnd_3952090 := by exact prefixLift 3952090
  have htrace : WordTrace (prefixWord ++ tailWord_3952090) baseStart_3952090 baseEnd_3952090 := by
    simpa [prefixWord, tailWord_3952090, baseEnd_3952090] using wordTrace_append hprefix tailTrace_3952090
  have hstable : (prefixWord ++ tailWord_3952090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952090).length < 2 ^ (prefixWord ++ tailWord_3952090).sum := by decide
  have hdescent : baseEnd_3952090 < baseStart_3952090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952103 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_3952103 : Nat := 118140960795 + 3952103 * 2 ^ 59
def prefixEnd_3952103 : Nat := 4983230072969 + 3 ^ 40 * 3952103 * 2
def baseEnd_3952103 : Nat := 2029328435076056112537115

theorem tailTrace_3952103 : CollatzResearch.WordTrace tailWord_3952103 prefixEnd_3952103 2029328435076056112537115 := by
  unfold tailWord_3952103
  simp only [CollatzResearch.WordTrace]
  refine ⟨144145038401213271300764963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96096692267475514200509975 144145038401213271300764963)
  ·
    refine ⟨216217557601819906951147445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144145038401213271300764963 216217557601819906951147445)
    ·
      refine ⟨20270396025170616276670073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216217557601819906951147445 20270396025170616276670073)
      ·
        refine ⟨15202797018877962207502555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20270396025170616276670073 15202797018877962207502555)
        ·
          refine ⟨22804195528316943311253833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15202797018877962207502555 22804195528316943311253833)
          ·
            refine ⟨17103146646237707483440375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22804195528316943311253833 17103146646237707483440375)
            ·
              refine ⟨25654719969356561225160563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17103146646237707483440375 25654719969356561225160563)
              ·
                refine ⟨38482079954034841837740845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25654719969356561225160563 38482079954034841837740845)
                ·
                  refine ⟨14430779982763065689152817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38482079954034841837740845 14430779982763065689152817)
                  ·
                    refine ⟨10823084987072299266864613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14430779982763065689152817 10823084987072299266864613)
                    ·
                      refine ⟨2029328435076056112537115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10823084987072299266864613 2029328435076056112537115)
                      ·
                        rfl

theorem cell23_3952103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_3952103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952103 prefixEnd_3952103 := by exact prefixLift 3952103
  have htrace : WordTrace (prefixWord ++ tailWord_3952103) baseStart_3952103 baseEnd_3952103 := by
    simpa [prefixWord, tailWord_3952103, baseEnd_3952103] using wordTrace_append hprefix tailTrace_3952103
  have hstable : (prefixWord ++ tailWord_3952103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952103).length < 2 ^ (prefixWord ++ tailWord_3952103).sum := by decide
  have hdescent : baseEnd_3952103 < baseStart_3952103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952117 : List Nat := [1, 3, 5, 1, 1, 1, 1, 4, 2, 4]
def baseStart_3952117 : Nat := 118140960795 + 3952117 * 2 ^ 59
def prefixEnd_3952117 : Nat := 4983230072969 + 3 ^ 40 * 3952117 * 2
def baseEnd_3952117 : Nat := 676445207935073019254017

theorem tailTrace_3952117 : CollatzResearch.WordTrace tailWord_3952117 prefixEnd_3952117 676445207935073019254017 := by
  unfold tailWord_3952117
  simp only [CollatzResearch.WordTrace]
  refine ⟨144145549023162551691774605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96097032682108367794516403 144145549023162551691774605)
  ·
    refine ⟨54054580883685956884415477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144145549023162551691774605 54054580883685956884415477)
    ·
      refine ⟨5067616957845558457913951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54054580883685956884415477 5067616957845558457913951)
      ·
        refine ⟨7601425436768337686870927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5067616957845558457913951 7601425436768337686870927)
        ·
          refine ⟨11402138155152506530306391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7601425436768337686870927 11402138155152506530306391)
          ·
            refine ⟨17103207232728759795459587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11402138155152506530306391 17103207232728759795459587)
            ·
              refine ⟨25654810849093139693189381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17103207232728759795459587 25654810849093139693189381)
              ·
                refine ⟨4810277034204963692473009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25654810849093139693189381 4810277034204963692473009)
                ·
                  refine ⟨3607707775653722769354757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4810277034204963692473009 3607707775653722769354757)
                  ·
                    refine ⟨676445207935073019254017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3607707775653722769354757 676445207935073019254017)
                    ·
                      rfl

theorem cell23_3952117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_3952117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952117 prefixEnd_3952117 := by exact prefixLift 3952117
  have htrace : WordTrace (prefixWord ++ tailWord_3952117) baseStart_3952117 baseEnd_3952117 := by
    simpa [prefixWord, tailWord_3952117, baseEnd_3952117] using wordTrace_append hprefix tailTrace_3952117
  have hstable : (prefixWord ++ tailWord_3952117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952117).length < 2 ^ (prefixWord ++ tailWord_3952117).sum := by decide
  have hdescent : baseEnd_3952117 < baseStart_3952117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952130 : List Nat := [3, 4, 1, 2, 1, 1, 3, 8]
def baseStart_3952130 : Nat := 118140960795 + 3952130 * 2 ^ 59
def prefixEnd_3952130 : Nat := 4983230072969 + 3 ^ 40 * 3952130 * 2
def baseEnd_3952130 : Nat := 75160825890878796551833

theorem tailTrace_3952130 : CollatzResearch.WordTrace tailWord_3952130 prefixEnd_3952130 75160825890878796551833 := by
  unfold tailWord_3952130
  simp only [CollatzResearch.WordTrace]
  refine ⟨36036505793028863727999461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96097348781410303274665229 36036505793028863727999461)
  ·
    refine ⟨6756844836192911948999899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36036505793028863727999461 6756844836192911948999899)
    ·
      refine ⟨10135267254289367923499849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6756844836192911948999899 10135267254289367923499849)
      ·
        refine ⟨7601450440717025942624887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10135267254289367923499849 7601450440717025942624887)
        ·
          refine ⟨11402175661075538913937331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7601450440717025942624887 11402175661075538913937331)
          ·
            refine ⟨17103263491613308370905997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11402175661075538913937331 17103263491613308370905997)
            ·
              refine ⟨6413723809354990639089749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17103263491613308370905997 6413723809354990639089749)
              ·
                refine ⟨75160825890878796551833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6413723809354990639089749 75160825890878796551833)
                ·
                  rfl

theorem cell23_3952130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 8].length) (baseStart_3952130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952130 prefixEnd_3952130 := by exact prefixLift 3952130
  have htrace : WordTrace (prefixWord ++ tailWord_3952130) baseStart_3952130 baseEnd_3952130 := by
    simpa [prefixWord, tailWord_3952130, baseEnd_3952130] using wordTrace_append hprefix tailTrace_3952130
  have hstable : (prefixWord ++ tailWord_3952130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952130).length < 2 ^ (prefixWord ++ tailWord_3952130).sum := by decide
  have hdescent : baseEnd_3952130 < baseStart_3952130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952174 : List Nat := [4, 1, 3, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_3952174 : Nat := 118140960795 + 3952174 * 2 ^ 59
def prefixEnd_3952174 : Nat := 4983230072969 + 3 ^ 40 * 3952174 * 2
def baseEnd_3952174 : Nat := 2029364892202525334749289

theorem tailTrace_3952174 : CollatzResearch.WordTrace tailWord_3952174 prefixEnd_3952174 2029364892202525334749289 := by
  unfold tailWord_3952174
  simp only [CollatzResearch.WordTrace]
  refine ⟨18018453497994506303324947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96098418655970700284399717 18018453497994506303324947)
  ·
    refine ⟨27027680246991759454987421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18018453497994506303324947 27027680246991759454987421)
    ·
      refine ⟨10135380092621909795620283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27027680246991759454987421 10135380092621909795620283)
      ·
        refine ⟨15203070138932864693430425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10135380092621909795620283 15203070138932864693430425)
        ·
          refine ⟨11402302604199648520072819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15203070138932864693430425 11402302604199648520072819)
          ·
            refine ⟨17103453906299472780109229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11402302604199648520072819 17103453906299472780109229)
            ·
              refine ⟨6413795214862302292540961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17103453906299472780109229 6413795214862302292540961)
              ·
                refine ⟨4810346411146726719405721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6413795214862302292540961 4810346411146726719405721)
                ·
                  refine ⟨3607759808360045039554291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4810346411146726719405721 3607759808360045039554291)
                  ·
                    refine ⟨5411639712540067559331437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3607759808360045039554291 5411639712540067559331437)
                    ·
                      refine ⟨2029364892202525334749289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5411639712540067559331437 2029364892202525334749289)
                      ·
                        rfl

theorem cell23_3952174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_3952174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952174 prefixEnd_3952174 := by exact prefixLift 3952174
  have htrace : WordTrace (prefixWord ++ tailWord_3952174) baseStart_3952174 baseEnd_3952174 := by
    simpa [prefixWord, tailWord_3952174, baseEnd_3952174] using wordTrace_append hprefix tailTrace_3952174
  have hstable : (prefixWord ++ tailWord_3952174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952174).length < 2 ^ (prefixWord ++ tailWord_3952174).sum := by decide
  have hdescent : baseEnd_3952174 < baseStart_3952174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952233 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 4, 5]
def baseStart_3952233 : Nat := 118140960795 + 3952233 * 2 ^ 59
def prefixEnd_3952233 : Nat := 4983230072969 + 3 ^ 40 * 3952233 * 2
def baseEnd_3952233 : Nat := 676465062520380201303839

theorem tailTrace_3952233 : CollatzResearch.WordTrace tailWord_3952233 prefixEnd_3952233 676465062520380201303839 := by
  unfold tailWord_3952233
  simp only [CollatzResearch.WordTrace]
  refine ⟨144149779890742303502997353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96099853260494869001998235 144149779890742303502997353)
  ·
    refine ⟨108112334918056727627248015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144149779890742303502997353 108112334918056727627248015)
    ·
      refine ⟨162168502377085091440872023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108112334918056727627248015 162168502377085091440872023)
      ·
        refine ⟨243252753565627637161308035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162168502377085091440872023 243252753565627637161308035)
        ·
          refine ⟨364879130348441455741962053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243252753565627637161308035 364879130348441455741962053)
          ·
            refine ⟨68414836940332772951617885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364879130348441455741962053 68414836940332772951617885)
            ·
              refine ⟨25655563852624789856856707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68414836940332772951617885 25655563852624789856856707)
              ·
                refine ⟨38483345778937184785285061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25655563852624789856856707 38483345778937184785285061)
                ·
                  refine ⟨7215627333550722147240949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38483345778937184785285061 7215627333550722147240949)
                  ·
                    refine ⟨676465062520380201303839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7215627333550722147240949 676465062520380201303839)
                    ·
                      rfl

theorem cell23_3952233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 5].length) (baseStart_3952233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952233 prefixEnd_3952233 := by exact prefixLift 3952233
  have htrace : WordTrace (prefixWord ++ tailWord_3952233) baseStart_3952233 baseEnd_3952233 := by
    simpa [prefixWord, tailWord_3952233, baseEnd_3952233] using wordTrace_append hprefix tailTrace_3952233
  have hstable : (prefixWord ++ tailWord_3952233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952233).length < 2 ^ (prefixWord ++ tailWord_3952233).sum := by decide
  have hdescent : baseEnd_3952233 < baseStart_3952233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952237 : List Nat := [1, 5, 1, 1, 4, 2, 1, 1, 7]
def baseStart_3952237 : Nat := 118140960795 + 3952237 * 2 ^ 59
def prefixEnd_3952237 : Nat := 4983230072969 + 3 ^ 40 * 3952237 * 2
def baseEnd_3952237 : Nat := 225488582387084287584611

theorem tailTrace_3952237 : CollatzResearch.WordTrace tailWord_3952237 prefixEnd_3952237 225488582387084287584611 := by
  unfold tailWord_3952237
  simp only [CollatzResearch.WordTrace]
  refine ⟨144149925782727812186142965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96099950521818541457428643 144149925782727812186142965)
  ·
    refine ⟨13514055542130732392450903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144149925782727812186142965 13514055542130732392450903)
    ·
      refine ⟨20271083313196098588676355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13514055542130732392450903 20271083313196098588676355)
      ·
        refine ⟨30406624969794147883014533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20271083313196098588676355 30406624969794147883014533)
        ·
          refine ⟨5701242181836402728065225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30406624969794147883014533 5701242181836402728065225)
          ·
            refine ⟨4275931636377302046048919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5701242181836402728065225 4275931636377302046048919)
            ·
              refine ⟨6413897454565953069073379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4275931636377302046048919 6413897454565953069073379)
              ·
                refine ⟨9620846181848929603610069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6413897454565953069073379 9620846181848929603610069)
                ·
                  refine ⟨225488582387084287584611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9620846181848929603610069 225488582387084287584611)
                  ·
                    rfl

theorem cell23_3952237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_3952237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952237 prefixEnd_3952237 := by exact prefixLift 3952237
  have htrace : WordTrace (prefixWord ++ tailWord_3952237) baseStart_3952237 baseEnd_3952237 := by
    simpa [prefixWord, tailWord_3952237, baseEnd_3952237] using wordTrace_append hprefix tailTrace_3952237
  have hstable : (prefixWord ++ tailWord_3952237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952237).length < 2 ^ (prefixWord ++ tailWord_3952237).sum := by decide
  have hdescent : baseEnd_3952237 < baseStart_3952237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952293 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 8]
def baseStart_3952293 : Nat := 118140960795 + 3952293 * 2 ^ 59
def prefixEnd_3952293 : Nat := 4983230072969 + 3 ^ 40 * 3952293 * 2
def baseEnd_3952293 : Nat := 225491777377823374351249

theorem tailTrace_3952293 : CollatzResearch.WordTrace tailWord_3952293 prefixEnd_3952293 225491777377823374351249 := by
  unfold tailWord_3952293
  simp only [CollatzResearch.WordTrace]
  refine ⟨144151968270524933750181533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96101312180349955833454355 144151968270524933750181533)
  ·
    refine ⟨54056988101446850156318075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144151968270524933750181533 54056988101446850156318075)
    ·
      refine ⟨81085482152170275234477113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54056988101446850156318075 81085482152170275234477113)
      ·
        refine ⟨60814111614127706425857835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81085482152170275234477113 60814111614127706425857835)
        ·
          refine ⟨91221167421191559638786753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60814111614127706425857835 91221167421191559638786753)
          ·
            refine ⟨68415875565893669729090065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91221167421191559638786753 68415875565893669729090065)
            ·
              refine ⟨51311906674420252296817549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68415875565893669729090065 51311906674420252296817549)
              ·
                refine ⟨19241965002907594611306581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51311906674420252296817549 19241965002907594611306581)
                ·
                  refine ⟨225491777377823374351249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19241965002907594611306581 225491777377823374351249)
                  ·
                    rfl

theorem cell23_3952293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 8].length) (baseStart_3952293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952293 prefixEnd_3952293 := by exact prefixLift 3952293
  have htrace : WordTrace (prefixWord ++ tailWord_3952293) baseStart_3952293 baseEnd_3952293 := by
    simpa [prefixWord, tailWord_3952293, baseEnd_3952293] using wordTrace_append hprefix tailTrace_3952293
  have hstable : (prefixWord ++ tailWord_3952293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952293).length < 2 ^ (prefixWord ++ tailWord_3952293).sum := by decide
  have hdescent : baseEnd_3952293 < baseStart_3952293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952374 : List Nat := [5, 1, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_3952374 : Nat := 118140960795 + 3952374 * 2 ^ 59
def prefixEnd_3952374 : Nat := 4983230072969 + 3 ^ 40 * 3952374 * 2
def baseEnd_3952374 : Nat := 676489196111141517416123

theorem tailTrace_3952374 : CollatzResearch.WordTrace tailWord_3952374 prefixEnd_3952374 676489196111141517416123 := by
  unfold tailWord_3952374
  simp only [CollatzResearch.WordTrace]
  refine ⟨9009682661451967786492511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96103281722154323055920117 9009682661451967786492511)
  ·
    refine ⟨13514523992177951679738767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9009682661451967786492511 13514523992177951679738767)
    ·
      refine ⟨20271785988266927519608151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13514523992177951679738767 20271785988266927519608151)
      ·
        refine ⟨30407678982400391279412227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20271785988266927519608151 30407678982400391279412227)
        ·
          refine ⟨45611518473600586919118341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30407678982400391279412227 45611518473600586919118341)
          ·
            refine ⟨8552159713800110047334689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45611518473600586919118341 8552159713800110047334689)
            ·
              refine ⟨6414119785350082535501017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8552159713800110047334689 6414119785350082535501017)
              ·
                refine ⟨4810589839012561901625763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6414119785350082535501017 4810589839012561901625763)
                ·
                  refine ⟨7215884758518842852438645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4810589839012561901625763 7215884758518842852438645)
                  ·
                    refine ⟨676489196111141517416123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7215884758518842852438645 676489196111141517416123)
                    ·
                      rfl

theorem cell23_3952374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_3952374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952374 prefixEnd_3952374 := by exact prefixLift 3952374
  have htrace : WordTrace (prefixWord ++ tailWord_3952374) baseStart_3952374 baseEnd_3952374 := by
    simpa [prefixWord, tailWord_3952374, baseEnd_3952374] using wordTrace_append hprefix tailTrace_3952374
  have hstable : (prefixWord ++ tailWord_3952374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952374).length < 2 ^ (prefixWord ++ tailWord_3952374).sum := by decide
  have hdescent : baseEnd_3952374 < baseStart_3952374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952380 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_3952380 : Nat := 118140960795 + 3952380 * 2 ^ 59
def prefixEnd_3952380 : Nat := 4983230072969 + 3 ^ 40 * 3952380 * 2
def baseEnd_3952380 : Nat := 2029470669217351528773341

theorem tailTrace_3952380 : CollatzResearch.WordTrace tailWord_3952380 prefixEnd_3952380 2029470669217351528773341 := by
  unfold tailWord_3952380
  simp only [CollatzResearch.WordTrace]
  refine ⟨72077570710604873804299297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96103427614139831739065729 72077570710604873804299297)
  ·
    refine ⟨54058178032953655353224473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72077570710604873804299297 54058178032953655353224473)
    ·
      refine ⟨40543633524715241514918355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54058178032953655353224473 40543633524715241514918355)
      ·
        refine ⟨60815450287072862272377533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40543633524715241514918355 60815450287072862272377533)
        ·
          refine ⟨22805793857652323352141575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60815450287072862272377533 22805793857652323352141575)
          ·
            refine ⟨34208690786478485028212363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22805793857652323352141575 34208690786478485028212363)
            ·
              refine ⟨51313036179717727542318545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34208690786478485028212363 51313036179717727542318545)
              ·
                refine ⟨38484777134788295656738909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51313036179717727542318545 38484777134788295656738909)
                ·
                  refine ⟨14431791425545610871277091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38484777134788295656738909 14431791425545610871277091)
                  ·
                    refine ⟨21647687138318416306915637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14431791425545610871277091 21647687138318416306915637)
                    ·
                      refine ⟨2029470669217351528773341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21647687138318416306915637 2029470669217351528773341)
                      ·
                        rfl

theorem cell23_3952380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_3952380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952380 prefixEnd_3952380 := by exact prefixLift 3952380
  have htrace : WordTrace (prefixWord ++ tailWord_3952380) baseStart_3952380 baseEnd_3952380 := by
    simpa [prefixWord, tailWord_3952380, baseEnd_3952380] using wordTrace_append hprefix tailTrace_3952380
  have hstable : (prefixWord ++ tailWord_3952380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952380).length < 2 ^ (prefixWord ++ tailWord_3952380).sum := by decide
  have hdescent : baseEnd_3952380 < baseStart_3952380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952388 : List Nat := [2, 3, 2, 2, 1, 4, 1, 3, 1, 1, 3]
def baseStart_3952388 : Nat := 118140960795 + 3952388 * 2 ^ 59
def prefixEnd_3952388 : Nat := 4983230072969 + 3 ^ 40 * 3952388 * 2
def baseEnd_3952388 : Nat := 2029474777062587497473305

theorem tailTrace_3952388 : CollatzResearch.WordTrace tailWord_3952388 prefixEnd_3952388 2029474777062587497473305 := by
  unfold tailWord_3952388
  simp only [CollatzResearch.WordTrace]
  refine ⟨72077716602590382487444909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96103622136787176649926545 72077716602590382487444909)
  ·
    refine ⟨27029143725971393432791841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72077716602590382487444909 27029143725971393432791841)
    ·
      refine ⟨20271857794478545074593881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27029143725971393432791841 20271857794478545074593881)
      ·
        refine ⟨15203893345858908805945411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20271857794478545074593881 15203893345858908805945411)
        ·
          refine ⟨22805840018788363208918117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15203893345858908805945411 22805840018788363208918117)
          ·
            refine ⟨4276095003522818101672147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22805840018788363208918117 4276095003522818101672147)
            ·
              refine ⟨6414142505284227152508221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4276095003522818101672147 6414142505284227152508221)
              ·
                refine ⟨2405303439481585182190583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6414142505284227152508221 2405303439481585182190583)
                ·
                  refine ⟨3607955159222377773285875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2405303439481585182190583 3607955159222377773285875)
                  ·
                    refine ⟨5411932738833566659928813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3607955159222377773285875 5411932738833566659928813)
                    ·
                      refine ⟨2029474777062587497473305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5411932738833566659928813 2029474777062587497473305)
                      ·
                        rfl

theorem cell23_3952388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_3952388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952388 prefixEnd_3952388 := by exact prefixLift 3952388
  have htrace : WordTrace (prefixWord ++ tailWord_3952388) baseStart_3952388 baseEnd_3952388 := by
    simpa [prefixWord, tailWord_3952388, baseEnd_3952388] using wordTrace_append hprefix tailTrace_3952388
  have hstable : (prefixWord ++ tailWord_3952388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952388).length < 2 ^ (prefixWord ++ tailWord_3952388).sum := by decide
  have hdescent : baseEnd_3952388 < baseStart_3952388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952421 : List Nat := [1, 3, 1, 2, 3, 4, 2, 1, 2, 4]
def baseStart_3952421 : Nat := 118140960795 + 3952421 * 2 ^ 59
def prefixEnd_3952421 : Nat := 4983230072969 + 3 ^ 40 * 3952421 * 2
def baseEnd_3952421 : Nat := 676497240641395289453551

theorem tailTrace_3952421 : CollatzResearch.WordTrace tailWord_3952421 prefixEnd_3952421 676497240641395289453551 := by
  unfold tailWord_3952421
  simp only [CollatzResearch.WordTrace]
  refine ⟨144156636814061211610841117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96104424542707474407227411 144156636814061211610841117)
  ·
    refine ⟨54058738805272954354065419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144156636814061211610841117 54058738805272954354065419)
    ·
      refine ⟨81088108207909431531098129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54058738805272954354065419 81088108207909431531098129)
      ·
        refine ⟨60816081155932073648323597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81088108207909431531098129 60816081155932073648323597)
        ·
          refine ⟨22806030433474527618121349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60816081155932073648323597 22806030433474527618121349)
          ·
            refine ⟨4276130706276473928397753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22806030433474527618121349 4276130706276473928397753)
            ·
              refine ⟨3207098029707355446298315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4276130706276473928397753 3207098029707355446298315)
              ·
                refine ⟨4810647044561033169447473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3207098029707355446298315 4810647044561033169447473)
                ·
                  refine ⟨3607985283420774877085605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4810647044561033169447473 3607985283420774877085605)
                  ·
                    refine ⟨676497240641395289453551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3607985283420774877085605 676497240641395289453551)
                    ·
                      rfl

theorem cell23_3952421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 2, 4].length) (baseStart_3952421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952421 prefixEnd_3952421 := by exact prefixLift 3952421
  have htrace : WordTrace (prefixWord ++ tailWord_3952421) baseStart_3952421 baseEnd_3952421 := by
    simpa [prefixWord, tailWord_3952421, baseEnd_3952421] using wordTrace_append hprefix tailTrace_3952421
  have hstable : (prefixWord ++ tailWord_3952421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952421).length < 2 ^ (prefixWord ++ tailWord_3952421).sum := by decide
  have hdescent : baseEnd_3952421 < baseStart_3952421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952487 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_3952487 : Nat := 118140960795 + 3952487 * 2 ^ 59
def prefixEnd_3952487 : Nat := 4983230072969 + 3 ^ 40 * 3952487 * 2
def baseEnd_3952487 : Nat := 2029525611647382610135349

theorem tailTrace_3952487 : CollatzResearch.WordTrace tailWord_3952487 prefixEnd_3952487 2029525611647382610135349 := by
  unfold tailWord_3952487
  simp only [CollatzResearch.WordTrace]
  refine ⟨144159044031822104882743715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96106029354548069921829143 144159044031822104882743715)
  ·
    refine ⟨216238566047733157324115573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144159044031822104882743715 216238566047733157324115573)
    ·
      refine ⟨20272365566974983499135835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216238566047733157324115573 20272365566974983499135835)
      ·
        refine ⟨30408548350462475248703753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20272365566974983499135835 30408548350462475248703753)
        ·
          refine ⟨22806411262846856436527815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30408548350462475248703753 22806411262846856436527815)
          ·
            refine ⟨34209616894270284654791723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22806411262846856436527815 34209616894270284654791723)
            ·
              refine ⟨51314425341405426982187585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34209616894270284654791723 51314425341405426982187585)
              ·
                refine ⟨38485819006054070236640689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51314425341405426982187585 38485819006054070236640689)
                ·
                  refine ⟨28864364254540552677480517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38485819006054070236640689 28864364254540552677480517)
                  ·
                    refine ⟨5412068297726353627027597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28864364254540552677480517 5412068297726353627027597)
                    ·
                      refine ⟨2029525611647382610135349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5412068297726353627027597 2029525611647382610135349)
                      ·
                        rfl

theorem cell23_3952487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_3952487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952487 prefixEnd_3952487 := by exact prefixLift 3952487
  have htrace : WordTrace (prefixWord ++ tailWord_3952487) baseStart_3952487 baseEnd_3952487 := by
    simpa [prefixWord, tailWord_3952487, baseEnd_3952487] using wordTrace_append hprefix tailTrace_3952487
  have hstable : (prefixWord ++ tailWord_3952487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952487).length < 2 ^ (prefixWord ++ tailWord_3952487).sum := by decide
  have hdescent : baseEnd_3952487 < baseStart_3952487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952501 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_3952501 : Nat := 118140960795 + 3952501 * 2 ^ 59
def prefixEnd_3952501 : Nat := 4983230072969 + 3 ^ 40 * 3952501 * 2
def baseEnd_3952501 : Nat := 2029532800376545555360285

theorem tailTrace_3952501 : CollatzResearch.WordTrace tailWord_3952501 prefixEnd_3952501 2029532800376545555360285 := by
  unfold tailWord_3952501
  simp only [CollatzResearch.WordTrace]
  refine ⟨144159554653771385273753357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96106369769180923515835571 144159554653771385273753357)
  ·
    refine ⟨54059832995164269477657509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144159554653771385273753357 54059832995164269477657509)
    ·
      refine ⟨10136218686593300527060783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54059832995164269477657509 10136218686593300527060783)
      ·
        refine ⟨15204328029889950790591175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10136218686593300527060783 15204328029889950790591175)
        ·
          refine ⟨22806492044834926185886763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15204328029889950790591175 22806492044834926185886763)
          ·
            refine ⟨34209738067252389278830145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22806492044834926185886763 34209738067252389278830145)
            ·
              refine ⟨25657303550439291959122609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34209738067252389278830145 25657303550439291959122609)
              ·
                refine ⟨19242977662829468969341957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25657303550439291959122609 19242977662829468969341957)
                ·
                  refine ⟨3608058311780525431751617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19242977662829468969341957 3608058311780525431751617)
                  ·
                    refine ⟨2706043733835394073813713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3608058311780525431751617 2706043733835394073813713)
                    ·
                      refine ⟨2029532800376545555360285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2706043733835394073813713 2029532800376545555360285)
                      ·
                        rfl

theorem cell23_3952501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_3952501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952501 prefixEnd_3952501 := by exact prefixLift 3952501
  have htrace : WordTrace (prefixWord ++ tailWord_3952501) baseStart_3952501 baseEnd_3952501 := by
    simpa [prefixWord, tailWord_3952501, baseEnd_3952501] using wordTrace_append hprefix tailTrace_3952501
  have hstable : (prefixWord ++ tailWord_3952501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952501).length < 2 ^ (prefixWord ++ tailWord_3952501).sum := by decide
  have hdescent : baseEnd_3952501 < baseStart_3952501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952517 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 4, 3, 3]
def baseStart_3952517 : Nat := 118140960795 + 3952517 * 2 ^ 59
def prefixEnd_3952517 : Nat := 4983230072969 + 3 ^ 40 * 3952517 * 2
def baseEnd_3952517 : Nat := 2029541016067017492760211

theorem tailTrace_3952517 : CollatzResearch.WordTrace tailWord_3952517 prefixEnd_3952517 2029541016067017492760211 := by
  unfold tailWord_3952517
  simp only [CollatzResearch.WordTrace]
  refine ⟨144160138221713420006335805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96106758814475613337557203 144160138221713420006335805)
  ·
    refine ⟨54060051833142532502375927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144160138221713420006335805 54060051833142532502375927)
    ·
      refine ⟨81090077749713798753563891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54060051833142532502375927 81090077749713798753563891)
      ·
        refine ⟨121635116624570698130345837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81090077749713798753563891 121635116624570698130345837)
        ·
          refine ⟨45613168734214011798879689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121635116624570698130345837 45613168734214011798879689)
          ·
            refine ⟨34209876550660508849159767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45613168734214011798879689 34209876550660508849159767)
            ·
              refine ⟨51314814825990763273739651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34209876550660508849159767 51314814825990763273739651)
              ·
                refine ⟨76972222238986144910609477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51314814825990763273739651 76972222238986144910609477)
                ·
                  refine ⟨14432291669809902170739277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76972222238986144910609477 14432291669809902170739277)
                  ·
                    refine ⟨5412109376178713314027229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14432291669809902170739277 5412109376178713314027229)
                    ·
                      refine ⟨2029541016067017492760211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5412109376178713314027229 2029541016067017492760211)
                      ·
                        rfl

theorem cell23_3952517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_3952517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952517 prefixEnd_3952517 := by exact prefixLift 3952517
  have htrace : WordTrace (prefixWord ++ tailWord_3952517) baseStart_3952517 baseEnd_3952517 := by
    simpa [prefixWord, tailWord_3952517, baseEnd_3952517] using wordTrace_append hprefix tailTrace_3952517
  have hstable : (prefixWord ++ tailWord_3952517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952517).length < 2 ^ (prefixWord ++ tailWord_3952517).sum := by decide
  have hdescent : baseEnd_3952517 < baseStart_3952517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952574 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_3952574 : Nat := 118140960795 + 3952574 * 2 ^ 59
def prefixEnd_3952574 : Nat := 4983230072969 + 3 ^ 40 * 3952574 * 2
def baseEnd_3952574 : Nat := 2029570284464323769747449

theorem tailTrace_3952574 : CollatzResearch.WordTrace tailWord_3952574 prefixEnd_3952574 2029570284464323769747449 := by
  unfold tailWord_3952574
  simp only [CollatzResearch.WordTrace]
  refine ⟨18020277147813364842645097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96108144788337945827440517 18020277147813364842645097)
  ·
    refine ⟨13515207860860023631983823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18020277147813364842645097 13515207860860023631983823)
    ·
      refine ⟨20272811791290035447975735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13515207860860023631983823 20272811791290035447975735)
      ·
        refine ⟨30409217686935053171963603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20272811791290035447975735 30409217686935053171963603)
        ·
          refine ⟨45613826530402579757945405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30409217686935053171963603 45613826530402579757945405)
          ·
            refine ⟨17105184948900967409229527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45613826530402579757945405 17105184948900967409229527)
            ·
              refine ⟨25657777423351451113844291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17105184948900967409229527 25657777423351451113844291)
              ·
                refine ⟨38486666135027176670766437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25657777423351451113844291 38486666135027176670766437)
                ·
                  refine ⟨7216249900317595625768707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38486666135027176670766437 7216249900317595625768707)
                  ·
                    refine ⟨10824374850476393438653061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7216249900317595625768707 10824374850476393438653061)
                    ·
                      refine ⟨2029570284464323769747449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10824374850476393438653061 2029570284464323769747449)
                      ·
                        rfl

theorem cell23_3952574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_3952574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952574 prefixEnd_3952574 := by exact prefixLift 3952574
  have htrace : WordTrace (prefixWord ++ tailWord_3952574) baseStart_3952574 baseEnd_3952574 := by
    simpa [prefixWord, tailWord_3952574, baseEnd_3952574] using wordTrace_append hprefix tailTrace_3952574
  have hstable : (prefixWord ++ tailWord_3952574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952574).length < 2 ^ (prefixWord ++ tailWord_3952574).sum := by decide
  have hdescent : baseEnd_3952574 < baseStart_3952574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952611 : List Nat := [1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 3]
def baseStart_3952611 : Nat := 118140960795 + 3952611 * 2 ^ 59
def prefixEnd_3952611 : Nat := 4983230072969 + 3 ^ 40 * 3952611 * 2
def baseEnd_3952611 : Nat := 2029589283248540124984779

theorem tailTrace_3952611 : CollatzResearch.WordTrace tailWord_3952611 prefixEnd_3952611 2029589283248540124984779 := by
  unfold tailWord_3952611
  simp only [CollatzResearch.WordTrace]
  refine ⟨144163566683372874060257687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96109044455581916040171791 144163566683372874060257687)
  ·
    refine ⟨216245350025059311090386531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144163566683372874060257687 216245350025059311090386531)
    ·
      refine ⟨324368025037588966635579797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216245350025059311090386531 324368025037588966635579797)
      ·
        refine ⟨15204751173636982811042803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 324368025037588966635579797 15204751173636982811042803)
        ·
          refine ⟨22807126760455474216564205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15204751173636982811042803 22807126760455474216564205)
          ·
            refine ⟨8552672535170802831211577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22807126760455474216564205 8552672535170802831211577)
            ·
              refine ⟨6414504401378102123408683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8552672535170802831211577 6414504401378102123408683)
              ·
                refine ⟨9621756602067153185113025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6414504401378102123408683 9621756602067153185113025)
                ·
                  refine ⟨7216317451550364888834769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9621756602067153185113025 7216317451550364888834769)
                  ·
                    refine ⟨5412238088662773666626077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7216317451550364888834769 5412238088662773666626077)
                    ·
                      refine ⟨2029589283248540124984779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5412238088662773666626077 2029589283248540124984779)
                      ·
                        rfl

theorem cell23_3952611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_3952611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952611 prefixEnd_3952611 := by exact prefixLift 3952611
  have htrace : WordTrace (prefixWord ++ tailWord_3952611) baseStart_3952611 baseEnd_3952611 := by
    simpa [prefixWord, tailWord_3952611, baseEnd_3952611] using wordTrace_append hprefix tailTrace_3952611
  have hstable : (prefixWord ++ tailWord_3952611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952611).length < 2 ^ (prefixWord ++ tailWord_3952611).sum := by decide
  have hdescent : baseEnd_3952611 < baseStart_3952611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952634 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2]
def baseStart_3952634 : Nat := 118140960795 + 3952634 * 2 ^ 59
def prefixEnd_3952634 : Nat := 4983230072969 + 3 ^ 40 * 3952634 * 2
def baseEnd_3952634 : Nat := 2029601093303593534997173

theorem tailTrace_3952634 : CollatzResearch.WordTrace tailWord_3952634 prefixEnd_3952634 2029601093303593534997173 := by
  unfold tailWord_3952634
  simp only [CollatzResearch.WordTrace]
  refine ⟨36041101390572387247086239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96109603708193032658896637 36041101390572387247086239)
  ·
    refine ⟨54061652085858580870629359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36041101390572387247086239 54061652085858580870629359)
    ·
      refine ⟨81092478128787871305944039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54061652085858580870629359 81092478128787871305944039)
      ·
        refine ⟨121638717193181806958916059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81092478128787871305944039 121638717193181806958916059)
        ·
          refine ⟨182458075789772710438374089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121638717193181806958916059 182458075789772710438374089)
          ·
            refine ⟨136843556842329532828780567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182458075789772710438374089 136843556842329532828780567)
            ·
              refine ⟨205265335263494299243170851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136843556842329532828780567 205265335263494299243170851)
              ·
                refine ⟨307898002895241448864756277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205265335263494299243170851 307898002895241448864756277)
                ·
                  refine ⟨28865437771428885831070901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 307898002895241448864756277 28865437771428885831070901)
                  ·
                    refine ⟨2706134791071458046662897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28865437771428885831070901 2706134791071458046662897)
                    ·
                      refine ⟨2029601093303593534997173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2706134791071458046662897 2029601093303593534997173)
                      ·
                        rfl

theorem cell23_3952634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2].length) (baseStart_3952634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952634 prefixEnd_3952634 := by exact prefixLift 3952634
  have htrace : WordTrace (prefixWord ++ tailWord_3952634) baseStart_3952634 baseEnd_3952634 := by
    simpa [prefixWord, tailWord_3952634, baseEnd_3952634] using wordTrace_append hprefix tailTrace_3952634
  have hstable : (prefixWord ++ tailWord_3952634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952634).length < 2 ^ (prefixWord ++ tailWord_3952634).sum := by decide
  have hdescent : baseEnd_3952634 < baseStart_3952634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952641 : List Nat := [1, 2, 4, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_3952641 : Nat := 118140960795 + 3952641 * 2 ^ 59
def prefixEnd_3952641 : Nat := 4983230072969 + 3 ^ 40 * 3952641 * 2
def baseEnd_3952641 : Nat := 2029604687668175007609641

theorem tailTrace_3952641 : CollatzResearch.WordTrace tailWord_3952641 prefixEnd_3952641 2029604687668175007609641 := by
  unfold tailWord_3952641
  simp only [CollatzResearch.WordTrace]
  refine ⟨144164660873264189183849777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96109773915509459455899851 144164660873264189183849777)
  ·
    refine ⟨108123495654948141887887333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144164660873264189183849777 108123495654948141887887333)
    ·
      refine ⟨20273155435302776603978875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108123495654948141887887333 20273155435302776603978875)
      ·
        refine ⟨30409733152954164905968313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20273155435302776603978875 30409733152954164905968313)
        ·
          refine ⟨22807299864715623679476235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30409733152954164905968313 22807299864715623679476235)
          ·
            refine ⟨34210949797073435519214353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22807299864715623679476235 34210949797073435519214353)
            ·
              refine ⟨25658212347805076639410765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34210949797073435519214353 25658212347805076639410765)
              ·
                refine ⟨9621829630426903739779037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25658212347805076639410765 9621829630426903739779037)
                ·
                  refine ⟨3608186111410088902417139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9621829630426903739779037 3608186111410088902417139)
                  ·
                    refine ⟨5412279167115133353625709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3608186111410088902417139 5412279167115133353625709)
                    ·
                      refine ⟨2029604687668175007609641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5412279167115133353625709 2029604687668175007609641)
                      ·
                        rfl

theorem cell23_3952641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_3952641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952641 prefixEnd_3952641 := by exact prefixLift 3952641
  have htrace : WordTrace (prefixWord ++ tailWord_3952641) baseStart_3952641 baseEnd_3952641 := by
    simpa [prefixWord, tailWord_3952641, baseEnd_3952641] using wordTrace_append hprefix tailTrace_3952641
  have hstable : (prefixWord ++ tailWord_3952641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952641).length < 2 ^ (prefixWord ++ tailWord_3952641).sum := by decide
  have hdescent : baseEnd_3952641 < baseStart_3952641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952664 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 3, 1, 4]
def baseStart_3952664 : Nat := 118140960795 + 3952664 * 2 ^ 59
def prefixEnd_3952664 : Nat := 4983230072969 + 3 ^ 40 * 3952664 * 2
def baseEnd_3952664 : Nat := 2029616497723228417622035

theorem tailTrace_3952664 : CollatzResearch.WordTrace tailWord_3952664 prefixEnd_3952664 2029616497723228417622035 := by
  unfold tailWord_3952664
  simp only [CollatzResearch.WordTrace]
  refine ⟨72082749876090432055968523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96110333168120576074624697 72082749876090432055968523)
  ·
    refine ⟨108124124814135648083952785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72082749876090432055968523 108124124814135648083952785)
    ·
      refine ⟨81093093610601736062964589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108124124814135648083952785 81093093610601736062964589)
      ·
        refine ⟨30409910103975651023611721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81093093610601736062964589 30409910103975651023611721)
        ·
          refine ⟨22807432577981738267708791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30409910103975651023611721 22807432577981738267708791)
          ·
            refine ⟨34211148866972607401563187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22807432577981738267708791 34211148866972607401563187)
            ·
              refine ⟨51316723300458911102344781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34211148866972607401563187 51316723300458911102344781)
              ·
                refine ⟨19243771237672091663379293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51316723300458911102344781 19243771237672091663379293)
                ·
                  refine ⟨7216414214127034373767235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19243771237672091663379293 7216414214127034373767235)
                  ·
                    refine ⟨10824621321190551560650853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7216414214127034373767235 10824621321190551560650853)
                    ·
                      refine ⟨2029616497723228417622035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10824621321190551560650853 2029616497723228417622035)
                      ·
                        rfl

theorem cell23_3952664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_3952664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952664 prefixEnd_3952664 := by exact prefixLift 3952664
  have htrace : WordTrace (prefixWord ++ tailWord_3952664) baseStart_3952664 baseEnd_3952664 := by
    simpa [prefixWord, tailWord_3952664, baseEnd_3952664] using wordTrace_append hprefix tailTrace_3952664
  have hstable : (prefixWord ++ tailWord_3952664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952664).length < 2 ^ (prefixWord ++ tailWord_3952664).sum := by decide
  have hdescent : baseEnd_3952664 < baseStart_3952664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952667 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 5]
def baseStart_3952667 : Nat := 118140960795 + 3952667 * 2 ^ 59
def prefixEnd_3952667 : Nat := 4983230072969 + 3 ^ 40 * 3952667 * 2
def baseEnd_3952667 : Nat := 2029618038165191905884521

theorem tailTrace_3952667 : CollatzResearch.WordTrace tailWord_3952667 prefixEnd_3952667 2029618038165191905884521 := by
  unfold tailWord_3952667
  simp only [CollatzResearch.WordTrace]
  refine ⟨144165609171169995624296255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96110406114113330416197503 144165609171169995624296255)
  ·
    refine ⟨216248413756754993436444383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144165609171169995624296255 216248413756754993436444383)
    ·
      refine ⟨324372620635132490154666575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216248413756754993436444383 324372620635132490154666575)
      ·
        refine ⟨486558930952698735231999863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324372620635132490154666575 486558930952698735231999863)
        ·
          refine ⟨729838396429048102847999795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486558930952698735231999863 729838396429048102847999795)
          ·
            refine ⟨1094757594643572154271999693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729838396429048102847999795 1094757594643572154271999693)
            ·
              refine ⟨410534097991339557851999885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1094757594643572154271999693 410534097991339557851999885)
              ·
                refine ⟨153950286746752334194499957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410534097991339557851999885 153950286746752334194499957)
                ·
                  refine ⟨14432839382508031330734371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153950286746752334194499957 14432839382508031330734371)
                  ·
                    refine ⟨21649259073762046996101557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14432839382508031330734371 21649259073762046996101557)
                    ·
                      refine ⟨2029618038165191905884521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21649259073762046996101557 2029618038165191905884521)
                      ·
                        rfl

theorem cell23_3952667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 5].length) (baseStart_3952667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952667 prefixEnd_3952667 := by exact prefixLift 3952667
  have htrace : WordTrace (prefixWord ++ tailWord_3952667) baseStart_3952667 baseEnd_3952667 := by
    simpa [prefixWord, tailWord_3952667, baseEnd_3952667] using wordTrace_append hprefix tailTrace_3952667
  have hstable : (prefixWord ++ tailWord_3952667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952667).length < 2 ^ (prefixWord ++ tailWord_3952667).sum := by decide
  have hdescent : baseEnd_3952667 < baseStart_3952667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952668 : List Nat := [2, 2, 3, 1, 3, 1, 3, 1, 2, 3, 2]
def baseStart_3952668 : Nat := 118140960795 + 3952668 * 2 ^ 59
def prefixEnd_3952668 : Nat := 4983230072969 + 3 ^ 40 * 3952668 * 2
def baseEnd_3952668 : Nat := 2029618551645846401972017

theorem tailTrace_3952668 : CollatzResearch.WordTrace tailWord_3952668 prefixEnd_3952668 2029618551645846401972017 := by
  unfold tailWord_3952668
  simp only [CollatzResearch.WordTrace]
  refine ⟨72082822822083186397541329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96110430429444248530055105 72082822822083186397541329)
  ·
    refine ⟨54062117116562389798155997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72082822822083186397541329 54062117116562389798155997)
    ·
      refine ⟨20273293918710896174308499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54062117116562389798155997 20273293918710896174308499)
      ·
        refine ⟨30409940878066344261462749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20273293918710896174308499 30409940878066344261462749)
        ·
          refine ⟨11403727829274879098048531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30409940878066344261462749 11403727829274879098048531)
          ·
            refine ⟨17105591743912318647072797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11403727829274879098048531 17105591743912318647072797)
            ·
              refine ⟨6414596903967119492652299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17105591743912318647072797 6414596903967119492652299)
              ·
                refine ⟨9621895355950679238978449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6414596903967119492652299 9621895355950679238978449)
                ·
                  refine ⟨7216421516963009429233837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9621895355950679238978449 7216421516963009429233837)
                  ·
                    refine ⟨2706158068861128535962689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7216421516963009429233837 2706158068861128535962689)
                    ·
                      refine ⟨2029618551645846401972017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2706158068861128535962689 2029618551645846401972017)
                      ·
                        rfl

theorem cell23_3952668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_3952668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952668 prefixEnd_3952668 := by exact prefixLift 3952668
  have htrace : WordTrace (prefixWord ++ tailWord_3952668) baseStart_3952668 baseEnd_3952668 := by
    simpa [prefixWord, tailWord_3952668, baseEnd_3952668] using wordTrace_append hprefix tailTrace_3952668
  have hstable : (prefixWord ++ tailWord_3952668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952668).length < 2 ^ (prefixWord ++ tailWord_3952668).sum := by decide
  have hdescent : baseEnd_3952668 < baseStart_3952668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952674 : List Nat := [3, 3, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_3952674 : Nat := 118140960795 + 3952674 * 2 ^ 59
def prefixEnd_3952674 : Nat := 4983230072969 + 3 ^ 40 * 3952674 * 2
def baseEnd_3952674 : Nat := 676540544176591126165663

theorem tailTrace_3952674 : CollatzResearch.WordTrace tailWord_3952674 prefixEnd_3952674 676540544176591126165663 := by
  unfold tailWord_3952674
  simp only [CollatzResearch.WordTrace]
  refine ⟨36041466120536158954950269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96110576321429757213200717 36041466120536158954950269)
  ·
    refine ⟨13515549795201059608106351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36041466120536158954950269 13515549795201059608106351)
    ·
      refine ⟨20273324692801589412159527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13515549795201059608106351 20273324692801589412159527)
      ·
        refine ⟨30409987039202384118239291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20273324692801589412159527 30409987039202384118239291)
        ·
          refine ⟨45614980558803576177358937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30409987039202384118239291 45614980558803576177358937)
          ·
            refine ⟨34211235419102682133019203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45614980558803576177358937 34211235419102682133019203)
            ·
              refine ⟨51316853128654023199528805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34211235419102682133019203 51316853128654023199528805)
              ·
                refine ⟨9621909961622629349911651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51316853128654023199528805 9621909961622629349911651)
                ·
                  refine ⟨14432864942433944024867477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9621909961622629349911651 14432864942433944024867477)
                  ·
                    refine ⟨676540544176591126165663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14432864942433944024867477 676540544176591126165663)
                    ·
                      rfl

theorem cell23_3952674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_3952674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952674 prefixEnd_3952674 := by exact prefixLift 3952674
  have htrace : WordTrace (prefixWord ++ tailWord_3952674) baseStart_3952674 baseEnd_3952674 := by
    simpa [prefixWord, tailWord_3952674, baseEnd_3952674] using wordTrace_append hprefix tailTrace_3952674
  have hstable : (prefixWord ++ tailWord_3952674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952674).length < 2 ^ (prefixWord ++ tailWord_3952674).sum := by decide
  have hdescent : baseEnd_3952674 < baseStart_3952674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952684 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 3]
def baseStart_3952684 : Nat := 118140960795 + 3952684 * 2 ^ 59
def prefixEnd_3952684 : Nat := 4983230072969 + 3 ^ 40 * 3952684 * 2
def baseEnd_3952684 : Nat := 2029626767336318339371943

theorem tailTrace_3952684 : CollatzResearch.WordTrace tailWord_3952684 prefixEnd_3952684 2029626767336318339371943 := by
  unfold tailWord_3952684
  simp only [CollatzResearch.WordTrace]
  refine ⟨72083114606054203763832553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96110819474738938351776737 72083114606054203763832553)
  ·
    refine ⟨54062335954540652822874415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72083114606054203763832553 54062335954540652822874415)
    ·
      refine ⟨81093503931810979234311623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54062335954540652822874415 81093503931810979234311623)
      ·
        refine ⟨121640255897716468851467435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81093503931810979234311623 121640255897716468851467435)
        ·
          refine ⟨182460383846574703277201153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121640255897716468851467435 182460383846574703277201153)
          ·
            refine ⟨136845287884931027457900865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182460383846574703277201153 136845287884931027457900865)
            ·
              refine ⟨102633965913698270593425649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136845287884931027457900865 102633965913698270593425649)
              ·
                refine ⟨76975474435273702945069237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102633965913698270593425649 76975474435273702945069237)
                ·
                  refine ⟨7216450728306909651100241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76975474435273702945069237 7216450728306909651100241)
                  ·
                    refine ⟨5412338046230182238325181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7216450728306909651100241 5412338046230182238325181)
                    ·
                      refine ⟨2029626767336318339371943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5412338046230182238325181 2029626767336318339371943)
                      ·
                        rfl

theorem cell23_3952684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_3952684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952684 prefixEnd_3952684 := by exact prefixLift 3952684
  have htrace : WordTrace (prefixWord ++ tailWord_3952684) baseStart_3952684 baseEnd_3952684 := by
    simpa [prefixWord, tailWord_3952684, baseEnd_3952684] using wordTrace_append hprefix tailTrace_3952684
  have hstable : (prefixWord ++ tailWord_3952684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952684).length < 2 ^ (prefixWord ++ tailWord_3952684).sum := by decide
  have hdescent : baseEnd_3952684 < baseStart_3952684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952691 : List Nat := [1, 1, 1, 2, 4, 1, 5, 2, 2, 4]
def baseStart_3952691 : Nat := 118140960795 + 3952691 * 2 ^ 59
def prefixEnd_3952691 : Nat := 4983230072969 + 3 ^ 40 * 3952691 * 2
def baseEnd_3952691 : Nat := 676543453900299937328137

theorem tailTrace_3952691 : CollatzResearch.WordTrace tailWord_3952691 prefixEnd_3952691 676543453900299937328137 := by
  unfold tailWord_3952691
  simp only [CollatzResearch.WordTrace]
  refine ⟨144166484523083047723169927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96110989682055365148779951 144166484523083047723169927)
  ·
    refine ⟨216249726784624571584754891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144166484523083047723169927 216249726784624571584754891)
    ·
      refine ⟨324374590176936857377132337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216249726784624571584754891 324374590176936857377132337)
      ·
        refine ⟨243280942632702643032849253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324374590176936857377132337 243280942632702643032849253)
        ·
          refine ⟨45615176743631745568659235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243280942632702643032849253 45615176743631745568659235)
          ·
            refine ⟨68422765115447618352988853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45615176743631745568659235 68422765115447618352988853)
            ·
              refine ⟨6414634229573214220592705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68422765115447618352988853 6414634229573214220592705)
              ·
                refine ⟨4810975672179910665444529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6414634229573214220592705 4810975672179910665444529)
                ·
                  refine ⟨3608231754134932999083397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4810975672179910665444529 3608231754134932999083397)
                  ·
                    refine ⟨676543453900299937328137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3608231754134932999083397 676543453900299937328137)
                    ·
                      rfl

theorem cell23_3952691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 4].length) (baseStart_3952691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952691 prefixEnd_3952691 := by exact prefixLift 3952691
  have htrace : WordTrace (prefixWord ++ tailWord_3952691) baseStart_3952691 baseEnd_3952691 := by
    simpa [prefixWord, tailWord_3952691, baseEnd_3952691] using wordTrace_append hprefix tailTrace_3952691
  have hstable : (prefixWord ++ tailWord_3952691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952691).length < 2 ^ (prefixWord ++ tailWord_3952691).sum := by decide
  have hdescent : baseEnd_3952691 < baseStart_3952691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952707 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 6]
def baseStart_3952707 : Nat := 118140960795 + 3952707 * 2 ^ 59
def prefixEnd_3952707 : Nat := 4983230072969 + 3 ^ 40 * 3952707 * 2
def baseEnd_3952707 : Nat := 2029638577391371749384337

theorem tailTrace_3952707 : CollatzResearch.WordTrace tailWord_3952707 prefixEnd_3952707 2029638577391371749384337 := by
  unfold tailWord_3952707
  simp only [CollatzResearch.WordTrace]
  refine ⟨144167068091025082455752375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96111378727350054970501583 144167068091025082455752375)
  ·
    refine ⟨216250602136537623683628563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144167068091025082455752375 216250602136537623683628563)
    ·
      refine ⟨324375903204806435525442845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216250602136537623683628563 324375903204806435525442845)
      ·
        refine ⟨121640963701802413322041067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324375903204806435525442845 121640963701802413322041067)
        ·
          refine ⟨182461445552703619983061601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121640963701802413322041067 182461445552703619983061601)
          ·
            refine ⟨136846084164527714987296201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182461445552703619983061601 136846084164527714987296201)
            ·
              refine ⟨102634563123395786240472151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136846084164527714987296201 102634563123395786240472151)
              ·
                refine ⟨153951844685093679360708227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102634563123395786240472151 153951844685093679360708227)
                ·
                  refine ⟨230927767027640519041062341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153951844685093679360708227 230927767027640519041062341)
                  ·
                    refine ⟨43298956317682597320199189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 230927767027640519041062341 43298956317682597320199189)
                    ·
                      refine ⟨2029638577391371749384337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43298956317682597320199189 2029638577391371749384337)
                      ·
                        rfl

theorem cell23_3952707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_3952707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952707 prefixEnd_3952707 := by exact prefixLift 3952707
  have htrace : WordTrace (prefixWord ++ tailWord_3952707) baseStart_3952707 baseEnd_3952707 := by
    simpa [prefixWord, tailWord_3952707, baseEnd_3952707] using wordTrace_append hprefix tailTrace_3952707
  have hstable : (prefixWord ++ tailWord_3952707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952707).length < 2 ^ (prefixWord ++ tailWord_3952707).sum := by decide
  have hdescent : baseEnd_3952707 < baseStart_3952707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952718 : List Nat := [4, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3]
def baseStart_3952718 : Nat := 118140960795 + 3952718 * 2 ^ 59
def prefixEnd_3952718 : Nat := 4983230072969 + 3 ^ 40 * 3952718 * 2
def baseEnd_3952718 : Nat := 2029644225678571206346787

theorem tailTrace_3952718 : CollatzResearch.WordTrace tailWord_3952718 prefixEnd_3952718 2029644225678571206346787 := by
  unfold tailWord_3952718
  simp only [CollatzResearch.WordTrace]
  refine ⟨18020933661748153916800351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96111646195990154222935205 18020933661748153916800351)
  ·
    refine ⟨27031400492622230875200527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18020933661748153916800351 27031400492622230875200527)
    ·
      refine ⟨40547100738933346312800791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27031400492622230875200527 40547100738933346312800791)
      ·
        refine ⟨60820651108400019469201187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40547100738933346312800791 60820651108400019469201187)
        ·
          refine ⟨91230976662600029203801781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60820651108400019469201187 91230976662600029203801781)
          ·
            refine ⟨8552904062118752737856417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91230976662600029203801781 8552904062118752737856417)
            ·
              refine ⟨6414678046589064553392313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8552904062118752737856417 6414678046589064553392313)
              ·
                refine ⟨4811008534941798415044235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6414678046589064553392313 4811008534941798415044235)
                ·
                  refine ⟨7216512802412697622566353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4811008534941798415044235 7216512802412697622566353)
                  ·
                    refine ⟨5412384601809523216924765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7216512802412697622566353 5412384601809523216924765)
                    ·
                      refine ⟨2029644225678571206346787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5412384601809523216924765 2029644225678571206346787)
                      ·
                        rfl

theorem cell23_3952718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_3952718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952718 prefixEnd_3952718 := by exact prefixLift 3952718
  have htrace : WordTrace (prefixWord ++ tailWord_3952718) baseStart_3952718 baseEnd_3952718 := by
    simpa [prefixWord, tailWord_3952718, baseEnd_3952718] using wordTrace_append hprefix tailTrace_3952718
  have hstable : (prefixWord ++ tailWord_3952718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952718).length < 2 ^ (prefixWord ++ tailWord_3952718).sum := by decide
  have hdescent : baseEnd_3952718 < baseStart_3952718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952732 : List Nat := [2, 2, 4, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_3952732 : Nat := 118140960795 + 3952732 * 2 ^ 59
def prefixEnd_3952732 : Nat := 4983230072969 + 3 ^ 40 * 3952732 * 2
def baseEnd_3952732 : Nat := 2029651414407734151571723

theorem tailTrace_3952732 : CollatzResearch.WordTrace tailWord_3952732 prefixEnd_3952732 2029651414407734151571723 := by
  unfold tailWord_3952732
  simp only [CollatzResearch.WordTrace]
  refine ⟨72083989957967255862706225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96111986610623007816941633 72083989957967255862706225)
  ·
    refine ⟨54062992468475441897029669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72083989957967255862706225 54062992468475441897029669)
    ·
      refine ⟨10136811087839145355693063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54062992468475441897029669 10136811087839145355693063)
      ·
        refine ⟨15205216631758718033539595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10136811087839145355693063 15205216631758718033539595)
        ·
          refine ⟨22807824947638077050309393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15205216631758718033539595 22807824947638077050309393)
          ·
            refine ⟨17105868710728557787732045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22807824947638077050309393 17105868710728557787732045)
            ·
              refine ⟨6414700766523209170399517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17105868710728557787732045 6414700766523209170399517)
              ·
                refine ⟨2405512787446203438899819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6414700766523209170399517 2405512787446203438899819)
                ·
                  refine ⟨3608269181169305158349729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2405512787446203438899819 3608269181169305158349729)
                  ·
                    refine ⟨2706201885876978868762297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3608269181169305158349729 2706201885876978868762297)
                    ·
                      refine ⟨2029651414407734151571723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2706201885876978868762297 2029651414407734151571723)
                      ·
                        rfl

theorem cell23_3952732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_3952732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952732 prefixEnd_3952732 := by exact prefixLift 3952732
  have htrace : WordTrace (prefixWord ++ tailWord_3952732) baseStart_3952732 baseEnd_3952732 := by
    simpa [prefixWord, tailWord_3952732, baseEnd_3952732] using wordTrace_append hprefix tailTrace_3952732
  have hstable : (prefixWord ++ tailWord_3952732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952732).length < 2 ^ (prefixWord ++ tailWord_3952732).sum := by decide
  have hdescent : baseEnd_3952732 < baseStart_3952732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952738 : List Nat := [3, 3, 2, 2, 3, 1, 9]
def baseStart_3952738 : Nat := 118140960795 + 3952738 * 2 ^ 59
def prefixEnd_3952738 : Nat := 4983230072969 + 3 ^ 40 * 3952738 * 2
def baseEnd_3952738 : Nat := 25057462904835322569095

theorem tailTrace_3952738 : CollatzResearch.WordTrace tailWord_3952738 prefixEnd_3952738 25057462904835322569095 := by
  unfold tailWord_3952738
  simp only [CollatzResearch.WordTrace]
  refine ⟨36042049688478193687532717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96112132502608516500087245 36042049688478193687532717)
  ·
    refine ⟨13515768633179322632824769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36042049688478193687532717 13515768633179322632824769)
    ·
      refine ⟨10136826474884491974618577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13515768633179322632824769 10136826474884491974618577)
      ·
        refine ⟨7602619856163368980963933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10136826474884491974618577 7602619856163368980963933)
        ·
          refine ⟨2850982446061263367861475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7602619856163368980963933 2850982446061263367861475)
          ·
            refine ⟨4276473669091895051792213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2850982446061263367861475 4276473669091895051792213)
            ·
              refine ⟨25057462904835322569095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4276473669091895051792213 25057462904835322569095)
              ·
                rfl

theorem cell23_3952738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 9].length) (baseStart_3952738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952738 prefixEnd_3952738 := by exact prefixLift 3952738
  have htrace : WordTrace (prefixWord ++ tailWord_3952738) baseStart_3952738 baseEnd_3952738 := by
    simpa [prefixWord, tailWord_3952738, baseEnd_3952738] using wordTrace_append hprefix tailTrace_3952738
  have hstable : (prefixWord ++ tailWord_3952738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952738).length < 2 ^ (prefixWord ++ tailWord_3952738).sum := by decide
  have hdescent : baseEnd_3952738 < baseStart_3952738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952765 : List Nat := [1, 4, 1, 1, 3, 2, 4, 1, 2, 1, 3]
def baseStart_3952765 : Nat := 118140960795 + 3952765 * 2 ^ 59
def prefixEnd_3952765 : Nat := 4983230072969 + 3 ^ 40 * 3952765 * 2
def baseEnd_3952765 : Nat := 2029668359269332522459071

theorem tailTrace_3952765 : CollatzResearch.WordTrace tailWord_3952765 prefixEnd_3952765 2029668359269332522459071 := by
  unfold tailWord_3952765
  simp only [CollatzResearch.WordTrace]
  refine ⟨144169183524814958361363749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96112789016543305574242499 144169183524814958361363749)
  ·
    refine ⟨27031721910902804692755703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144169183524814958361363749 27031721910902804692755703)
    ·
      refine ⟨40547582866354207039133555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27031721910902804692755703 40547582866354207039133555)
      ·
        refine ⟨60821374299531310558700333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40547582866354207039133555 60821374299531310558700333)
        ·
          refine ⟨22808015362324241459512625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60821374299531310558700333 22808015362324241459512625)
          ·
            refine ⟨17106011521743181094634469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22808015362324241459512625 17106011521743181094634469)
            ·
              refine ⟨3207377160326846455243963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17106011521743181094634469 3207377160326846455243963)
              ·
                refine ⟨4811065740490269682865945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3207377160326846455243963 4811065740490269682865945)
                ·
                  refine ⟨3608299305367702262149459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4811065740490269682865945 3608299305367702262149459)
                  ·
                    refine ⟨5412448958051553393224189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3608299305367702262149459 5412448958051553393224189)
                    ·
                      refine ⟨2029668359269332522459071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5412448958051553393224189 2029668359269332522459071)
                      ·
                        rfl

theorem cell23_3952765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_3952765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952765 prefixEnd_3952765 := by exact prefixLift 3952765
  have htrace : WordTrace (prefixWord ++ tailWord_3952765) baseStart_3952765 baseEnd_3952765 := by
    simpa [prefixWord, tailWord_3952765, baseEnd_3952765] using wordTrace_append hprefix tailTrace_3952765
  have hstable : (prefixWord ++ tailWord_3952765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952765).length < 2 ^ (prefixWord ++ tailWord_3952765).sum := by decide
  have hdescent : baseEnd_3952765 < baseStart_3952765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952792 : List Nat := [2, 1, 2, 4, 3, 1, 3, 1, 1, 3, 2]
def baseStart_3952792 : Nat := 118140960795 + 3952792 * 2 ^ 59
def prefixEnd_3952792 : Nat := 4983230072969 + 3 ^ 40 * 3952792 * 2
def baseEnd_3952792 : Nat := 2029682223247003916821447

theorem tailTrace_3952792 : CollatzResearch.WordTrace tailWord_3952792 prefixEnd_3952792 2029682223247003916821447 := by
  unfold tailWord_3952792
  simp only [CollatzResearch.WordTrace]
  refine ⟨72085084147858570986298315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96113445530478094648397753 72085084147858570986298315)
  ·
    refine ⟨108127626221787856479447473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72085084147858570986298315 108127626221787856479447473)
    ·
      refine ⟨81095719666340892359585605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108127626221787856479447473 81095719666340892359585605)
      ·
        refine ⟨15205447437438917317422301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81095719666340892359585605 15205447437438917317422301)
        ·
          refine ⟨5702042789039593994033363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15205447437438917317422301 5702042789039593994033363)
          ·
            refine ⟨8553064183559390991050045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5702042789039593994033363 8553064183559390991050045)
            ·
              refine ⟨3207399068834771621643767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8553064183559390991050045 3207399068834771621643767)
              ·
                refine ⟨4811098603252157432465651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3207399068834771621643767 4811098603252157432465651)
                ·
                  refine ⟨7216647904878236148698477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4811098603252157432465651 7216647904878236148698477)
                  ·
                    refine ⟨2706242964329338555761929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7216647904878236148698477 2706242964329338555761929)
                    ·
                      refine ⟨2029682223247003916821447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2706242964329338555761929 2029682223247003916821447)
                      ·
                        rfl

theorem cell23_3952792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_3952792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952792 prefixEnd_3952792 := by exact prefixLift 3952792
  have htrace : WordTrace (prefixWord ++ tailWord_3952792) baseStart_3952792 baseEnd_3952792 := by
    simpa [prefixWord, tailWord_3952792, baseEnd_3952792] using wordTrace_append hprefix tailTrace_3952792
  have hstable : (prefixWord ++ tailWord_3952792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952792).length < 2 ^ (prefixWord ++ tailWord_3952792).sum := by decide
  have hdescent : baseEnd_3952792 < baseStart_3952792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952805 : List Nat := [1, 3, 1, 2, 1, 3, 4, 2, 2, 2, 2]
def baseStart_3952805 : Nat := 118140960795 + 3952805 * 2 ^ 59
def prefixEnd_3952805 : Nat := 4983230072969 + 3 ^ 40 * 3952805 * 2
def baseEnd_3952805 : Nat := 2029688898495512365958887

theorem tailTrace_3952805 : CollatzResearch.WordTrace tailWord_3952805 prefixEnd_3952805 2029688898495512365958887 := by
  unfold tailWord_3952805
  simp only [CollatzResearch.WordTrace]
  refine ⟨144170642444670045192819869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96113761629780030128546579 144170642444670045192819869)
  ·
    refine ⟨54063990916751266947307451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144170642444670045192819869 54063990916751266947307451)
    ·
      refine ⟨81095986375126900420961177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54063990916751266947307451 81095986375126900420961177)
      ·
        refine ⟨60821989781345175315720883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81095986375126900420961177 60821989781345175315720883)
        ·
          refine ⟨91232984672017762973581325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60821989781345175315720883 91232984672017762973581325)
          ·
            refine ⟨34212369252006661115092997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91232984672017762973581325 34212369252006661115092997)
            ·
              refine ⟨6414819234751248959079937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34212369252006661115092997 6414819234751248959079937)
              ·
                refine ⟨4811114426063436719309953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6414819234751248959079937 4811114426063436719309953)
                ·
                  refine ⟨3608335819547577539482465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4811114426063436719309953 3608335819547577539482465)
                  ·
                    refine ⟨2706251864660683154611849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3608335819547577539482465 2706251864660683154611849)
                    ·
                      refine ⟨2029688898495512365958887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2706251864660683154611849 2029688898495512365958887)
                      ·
                        rfl

theorem cell23_3952805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_3952805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952805 prefixEnd_3952805 := by exact prefixLift 3952805
  have htrace : WordTrace (prefixWord ++ tailWord_3952805) baseStart_3952805 baseEnd_3952805 := by
    simpa [prefixWord, tailWord_3952805, baseEnd_3952805] using wordTrace_append hprefix tailTrace_3952805
  have hstable : (prefixWord ++ tailWord_3952805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952805).length < 2 ^ (prefixWord ++ tailWord_3952805).sum := by decide
  have hdescent : baseEnd_3952805 < baseStart_3952805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952824 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 1, 7]
def baseStart_3952824 : Nat := 118140960795 + 3952824 * 2 ^ 59
def prefixEnd_3952824 : Nat := 4983230072969 + 3 ^ 40 * 3952824 * 2
def baseEnd_3952824 : Nat := 676566218209315930540433

theorem tailTrace_3952824 : CollatzResearch.WordTrace tailWord_3952824 prefixEnd_3952824 676566218209315930540433 := by
  unfold tailWord_3952824
  simp only [CollatzResearch.WordTrace]
  refine ⟨72085667715800605718880763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96114223621067474291841017 72085667715800605718880763)
  ·
    refine ⟨108128501573700908578321145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72085667715800605718880763 108128501573700908578321145)
    ·
      refine ⟨81096376180275681433740859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108128501573700908578321145 81096376180275681433740859)
      ·
        refine ⟨121644564270413522150611289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81096376180275681433740859 121644564270413522150611289)
        ·
          refine ⟨91233423202810141612958467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121644564270413522150611289 91233423202810141612958467)
          ·
            refine ⟨136850134804215212419437701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91233423202810141612958467 136850134804215212419437701)
            ·
              refine ⟨25659400275790352328644569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136850134804215212419437701 25659400275790352328644569)
              ·
                refine ⟨19244550206842764246483427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25659400275790352328644569 19244550206842764246483427)
                ·
                  refine ⟨28866825310264146369725141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19244550206842764246483427 28866825310264146369725141)
                  ·
                    refine ⟨676566218209315930540433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28866825310264146369725141 676566218209315930540433)
                    ·
                      rfl

theorem cell23_3952824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_3952824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952824 prefixEnd_3952824 := by exact prefixLift 3952824
  have htrace : WordTrace (prefixWord ++ tailWord_3952824) baseStart_3952824 baseEnd_3952824 := by
    simpa [prefixWord, tailWord_3952824, baseEnd_3952824] using wordTrace_append hprefix tailTrace_3952824
  have hstable : (prefixWord ++ tailWord_3952824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952824).length < 2 ^ (prefixWord ++ tailWord_3952824).sum := by decide
  have hdescent : baseEnd_3952824 < baseStart_3952824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952831 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 4, 5, 2]
def baseStart_3952831 : Nat := 118140960795 + 3952831 * 2 ^ 59
def prefixEnd_3952831 : Nat := 4983230072969 + 3 ^ 40 * 3952831 * 2
def baseEnd_3952831 : Nat := 2029702248992529264233767

theorem tailTrace_3952831 : CollatzResearch.WordTrace tailWord_3952831 prefixEnd_3952831 2029702248992529264233767 := by
  unfold tailWord_3952831
  simp only [CollatzResearch.WordTrace]
  refine ⟨144171590742575851633266347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96114393828383901088844231 144171590742575851633266347)
  ·
    refine ⟨216257386113863777449899521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144171590742575851633266347 216257386113863777449899521)
    ·
      refine ⟨162193039585397833087424641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216257386113863777449899521 162193039585397833087424641)
      ·
        refine ⟨121644779689048374815568481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162193039585397833087424641 121644779689048374815568481)
        ·
          refine ⟨91233584766786281111676361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121644779689048374815568481 91233584766786281111676361)
          ·
            refine ⟨68425188575089710833757271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91233584766786281111676361 68425188575089710833757271)
            ·
              refine ⟨102637782862634566250635907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68425188575089710833757271 102637782862634566250635907)
              ·
                refine ⟨153956674293951849375953861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102637782862634566250635907 153956674293951849375953861)
                ·
                  refine ⟨28866876430115971757991349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153956674293951849375953861 28866876430115971757991349)
                  ·
                    refine ⟨2706269665323372352311689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28866876430115971757991349 2706269665323372352311689)
                    ·
                      refine ⟨2029702248992529264233767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2706269665323372352311689 2029702248992529264233767)
                      ·
                        rfl

theorem cell23_3952831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 5, 2].length) (baseStart_3952831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952831 prefixEnd_3952831 := by exact prefixLift 3952831
  have htrace : WordTrace (prefixWord ++ tailWord_3952831) baseStart_3952831 baseEnd_3952831 := by
    simpa [prefixWord, tailWord_3952831, baseEnd_3952831] using wordTrace_append hprefix tailTrace_3952831
  have hstable : (prefixWord ++ tailWord_3952831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952831).length < 2 ^ (prefixWord ++ tailWord_3952831).sum := by decide
  have hdescent : baseEnd_3952831 < baseStart_3952831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952881 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 1, 4, 3]
def baseStart_3952881 : Nat := 118140960795 + 3952881 * 2 ^ 59
def prefixEnd_3952881 : Nat := 4983230072969 + 3 ^ 40 * 3952881 * 2
def baseEnd_3952881 : Nat := 2029727923025254068608537

theorem tailTrace_3952881 : CollatzResearch.WordTrace tailWord_3952881 prefixEnd_3952881 2029727923025254068608537 := by
  unfold tailWord_3952881
  simp only [CollatzResearch.WordTrace]
  refine ⟨144173414392394710172586497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96115609594929806781724331 144173414392394710172586497)
  ·
    refine ⟨108130060794296032629439873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144173414392394710172586497 108130060794296032629439873)
    ·
      refine ⟨81097545595722024472079905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108130060794296032629439873 81097545595722024472079905)
      ·
        refine ⟨60823159196791518354059929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81097545595722024472079905 60823159196791518354059929)
        ·
          refine ⟨45617369397593638765544947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60823159196791518354059929 45617369397593638765544947)
          ·
            refine ⟨68426054096390458148317421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45617369397593638765544947 68426054096390458148317421)
            ·
              refine ⟨25659770286146421805619033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68426054096390458148317421 25659770286146421805619033)
              ·
                refine ⟨19244827714609816354214275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25659770286146421805619033 19244827714609816354214275)
                ·
                  refine ⟨28867241571914724531321413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19244827714609816354214275 28867241571914724531321413)
                  ·
                    refine ⟨5412607794734010849622765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28867241571914724531321413 5412607794734010849622765)
                    ·
                      refine ⟨2029727923025254068608537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5412607794734010849622765 2029727923025254068608537)
                      ·
                        rfl

theorem cell23_3952881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_3952881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952881 prefixEnd_3952881 := by exact prefixLift 3952881
  have htrace : WordTrace (prefixWord ++ tailWord_3952881) baseStart_3952881 baseEnd_3952881 := by
    simpa [prefixWord, tailWord_3952881, baseEnd_3952881] using wordTrace_append hprefix tailTrace_3952881
  have hstable : (prefixWord ++ tailWord_3952881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952881).length < 2 ^ (prefixWord ++ tailWord_3952881).sum := by decide
  have hdescent : baseEnd_3952881 < baseStart_3952881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952905 : List Nat := [1, 2, 1, 1, 3, 4, 3, 3, 1, 4]
def baseStart_3952905 : Nat := 118140960795 + 3952905 * 2 ^ 59
def prefixEnd_3952905 : Nat := 4983230072969 + 3 ^ 40 * 3952905 * 2
def baseEnd_3952905 : Nat := 676580082186987324902809

theorem tailTrace_3952905 : CollatzResearch.WordTrace tailWord_3952905 prefixEnd_3952905 676580082186987324902809 := by
  unfold tailWord_3952905
  simp only [CollatzResearch.WordTrace]
  refine ⟨144174289744307762271460169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96116193162871841514306779 144174289744307762271460169)
  ·
    refine ⟨108130717308230821703595127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144174289744307762271460169 108130717308230821703595127)
    ·
      refine ⟨162196075962346232555392691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108130717308230821703595127 162196075962346232555392691)
      ·
        refine ⟨243294113943519348833089037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162196075962346232555392691 243294113943519348833089037)
        ·
          refine ⟨91235292728819755812408389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243294113943519348833089037 91235292728819755812408389)
          ·
            refine ⟨17106617386653704214826573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91235292728819755812408389 17106617386653704214826573)
            ·
              refine ⟨6414981519995139080559965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17106617386653704214826573 6414981519995139080559965)
              ·
                refine ⟨2405618069998177155209987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6414981519995139080559965 2405618069998177155209987)
                ·
                  refine ⟨3608427104997265732814981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2405618069998177155209987 3608427104997265732814981)
                  ·
                    refine ⟨676580082186987324902809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3608427104997265732814981 676580082186987324902809)
                    ·
                      rfl

theorem cell23_3952905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 1, 4].length) (baseStart_3952905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952905 prefixEnd_3952905 := by exact prefixLift 3952905
  have htrace : WordTrace (prefixWord ++ tailWord_3952905) baseStart_3952905 baseEnd_3952905 := by
    simpa [prefixWord, tailWord_3952905, baseEnd_3952905] using wordTrace_append hprefix tailTrace_3952905
  have hstable : (prefixWord ++ tailWord_3952905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952905).length < 2 ^ (prefixWord ++ tailWord_3952905).sum := by decide
  have hdescent : baseEnd_3952905 < baseStart_3952905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952922 : List Nat := [3, 1, 1, 3, 5, 1, 1, 1, 3, 4]
def baseStart_3952922 : Nat := 118140960795 + 3952922 * 2 ^ 59
def prefixEnd_3952922 : Nat := 4983230072969 + 3 ^ 40 * 3952922 * 2
def baseEnd_3952922 : Nat := 676582991910696136065283

theorem tailTrace_3952922 : CollatzResearch.WordTrace tailWord_3952922 prefixEnd_3952922 676582991910696136065283 := by
  unfold tailWord_3952922
  simp only [CollatzResearch.WordTrace]
  refine ⟨36043727446311543543707255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96116606523497449449886013 36043727446311543543707255)
  ·
    refine ⟨54065591169467315315560883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36043727446311543543707255 54065591169467315315560883)
    ·
      refine ⟨81098386754200972973341325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54065591169467315315560883 81098386754200972973341325)
      ·
        refine ⟨30411895032825364865002997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81098386754200972973341325 30411895032825364865002997)
        ·
          refine ⟨2851115159327377956094031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30411895032825364865002997 2851115159327377956094031)
          ·
            refine ⟨4276672738991066934141047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2851115159327377956094031 4276672738991066934141047)
            ·
              refine ⟨6415009108486600401211571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4276672738991066934141047 6415009108486600401211571)
              ·
                refine ⟨9622513662729900601817357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6415009108486600401211571 9622513662729900601817357)
                ·
                  refine ⟨3608442623523712725681509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9622513662729900601817357 3608442623523712725681509)
                  ·
                    refine ⟨676582991910696136065283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3608442623523712725681509 676582991910696136065283)
                    ·
                      rfl

theorem cell23_3952922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 3, 4].length) (baseStart_3952922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952922 prefixEnd_3952922 := by exact prefixLift 3952922
  have htrace : WordTrace (prefixWord ++ tailWord_3952922) baseStart_3952922 baseEnd_3952922 := by
    simpa [prefixWord, tailWord_3952922, baseEnd_3952922] using wordTrace_append hprefix tailTrace_3952922
  have hstable : (prefixWord ++ tailWord_3952922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952922).length < 2 ^ (prefixWord ++ tailWord_3952922).sum := by decide
  have hdescent : baseEnd_3952922 < baseStart_3952922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952931 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 3, 5]
def baseStart_3952931 : Nat := 118140960795 + 3952931 * 2 ^ 59
def prefixEnd_3952931 : Nat := 4983230072969 + 3 ^ 40 * 3952931 * 2
def baseEnd_3952931 : Nat := 676584532352659624327769

theorem tailTrace_3952931 : CollatzResearch.WordTrace tailWord_3952931 prefixEnd_3952931 676584532352659624327769 := by
  unfold tailWord_3952931
  simp only [CollatzResearch.WordTrace]
  refine ⟨144175238042213568711906647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96116825361475712474604431 144175238042213568711906647)
  ·
    refine ⟨216262857063320353067859971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144175238042213568711906647 216262857063320353067859971)
    ·
      refine ⟨324394285594980529601789957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216262857063320353067859971 324394285594980529601789957)
      ·
        refine ⟨60823928549058849300335617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324394285594980529601789957 60823928549058849300335617)
        ·
          refine ⟨45617946411794136975251713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60823928549058849300335617 45617946411794136975251713)
          ·
            refine ⟨34213459808845602731438785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45617946411794136975251713 34213459808845602731438785)
            ·
              refine ⟨25660094856634202048579089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34213459808845602731438785 25660094856634202048579089)
              ·
                refine ⟨19245071142475651536434317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25660094856634202048579089 19245071142475651536434317)
                ·
                  refine ⟨7216901678428369326162869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19245071142475651536434317 7216901678428369326162869)
                  ·
                    refine ⟨676584532352659624327769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7216901678428369326162869 676584532352659624327769)
                    ·
                      rfl

theorem cell23_3952931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 5].length) (baseStart_3952931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952931 prefixEnd_3952931 := by exact prefixLift 3952931
  have htrace : WordTrace (prefixWord ++ tailWord_3952931) baseStart_3952931 baseEnd_3952931 := by
    simpa [prefixWord, tailWord_3952931, baseEnd_3952931] using wordTrace_append hprefix tailTrace_3952931
  have hstable : (prefixWord ++ tailWord_3952931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952931).length < 2 ^ (prefixWord ++ tailWord_3952931).sum := by decide
  have hdescent : baseEnd_3952931 < baseStart_3952931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952968 : List Nat := [2, 1, 3, 1, 1, 2, 2, 5, 1, 1, 4]
def baseStart_3952968 : Nat := 118140960795 + 3952968 * 2 ^ 59
def prefixEnd_3952968 : Nat := 4983230072969 + 3 ^ 40 * 3952968 * 2
def baseEnd_3952968 : Nat := 2029772595842195228220637

theorem tailTrace_3952968 : CollatzResearch.WordTrace tailWord_3952968 prefixEnd_3952968 2029772595842195228220637 := by
  unfold tailWord_3952968
  simp only [CollatzResearch.WordTrace]
  refine ⟨72088293771539762015501779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96117725028719682687335705 72088293771539762015501779)
  ·
    refine ⟨108132440657309643023252669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72088293771539762015501779 108132440657309643023252669)
    ·
      refine ⟨40549665246491116133719751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108132440657309643023252669 40549665246491116133719751)
      ·
        refine ⟨60824497869736674200579627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40549665246491116133719751 60824497869736674200579627)
        ·
          refine ⟨91236746804605011300869441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60824497869736674200579627 91236746804605011300869441)
          ·
            refine ⟨68427560103453758475652081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91236746804605011300869441 68427560103453758475652081)
            ·
              refine ⟨51320670077590318856739061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68427560103453758475652081 51320670077590318856739061)
              ·
                refine ⟨4811312819774092392819287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51320670077590318856739061 4811312819774092392819287)
                ·
                  refine ⟨7216969229661138589228931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4811312819774092392819287 7216969229661138589228931)
                  ·
                    refine ⟨10825453844491707883843397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7216969229661138589228931 10825453844491707883843397)
                    ·
                      refine ⟨2029772595842195228220637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10825453844491707883843397 2029772595842195228220637)
                      ·
                        rfl

theorem cell23_3952968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_3952968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952968 prefixEnd_3952968 := by exact prefixLift 3952968
  have htrace : WordTrace (prefixWord ++ tailWord_3952968) baseStart_3952968 baseEnd_3952968 := by
    simpa [prefixWord, tailWord_3952968, baseEnd_3952968] using wordTrace_append hprefix tailTrace_3952968
  have hstable : (prefixWord ++ tailWord_3952968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952968).length < 2 ^ (prefixWord ++ tailWord_3952968).sum := by decide
  have hdescent : baseEnd_3952968 < baseStart_3952968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952971 : List Nat := [1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 5]
def baseStart_3952971 : Nat := 118140960795 + 3952971 * 2 ^ 59
def prefixEnd_3952971 : Nat := 4983230072969 + 3 ^ 40 * 3952971 * 2
def baseEnd_3952971 : Nat := 2029774136284158716483123

theorem tailTrace_3952971 : CollatzResearch.WordTrace tailWord_3952971 prefixEnd_3952971 2029774136284158716483123 := by
  unfold tailWord_3952971
  simp only [CollatzResearch.WordTrace]
  refine ⟨144176696962068655543362767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96117797974712437028908511 144176696962068655543362767)
  ·
    refine ⟨216265045443102983315044151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144176696962068655543362767 216265045443102983315044151)
    ·
      refine ⟨324397568164654474972566227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216265045443102983315044151 324397568164654474972566227)
      ·
        refine ⟨486596352246981712458849341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324397568164654474972566227 486596352246981712458849341)
        ·
          refine ⟨182473632092618142172068503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 486596352246981712458849341 182473632092618142172068503)
          ·
            refine ⟨273710448138927213258102755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182473632092618142172068503 273710448138927213258102755)
            ·
              refine ⟨410565672208390819887154133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273710448138927213258102755 410565672208390819887154133)
              ·
                refine ⟨9622632942384159841105175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 410565672208390819887154133 9622632942384159841105175)
                ·
                  refine ⟨14433949413576239761657763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9622632942384159841105175 14433949413576239761657763)
                  ·
                    refine ⟨21650924120364359642486645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14433949413576239761657763 21650924120364359642486645)
                    ·
                      refine ⟨2029774136284158716483123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21650924120364359642486645 2029774136284158716483123)
                      ·
                        rfl

theorem cell23_3952971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 5].length) (baseStart_3952971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952971 prefixEnd_3952971 := by exact prefixLift 3952971
  have htrace : WordTrace (prefixWord ++ tailWord_3952971) baseStart_3952971 baseEnd_3952971 := by
    simpa [prefixWord, tailWord_3952971, baseEnd_3952971] using wordTrace_append hprefix tailTrace_3952971
  have hstable : (prefixWord ++ tailWord_3952971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952971).length < 2 ^ (prefixWord ++ tailWord_3952971).sum := by decide
  have hdescent : baseEnd_3952971 < baseStart_3952971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952978 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 4, 4]
def baseStart_3952978 : Nat := 118140960795 + 3952978 * 2 ^ 59
def prefixEnd_3952978 : Nat := 4983230072969 + 3 ^ 40 * 3952978 * 2
def baseEnd_3952978 : Nat := 676592576882913396365197

theorem tailTrace_3952978 : CollatzResearch.WordTrace tailWord_3952978 prefixEnd_3952978 676592576882913396365197 := by
  unfold tailWord_3952978
  simp only [CollatzResearch.WordTrace]
  refine ⟨36044238068260823934716897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96117968182028863825911725 36044238068260823934716897)
  ·
    refine ⟨27033178551195617951037673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36044238068260823934716897 27033178551195617951037673)
    ·
      refine ⟨20274883913396713463278255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27033178551195617951037673 20274883913396713463278255)
      ·
        refine ⟨30412325870095070194917383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20274883913396713463278255 30412325870095070194917383)
        ·
          refine ⟨45618488805142605292376075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30412325870095070194917383 45618488805142605292376075)
          ·
            refine ⟨68427733207713907938564113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45618488805142605292376075 68427733207713907938564113)
            ·
              refine ⟨51320799905785430953923085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68427733207713907938564113 51320799905785430953923085)
              ·
                refine ⟨19245299964669536607721157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51320799905785430953923085 19245299964669536607721157)
                ·
                  refine ⟨3608493743375538113947717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19245299964669536607721157 3608493743375538113947717)
                  ·
                    refine ⟨676592576882913396365197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3608493743375538113947717 676592576882913396365197)
                    ·
                      rfl

theorem cell23_3952978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_3952978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952978 prefixEnd_3952978 := by exact prefixLift 3952978
  have htrace : WordTrace (prefixWord ++ tailWord_3952978) baseStart_3952978 baseEnd_3952978 := by
    simpa [prefixWord, tailWord_3952978, baseEnd_3952978] using wordTrace_append hprefix tailTrace_3952978
  have hstable : (prefixWord ++ tailWord_3952978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952978).length < 2 ^ (prefixWord ++ tailWord_3952978).sum := by decide
  have hdescent : baseEnd_3952978 < baseStart_3952978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952985 : List Nat := [1, 2, 1, 2, 2, 2, 1, 5, 3, 2, 2]
def baseStart_3952985 : Nat := 118140960795 + 3952985 * 2 ^ 59
def prefixEnd_3952985 : Nat := 4983230072969 + 3 ^ 40 * 3952985 * 2
def baseEnd_3952985 : Nat := 2029781325013321661708059

theorem tailTrace_3952985 : CollatzResearch.WordTrace tailWord_3952985 prefixEnd_3952985 2029781325013321661708059 := by
  unfold tailWord_3952985
  simp only [CollatzResearch.WordTrace]
  refine ⟨144177207584017935934372409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96118138389345290622914939 144177207584017935934372409)
  ·
    refine ⟨108132905688013451950779307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144177207584017935934372409 108132905688013451950779307)
    ·
      refine ⟨162199358532020177926168961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108132905688013451950779307 162199358532020177926168961)
      ·
        refine ⟨121649518899015133444626721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162199358532020177926168961 121649518899015133444626721)
        ·
          refine ⟨91237139174261350083470041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121649518899015133444626721 91237139174261350083470041)
          ·
            refine ⟨68427854380696012562602531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91237139174261350083470041 68427854380696012562602531)
            ·
              refine ⟨102641781571044018843903797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68427854380696012562602531 102641781571044018843903797)
              ·
                refine ⟨9622667022285376766615981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102641781571044018843903797 9622667022285376766615981)
                ·
                  refine ⟨3608500133357016287480993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9622667022285376766615981 3608500133357016287480993)
                  ·
                    refine ⟨2706375100017762215610745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3608500133357016287480993 2706375100017762215610745)
                    ·
                      refine ⟨2029781325013321661708059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2706375100017762215610745 2029781325013321661708059)
                      ·
                        rfl

theorem cell23_3952985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 2, 2].length) (baseStart_3952985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952985 prefixEnd_3952985 := by exact prefixLift 3952985
  have htrace : WordTrace (prefixWord ++ tailWord_3952985) baseStart_3952985 baseEnd_3952985 := by
    simpa [prefixWord, tailWord_3952985, baseEnd_3952985] using wordTrace_append hprefix tailTrace_3952985
  have hstable : (prefixWord ++ tailWord_3952985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952985).length < 2 ^ (prefixWord ++ tailWord_3952985).sum := by decide
  have hdescent : baseEnd_3952985 < baseStart_3952985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952991 : List Nat := [1, 1, 2, 3, 1, 2, 5, 8]
def baseStart_3952991 : Nat := 118140960795 + 3952991 * 2 ^ 59
def prefixEnd_3952991 : Nat := 4983230072969 + 3 ^ 40 * 3952991 * 2
def baseEnd_3952991 : Nat := 75177200218416616230853

theorem tailTrace_3952991 : CollatzResearch.WordTrace tailWord_3952991 prefixEnd_3952991 75177200218416616230853 := by
  unfold tailWord_3952991
  simp only [CollatzResearch.WordTrace]
  refine ⟨144177426421996198959090827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96118284281330799306060551 144177426421996198959090827)
  ·
    refine ⟨216266139632994298438636241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144177426421996198959090827 216266139632994298438636241)
    ·
      refine ⟨162199604724745723828977181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216266139632994298438636241 162199604724745723828977181)
      ·
        refine ⟨60824851771779646435866443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162199604724745723828977181 60824851771779646435866443)
        ·
          refine ⟨91237277657669469653799665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60824851771779646435866443 91237277657669469653799665)
          ·
            refine ⟨68427958243252102240349749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91237277657669469653799665 68427958243252102240349749)
            ·
              refine ⟨6415121085304884585032789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68427958243252102240349749 6415121085304884585032789)
              ·
                refine ⟨75177200218416616230853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6415121085304884585032789 75177200218416616230853)
                ·
                  rfl

theorem cell23_3952991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 8].length) (baseStart_3952991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3952991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3952991 prefixEnd_3952991 := by exact prefixLift 3952991
  have htrace : WordTrace (prefixWord ++ tailWord_3952991) baseStart_3952991 baseEnd_3952991 := by
    simpa [prefixWord, tailWord_3952991, baseEnd_3952991] using wordTrace_append hprefix tailTrace_3952991
  have hstable : (prefixWord ++ tailWord_3952991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952991).length < 2 ^ (prefixWord ++ tailWord_3952991).sum := by decide
  have hdescent : baseEnd_3952991 < baseStart_3952991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953002 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 5, 2, 2]
def baseStart_3953002 : Nat := 118140960795 + 3953002 * 2 ^ 59
def prefixEnd_3953002 : Nat := 4983230072969 + 3 ^ 40 * 3953002 * 2
def baseEnd_3953002 : Nat := 2029790054184448095195481

theorem tailTrace_3953002 : CollatzResearch.WordTrace tailWord_3953002 prefixEnd_3953002 2029790054184448095195481 := by
  unfold tailWord_3953002
  simp only [CollatzResearch.WordTrace]
  refine ⟨36044456906239086959435315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96118551749970898558494173 36044456906239086959435315)
  ·
    refine ⟨54066685359358630439152973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36044456906239086959435315 54066685359358630439152973)
    ·
      refine ⟨20275007009759486414682365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54066685359358630439152973 20275007009759486414682365)
      ·
        refine ⟨7603127628659807405505887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20275007009759486414682365 7603127628659807405505887)
        ·
          refine ⟨11404691442989711108258831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7603127628659807405505887 11404691442989711108258831)
          ·
            refine ⟨17107037164484566662388247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11404691442989711108258831 17107037164484566662388247)
            ·
              refine ⟨25660555746726849993582371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17107037164484566662388247 25660555746726849993582371)
              ·
                refine ⟨38490833620090274990373557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25660555746726849993582371 38490833620090274990373557)
                ·
                  refine ⟨3608515651883463280347521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38490833620090274990373557 3608515651883463280347521)
                  ·
                    refine ⟨2706386738912597460260641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3608515651883463280347521 2706386738912597460260641)
                    ·
                      refine ⟨2029790054184448095195481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2706386738912597460260641 2029790054184448095195481)
                      ·
                        rfl

theorem cell23_3953002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_3953002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953002 prefixEnd_3953002 := by exact prefixLift 3953002
  have htrace : WordTrace (prefixWord ++ tailWord_3953002) baseStart_3953002 baseEnd_3953002 := by
    simpa [prefixWord, tailWord_3953002, baseEnd_3953002] using wordTrace_append hprefix tailTrace_3953002
  have hstable : (prefixWord ++ tailWord_3953002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953002).length < 2 ^ (prefixWord ++ tailWord_3953002).sum := by decide
  have hdescent : baseEnd_3953002 < baseStart_3953002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953005 : List Nat := [1, 5, 1, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_3953005 : Nat := 118140960795 + 3953005 * 2 ^ 59
def prefixEnd_3953005 : Nat := 4983230072969 + 3 ^ 40 * 3953005 * 2
def baseEnd_3953005 : Nat := 2029791594626411583457967

theorem tailTrace_3953005 : CollatzResearch.WordTrace tailWord_3953005 prefixEnd_3953005 2029791594626411583457967 := by
  unfold tailWord_3953005
  simp only [CollatzResearch.WordTrace]
  refine ⟨144177937043945479350100469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96118624695963652900066979 144177937043945479350100469)
  ·
    refine ⟨13516681597869888689071919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144177937043945479350100469 13516681597869888689071919)
    ·
      refine ⟨20275022396804833033607879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13516681597869888689071919 20275022396804833033607879)
      ·
        refine ⟨30412533595207249550411819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20275022396804833033607879 30412533595207249550411819)
        ·
          refine ⟨45618800392810874325617729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30412533595207249550411819 45618800392810874325617729)
          ·
            refine ⟨34214100294608155744213297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45618800392810874325617729 34214100294608155744213297)
            ·
              refine ⟨25660575220956116808159973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34214100294608155744213297 25660575220956116808159973)
              ·
                refine ⟨4811357853929271901529995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25660575220956116808159973 4811357853929271901529995)
                ·
                  refine ⟨7217036780893907852294993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4811357853929271901529995 7217036780893907852294993)
                  ·
                    refine ⟨5412777585670430889221245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7217036780893907852294993 5412777585670430889221245)
                    ·
                      refine ⟨2029791594626411583457967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5412777585670430889221245 2029791594626411583457967)
                      ·
                        rfl

theorem cell23_3953005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_3953005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953005 prefixEnd_3953005 := by exact prefixLift 3953005
  have htrace : WordTrace (prefixWord ++ tailWord_3953005) baseStart_3953005 baseEnd_3953005 := by
    simpa [prefixWord, tailWord_3953005, baseEnd_3953005] using wordTrace_append hprefix tailTrace_3953005
  have hstable : (prefixWord ++ tailWord_3953005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953005).length < 2 ^ (prefixWord ++ tailWord_3953005).sum := by decide
  have hdescent : baseEnd_3953005 < baseStart_3953005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953008 : List Nat := [2, 1, 1, 1, 4, 4, 3, 7]
def baseStart_3953008 : Nat := 118140960795 + 3953008 * 2 ^ 59
def prefixEnd_3953008 : Nat := 4983230072969 + 3 ^ 40 * 3953008 * 2
def baseEnd_3953008 : Nat := 75177523521050928582239

theorem tailTrace_3953008 : CollatzResearch.WordTrace tailWord_3953008 prefixEnd_3953008 75177523521050928582239 := by
  unfold tailWord_3953008
  simp only [CollatzResearch.WordTrace]
  refine ⟨72089023231467305431229839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96118697641956407241639785 72089023231467305431229839)
  ·
    refine ⟨108133534847200958146844759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72089023231467305431229839 108133534847200958146844759)
    ·
      refine ⟨162200302270801437220267139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108133534847200958146844759 162200302270801437220267139)
      ·
        refine ⟨243300453406202155830400709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162200302270801437220267139 243300453406202155830400709)
        ·
          refine ⟨45618835013662904218200133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243300453406202155830400709 45618835013662904218200133)
          ·
            refine ⟨8553531565061794540912525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45618835013662904218200133 8553531565061794540912525)
            ·
              refine ⟨3207574336898172952842197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8553531565061794540912525 3207574336898172952842197)
              ·
                refine ⟨75177523521050928582239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3207574336898172952842197 75177523521050928582239)
                ·
                  rfl

theorem cell23_3953008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 7].length) (baseStart_3953008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953008 prefixEnd_3953008 := by exact prefixLift 3953008
  have htrace : WordTrace (prefixWord ++ tailWord_3953008) baseStart_3953008 baseEnd_3953008 := by
    simpa [prefixWord, tailWord_3953008, baseEnd_3953008] using wordTrace_append hprefix tailTrace_3953008
  have hstable : (prefixWord ++ tailWord_3953008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953008).length < 2 ^ (prefixWord ++ tailWord_3953008).sum := by decide
  have hdescent : baseEnd_3953008 < baseStart_3953008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953019 : List Nat := [1, 1, 1, 1, 1, 8, 2, 3, 1, 2, 2]
def baseStart_3953019 : Nat := 118140960795 + 3953019 * 2 ^ 59
def prefixEnd_3953019 : Nat := 4983230072969 + 3 ^ 40 * 3953019 * 2
def baseEnd_3953019 : Nat := 2029798783355574528682903

theorem tailTrace_3953019 : CollatzResearch.WordTrace tailWord_3953019 prefixEnd_3953019 2029798783355574528682903 := by
  unfold tailWord_3953019
  simp only [CollatzResearch.WordTrace]
  refine ⟨144178447665894759741110111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96118965110596506494073407 144178447665894759741110111)
  ·
    refine ⟨216267671498842139611665167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144178447665894759741110111 216267671498842139611665167)
    ·
      refine ⟨324401507248263209417497751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216267671498842139611665167 324401507248263209417497751)
      ·
        refine ⟨486602260872394814126246627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324401507248263209417497751 486602260872394814126246627)
        ·
          refine ⟨729903391308592221189369941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486602260872394814126246627 729903391308592221189369941)
          ·
            refine ⟨8553555366897565092062929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 729903391308592221189369941 8553555366897565092062929)
            ·
              refine ⟨6415166525173173819047197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8553555366897565092062929 6415166525173173819047197)
              ·
                refine ⟨2405687446939940182142699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6415166525173173819047197 2405687446939940182142699)
                ·
                  refine ⟨3608531170409910273214049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2405687446939940182142699 3608531170409910273214049)
                  ·
                    refine ⟨2706398377807432704910537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3608531170409910273214049 2706398377807432704910537)
                    ·
                      refine ⟨2029798783355574528682903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2706398377807432704910537 2029798783355574528682903)
                      ·
                        rfl

theorem cell23_3953019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 1, 2, 2].length) (baseStart_3953019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953019 prefixEnd_3953019 := by exact prefixLift 3953019
  have htrace : WordTrace (prefixWord ++ tailWord_3953019) baseStart_3953019 baseEnd_3953019 := by
    simpa [prefixWord, tailWord_3953019, baseEnd_3953019] using wordTrace_append hprefix tailTrace_3953019
  have hstable : (prefixWord ++ tailWord_3953019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953019).length < 2 ^ (prefixWord ++ tailWord_3953019).sum := by decide
  have hdescent : baseEnd_3953019 < baseStart_3953019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953035 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 4, 1, 3]
def baseStart_3953035 : Nat := 118140960795 + 3953035 * 2 ^ 59
def prefixEnd_3953035 : Nat := 4983230072969 + 3 ^ 40 * 3953035 * 2
def baseEnd_3953035 : Nat := 2029806999046046466082829

theorem tailTrace_3953035 : CollatzResearch.WordTrace tailWord_3953035 prefixEnd_3953035 2029806999046046466082829 := by
  unfold tailWord_3953035
  simp only [CollatzResearch.WordTrace]
  refine ⟨144179031233836794473692559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96119354155891196315795039 144179031233836794473692559)
  ·
    refine ⟨216268546850755191710538839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144179031233836794473692559 216268546850755191710538839)
    ·
      refine ⟨324402820276132787565808259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216268546850755191710538839 324402820276132787565808259)
      ·
        refine ⟨486604230414199181348712389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324402820276132787565808259 486604230414199181348712389)
        ·
          refine ⟨91238293202662346502883573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 486604230414199181348712389 91238293202662346502883573)
          ·
            refine ⟨8553589987749594984645335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91238293202662346502883573 8553589987749594984645335)
            ·
              refine ⟨12830384981624392476968003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8553589987749594984645335 12830384981624392476968003)
              ·
                refine ⟨19245577472436588715452005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12830384981624392476968003 19245577472436588715452005)
                ·
                  refine ⟨3608545776081860384147251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19245577472436588715452005 3608545776081860384147251)
                  ·
                    refine ⟨5412818664122790576220877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3608545776081860384147251 5412818664122790576220877)
                    ·
                      refine ⟨2029806999046046466082829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5412818664122790576220877 2029806999046046466082829)
                      ·
                        rfl

theorem cell23_3953035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 1, 3].length) (baseStart_3953035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953035 prefixEnd_3953035 := by exact prefixLift 3953035
  have htrace : WordTrace (prefixWord ++ tailWord_3953035) baseStart_3953035 baseEnd_3953035 := by
    simpa [prefixWord, tailWord_3953035, baseEnd_3953035] using wordTrace_append hprefix tailTrace_3953035
  have hstable : (prefixWord ++ tailWord_3953035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953035).length < 2 ^ (prefixWord ++ tailWord_3953035).sum := by decide
  have hdescent : baseEnd_3953035 < baseStart_3953035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953046 : List Nat := [5, 3, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_3953046 : Nat := 118140960795 + 3953046 * 2 ^ 59
def prefixEnd_3953046 : Nat := 4983230072969 + 3 ^ 40 * 3953046 * 2
def baseEnd_3953046 : Nat := 676604215777748641015093

theorem tailTrace_3953046 : CollatzResearch.WordTrace tailWord_3953046 prefixEnd_3953046 676604215777748641015093 := by
  unfold tailWord_3953046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9011214527299808959521437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96119621624531295568228661 9011214527299808959521437)
  ·
    refine ⟨3379205447737428359820539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9011214527299808959521437 3379205447737428359820539)
    ·
      refine ⟨5068808171606142539730809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3379205447737428359820539 5068808171606142539730809)
      ·
        refine ⟨3801606128704606904798107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5068808171606142539730809 3801606128704606904798107)
        ·
          refine ⟨5702409193056910357197161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3801606128704606904798107 5702409193056910357197161)
          ·
            refine ⟨4276806894792682767897871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5702409193056910357197161 4276806894792682767897871)
            ·
              refine ⟨6415210342189024151846807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4276806894792682767897871 6415210342189024151846807)
              ·
                refine ⟨9622815513283536227770211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6415210342189024151846807 9622815513283536227770211)
                ·
                  refine ⟨14434223269925304341655317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9622815513283536227770211 14434223269925304341655317)
                  ·
                    refine ⟨676604215777748641015093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14434223269925304341655317 676604215777748641015093)
                    ·
                      rfl

theorem cell23_3953046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_3953046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953046 prefixEnd_3953046 := by exact prefixLift 3953046
  have htrace : WordTrace (prefixWord ++ tailWord_3953046) baseStart_3953046 baseEnd_3953046 := by
    simpa [prefixWord, tailWord_3953046, baseEnd_3953046] using wordTrace_append hprefix tailTrace_3953046
  have hstable : (prefixWord ++ tailWord_3953046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953046).length < 2 ^ (prefixWord ++ tailWord_3953046).sum := by decide
  have hdescent : baseEnd_3953046 < baseStart_3953046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953091 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 9]
def baseStart_3953091 : Nat := 118140960795 + 3953091 * 2 ^ 59
def prefixEnd_3953091 : Nat := 4983230072969 + 3 ^ 40 * 3953091 * 2
def baseEnd_3953091 : Nat := 2029835753962698246982571

theorem tailTrace_3953091 : CollatzResearch.WordTrace tailWord_3953091 prefixEnd_3953091 2029835753962698246982571 := by
  unfold tailWord_3953091
  simp only [CollatzResearch.WordTrace]
  refine ⟨144181073721633916037731127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96120715814422610691820751 144181073721633916037731127)
  ·
    refine ⟨216271610582450874056596691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144181073721633916037731127 216271610582450874056596691)
    ·
      refine ⟨324407415873676311084895037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216271610582450874056596691 324407415873676311084895037)
      ·
        refine ⟨121652780952628616656835639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324407415873676311084895037 121652780952628616656835639)
        ·
          refine ⟨182479171428942924985253459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121652780952628616656835639 182479171428942924985253459)
          ·
            refine ⟨273718757143414387477880189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182479171428942924985253459 273718757143414387477880189)
            ·
              refine ⟨102644533928780395304205071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273718757143414387477880189 102644533928780395304205071)
              ·
                refine ⟨153966800893170592956307607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102644533928780395304205071 153966800893170592956307607)
                ·
                  refine ⟨230950201339755889434461411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153966800893170592956307607 230950201339755889434461411)
                  ·
                    refine ⟨346425302009633834151692117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 230950201339755889434461411 346425302009633834151692117)
                    ·
                      refine ⟨2029835753962698246982571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 346425302009633834151692117 2029835753962698246982571)
                      ·
                        rfl

theorem cell23_3953091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_3953091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953091 prefixEnd_3953091 := by exact prefixLift 3953091
  have htrace : WordTrace (prefixWord ++ tailWord_3953091) baseStart_3953091 baseEnd_3953091 := by
    simpa [prefixWord, tailWord_3953091, baseEnd_3953091] using wordTrace_append hprefix tailTrace_3953091
  have hstable : (prefixWord ++ tailWord_3953091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953091).length < 2 ^ (prefixWord ++ tailWord_3953091).sum := by decide
  have hdescent : baseEnd_3953091 < baseStart_3953091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953109 : List Nat := [1, 3, 2, 3, 1, 3, 1, 3, 2, 2, 2]
def baseStart_3953109 : Nat := 118140960795 + 3953109 * 2 ^ 59
def prefixEnd_3953109 : Nat := 4983230072969 + 3 ^ 40 * 3953109 * 2
def baseEnd_3953109 : Nat := 2029844996614479176557489

theorem tailTrace_3953109 : CollatzResearch.WordTrace tailWord_3953109 prefixEnd_3953109 2029844996614479176557489 := by
  unfold tailWord_3953109
  simp only [CollatzResearch.WordTrace]
  refine ⟨144181730235568705111886381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96121153490379136741257587 144181730235568705111886381)
  ·
    refine ⟨54068148838338264416957393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144181730235568705111886381 54068148838338264416957393)
    ·
      refine ⟨40551111628753698312718045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54068148838338264416957393 40551111628753698312718045)
      ·
        refine ⟨15206666860782636867269267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40551111628753698312718045 15206666860782636867269267)
        ·
          refine ⟨22810000291173955300903901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15206666860782636867269267 22810000291173955300903901)
          ·
            refine ⟨8553750109190233237838963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22810000291173955300903901 8553750109190233237838963)
            ·
              refine ⟨12830625163785349856758445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8553750109190233237838963 12830625163785349856758445)
              ·
                refine ⟨4811484436419506196284417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12830625163785349856758445 4811484436419506196284417)
                ·
                  refine ⟨3608613327314629647213313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4811484436419506196284417 3608613327314629647213313)
                  ·
                    refine ⟨2706459995485972235409985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3608613327314629647213313 2706459995485972235409985)
                    ·
                      refine ⟨2029844996614479176557489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2706459995485972235409985 2029844996614479176557489)
                      ·
                        rfl

theorem cell23_3953109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_3953109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953109 prefixEnd_3953109 := by exact prefixLift 3953109
  have htrace : WordTrace (prefixWord ++ tailWord_3953109) baseStart_3953109 baseEnd_3953109 := by
    simpa [prefixWord, tailWord_3953109, baseEnd_3953109] using wordTrace_append hprefix tailTrace_3953109
  have hstable : (prefixWord ++ tailWord_3953109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953109).length < 2 ^ (prefixWord ++ tailWord_3953109).sum := by decide
  have hdescent : baseEnd_3953109 < baseStart_3953109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953148 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_3953148 : Nat := 118140960795 + 3953148 * 2 ^ 59
def prefixEnd_3953148 : Nat := 4983230072969 + 3 ^ 40 * 3953148 * 2
def baseEnd_3953148 : Nat := 2029865022360004523969809

theorem tailTrace_3953148 : CollatzResearch.WordTrace tailWord_3953148 prefixEnd_3953148 2029865022360004523969809 := by
  unfold tailWord_3953148
  simp only [CollatzResearch.WordTrace]
  refine ⟨72091576341213707386278049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96122101788284943181704065 72091576341213707386278049)
  ·
    refine ⟨54068682255910280539708537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72091576341213707386278049 54068682255910280539708537)
    ·
      refine ⟨40551511691932710404781403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54068682255910280539708537 40551511691932710404781403)
      ·
        refine ⟨60827267537899065607172105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40551511691932710404781403 60827267537899065607172105)
        ·
          refine ⟨45620450653424299205379079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60827267537899065607172105 45620450653424299205379079)
          ·
            refine ⟨68430675980136448808068619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45620450653424299205379079 68430675980136448808068619)
            ·
              refine ⟨102646013970204673212102929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68430675980136448808068619 102646013970204673212102929)
              ·
                refine ⟨76984510477653504909077197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102646013970204673212102929 76984510477653504909077197)
                ·
                  refine ⟨28869191429120064340903949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76984510477653504909077197 28869191429120064340903949)
                  ·
                    refine ⟨10825946785920024127838981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28869191429120064340903949 10825946785920024127838981)
                    ·
                      refine ⟨2029865022360004523969809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10825946785920024127838981 2029865022360004523969809)
                      ·
                        rfl

theorem cell23_3953148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_3953148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953148 prefixEnd_3953148 := by exact prefixLift 3953148
  have htrace : WordTrace (prefixWord ++ tailWord_3953148) baseStart_3953148 baseEnd_3953148 := by
    simpa [prefixWord, tailWord_3953148, baseEnd_3953148] using wordTrace_append hprefix tailTrace_3953148
  have hstable : (prefixWord ++ tailWord_3953148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953148).length < 2 ^ (prefixWord ++ tailWord_3953148).sum := by decide
  have hdescent : baseEnd_3953148 < baseStart_3953148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953168 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 3]
def baseStart_3953168 : Nat := 118140960795 + 3953168 * 2 ^ 59
def prefixEnd_3953168 : Nat := 4983230072969 + 3 ^ 40 * 3953168 * 2
def baseEnd_3953168 : Nat := 2029875291973094445719717

theorem tailTrace_3953168 : CollatzResearch.WordTrace tailWord_3953168 prefixEnd_3953168 2029875291973094445719717 := by
  unfold tailWord_3953168
  simp only [CollatzResearch.WordTrace]
  refine ⟨72091941071177479094142079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96122588094903305458856105 72091941071177479094142079)
  ·
    refine ⟨108137911606766218641213119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72091941071177479094142079 108137911606766218641213119)
    ·
      refine ⟨162206867410149327961819679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108137911606766218641213119 162206867410149327961819679)
      ·
        refine ⟨243310301115223991942729519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162206867410149327961819679 243310301115223991942729519)
        ·
          refine ⟨364965451672835987914094279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243310301115223991942729519 364965451672835987914094279)
          ·
            refine ⟨547448177509253981871141419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364965451672835987914094279 547448177509253981871141419)
            ·
              refine ⟨821172266263880972806712129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547448177509253981871141419 821172266263880972806712129)
              ·
                refine ⟨615879199697910729605034097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 821172266263880972806712129 615879199697910729605034097)
                ·
                  refine ⟨461909399773433047203775573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615879199697910729605034097 461909399773433047203775573)
                  ·
                    refine ⟨5413000778594918521919245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 461909399773433047203775573 5413000778594918521919245)
                    ·
                      refine ⟨2029875291973094445719717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5413000778594918521919245 2029875291973094445719717)
                      ·
                        rfl

theorem cell23_3953168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 3].length) (baseStart_3953168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953168 prefixEnd_3953168 := by exact prefixLift 3953168
  have htrace : WordTrace (prefixWord ++ tailWord_3953168) baseStart_3953168 baseEnd_3953168 := by
    simpa [prefixWord, tailWord_3953168, baseEnd_3953168] using wordTrace_append hprefix tailTrace_3953168
  have hstable : (prefixWord ++ tailWord_3953168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953168).length < 2 ^ (prefixWord ++ tailWord_3953168).sum := by decide
  have hdescent : baseEnd_3953168 < baseStart_3953168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953185 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 1, 4, 3]
def baseStart_3953185 : Nat := 118140960795 + 3953185 * 2 ^ 59
def prefixEnd_3953185 : Nat := 4983230072969 + 3 ^ 40 * 3953185 * 2
def baseEnd_3953185 : Nat := 2029884021144220879207139

theorem tailTrace_3953185 : CollatzResearch.WordTrace tailWord_3953185 prefixEnd_3953185 2029884021144220879207139 := by
  unfold tailWord_3953185
  simp only [CollatzResearch.WordTrace]
  refine ⟨144184502183293370091653009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96123001455528913394435339 144184502183293370091653009)
  ·
    refine ⟨108138376637470027568739757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144184502183293370091653009 108138376637470027568739757)
    ·
      refine ⟨40551891239051260338277409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108138376637470027568739757 40551891239051260338277409)
      ·
        refine ⟨30413918429288445253708057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40551891239051260338277409 30413918429288445253708057)
        ·
          refine ⟨22810438821966333940281043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30413918429288445253708057 22810438821966333940281043)
          ·
            refine ⟨34215658232949500910421565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22810438821966333940281043 34215658232949500910421565)
            ·
              refine ⟨12830871837356062841408087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34215658232949500910421565 12830871837356062841408087)
              ·
                refine ⟨19246307756034094262112131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12830871837356062841408087 19246307756034094262112131)
                ·
                  refine ⟨28869461634051141393168197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19246307756034094262112131 28869461634051141393168197)
                  ·
                    refine ⟨5413024056384589011219037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28869461634051141393168197 5413024056384589011219037)
                    ·
                      refine ⟨2029884021144220879207139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5413024056384589011219037 2029884021144220879207139)
                      ·
                        rfl

theorem cell23_3953185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_3953185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953185 prefixEnd_3953185 := by exact prefixLift 3953185
  have htrace : WordTrace (prefixWord ++ tailWord_3953185) baseStart_3953185 baseEnd_3953185 := by
    simpa [prefixWord, tailWord_3953185, baseEnd_3953185] using wordTrace_append hprefix tailTrace_3953185
  have hstable : (prefixWord ++ tailWord_3953185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953185).length < 2 ^ (prefixWord ++ tailWord_3953185).sum := by decide
  have hdescent : baseEnd_3953185 < baseStart_3953185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953208 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 1, 1, 8]
def baseStart_3953208 : Nat := 118140960795 + 3953208 * 2 ^ 59
def prefixEnd_3953208 : Nat := 4983230072969 + 3 ^ 40 * 3953208 * 2
def baseEnd_3953208 : Nat := 2029895831199274289219533

theorem tailTrace_3953208 : CollatzResearch.WordTrace tailWord_3953208 prefixEnd_3953208 2029895831199274289219533 := by
  unfold tailWord_3953208
  simp only [CollatzResearch.WordTrace]
  refine ⟨72092670531105022509870139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96123560708140030013160185 72092670531105022509870139)
  ·
    refine ⟨108139005796657533764805209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72092670531105022509870139 108139005796657533764805209)
    ·
      refine ⟨81104254347493150323603907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108139005796657533764805209 81104254347493150323603907)
      ·
        refine ⟨121656381521239725485405861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81104254347493150323603907 121656381521239725485405861)
        ·
          refine ⟨22810571535232448528513599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121656381521239725485405861 22810571535232448528513599)
          ·
            refine ⟨34215857302848672792770399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22810571535232448528513599 34215857302848672792770399)
            ·
              refine ⟨51323785954273009189155599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34215857302848672792770399 51323785954273009189155599)
              ·
                refine ⟨76985678931409513783733399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51323785954273009189155599 76985678931409513783733399)
                ·
                  refine ⟨115478518397114270675600099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76985678931409513783733399 115478518397114270675600099)
                  ·
                    refine ⟨173217777595671406013400149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115478518397114270675600099 173217777595671406013400149)
                    ·
                      refine ⟨2029895831199274289219533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 173217777595671406013400149 2029895831199274289219533)
                      ·
                        rfl

theorem cell23_3953208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_3953208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953208 prefixEnd_3953208 := by exact prefixLift 3953208
  have htrace : WordTrace (prefixWord ++ tailWord_3953208) baseStart_3953208 baseEnd_3953208 := by
    simpa [prefixWord, tailWord_3953208, baseEnd_3953208] using wordTrace_append hprefix tailTrace_3953208
  have hstable : (prefixWord ++ tailWord_3953208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953208).length < 2 ^ (prefixWord ++ tailWord_3953208).sum := by decide
  have hdescent : baseEnd_3953208 < baseStart_3953208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953255 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_3953255 : Nat := 118140960795 + 3953255 * 2 ^ 59
def prefixEnd_3953255 : Nat := 4983230072969 + 3 ^ 40 * 3953255 * 2
def baseEnd_3953255 : Nat := 2029919964790035605331817

theorem tailTrace_3953255 : CollatzResearch.WordTrace tailWord_3953255 prefixEnd_3953255 2029919964790035605331817 := by
  unfold tailWord_3953255
  simp only [CollatzResearch.WordTrace]
  refine ⟨144187055293039772046701219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96124703528693181364467479 144187055293039772046701219)
  ·
    refine ⟨216280582939559658070051829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144187055293039772046701219 216280582939559658070051829)
    ·
      refine ⟨20276304650583717944067359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216280582939559658070051829 20276304650583717944067359)
      ·
        refine ⟨30414456975875576916101039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20276304650583717944067359 30414456975875576916101039)
        ·
          refine ⟨45621685463813365374151559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30414456975875576916101039 45621685463813365374151559)
          ·
            refine ⟨68432528195720048061227339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45621685463813365374151559 68432528195720048061227339)
            ·
              refine ⟨102648792293580072091841009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68432528195720048061227339 102648792293580072091841009)
              ·
                refine ⟨76986594220185054068880757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102648792293580072091841009 76986594220185054068880757)
                ·
                  refine ⟨7217493208142348818957571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76986594220185054068880757 7217493208142348818957571)
                  ·
                    refine ⟨10826239812213523228436357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7217493208142348818957571 10826239812213523228436357)
                    ·
                      refine ⟨2029919964790035605331817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10826239812213523228436357 2029919964790035605331817)
                      ·
                        rfl

theorem cell23_3953255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_3953255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953255 prefixEnd_3953255 := by exact prefixLift 3953255
  have htrace : WordTrace (prefixWord ++ tailWord_3953255) baseStart_3953255 baseEnd_3953255 := by
    simpa [prefixWord, tailWord_3953255, baseEnd_3953255] using wordTrace_append hprefix tailTrace_3953255
  have hstable : (prefixWord ++ tailWord_3953255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953255).length < 2 ^ (prefixWord ++ tailWord_3953255).sum := by decide
  have hdescent : baseEnd_3953255 < baseStart_3953255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953266 : List Nat := [3, 2, 1, 2, 4, 2, 1, 1, 3, 1, 3]
def baseStart_3953266 : Nat := 118140960795 + 3953266 * 2 ^ 59
def prefixEnd_3953266 : Nat := 4983230072969 + 3 ^ 40 * 3953266 * 2
def baseEnd_3953266 : Nat := 2029925613077235062294267

theorem tailTrace_3953266 : CollatzResearch.WordTrace tailWord_3953266 prefixEnd_3953266 2029925613077235062294267 := by
  unfold tailWord_3953266
  simp only [CollatzResearch.WordTrace]
  refine ⟨36046864123999980231337913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96124970997333280616901101 36046864123999980231337913)
  ·
    refine ⟨27035148092999985173503435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36046864123999980231337913 27035148092999985173503435)
    ·
      refine ⟨40552722139499977760255153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27035148092999985173503435 40552722139499977760255153)
      ·
        refine ⟨30414541604624983320191365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40552722139499977760255153 30414541604624983320191365)
        ·
          refine ⟨5702726550867184372535881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30414541604624983320191365 5702726550867184372535881)
          ·
            refine ⟨4277044913150388279401911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5702726550867184372535881 4277044913150388279401911)
            ·
              refine ⟨6415567369725582419102867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4277044913150388279401911 6415567369725582419102867)
              ·
                refine ⟨9623351054588373628654301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6415567369725582419102867 9623351054588373628654301)
                ·
                  refine ⟨3608756645470640110745363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9623351054588373628654301 3608756645470640110745363)
                  ·
                    refine ⟨5413134968205960166118045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3608756645470640110745363 5413134968205960166118045)
                    ·
                      refine ⟨2029925613077235062294267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5413134968205960166118045 2029925613077235062294267)
                      ·
                        rfl

theorem cell23_3953266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_3953266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953266 prefixEnd_3953266 := by exact prefixLift 3953266
  have htrace : WordTrace (prefixWord ++ tailWord_3953266) baseStart_3953266 baseEnd_3953266 := by
    simpa [prefixWord, tailWord_3953266, baseEnd_3953266] using wordTrace_append hprefix tailTrace_3953266
  have hstable : (prefixWord ++ tailWord_3953266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953266).length < 2 ^ (prefixWord ++ tailWord_3953266).sum := by decide
  have hdescent : baseEnd_3953266 < baseStart_3953266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953285 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 1, 1, 6]
def baseStart_3953285 : Nat := 118140960795 + 3953285 * 2 ^ 59
def prefixEnd_3953285 : Nat := 4983230072969 + 3 ^ 40 * 3953285 * 2
def baseEnd_3953285 : Nat := 2029935369209670487956679

theorem tailTrace_3953285 : CollatzResearch.WordTrace tailWord_3953285 prefixEnd_3953285 2029935369209670487956679 := by
  unfold tailWord_3953285
  simp only [CollatzResearch.WordTrace]
  refine ⟨144188149482931087170293309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96125432988620724780195539 144188149482931087170293309)
  ·
    refine ⟨54070556056099157688859991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144188149482931087170293309 54070556056099157688859991)
    ·
      refine ⟨81105834084148736533289987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54070556056099157688859991 81105834084148736533289987)
      ·
        refine ⟨121658751126223104799934981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81105834084148736533289987 121658751126223104799934981)
        ·
          refine ⟨22811015836166832149987809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121658751126223104799934981 22811015836166832149987809)
          ·
            refine ⟨17108261877125124112490857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22811015836166832149987809 17108261877125124112490857)
            ·
              refine ⟨12831196407843843084368143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17108261877125124112490857 12831196407843843084368143)
              ·
                refine ⟨19246794611765764626552215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12831196407843843084368143 19246794611765764626552215)
                ·
                  refine ⟨28870191917648646939828323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19246794611765764626552215 28870191917648646939828323)
                  ·
                    refine ⟨43305287876472970409742485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28870191917648646939828323 43305287876472970409742485)
                    ·
                      refine ⟨2029935369209670487956679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43305287876472970409742485 2029935369209670487956679)
                      ·
                        rfl

theorem cell23_3953285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_3953285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953285 prefixEnd_3953285 := by exact prefixLift 3953285
  have htrace : WordTrace (prefixWord ++ tailWord_3953285) baseStart_3953285 baseEnd_3953285 := by
    simpa [prefixWord, tailWord_3953285, baseEnd_3953285] using wordTrace_append hprefix tailTrace_3953285
  have hstable : (prefixWord ++ tailWord_3953285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953285).length < 2 ^ (prefixWord ++ tailWord_3953285).sum := by decide
  have hdescent : baseEnd_3953285 < baseStart_3953285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953292 : List Nat := [2, 2, 1, 2, 1, 1, 2, 6, 1, 2, 3]
def baseStart_3953292 : Nat := 118140960795 + 3953292 * 2 ^ 59
def prefixEnd_3953292 : Nat := 4983230072969 + 3 ^ 40 * 3953292 * 2
def baseEnd_3953292 : Nat := 2029938963574251960569147

theorem tailTrace_3953292 : CollatzResearch.WordTrace tailWord_3953292 prefixEnd_3953292 2029938963574251960569147 := by
  unfold tailWord_3953292
  simp only [CollatzResearch.WordTrace]
  refine ⟨72094202396952863682899065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96125603195937151577198753 72094202396952863682899065)
  ·
    refine ⟨54070651797714647762174299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72094202396952863682899065 54070651797714647762174299)
    ·
      refine ⟨81105977696571971643261449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54070651797714647762174299 81105977696571971643261449)
      ·
        refine ⟨60829483272428978732446087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81105977696571971643261449 60829483272428978732446087)
        ·
          refine ⟨91244224908643468098669131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60829483272428978732446087 91244224908643468098669131)
          ·
            refine ⟨136866337362965202148003697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91244224908643468098669131 136866337362965202148003697)
            ·
              refine ⟨102649753022223901611002773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136866337362965202148003697 102649753022223901611002773)
              ·
                refine ⟨4811707172916745388015755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102649753022223901611002773 4811707172916745388015755)
                ·
                  refine ⟨7217560759375118082023633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4811707172916745388015755 7217560759375118082023633)
                  ·
                    refine ⟨5413170569531338561517725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7217560759375118082023633 5413170569531338561517725)
                    ·
                      refine ⟨2029938963574251960569147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5413170569531338561517725 2029938963574251960569147)
                      ·
                        rfl

theorem cell23_3953292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_3953292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953292 prefixEnd_3953292 := by exact prefixLift 3953292
  have htrace : WordTrace (prefixWord ++ tailWord_3953292) baseStart_3953292 baseEnd_3953292 := by
    simpa [prefixWord, tailWord_3953292, baseEnd_3953292] using wordTrace_append hprefix tailTrace_3953292
  have hstable : (prefixWord ++ tailWord_3953292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953292).length < 2 ^ (prefixWord ++ tailWord_3953292).sum := by decide
  have hdescent : baseEnd_3953292 < baseStart_3953292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953329 : List Nat := [1, 2, 2, 6, 1, 2, 1, 8]
def baseStart_3953329 : Nat := 118140960795 + 3953329 * 2 ^ 59
def prefixEnd_3953329 : Nat := 4983230072969 + 3 ^ 40 * 3953329 * 2
def baseEnd_3953329 : Nat := 75183628235498826511351

theorem tailTrace_3953329 : CollatzResearch.WordTrace tailWord_3953329 prefixEnd_3953329 75183628235498826511351 := by
  unfold tailWord_3953329
  simp only [CollatzResearch.WordTrace]
  refine ⟨144189754294771682684895041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96126502863181121789930027 144189754294771682684895041)
  ·
    refine ⟨108142315721078762013671281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144189754294771682684895041 108142315721078762013671281)
    ·
      refine ⟨81106736790809071510253461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108142315721078762013671281 81106736790809071510253461)
      ·
        refine ⟨3801878287069175227043131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81106736790809071510253461 3801878287069175227043131)
        ·
          refine ⟨5702817430603762840564697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3801878287069175227043131 5702817430603762840564697)
          ·
            refine ⟨4277113072952822130423523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5702817430603762840564697 4277113072952822130423523)
            ·
              refine ⟨6415669609429233195635285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4277113072952822130423523 6415669609429233195635285)
              ·
                refine ⟨75183628235498826511351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6415669609429233195635285 75183628235498826511351)
                ·
                  rfl

theorem cell23_3953329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 8].length) (baseStart_3953329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953329 prefixEnd_3953329 := by exact prefixLift 3953329
  have htrace : WordTrace (prefixWord ++ tailWord_3953329) baseStart_3953329 baseEnd_3953329 := by
    simpa [prefixWord, tailWord_3953329, baseEnd_3953329] using wordTrace_append hprefix tailTrace_3953329
  have hstable : (prefixWord ++ tailWord_3953329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953329).length < 2 ^ (prefixWord ++ tailWord_3953329).sum := by decide
  have hdescent : baseEnd_3953329 < baseStart_3953329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953357 : List Nat := [1, 6, 2, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_3953357 : Nat := 118140960795 + 3953357 * 2 ^ 59
def prefixEnd_3953357 : Nat := 4983230072969 + 3 ^ 40 * 3953357 * 2
def baseEnd_3953357 : Nat := 2029972339816794206256349

theorem tailTrace_3953357 : CollatzResearch.WordTrace tailWord_3953357 prefixEnd_3953357 2029972339816794206256349 := by
  unfold tailWord_3953357
  simp only [CollatzResearch.WordTrace]
  refine ⟨144190775538670243466914325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96127183692446828977942883 144190775538670243466914325)
  ·
    refine ⟨6758942603375167662511609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 144190775538670243466914325 6758942603375167662511609)
    ·
      refine ⟨5069206952531375746883707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6758942603375167662511609 5069206952531375746883707)
      ·
        refine ⟨7603810428797063620325561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5069206952531375746883707 7603810428797063620325561)
        ·
          refine ⟨5702857821597797715244171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7603810428797063620325561 5702857821597797715244171)
          ·
            refine ⟨8554286732396696572866257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5702857821597797715244171 8554286732396696572866257)
            ·
              refine ⟨6415715049297522429649693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8554286732396696572866257 6415715049297522429649693)
              ·
                refine ⟨2405893143486570911118635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6415715049297522429649693 2405893143486570911118635)
                ·
                  refine ⟨3608839715229856366677953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2405893143486570911118635 3608839715229856366677953)
                  ·
                    refine ⟨2706629786422392275008465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3608839715229856366677953 2706629786422392275008465)
                    ·
                      refine ⟨2029972339816794206256349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2706629786422392275008465 2029972339816794206256349)
                      ·
                        rfl

theorem cell23_3953357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_3953357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953357 prefixEnd_3953357 := by exact prefixLift 3953357
  have htrace : WordTrace (prefixWord ++ tailWord_3953357) baseStart_3953357 baseEnd_3953357 := by
    simpa [prefixWord, tailWord_3953357, baseEnd_3953357] using wordTrace_append hprefix tailTrace_3953357
  have hstable : (prefixWord ++ tailWord_3953357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953357).length < 2 ^ (prefixWord ++ tailWord_3953357).sum := by decide
  have hdescent : baseEnd_3953357 < baseStart_3953357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953385 : List Nat := [1, 2, 1, 1, 1, 2, 5, 3, 7]
def baseStart_3953385 : Nat := 118140960795 + 3953385 * 2 ^ 59
def prefixEnd_3953385 : Nat := 4983230072969 + 3 ^ 40 * 3953385 * 2
def baseEnd_3953385 : Nat := 225554079697235566300691

theorem tailTrace_3953385 : CollatzResearch.WordTrace tailWord_3953385 prefixEnd_3953385 225554079697235566300691 := by
  unfold tailWord_3953385
  simp only [CollatzResearch.WordTrace]
  refine ⟨144191796782568804248933609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96127864521712536165955739 144191796782568804248933609)
  ·
    refine ⟨108143847586926603186700207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144191796782568804248933609 108143847586926603186700207)
    ·
      refine ⟨162215771380389904780050311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108143847586926603186700207 162215771380389904780050311)
      ·
        refine ⟨243323657070584857170075467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162215771380389904780050311 243323657070584857170075467)
        ·
          refine ⟨364985485605877285755113201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243323657070584857170075467 364985485605877285755113201)
          ·
            refine ⟨273739114204407964316334901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364985485605877285755113201 273739114204407964316334901)
            ·
              refine ⟨25663041956663246654656397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 273739114204407964316334901 25663041956663246654656397)
              ·
                refine ⟨9623640733748717495496149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25663041956663246654656397 9623640733748717495496149)
                ·
                  refine ⟨225554079697235566300691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9623640733748717495496149 225554079697235566300691)
                  ·
                    rfl

theorem cell23_3953385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 7].length) (baseStart_3953385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953385 prefixEnd_3953385 := by exact prefixLift 3953385
  have htrace : WordTrace (prefixWord ++ tailWord_3953385) baseStart_3953385 baseEnd_3953385 := by
    simpa [prefixWord, tailWord_3953385, baseEnd_3953385] using wordTrace_append hprefix tailTrace_3953385
  have hstable : (prefixWord ++ tailWord_3953385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953385).length < 2 ^ (prefixWord ++ tailWord_3953385).sum := by decide
  have hdescent : baseEnd_3953385 < baseStart_3953385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953436 : List Nat := [2, 2, 3, 1, 1, 4, 3, 2, 5]
def baseStart_3953436 : Nat := 118140960795 + 3953436 * 2 ^ 59
def prefixEnd_3953436 : Nat := 4983230072969 + 3 ^ 40 * 3953436 * 2
def baseEnd_3953436 : Nat := 225556989420944377463165

theorem tailTrace_3953436 : CollatzResearch.WordTrace tailWord_3953436 prefixEnd_3953436 225556989420944377463165 := by
  unfold tailWord_3953436
  simp only [CollatzResearch.WordTrace]
  refine ⟨72096828452692019979520081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96129104603589359972693441 72096828452692019979520081)
  ·
    refine ⟨54072621339519014984640061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72096828452692019979520081 54072621339519014984640061)
    ·
      refine ⟨20277233002319630619240023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54072621339519014984640061 20277233002319630619240023)
      ·
        refine ⟨30415849503479445928860035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20277233002319630619240023 30415849503479445928860035)
        ·
          refine ⟨45623774255219168893290053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30415849503479445928860035 45623774255219168893290053)
          ·
            refine ⟨8554457672853594167491885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45623774255219168893290053 8554457672853594167491885)
            ·
              refine ⟨3207921627320097812809457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8554457672853594167491885 3207921627320097812809457)
              ·
                refine ⟨2405941220490073359607093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3207921627320097812809457 2405941220490073359607093)
                ·
                  refine ⟨225556989420944377463165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2405941220490073359607093 225556989420944377463165)
                  ·
                    rfl

theorem cell23_3953436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 5].length) (baseStart_3953436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953436 prefixEnd_3953436 := by exact prefixLift 3953436
  have htrace : WordTrace (prefixWord ++ tailWord_3953436) baseStart_3953436 baseEnd_3953436 := by
    simpa [prefixWord, tailWord_3953436, baseEnd_3953436] using wordTrace_append hprefix tailTrace_3953436
  have hstable : (prefixWord ++ tailWord_3953436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953436).length < 2 ^ (prefixWord ++ tailWord_3953436).sum := by decide
  have hdescent : baseEnd_3953436 < baseStart_3953436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953442 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_3953442 : Nat := 118140960795 + 3953442 * 2 ^ 59
def prefixEnd_3953442 : Nat := 4983230072969 + 3 ^ 40 * 3953442 * 2
def baseEnd_3953442 : Nat := 2030015985672426373693457

theorem tailTrace_3953442 : CollatzResearch.WordTrace tailWord_3953442 prefixEnd_3953442 2030015985672426373693457 := by
  unfold tailWord_3953442
  simp only [CollatzResearch.WordTrace]
  refine ⟨36048468935840575745939645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96129250495574868655839053 36048468935840575745939645)
  ·
    refine ⟨13518175850940215904727367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36048468935840575745939645 13518175850940215904727367)
    ·
      refine ⟨20277263776410323857091051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13518175850940215904727367 20277263776410323857091051)
      ·
        refine ⟨30415895664615485785636577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20277263776410323857091051 30415895664615485785636577)
        ·
          refine ⟨22811921748461614339227433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30415895664615485785636577 22811921748461614339227433)
          ·
            refine ⟨17108941311346210754420575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22811921748461614339227433 17108941311346210754420575)
            ·
              refine ⟨25663411967019316131630863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17108941311346210754420575 25663411967019316131630863)
              ·
                refine ⟨38495117950528974197446295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25663411967019316131630863 38495117950528974197446295)
                ·
                  refine ⟨57742676925793461296169443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38495117950528974197446295 57742676925793461296169443)
                  ·
                    refine ⟨86614015388690191944254165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57742676925793461296169443 86614015388690191944254165)
                    ·
                      refine ⟨2030015985672426373693457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86614015388690191944254165 2030015985672426373693457)
                      ·
                        rfl

theorem cell23_3953442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_3953442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953442 prefixEnd_3953442 := by exact prefixLift 3953442
  have htrace : WordTrace (prefixWord ++ tailWord_3953442) baseStart_3953442 baseEnd_3953442 := by
    simpa [prefixWord, tailWord_3953442, baseEnd_3953442] using wordTrace_append hprefix tailTrace_3953442
  have hstable : (prefixWord ++ tailWord_3953442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953442).length < 2 ^ (prefixWord ++ tailWord_3953442).sum := by decide
  have hdescent : baseEnd_3953442 < baseStart_3953442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953452 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 4]
def baseStart_3953452 : Nat := 118140960795 + 3953452 * 2 ^ 59
def prefixEnd_3953452 : Nat := 4983230072969 + 3 ^ 40 * 3953452 * 2
def baseEnd_3953452 : Nat := 2030021120478971334568411

theorem tailTrace_3953452 : CollatzResearch.WordTrace tailWord_3953452 prefixEnd_3953452 2030021120478971334568411 := by
  unfold tailWord_3953452
  simp only [CollatzResearch.WordTrace]
  refine ⟨72097120236663037345811305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96129493648884049794415073 72097120236663037345811305)
  ·
    refine ⟨54072840177497278009358479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72097120236663037345811305 54072840177497278009358479)
    ·
      refine ⟨81109260266245917014037719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54072840177497278009358479 81109260266245917014037719)
      ·
        refine ⟨121663890399368875521056579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81109260266245917014037719 121663890399368875521056579)
        ·
          refine ⟨182495835599053313281584869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121663890399368875521056579 182495835599053313281584869)
          ·
            refine ⟨34217969174822496240297163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182495835599053313281584869 34217969174822496240297163)
            ·
              refine ⟨51326953762233744360445745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34217969174822496240297163 51326953762233744360445745)
              ·
                refine ⟨38495215321675308270334309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51326953762233744360445745 38495215321675308270334309)
                ·
                  refine ⟨7217852872814120300687683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38495215321675308270334309 7217852872814120300687683)
                  ·
                    refine ⟨10826779309221180451031525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7217852872814120300687683 10826779309221180451031525)
                    ·
                      refine ⟨2030021120478971334568411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10826779309221180451031525 2030021120478971334568411)
                      ·
                        rfl

theorem cell23_3953452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_3953452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953452 prefixEnd_3953452 := by exact prefixLift 3953452
  have htrace : WordTrace (prefixWord ++ tailWord_3953452) baseStart_3953452 baseEnd_3953452 := by
    simpa [prefixWord, tailWord_3953452, baseEnd_3953452] using wordTrace_append hprefix tailTrace_3953452
  have hstable : (prefixWord ++ tailWord_3953452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953452).length < 2 ^ (prefixWord ++ tailWord_3953452).sum := by decide
  have hdescent : baseEnd_3953452 < baseStart_3953452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953472 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 3]
def baseStart_3953472 : Nat := 118140960795 + 3953472 * 2 ^ 59
def prefixEnd_3953472 : Nat := 4983230072969 + 3 ^ 40 * 3953472 * 2
def baseEnd_3953472 : Nat := 2030031390092061256318319

theorem tailTrace_3953472 : CollatzResearch.WordTrace tailWord_3953472 prefixEnd_3953472 2030031390092061256318319 := by
  unfold tailWord_3953472
  simp only [CollatzResearch.WordTrace]
  refine ⟨72097484966626809053675335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96129979955502412071567113 72097484966626809053675335)
  ·
    refine ⟨108146227449940213580513003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72097484966626809053675335 108146227449940213580513003)
    ·
      refine ⟨162219341174910320370769505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108146227449940213580513003 162219341174910320370769505)
      ·
        refine ⟨121664505881182740278077129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162219341174910320370769505 121664505881182740278077129)
        ·
          refine ⟨91248379410887055208557847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121664505881182740278077129 91248379410887055208557847)
          ·
            refine ⟨136872569116330582812836771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91248379410887055208557847 136872569116330582812836771)
            ·
              refine ⟨205308853674495874219255157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136872569116330582812836771 205308853674495874219255157)
              ·
                refine ⟨19247705031983988208055171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205308853674495874219255157 19247705031983988208055171)
                ·
                  refine ⟨28871557547975982312082757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19247705031983988208055171 28871557547975982312082757)
                  ·
                    refine ⟨5413417040245496683515517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28871557547975982312082757 5413417040245496683515517)
                    ·
                      refine ⟨2030031390092061256318319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5413417040245496683515517 2030031390092061256318319)
                      ·
                        rfl

theorem cell23_3953472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_3953472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953472 prefixEnd_3953472 := by exact prefixLift 3953472
  have htrace : WordTrace (prefixWord ++ tailWord_3953472) baseStart_3953472 baseEnd_3953472 := by
    simpa [prefixWord, tailWord_3953472, baseEnd_3953472] using wordTrace_append hprefix tailTrace_3953472
  have hstable : (prefixWord ++ tailWord_3953472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953472).length < 2 ^ (prefixWord ++ tailWord_3953472).sum := by decide
  have hdescent : baseEnd_3953472 < baseStart_3953472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953539 : List Nat := [1, 1, 1, 3, 4, 1, 3, 3, 1, 5]
def baseStart_3953539 : Nat := 118140960795 + 3953539 * 2 ^ 59
def prefixEnd_3953539 : Nat := 4983230072969 + 3 ^ 40 * 3953539 * 2
def baseEnd_3953539 : Nat := 676688597765304164726837

theorem tailTrace_3953539 : CollatzResearch.WordTrace tailWord_3953539 prefixEnd_3953539 676688597765304164726837 := by
  unfold tailWord_3953539
  simp only [CollatzResearch.WordTrace]
  refine ⟨144197413624010888550039671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96131609082673925700026447 144197413624010888550039671)
  ·
    refine ⟨216296120436016332825059507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144197413624010888550039671 216296120436016332825059507)
    ·
      refine ⟨324444180654024499237589261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216296120436016332825059507 324444180654024499237589261)
      ·
        refine ⟨121666567745259187214095973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324444180654024499237589261 121666567745259187214095973)
        ·
          refine ⟨22812481452236097602642995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121666567745259187214095973 22812481452236097602642995)
          ·
            refine ⟨34218722178354146403964493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22812481452236097602642995 34218722178354146403964493)
            ·
              refine ⟨12832020816882804901486685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34218722178354146403964493 12832020816882804901486685)
              ·
                refine ⟨4812007806331051838057507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12832020816882804901486685 4812007806331051838057507)
                ·
                  refine ⟨7218011709496577757086261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4812007806331051838057507 7218011709496577757086261)
                  ·
                    refine ⟨676688597765304164726837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7218011709496577757086261 676688597765304164726837)
                    ·
                      rfl

theorem cell23_3953539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 5].length) (baseStart_3953539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953539 prefixEnd_3953539 := by exact prefixLift 3953539
  have htrace : WordTrace (prefixWord ++ tailWord_3953539) baseStart_3953539 baseEnd_3953539 := by
    simpa [prefixWord, tailWord_3953539, baseEnd_3953539] using wordTrace_append hprefix tailTrace_3953539
  have hstable : (prefixWord ++ tailWord_3953539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953539).length < 2 ^ (prefixWord ++ tailWord_3953539).sum := by decide
  have hdescent : baseEnd_3953539 < baseStart_3953539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953589 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_3953589 : Nat := 118140960795 + 3953589 * 2 ^ 59
def prefixEnd_3953589 : Nat := 4983230072969 + 3 ^ 40 * 3953589 * 2
def baseEnd_3953589 : Nat := 2030091467328637298555281

theorem tailTrace_3953589 : CollatzResearch.WordTrace tailWord_3953589 prefixEnd_3953589 2030091467328637298555281 := by
  unfold tailWord_3953589
  simp only [CollatzResearch.WordTrace]
  refine ⟨144199237273829747089359821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96132824849219831392906547 144199237273829747089359821)
  ·
    refine ⟨54074713977686155158509933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144199237273829747089359821 54074713977686155158509933)
    ·
      refine ⟨20278017741632308184441225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54074713977686155158509933 20278017741632308184441225)
      ·
        refine ⟨15208513306224231138330919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20278017741632308184441225 15208513306224231138330919)
        ·
          refine ⟨22812769959336346707496379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15208513306224231138330919 22812769959336346707496379)
          ·
            refine ⟨34219154939004520061244569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22812769959336346707496379 34219154939004520061244569)
            ·
              refine ⟨25664366204253390045933427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34219154939004520061244569 25664366204253390045933427)
              ·
                refine ⟨38496549306380085068900141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25664366204253390045933427 38496549306380085068900141)
                ·
                  refine ⟨14436205989892531900837553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38496549306380085068900141 14436205989892531900837553)
                  ·
                    refine ⟨10827154492419398925628165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14436205989892531900837553 10827154492419398925628165)
                    ·
                      refine ⟨2030091467328637298555281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10827154492419398925628165 2030091467328637298555281)
                      ·
                        rfl

theorem cell23_3953589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_3953589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953589 prefixEnd_3953589 := by exact prefixLift 3953589
  have htrace : WordTrace (prefixWord ++ tailWord_3953589) baseStart_3953589 baseEnd_3953589 := by
    simpa [prefixWord, tailWord_3953589, baseEnd_3953589] using wordTrace_append hprefix tailTrace_3953589
  have hstable : (prefixWord ++ tailWord_3953589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953589).length < 2 ^ (prefixWord ++ tailWord_3953589).sum := by decide
  have hdescent : baseEnd_3953589 < baseStart_3953589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953604 : List Nat := [2, 3, 3, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_3953604 : Nat := 118140960795 + 3953604 * 2 ^ 59
def prefixEnd_3953604 : Nat := 4983230072969 + 3 ^ 40 * 3953604 * 2
def baseEnd_3953604 : Nat := 2030099169538454739867713

theorem tailTrace_3953604 : CollatzResearch.WordTrace tailWord_3953604 prefixEnd_3953604 2030099169538454739867713 := by
  unfold tailWord_3953604
  simp only [CollatzResearch.WordTrace]
  refine ⟨72099892184387702325577933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96133189579183603100770577 72099892184387702325577933)
  ·
    refine ⟨27037459569145388372091725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72099892184387702325577933 27037459569145388372091725)
    ·
      refine ⟨10139047338429520639534397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27037459569145388372091725 10139047338429520639534397)
      ·
        refine ⟨3802142751911070239825399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10139047338429520639534397 3802142751911070239825399)
        ·
          refine ⟨5703214127866605359738099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3802142751911070239825399 5703214127866605359738099)
          ·
            refine ⟨8554821191799908039607149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5703214127866605359738099 8554821191799908039607149)
            ·
              refine ⟨3208057946924965514852681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8554821191799908039607149 3208057946924965514852681)
              ·
                refine ⟨2406043460193724136139511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3208057946924965514852681 2406043460193724136139511)
                ·
                  refine ⟨3609065190290586204209267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2406043460193724136139511 3609065190290586204209267)
                  ·
                    refine ⟨5413597785435879306313901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3609065190290586204209267 5413597785435879306313901)
                    ·
                      refine ⟨2030099169538454739867713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5413597785435879306313901 2030099169538454739867713)
                      ·
                        rfl

theorem cell23_3953604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_3953604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953604 prefixEnd_3953604 := by exact prefixLift 3953604
  have htrace : WordTrace (prefixWord ++ tailWord_3953604) baseStart_3953604 baseEnd_3953604 := by
    simpa [prefixWord, tailWord_3953604, baseEnd_3953604] using wordTrace_append hprefix tailTrace_3953604
  have hstable : (prefixWord ++ tailWord_3953604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953604).length < 2 ^ (prefixWord ++ tailWord_3953604).sum := by decide
  have hdescent : baseEnd_3953604 < baseStart_3953604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953620 : List Nat := [2, 4, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_3953620 : Nat := 118140960795 + 3953620 * 2 ^ 59
def prefixEnd_3953620 : Nat := 4983230072969 + 3 ^ 40 * 3953620 * 2
def baseEnd_3953620 : Nat := 676702461742975559089213

theorem tailTrace_3953620 : CollatzResearch.WordTrace tailWord_3953620 prefixEnd_3953620 676702461742975559089213 := by
  unfold tailWord_3953620
  simp only [CollatzResearch.WordTrace]
  refine ⟨72100183968358719691869157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96133578624478292922492209 72100183968358719691869157)
  ·
    refine ⟨13518784494067259942225467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72100183968358719691869157 13518784494067259942225467)
    ·
      refine ⟨20278176741100889913338201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13518784494067259942225467 20278176741100889913338201)
      ·
        refine ⟨15208632555825667435003651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20278176741100889913338201 15208632555825667435003651)
        ·
          refine ⟨22812948833738501152505477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15208632555825667435003651 22812948833738501152505477)
          ·
            refine ⟨4277427906325968966094777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22812948833738501152505477 4277427906325968966094777)
            ·
              refine ⟨3208070929744476724571083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4277427906325968966094777 3208070929744476724571083)
              ·
                refine ⟨4812106394616715086856625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3208070929744476724571083 4812106394616715086856625)
                ·
                  refine ⟨3609079795962536315142469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4812106394616715086856625 3609079795962536315142469)
                  ·
                    refine ⟨676702461742975559089213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3609079795962536315142469 676702461742975559089213)
                    ·
                      rfl

theorem cell23_3953620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_3953620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953620 prefixEnd_3953620 := by exact prefixLift 3953620
  have htrace : WordTrace (prefixWord ++ tailWord_3953620) baseStart_3953620 baseEnd_3953620 := by
    simpa [prefixWord, tailWord_3953620, baseEnd_3953620] using wordTrace_append hprefix tailTrace_3953620
  have hstable : (prefixWord ++ tailWord_3953620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953620).length < 2 ^ (prefixWord ++ tailWord_3953620).sum := by decide
  have hdescent : baseEnd_3953620 < baseStart_3953620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953632 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 10]
def baseStart_3953632 : Nat := 118140960795 + 3953632 * 2 ^ 59
def prefixEnd_3953632 : Nat := 4983230072969 + 3 ^ 40 * 3953632 * 2
def baseEnd_3953632 : Nat := 2030113546996780630317583

theorem tailTrace_3953632 : CollatzResearch.WordTrace tailWord_3953632 prefixEnd_3953632 2030113546996780630317583 := by
  unfold tailWord_3953632
  simp only [CollatzResearch.WordTrace]
  refine ⟨72100402806336982716587575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96133870408449310288783433 72100402806336982716587575)
  ·
    refine ⟨108150604209505474074881363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72100402806336982716587575 108150604209505474074881363)
    ·
      refine ⟨162225906314258211112322045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108150604209505474074881363 162225906314258211112322045)
      ·
        refine ⟨60834714867846829167120767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162225906314258211112322045 60834714867846829167120767)
        ·
          refine ⟨91252072301770243750681151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60834714867846829167120767 91252072301770243750681151)
          ·
            refine ⟨136878108452655365626021727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91252072301770243750681151 136878108452655365626021727)
            ·
              refine ⟨205317162678983048439032591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136878108452655365626021727 205317162678983048439032591)
              ·
                refine ⟨307975744018474572658548887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205317162678983048439032591 307975744018474572658548887)
                ·
                  refine ⟨461963616027711858987823331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307975744018474572658548887 461963616027711858987823331)
                  ·
                    refine ⟨692945424041567788481734997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 461963616027711858987823331 692945424041567788481734997)
                    ·
                      refine ⟨2030113546996780630317583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 692945424041567788481734997 2030113546996780630317583)
                      ·
                        rfl

theorem cell23_3953632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_3953632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953632 prefixEnd_3953632 := by exact prefixLift 3953632
  have htrace : WordTrace (prefixWord ++ tailWord_3953632) baseStart_3953632 baseEnd_3953632 := by
    simpa [prefixWord, tailWord_3953632, baseEnd_3953632] using wordTrace_append hprefix tailTrace_3953632
  have hstable : (prefixWord ++ tailWord_3953632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953632).length < 2 ^ (prefixWord ++ tailWord_3953632).sum := by decide
  have hdescent : baseEnd_3953632 < baseStart_3953632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953669 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 1, 6, 3]
def baseStart_3953669 : Nat := 118140960795 + 3953669 * 2 ^ 59
def prefixEnd_3953669 : Nat := 4983230072969 + 3 ^ 40 * 3953669 * 2
def baseEnd_3953669 : Nat := 2030132545780996985554913

theorem tailTrace_3953669 : CollatzResearch.WordTrace tailWord_3953669 prefixEnd_3953669 2030132545780996985554913 := by
  unfold tailWord_3953669
  simp only [CollatzResearch.WordTrace]
  refine ⟨144202155113539920752272061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96134770075693280501514707 144202155113539920752272061)
  ·
    refine ⟨54075808167577470282102023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144202155113539920752272061 54075808167577470282102023)
    ·
      refine ⟨81113712251366205423153035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54075808167577470282102023 81113712251366205423153035)
      ·
        refine ⟨121670568377049308134729553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81113712251366205423153035 121670568377049308134729553)
        ·
          refine ⟨91252926282786981101047165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121670568377049308134729553 91252926282786981101047165)
          ·
            refine ⟨34219847356045117912892687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91252926282786981101047165 34219847356045117912892687)
            ·
              refine ⟨51329771034067676869339031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34219847356045117912892687 51329771034067676869339031)
              ·
                refine ⟨76994656551101515304008547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51329771034067676869339031 76994656551101515304008547)
                ·
                  refine ⟨115491984826652272956012821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76994656551101515304008547 115491984826652272956012821)
                  ·
                    refine ⟨5413686788749325294813101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115491984826652272956012821 5413686788749325294813101)
                    ·
                      refine ⟨2030132545780996985554913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5413686788749325294813101 2030132545780996985554913)
                      ·
                        rfl

theorem cell23_3953669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_3953669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953669 prefixEnd_3953669 := by exact prefixLift 3953669
  have htrace : WordTrace (prefixWord ++ tailWord_3953669) baseStart_3953669 baseEnd_3953669 := by
    simpa [prefixWord, tailWord_3953669, baseEnd_3953669] using wordTrace_append hprefix tailTrace_3953669
  have hstable : (prefixWord ++ tailWord_3953669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953669).length < 2 ^ (prefixWord ++ tailWord_3953669).sum := by decide
  have hdescent : baseEnd_3953669 < baseStart_3953669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953719 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 4, 5]
def baseStart_3953719 : Nat := 118140960795 + 3953719 * 2 ^ 59
def prefixEnd_3953719 : Nat := 4983230072969 + 3 ^ 40 * 3953719 * 2
def baseEnd_3953719 : Nat := 676719406604573929976561

theorem tailTrace_3953719 : CollatzResearch.WordTrace tailWord_3953719 prefixEnd_3953719 676719406604573929976561 := by
  unfold tailWord_3953719
  simp only [CollatzResearch.WordTrace]
  refine ⟨144203978763358779291592211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96135985842239186194394807 144203978763358779291592211)
  ·
    refine ⟨216305968145038168937388317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144203978763358779291592211 216305968145038168937388317)
    ·
      refine ⟨81114738054389313351520619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216305968145038168937388317 81114738054389313351520619)
      ·
        refine ⟨121672107081583970027280929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81114738054389313351520619 121672107081583970027280929)
        ·
          refine ⟨91254080311187977520460697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121672107081583970027280929 91254080311187977520460697)
          ·
            refine ⟨68440560233390983140345523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91254080311187977520460697 68440560233390983140345523)
            ·
              refine ⟨102660840350086474710518285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68440560233390983140345523 102660840350086474710518285)
              ·
                refine ⟨38497815131282428016444357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102660840350086474710518285 38497815131282428016444357)
                ·
                  refine ⟨7218340337115455253083317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38497815131282428016444357 7218340337115455253083317)
                  ·
                    refine ⟨676719406604573929976561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7218340337115455253083317 676719406604573929976561)
                    ·
                      rfl

theorem cell23_3953719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_3953719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953719 prefixEnd_3953719 := by exact prefixLift 3953719
  have htrace : WordTrace (prefixWord ++ tailWord_3953719) baseStart_3953719 baseEnd_3953719 := by
    simpa [prefixWord, tailWord_3953719, baseEnd_3953719] using wordTrace_append hprefix tailTrace_3953719
  have hstable : (prefixWord ++ tailWord_3953719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953719).length < 2 ^ (prefixWord ++ tailWord_3953719).sum := by decide
  have hdescent : baseEnd_3953719 < baseStart_3953719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953749 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 2, 8]
def baseStart_3953749 : Nat := 118140960795 + 3953749 * 2 ^ 59
def prefixEnd_3953749 : Nat := 4983230072969 + 3 ^ 40 * 3953749 * 2
def baseEnd_3953749 : Nat := 676724541411118890851515

theorem tailTrace_3953749 : CollatzResearch.WordTrace tailWord_3953749 prefixEnd_3953749 676724541411118890851515 := by
  unfold tailWord_3953749
  simp only [CollatzResearch.WordTrace]
  refine ⟨144205072953250094415184301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96136715302166729610122867 144205072953250094415184301)
  ·
    refine ⟨54076902357468785405694113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144205072953250094415184301 54076902357468785405694113)
    ·
      refine ⟨40557676768101589054270585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54076902357468785405694113 40557676768101589054270585)
      ·
        refine ⟨30418257576076191790702939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40557676768101589054270585 30418257576076191790702939)
        ·
          refine ⟨45627386364114287686054409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30418257576076191790702939 45627386364114287686054409)
          ·
            refine ⟨34220539773085715764540807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45627386364114287686054409 34220539773085715764540807)
            ·
              refine ⟨51330809659628573646811211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34220539773085715764540807 51330809659628573646811211)
              ·
                refine ⟨76996214489442860470216817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51330809659628573646811211 76996214489442860470216817)
                ·
                  refine ⟨57747160867082145352662613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76996214489442860470216817 57747160867082145352662613)
                  ·
                    refine ⟨676724541411118890851515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57747160867082145352662613 676724541411118890851515)
                    ·
                      rfl

theorem cell23_3953749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_3953749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953749 prefixEnd_3953749 := by exact prefixLift 3953749
  have htrace : WordTrace (prefixWord ++ tailWord_3953749) baseStart_3953749 baseEnd_3953749 := by
    simpa [prefixWord, tailWord_3953749, baseEnd_3953749] using wordTrace_append hprefix tailTrace_3953749
  have hstable : (prefixWord ++ tailWord_3953749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953749).length < 2 ^ (prefixWord ++ tailWord_3953749).sum := by decide
  have hdescent : baseEnd_3953749 < baseStart_3953749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953756 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3953756 : Nat := 118140960795 + 3953756 * 2 ^ 59
def prefixEnd_3953756 : Nat := 4983230072969 + 3 ^ 40 * 3953756 * 2
def baseEnd_3953756 : Nat := 2030177218597938145167013

theorem tailTrace_3953756 : CollatzResearch.WordTrace tailWord_3953756 prefixEnd_3953756 2030177218597938145167013 := by
  unfold tailWord_3953756
  simp only [CollatzResearch.WordTrace]
  refine ⟨72102664132112367305344561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96136885509483156407126081 72102664132112367305344561)
  ·
    refine ⟨54076998099084275479008421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72102664132112367305344561 54076998099084275479008421)
    ·
      refine ⟨10139437143578301652314079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54076998099084275479008421 10139437143578301652314079)
      ·
        refine ⟨15209155715367452478471119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10139437143578301652314079 15209155715367452478471119)
        ·
          refine ⟨22813733573051178717706679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15209155715367452478471119 22813733573051178717706679)
          ·
            refine ⟨34220600359576768076560019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22813733573051178717706679 34220600359576768076560019)
            ·
              refine ⟨51330900539365152114840029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34220600359576768076560019 51330900539365152114840029)
              ·
                refine ⟨19249087702261932043065011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51330900539365152114840029 19249087702261932043065011)
                ·
                  refine ⟨28873631553392898064597517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19249087702261932043065011 28873631553392898064597517)
                  ·
                    refine ⟨10827611832522336774224069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28873631553392898064597517 10827611832522336774224069)
                    ·
                      refine ⟨2030177218597938145167013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10827611832522336774224069 2030177218597938145167013)
                      ·
                        rfl

theorem cell23_3953756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3953756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953756 prefixEnd_3953756 := by exact prefixLift 3953756
  have htrace : WordTrace (prefixWord ++ tailWord_3953756) baseStart_3953756 baseEnd_3953756 := by
    simpa [prefixWord, tailWord_3953756, baseEnd_3953756] using wordTrace_append hprefix tailTrace_3953756
  have hstable : (prefixWord ++ tailWord_3953756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953756).length < 2 ^ (prefixWord ++ tailWord_3953756).sum := by decide
  have hdescent : baseEnd_3953756 < baseStart_3953756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953757 : List Nat := [1, 4, 4, 1, 2, 2, 1, 3, 5]
def baseStart_3953757 : Nat := 118140960795 + 3953757 * 2 ^ 59
def prefixEnd_3953757 : Nat := 4983230072969 + 3 ^ 40 * 3953757 * 2
def baseEnd_3953757 : Nat := 225575303564288071250501

theorem tailTrace_3953757 : CollatzResearch.WordTrace tailWord_3953757 prefixEnd_3953757 225575303564288071250501 := by
  unfold tailWord_3953757
  simp only [CollatzResearch.WordTrace]
  refine ⟨144205364737221111781475525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96136909824814074520983683 144205364737221111781475525)
  ·
    refine ⟨27038505888228958459026661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144205364737221111781475525 27038505888228958459026661)
    ·
      refine ⟨5069719854042929711067499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27038505888228958459026661 5069719854042929711067499)
      ·
        refine ⟨7604579781064394566601249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5069719854042929711067499 7604579781064394566601249)
        ·
          refine ⟨5703434835798295924950937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7604579781064394566601249 5703434835798295924950937)
          ·
            refine ⟨4277576126848721943713203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5703434835798295924950937 4277576126848721943713203)
            ·
              refine ⟨6416364190273082915569805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4277576126848721943713203 6416364190273082915569805)
              ·
                refine ⟨2406136571352406093338677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6416364190273082915569805 2406136571352406093338677)
                ·
                  refine ⟨225575303564288071250501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2406136571352406093338677 225575303564288071250501)
                  ·
                    rfl

theorem cell23_3953757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_3953757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953757 prefixEnd_3953757 := by exact prefixLift 3953757
  have htrace : WordTrace (prefixWord ++ tailWord_3953757) baseStart_3953757 baseEnd_3953757 := by
    simpa [prefixWord, tailWord_3953757, baseEnd_3953757] using wordTrace_append hprefix tailTrace_3953757
  have hstable : (prefixWord ++ tailWord_3953757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953757).length < 2 ^ (prefixWord ++ tailWord_3953757).sum := by decide
  have hdescent : baseEnd_3953757 < baseStart_3953757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953773 : List Nat := [1, 5, 1, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_3953773 : Nat := 118140960795 + 3953773 * 2 ^ 59
def prefixEnd_3953773 : Nat := 4983230072969 + 3 ^ 40 * 3953773 * 2
def baseEnd_3953773 : Nat := 2030185947769064578654435

theorem tailTrace_3953773 : CollatzResearch.WordTrace tailWord_3953773 prefixEnd_3953773 2030185947769064578654435 := by
  unfold tailWord_3953773
  simp only [CollatzResearch.WordTrace]
  refine ⟨144205948305163146514057973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96137298870108764342705315 144205948305163146514057973)
  ·
    refine ⟨13519307653609044985692935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144205948305163146514057973 13519307653609044985692935)
    ·
      refine ⟨20278961480413567478539403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13519307653609044985692935 20278961480413567478539403)
      ·
        refine ⟨30418442220620351217809105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20278961480413567478539403 30418442220620351217809105)
        ·
          refine ⟨22813831665465263413356829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30418442220620351217809105 22813831665465263413356829)
          ·
            refine ⟨8555186874549473780008811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22813831665465263413356829 8555186874549473780008811)
            ·
              refine ⟨12832780311824210670013217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8555186874549473780008811 12832780311824210670013217)
              ·
                refine ⟨9624585233868158002509913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12832780311824210670013217 9624585233868158002509913)
                ·
                  refine ⟨7218438925401118501882435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9624585233868158002509913 7218438925401118501882435)
                  ·
                    refine ⟨10827658388101677752823653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7218438925401118501882435 10827658388101677752823653)
                    ·
                      refine ⟨2030185947769064578654435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10827658388101677752823653 2030185947769064578654435)
                      ·
                        rfl

theorem cell23_3953773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_3953773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953773 prefixEnd_3953773 := by exact prefixLift 3953773
  have htrace : WordTrace (prefixWord ++ tailWord_3953773) baseStart_3953773 baseEnd_3953773 := by
    simpa [prefixWord, tailWord_3953773, baseEnd_3953773] using wordTrace_append hprefix tailTrace_3953773
  have hstable : (prefixWord ++ tailWord_3953773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953773).length < 2 ^ (prefixWord ++ tailWord_3953773).sum := by decide
  have hdescent : baseEnd_3953773 < baseStart_3953773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953810 : List Nat := [3, 2, 3, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_3953810 : Nat := 118140960795 + 3953810 * 2 ^ 59
def prefixEnd_3953810 : Nat := 4983230072969 + 3 ^ 40 * 3953810 * 2
def baseEnd_3953810 : Nat := 2030204946553280933891765

theorem tailTrace_3953810 : CollatzResearch.WordTrace tailWord_3953810 prefixEnd_3953810 2030204946553280933891765 := by
  unfold tailWord_3953810
  simp only [CollatzResearch.WordTrace]
  refine ⟨36051824451507275458288721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96138198537352734555436589 36051824451507275458288721)
  ·
    refine ⟨27038868338630456593716541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36051824451507275458288721 27038868338630456593716541)
    ·
      refine ⟨10139575626986421222643703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27038868338630456593716541 10139575626986421222643703)
      ·
        refine ⟨15209363440479631833965555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10139575626986421222643703 15209363440479631833965555)
        ·
          refine ⟨22814045160719447750948333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15209363440479631833965555 22814045160719447750948333)
          ·
            refine ⟨8555266935269792906605625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22814045160719447750948333 8555266935269792906605625)
            ·
              refine ⟨6416450201452344679954219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8555266935269792906605625 6416450201452344679954219)
              ·
                refine ⟨9624675302178517019931329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6416450201452344679954219 9624675302178517019931329)
                ·
                  refine ⟨7218506476633887764948497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9624675302178517019931329 7218506476633887764948497)
                  ·
                    refine ⟨5413879857475415823711373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7218506476633887764948497 5413879857475415823711373)
                    ·
                      refine ⟨2030204946553280933891765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5413879857475415823711373 2030204946553280933891765)
                      ·
                        rfl

theorem cell23_3953810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_3953810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953810 prefixEnd_3953810 := by exact prefixLift 3953810
  have htrace : WordTrace (prefixWord ++ tailWord_3953810) baseStart_3953810 baseEnd_3953810 := by
    simpa [prefixWord, tailWord_3953810, baseEnd_3953810] using wordTrace_append hprefix tailTrace_3953810
  have hstable : (prefixWord ++ tailWord_3953810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953810).length < 2 ^ (prefixWord ++ tailWord_3953810).sum := by decide
  have hdescent : baseEnd_3953810 < baseStart_3953810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953819 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 5]
def baseStart_3953819 : Nat := 118140960795 + 3953819 * 2 ^ 59
def prefixEnd_3953819 : Nat := 4983230072969 + 3 ^ 40 * 3953819 * 2
def baseEnd_3953819 : Nat := 2030209567879171398679223

theorem tailTrace_3953819 : CollatzResearch.WordTrace tailWord_3953819 prefixEnd_3953819 2030209567879171398679223 := by
  unfold tailWord_3953819
  simp only [CollatzResearch.WordTrace]
  refine ⟨144207626062996496370232511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96138417375330997580155007 144207626062996496370232511)
  ·
    refine ⟨216311439094494744555348767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144207626062996496370232511 216311439094494744555348767)
    ·
      refine ⟨324467158641742116833023151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216311439094494744555348767 324467158641742116833023151)
      ·
        refine ⟨486700737962613175249534727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324467158641742116833023151 486700737962613175249534727)
        ·
          refine ⟨730051106943919762874302091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486700737962613175249534727 730051106943919762874302091)
          ·
            refine ⟨1095076660415879644311453137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730051106943919762874302091 1095076660415879644311453137)
            ·
              refine ⟨821307495311909733233589853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1095076660415879644311453137 821307495311909733233589853)
              ·
                refine ⟨307990310741966149962596195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 821307495311909733233589853 307990310741966149962596195)
                ·
                  refine ⟨461985466112949224943894293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307990310741966149962596195 461985466112949224943894293)
                  ·
                    refine ⟨21655568724044494919245045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 461985466112949224943894293 21655568724044494919245045)
                    ·
                      refine ⟨2030209567879171398679223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21655568724044494919245045 2030209567879171398679223)
                      ·
                        rfl

theorem cell23_3953819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 5].length) (baseStart_3953819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953819 prefixEnd_3953819 := by exact prefixLift 3953819
  have htrace : WordTrace (prefixWord ++ tailWord_3953819) baseStart_3953819 baseEnd_3953819 := by
    simpa [prefixWord, tailWord_3953819, baseEnd_3953819] using wordTrace_append hprefix tailTrace_3953819
  have hstable : (prefixWord ++ tailWord_3953819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953819).length < 2 ^ (prefixWord ++ tailWord_3953819).sum := by decide
  have hdescent : baseEnd_3953819 < baseStart_3953819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953834 : List Nat := [3, 1, 5, 1, 1, 1, 4, 2, 1, 4]
def baseStart_3953834 : Nat := 118140960795 + 3953834 * 2 ^ 59
def prefixEnd_3953834 : Nat := 4983230072969 + 3 ^ 40 * 3953834 * 2
def baseEnd_3953834 : Nat := 676739090029662946663885

theorem tailTrace_3953834 : CollatzResearch.WordTrace tailWord_3953834 prefixEnd_3953834 676739090029662946663885 := by
  unfold tailWord_3953834
  simp only [CollatzResearch.WordTrace]
  refine ⟨36052043289485538483007139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96138782105294769288019037 36052043289485538483007139)
  ·
    refine ⟨54078064934228307724510709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36052043289485538483007139 54078064934228307724510709)
    ·
      refine ⟨5069818587583903849172879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54078064934228307724510709 5069818587583903849172879)
      ·
        refine ⟨7604727881375855773759319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5069818587583903849172879 7604727881375855773759319)
        ·
          refine ⟨11407091822063783660638979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7604727881375855773759319 11407091822063783660638979)
          ·
            refine ⟨17110637733095675490958469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11407091822063783660638979 17110637733095675490958469)
            ·
              refine ⟨3208244574955439154554713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17110637733095675490958469 3208244574955439154554713)
              ·
                refine ⟨2406183431216579365916035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3208244574955439154554713 2406183431216579365916035)
                ·
                  refine ⟨3609275146824869048874053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2406183431216579365916035 3609275146824869048874053)
                  ·
                    refine ⟨676739090029662946663885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3609275146824869048874053 676739090029662946663885)
                    ·
                      rfl

theorem cell23_3953834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_3953834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953834 prefixEnd_3953834 := by exact prefixLift 3953834
  have htrace : WordTrace (prefixWord ++ tailWord_3953834) baseStart_3953834 baseEnd_3953834 := by
    simpa [prefixWord, tailWord_3953834, baseEnd_3953834] using wordTrace_append hprefix tailTrace_3953834
  have hstable : (prefixWord ++ tailWord_3953834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953834).length < 2 ^ (prefixWord ++ tailWord_3953834).sum := by decide
  have hdescent : baseEnd_3953834 < baseStart_3953834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953840 : List Nat := [2, 1, 1, 1, 2, 1, 2, 8, 1, 1, 3]
def baseStart_3953840 : Nat := 118140960795 + 3953840 * 2 ^ 59
def prefixEnd_3953840 : Nat := 4983230072969 + 3 ^ 40 * 3953840 * 2
def baseEnd_3953840 : Nat := 2030220350972915816516627

theorem tailTrace_3953840 : CollatzResearch.WordTrace tailWord_3953840 prefixEnd_3953840 2030220350972915816516627 := by
  unfold tailWord_3953840
  simp only [CollatzResearch.WordTrace]
  refine ⟨72104195997960208478373487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96138927997280277971164649 72104195997960208478373487)
  ·
    refine ⟨108156293996940312717560231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72104195997960208478373487 108156293996940312717560231)
    ·
      refine ⟨162234440995410469076340347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108156293996940312717560231 162234440995410469076340347)
      ·
        refine ⟨243351661493115703614510521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162234440995410469076340347 243351661493115703614510521)
        ·
          refine ⟨182513746119836777710882891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243351661493115703614510521 182513746119836777710882891)
          ·
            refine ⟨273770619179755166566324337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182513746119836777710882891 273770619179755166566324337)
            ·
              refine ⟨205327964384816374924743253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273770619179755166566324337 205327964384816374924743253)
              ·
                refine ⟨2406187082634566893649335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 205327964384816374924743253 2406187082634566893649335)
                ·
                  refine ⟨3609280623951850340474003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2406187082634566893649335 3609280623951850340474003)
                  ·
                    refine ⟨5413920935927775510711005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3609280623951850340474003 5413920935927775510711005)
                    ·
                      refine ⟨2030220350972915816516627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5413920935927775510711005 2030220350972915816516627)
                      ·
                        rfl

theorem cell23_3953840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 1, 1, 3].length) (baseStart_3953840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953840 prefixEnd_3953840 := by exact prefixLift 3953840
  have htrace : WordTrace (prefixWord ++ tailWord_3953840) baseStart_3953840 baseEnd_3953840 := by
    simpa [prefixWord, tailWord_3953840, baseEnd_3953840] using wordTrace_append hprefix tailTrace_3953840
  have hstable : (prefixWord ++ tailWord_3953840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953840).length < 2 ^ (prefixWord ++ tailWord_3953840).sum := by decide
  have hdescent : baseEnd_3953840 < baseStart_3953840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953857 : List Nat := [1, 2, 6, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_3953857 : Nat := 118140960795 + 3953857 * 2 ^ 59
def prefixEnd_3953857 : Nat := 4983230072969 + 3 ^ 40 * 3953857 * 2
def baseEnd_3953857 : Nat := 2030229080144042250004049

theorem tailTrace_3953857 : CollatzResearch.WordTrace tailWord_3953857 prefixEnd_3953857 2030229080144042250004049 := by
  unfold tailWord_3953857
  simp only [CollatzResearch.WordTrace]
  refine ⟨144209012036858828860115825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96139341357905885906743883 144209012036858828860115825)
  ·
    refine ⟨108156759027644121645086869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144209012036858828860115825 108156759027644121645086869)
    ·
      refine ⟨5069848079420818202113447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108156759027644121645086869 5069848079420818202113447)
      ·
        refine ⟨7604772119131227303170171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5069848079420818202113447 7604772119131227303170171)
        ·
          refine ⟨11407158178696840954755257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7604772119131227303170171 11407158178696840954755257)
          ·
            refine ⟨8555368634022630716066443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11407158178696840954755257 8555368634022630716066443)
            ·
              refine ⟨12833052951033946074099665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8555368634022630716066443 12833052951033946074099665)
              ·
                refine ⟨9624789713275459555574749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12833052951033946074099665 9624789713275459555574749)
                ·
                  refine ⟨3609296142478297333340531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9624789713275459555574749 3609296142478297333340531)
                  ·
                    refine ⟨5413944213717446000010797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3609296142478297333340531 5413944213717446000010797)
                    ·
                      refine ⟨2030229080144042250004049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5413944213717446000010797 2030229080144042250004049)
                      ·
                        rfl

theorem cell23_3953857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_3953857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953857 prefixEnd_3953857 := by exact prefixLift 3953857
  have htrace : WordTrace (prefixWord ++ tailWord_3953857) baseStart_3953857 baseEnd_3953857 := by
    simpa [prefixWord, tailWord_3953857, baseEnd_3953857] using wordTrace_append hprefix tailTrace_3953857
  have hstable : (prefixWord ++ tailWord_3953857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953857).length < 2 ^ (prefixWord ++ tailWord_3953857).sum := by decide
  have hdescent : baseEnd_3953857 < baseStart_3953857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953877 : List Nat := [1, 3, 2, 4, 1, 3, 2, 1, 1, 5]
def baseStart_3953877 : Nat := 118140960795 + 3953877 * 2 ^ 59
def prefixEnd_3953877 : Nat := 4983230072969 + 3 ^ 40 * 3953877 * 2
def baseEnd_3953877 : Nat := 676746449919044057251319

theorem tailTrace_3953877 : CollatzResearch.WordTrace tailWord_3953877 prefixEnd_3953877 676746449919044057251319 := by
  unfold tailWord_3953877
  simp only [CollatzResearch.WordTrace]
  refine ⟨144209741496786372275843885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96139827664524248183895923 144209741496786372275843885)
  ·
    refine ⟨54078653061294889603441457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144209741496786372275843885 54078653061294889603441457)
    ·
      refine ⟨40558989795971167202581093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54078653061294889603441457 40558989795971167202581093)
      ·
        refine ⟨7604810586744593850483955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40558989795971167202581093 7604810586744593850483955)
        ·
          refine ⟨11407215880116890775725933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7604810586744593850483955 11407215880116890775725933)
          ·
            refine ⟨4277705955043834040897225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11407215880116890775725933 4277705955043834040897225)
            ·
              refine ⟨3208279466282875530672919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4277705955043834040897225 3208279466282875530672919)
              ·
                refine ⟨4812419199424313296009379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3208279466282875530672919 4812419199424313296009379)
                ·
                  refine ⟨7218628799136469944014069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4812419199424313296009379 7218628799136469944014069)
                  ·
                    refine ⟨676746449919044057251319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7218628799136469944014069 676746449919044057251319)
                    ·
                      rfl

theorem cell23_3953877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_3953877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953877 prefixEnd_3953877 := by exact prefixLift 3953877
  have htrace : WordTrace (prefixWord ++ tailWord_3953877) baseStart_3953877 baseEnd_3953877 := by
    simpa [prefixWord, tailWord_3953877, baseEnd_3953877] using wordTrace_append hprefix tailTrace_3953877
  have hstable : (prefixWord ++ tailWord_3953877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953877).length < 2 ^ (prefixWord ++ tailWord_3953877).sum := by decide
  have hdescent : baseEnd_3953877 < baseStart_3953877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953880 : List Nat := [2, 1, 2, 2, 5, 1, 1, 3, 1, 1, 4]
def baseStart_3953880 : Nat := 118140960795 + 3953880 * 2 ^ 59
def prefixEnd_3953880 : Nat := 4983230072969 + 3 ^ 40 * 3953880 * 2
def baseEnd_3953880 : Nat := 2030240890199095660016443

theorem tailTrace_3953880 : CollatzResearch.WordTrace tailWord_3953880 prefixEnd_3953880 2030240890199095660016443 := by
  unfold tailWord_3953880
  simp only [CollatzResearch.WordTrace]
  refine ⟨72104925457887751894101547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96139900610517002525468729 72104925457887751894101547)
  ·
    refine ⟨108157388186831627841152321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72104925457887751894101547 108157388186831627841152321)
    ·
      refine ⟨81118041140123720880864241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108157388186831627841152321 81118041140123720880864241)
      ·
        refine ⟨60838530855092790660648181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81118041140123720880864241 60838530855092790660648181)
        ·
          refine ⟨5703612267664949124435767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60838530855092790660648181 5703612267664949124435767)
          ·
            refine ⟨8555418401497423686653651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5703612267664949124435767 8555418401497423686653651)
            ·
              refine ⟨12833127602246135529980477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8555418401497423686653651 12833127602246135529980477)
              ·
                refine ⟨4812422850842300823742679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12833127602246135529980477 4812422850842300823742679)
                ·
                  refine ⟨7218634276263451235614019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4812422850842300823742679 7218634276263451235614019)
                  ·
                    refine ⟨10827951414395176853421029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7218634276263451235614019 10827951414395176853421029)
                    ·
                      refine ⟨2030240890199095660016443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10827951414395176853421029 2030240890199095660016443)
                      ·
                        rfl

theorem cell23_3953880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_3953880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953880 prefixEnd_3953880 := by exact prefixLift 3953880
  have htrace : WordTrace (prefixWord ++ tailWord_3953880) baseStart_3953880 baseEnd_3953880 := by
    simpa [prefixWord, tailWord_3953880, baseEnd_3953880] using wordTrace_append hprefix tailTrace_3953880
  have hstable : (prefixWord ++ tailWord_3953880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953880).length < 2 ^ (prefixWord ++ tailWord_3953880).sum := by decide
  have hdescent : baseEnd_3953880 < baseStart_3953880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953973 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_3953973 : Nat := 118140960795 + 3953973 * 2 ^ 59
def prefixEnd_3953973 : Nat := 4983230072969 + 3 ^ 40 * 3953973 * 2
def baseEnd_3953973 : Nat := 2030288643899963796153515

theorem tailTrace_3953973 : CollatzResearch.WordTrace tailWord_3953973 prefixEnd_3953973 2030288643899963796153515 := by
  unfold tailWord_3953973
  simp only [CollatzResearch.WordTrace]
  refine ⟨144213242904438580671338573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96142161936292387114225715 144213242904438580671338573)
  ·
    refine ⟨54079966089164467751751965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144213242904438580671338573 54079966089164467751751965)
    ·
      refine ⟨20279987283436675406906987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54079966089164467751751965 20279987283436675406906987)
      ·
        refine ⟨30419980925155013110360481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20279987283436675406906987 30419980925155013110360481)
        ·
          refine ⟨22814985693866259832770361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30419980925155013110360481 22814985693866259832770361)
          ·
            refine ⟨17111239270399694874577771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22814985693866259832770361 17111239270399694874577771)
            ·
              refine ⟨25666858905599542311866657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17111239270399694874577771 25666858905599542311866657)
              ·
                refine ⟨19250144179199656733899993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25666858905599542311866657 19250144179199656733899993)
                ·
                  refine ⟨14437608134399742550424995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19250144179199656733899993 14437608134399742550424995)
                  ·
                    refine ⟨21656412201599613825637493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14437608134399742550424995 21656412201599613825637493)
                    ·
                      refine ⟨2030288643899963796153515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21656412201599613825637493 2030288643899963796153515)
                      ·
                        rfl

theorem cell23_3953973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_3953973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953973 prefixEnd_3953973 := by exact prefixLift 3953973
  have htrace : WordTrace (prefixWord ++ tailWord_3953973) baseStart_3953973 baseEnd_3953973 := by
    simpa [prefixWord, tailWord_3953973, baseEnd_3953973] using wordTrace_append hprefix tailTrace_3953973
  have hstable : (prefixWord ++ tailWord_3953973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953973).length < 2 ^ (prefixWord ++ tailWord_3953973).sum := by decide
  have hdescent : baseEnd_3953973 < baseStart_3953973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953976 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 9]
def baseStart_3953976 : Nat := 118140960795 + 3953976 * 2 ^ 59
def prefixEnd_3953976 : Nat := 4983230072969 + 3 ^ 40 * 3953976 * 2
def baseEnd_3953976 : Nat := 225587798260214142712889

theorem tailTrace_3953976 : CollatzResearch.WordTrace tailWord_3953976 prefixEnd_3953976 225587798260214142712889 := by
  unfold tailWord_3953976
  simp only [CollatzResearch.WordTrace]
  refine ⟨72106676161713856091848891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96142234882285141455798521 72106676161713856091848891)
  ·
    refine ⟨108160014242570784137773337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72106676161713856091848891 108160014242570784137773337)
    ·
      refine ⟨81120010681928088103330003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108160014242570784137773337 81120010681928088103330003)
      ·
        refine ⟨121680016022892132154995005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81120010681928088103330003 121680016022892132154995005)
        ·
          refine ⟨45630006008584549558123127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121680016022892132154995005 45630006008584549558123127)
          ·
            refine ⟨68445009012876824337184691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45630006008584549558123127 68445009012876824337184691)
            ·
              refine ⟨102667513519315236505777037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68445009012876824337184691 102667513519315236505777037)
              ·
                refine ⟨38500317569743213689666389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102667513519315236505777037 38500317569743213689666389)
                ·
                  refine ⟨225587798260214142712889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38500317569743213689666389 225587798260214142712889)
                  ·
                    rfl

theorem cell23_3953976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 9].length) (baseStart_3953976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3953976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3953976 prefixEnd_3953976 := by exact prefixLift 3953976
  have htrace : WordTrace (prefixWord ++ tailWord_3953976) baseStart_3953976 baseEnd_3953976 := by
    simpa [prefixWord, tailWord_3953976, baseEnd_3953976] using wordTrace_append hprefix tailTrace_3953976
  have hstable : (prefixWord ++ tailWord_3953976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953976).length < 2 ^ (prefixWord ++ tailWord_3953976).sum := by decide
  have hdescent : baseEnd_3953976 < baseStart_3953976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954003 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 3]
def baseStart_3954003 : Nat := 118140960795 + 3954003 * 2 ^ 59
def prefixEnd_3954003 : Nat := 4983230072969 + 3 ^ 40 * 3954003 * 2
def baseEnd_3954003 : Nat := 2030304048319598678778377

theorem tailTrace_3954003 : CollatzResearch.WordTrace tailWord_3954003 prefixEnd_3954003 2030304048319598678778377 := by
  unfold tailWord_3954003
  simp only [CollatzResearch.WordTrace]
  refine ⟨144214337094329895794930663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96142891396219930529953775 144214337094329895794930663)
  ·
    refine ⟨216321505641494843692395995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144214337094329895794930663 216321505641494843692395995)
    ·
      refine ⟨324482258462242265538593993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216321505641494843692395995 324482258462242265538593993)
      ·
        refine ⟨243361693846681699153945495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324482258462242265538593993 243361693846681699153945495)
        ·
          refine ⟨365042540770022548730918243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243361693846681699153945495 365042540770022548730918243)
          ·
            refine ⟨547563811155033823096377365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365042540770022548730918243 547563811155033823096377365)
            ·
              refine ⟨25667053647892210457642689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 547563811155033823096377365 25667053647892210457642689)
              ·
                refine ⟨19250290235919157843232017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25667053647892210457642689 19250290235919157843232017)
                ·
                  refine ⟨14437717676939368382424013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19250290235919157843232017 14437717676939368382424013)
                  ·
                    refine ⟨5414144128852263143409005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14437717676939368382424013 5414144128852263143409005)
                    ·
                      refine ⟨2030304048319598678778377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5414144128852263143409005 2030304048319598678778377)
                      ·
                        rfl

theorem cell23_3954003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 3].length) (baseStart_3954003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954003 prefixEnd_3954003 := by exact prefixLift 3954003
  have htrace : WordTrace (prefixWord ++ tailWord_3954003) baseStart_3954003 baseEnd_3954003 := by
    simpa [prefixWord, tailWord_3954003, baseEnd_3954003] using wordTrace_append hprefix tailTrace_3954003
  have hstable : (prefixWord ++ tailWord_3954003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954003).length < 2 ^ (prefixWord ++ tailWord_3954003).sum := by decide
  have hdescent : baseEnd_3954003 < baseStart_3954003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954004 : List Nat := [2, 4, 1, 1, 2, 1, 4, 2, 2, 2, 2]
def baseStart_3954004 : Nat := 118140960795 + 3954004 * 2 ^ 59
def prefixEnd_3954004 : Nat := 4983230072969 + 3 ^ 40 * 3954004 * 2
def baseEnd_3954004 : Nat := 2030304561800253174865873

theorem tailTrace_3954004 : CollatzResearch.WordTrace tailWord_3954004 prefixEnd_3954004 2030304561800253174865873 := by
  unfold tailWord_3954004
  simp only [CollatzResearch.WordTrace]
  refine ⟨72107186783663136482858533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96142915711550848643811377 72107186783663136482858533)
  ·
    refine ⟨13520097521936838090535975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72107186783663136482858533 13520097521936838090535975)
    ·
      refine ⟨20280146282905257135803963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13520097521936838090535975 20280146282905257135803963)
      ·
        refine ⟨30420219424357885703705945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20280146282905257135803963 30420219424357885703705945)
        ·
          refine ⟨22815164568268414277779459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30420219424357885703705945 22815164568268414277779459)
          ·
            refine ⟨34222746852402621416669189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22815164568268414277779459 34222746852402621416669189)
            ·
              refine ⟨6416765034825491515625473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34222746852402621416669189 6416765034825491515625473)
              ·
                refine ⟨4812573776119118636719105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6416765034825491515625473 4812573776119118636719105)
                ·
                  refine ⟨3609430332089338977539329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4812573776119118636719105 3609430332089338977539329)
                  ·
                    refine ⟨2707072749067004233154497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3609430332089338977539329 2707072749067004233154497)
                    ·
                      refine ⟨2030304561800253174865873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2707072749067004233154497 2030304561800253174865873)
                      ·
                        rfl

theorem cell23_3954004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_3954004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954004 prefixEnd_3954004 := by exact prefixLift 3954004
  have htrace : WordTrace (prefixWord ++ tailWord_3954004) baseStart_3954004 baseEnd_3954004 := by
    simpa [prefixWord, tailWord_3954004, baseEnd_3954004] using wordTrace_append hprefix tailTrace_3954004
  have hstable : (prefixWord ++ tailWord_3954004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954004).length < 2 ^ (prefixWord ++ tailWord_3954004).sum := by decide
  have hdescent : baseEnd_3954004 < baseStart_3954004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954020 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 2, 3, 3]
def baseStart_3954020 : Nat := 118140960795 + 3954020 * 2 ^ 59
def prefixEnd_3954020 : Nat := 4983230072969 + 3 ^ 40 * 3954020 * 2
def baseEnd_3954020 : Nat := 2030312777490725112265799

theorem tailTrace_3954020 : CollatzResearch.WordTrace tailWord_3954020 prefixEnd_3954020 2030312777490725112265799 := by
  unfold tailWord_3954020
  simp only [CollatzResearch.WordTrace]
  refine ⟨72107478567634153849149757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96143304756845538465533009 72107478567634153849149757)
  ·
    refine ⟨27040304462862807693431159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72107478567634153849149757 27040304462862807693431159)
    ·
      refine ⟨40560456694294211540146739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27040304462862807693431159 40560456694294211540146739)
      ·
        refine ⟨60840685041441317310220109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40560456694294211540146739 60840685041441317310220109)
        ·
          refine ⟨22815256890540493991332541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60840685041441317310220109 22815256890540493991332541)
          ·
            refine ⟨8555721333952685246749703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22815256890540493991332541 8555721333952685246749703)
            ·
              refine ⟨12833582000929027870124555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8555721333952685246749703 12833582000929027870124555)
              ·
                refine ⟨19250373001393541805186833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12833582000929027870124555 19250373001393541805186833)
                ·
                  refine ⟨14437779751045156353890125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19250373001393541805186833 14437779751045156353890125)
                  ·
                    refine ⟨5414167406641933632708797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14437779751045156353890125 5414167406641933632708797)
                    ·
                      refine ⟨2030312777490725112265799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5414167406641933632708797 2030312777490725112265799)
                      ·
                        rfl

theorem cell23_3954020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_3954020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954020 prefixEnd_3954020 := by exact prefixLift 3954020
  have htrace : WordTrace (prefixWord ++ tailWord_3954020) baseStart_3954020 baseEnd_3954020 := by
    simpa [prefixWord, tailWord_3954020, baseEnd_3954020] using wordTrace_append hprefix tailTrace_3954020
  have hstable : (prefixWord ++ tailWord_3954020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954020).length < 2 ^ (prefixWord ++ tailWord_3954020).sum := by decide
  have hdescent : baseEnd_3954020 < baseStart_3954020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954043 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 4]
def baseStart_3954043 : Nat := 118140960795 + 3954043 * 2 ^ 59
def prefixEnd_3954043 : Nat := 4983230072969 + 3 ^ 40 * 3954043 * 2
def baseEnd_3954043 : Nat := 2030324587545778522278193

theorem tailTrace_3954043 : CollatzResearch.WordTrace tailWord_3954043 prefixEnd_3954043 2030324587545778522278193 := by
  unfold tailWord_3954043
  simp only [CollatzResearch.WordTrace]
  refine ⟨144215796014184982626386783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96143864009456655084257855 144215796014184982626386783)
  ·
    refine ⟨216323694021277473939580175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144215796014184982626386783 216323694021277473939580175)
    ·
      refine ⟨324485541031916210909370263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216323694021277473939580175 324485541031916210909370263)
      ·
        refine ⟨486728311547874316364055395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324485541031916210909370263 486728311547874316364055395)
        ·
          refine ⟨730092467321811474546083093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486728311547874316364055395 730092467321811474546083093)
          ·
            refine ⟨34223084405709912869347645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 730092467321811474546083093 34223084405709912869347645)
            ·
              refine ⟨12833656652141217326005367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34223084405709912869347645 12833656652141217326005367)
              ·
                refine ⟨19250484978211825989008051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12833656652141217326005367 19250484978211825989008051)
                ·
                  refine ⟨28875727467317738983512077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19250484978211825989008051 28875727467317738983512077)
                  ·
                    refine ⟨10828397800244152118817029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28875727467317738983512077 10828397800244152118817029)
                    ·
                      refine ⟨2030324587545778522278193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10828397800244152118817029 2030324587545778522278193)
                      ·
                        rfl

theorem cell23_3954043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 4].length) (baseStart_3954043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954043 prefixEnd_3954043 := by exact prefixLift 3954043
  have htrace : WordTrace (prefixWord ++ tailWord_3954043) baseStart_3954043 baseEnd_3954043 := by
    simpa [prefixWord, tailWord_3954043, baseEnd_3954043] using wordTrace_append hprefix tailTrace_3954043
  have hstable : (prefixWord ++ tailWord_3954043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954043).length < 2 ^ (prefixWord ++ tailWord_3954043).sum := by decide
  have hdescent : baseEnd_3954043 < baseStart_3954043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954060 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 4, 4, 2]
def baseStart_3954060 : Nat := 118140960795 + 3954060 * 2 ^ 59
def prefixEnd_3954060 : Nat := 4983230072969 + 3 ^ 40 * 3954060 * 2
def baseEnd_3954060 : Nat := 2030333316716904955765615

theorem tailTrace_3954060 : CollatzResearch.WordTrace tailWord_3954060 prefixEnd_3954060 2030333316716904955765615 := by
  unfold tailWord_3954060
  simp only [CollatzResearch.WordTrace]
  refine ⟨72108208027561697264877817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96144277370082263019837089 72108208027561697264877817)
  ·
    refine ⟨54081156020671272948658363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72108208027561697264877817 54081156020671272948658363)
    ·
      refine ⟨81121734031006909422987545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54081156020671272948658363 81121734031006909422987545)
      ·
        refine ⟨60841300523255182067240659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81121734031006909422987545 60841300523255182067240659)
        ·
          refine ⟨91261950784882773100860989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60841300523255182067240659 91261950784882773100860989)
          ·
            refine ⟨34223231544331039912822871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91261950784882773100860989 34223231544331039912822871)
            ·
              refine ⟨51334847316496559869234307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34223231544331039912822871 51334847316496559869234307)
              ·
                refine ⟨77002270974744839803851461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51334847316496559869234307 77002270974744839803851461)
                ·
                  refine ⟨14437925807764657463222149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77002270974744839803851461 14437925807764657463222149)
                  ·
                    refine ⟨2707111088955873274354153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14437925807764657463222149 2707111088955873274354153)
                    ·
                      refine ⟨2030333316716904955765615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2707111088955873274354153 2030333316716904955765615)
                      ·
                        rfl

theorem cell23_3954060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_3954060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954060 prefixEnd_3954060 := by exact prefixLift 3954060
  have htrace : WordTrace (prefixWord ++ tailWord_3954060) baseStart_3954060 baseEnd_3954060 := by
    simpa [prefixWord, tailWord_3954060, baseEnd_3954060] using wordTrace_append hprefix tailTrace_3954060
  have hstable : (prefixWord ++ tailWord_3954060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954060).length < 2 ^ (prefixWord ++ tailWord_3954060).sum := by decide
  have hdescent : baseEnd_3954060 < baseStart_3954060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954077 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 2, 4, 2]
def baseStart_3954077 : Nat := 118140960795 + 3954077 * 2 ^ 59
def prefixEnd_3954077 : Nat := 4983230072969 + 3 ^ 40 * 3954077 * 2
def baseEnd_3954077 : Nat := 2030342045888031389253037

theorem tailTrace_3954077 : CollatzResearch.WordTrace tailWord_3954077 prefixEnd_3954077 2030342045888031389253037 := by
  unfold tailWord_3954077
  simp only [CollatzResearch.WordTrace]
  refine ⟨144217036096061806433124485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96144690730707870955416323 144217036096061806433124485)
  ·
    refine ⟨27040694268011588706210841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144217036096061806433124485 27040694268011588706210841)
    ·
      refine ⟨20280520701008691529658131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27040694268011588706210841 20280520701008691529658131)
      ·
        refine ⟨30420781051513037294487197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20280520701008691529658131 30420781051513037294487197)
        ·
          refine ⟨11407792894317388985432699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30420781051513037294487197 11407792894317388985432699)
          ·
            refine ⟨17111689341476083478149049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11407792894317388985432699 17111689341476083478149049)
            ·
              refine ⟨12833767006107062608611787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17111689341476083478149049 12833767006107062608611787)
              ·
                refine ⟨19250650509160593912917681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12833767006107062608611787 19250650509160593912917681)
                ·
                  refine ⟨14437987881870445434688261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19250650509160593912917681 14437987881870445434688261)
                  ·
                    refine ⟨2707122727850708519004049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14437987881870445434688261 2707122727850708519004049)
                    ·
                      refine ⟨2030342045888031389253037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2707122727850708519004049 2030342045888031389253037)
                      ·
                        rfl

theorem cell23_3954077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_3954077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954077 prefixEnd_3954077 := by exact prefixLift 3954077
  have htrace : WordTrace (prefixWord ++ tailWord_3954077) baseStart_3954077 baseEnd_3954077 := by
    simpa [prefixWord, tailWord_3954077, baseEnd_3954077] using wordTrace_append hprefix tailTrace_3954077
  have hstable : (prefixWord ++ tailWord_3954077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954077).length < 2 ^ (prefixWord ++ tailWord_3954077).sum := by decide
  have hdescent : baseEnd_3954077 < baseStart_3954077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954127 : List Nat := [1, 1, 2, 1, 1, 4, 5, 1, 3, 1, 3]
def baseStart_3954127 : Nat := 118140960795 + 3954127 * 2 ^ 59
def prefixEnd_3954127 : Nat := 4983230072969 + 3 ^ 40 * 3954127 * 2
def baseEnd_3954127 : Nat := 2030367719920756193627807

theorem tailTrace_3954127 : CollatzResearch.WordTrace tailWord_3954127 prefixEnd_3954127 2030367719920756193627807 := by
  unfold tailWord_3954127
  simp only [CollatzResearch.WordTrace]
  refine ⟨144218859745880664972444635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96145906497253776648296423 144218859745880664972444635)
  ·
    refine ⟨216328289618820997458666953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144218859745880664972444635 216328289618820997458666953)
    ·
      refine ⟨162246217214115748094000215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216328289618820997458666953 162246217214115748094000215)
      ·
        refine ⟨243369325821173622141000323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162246217214115748094000215 243369325821173622141000323)
        ·
          refine ⟨365053988731760433211500485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243369325821173622141000323 365053988731760433211500485)
          ·
            refine ⟨68447622887205081227156341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 365053988731760433211500485 68447622887205081227156341)
            ·
              refine ⟨6416964645675476365045907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68447622887205081227156341 6416964645675476365045907)
              ·
                refine ⟨9625446968513214547568861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6416964645675476365045907 9625446968513214547568861)
                ·
                  refine ⟨3609542613192455455338323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9625446968513214547568861 3609542613192455455338323)
                  ·
                    refine ⟨5414313919788683183007485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3609542613192455455338323 5414313919788683183007485)
                    ·
                      refine ⟨2030367719920756193627807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5414313919788683183007485 2030367719920756193627807)
                      ·
                        rfl

theorem cell23_3954127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 1, 3].length) (baseStart_3954127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954127 prefixEnd_3954127 := by exact prefixLift 3954127
  have htrace : WordTrace (prefixWord ++ tailWord_3954127) baseStart_3954127 baseEnd_3954127 := by
    simpa [prefixWord, tailWord_3954127, baseEnd_3954127] using wordTrace_append hprefix tailTrace_3954127
  have hstable : (prefixWord ++ tailWord_3954127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954127).length < 2 ^ (prefixWord ++ tailWord_3954127).sum := by decide
  have hdescent : baseEnd_3954127 < baseStart_3954127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954134 : List Nat := [5, 2, 1, 1, 1, 2, 4, 1, 6]
def baseStart_3954134 : Nat := 118140960795 + 3954134 * 2 ^ 59
def prefixEnd_3954134 : Nat := 4983230072969 + 3 ^ 40 * 3954134 * 2
def baseEnd_3954134 : Nat := 225596812698370851804475

theorem tailTrace_3954134 : CollatzResearch.WordTrace tailWord_3954134 prefixEnd_3954134 225596812698370851804475 := by
  unfold tailWord_3954134
  simp only [CollatzResearch.WordTrace]
  refine ⟨9013694691053456572996841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96146076704570203445299637 9013694691053456572996841)
  ·
    refine ⟨6760271018290092429747631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9013694691053456572996841 6760271018290092429747631)
    ·
      refine ⟨10140406527435138644621447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6760271018290092429747631 10140406527435138644621447)
      ·
        refine ⟨15210609791152707966932171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10140406527435138644621447 15210609791152707966932171)
        ·
          refine ⟨22815914686729061950398257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15210609791152707966932171 22815914686729061950398257)
          ·
            refine ⟨17111936015046796462798693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22815914686729061950398257 17111936015046796462798693)
            ·
              refine ⟨3208488002821274336774755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17111936015046796462798693 3208488002821274336774755)
              ·
                refine ⟨4812732004231911505162133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3208488002821274336774755 4812732004231911505162133)
                ·
                  refine ⟨225596812698370851804475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4812732004231911505162133 225596812698370851804475)
                  ·
                    rfl

theorem cell23_3954134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_3954134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954134 prefixEnd_3954134 := by exact prefixLift 3954134
  have htrace : WordTrace (prefixWord ++ tailWord_3954134) baseStart_3954134 baseEnd_3954134 := by
    simpa [prefixWord, tailWord_3954134, baseEnd_3954134] using wordTrace_append hprefix tailTrace_3954134
  have hstable : (prefixWord ++ tailWord_3954134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954134).length < 2 ^ (prefixWord ++ tailWord_3954134).sum := by decide
  have hdescent : baseEnd_3954134 < baseStart_3954134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954147 : List Nat := [1, 1, 1, 6, 2, 1, 3, 2, 1, 5]
def baseStart_3954147 : Nat := 118140960795 + 3954147 * 2 ^ 59
def prefixEnd_3954147 : Nat := 4983230072969 + 3 ^ 40 * 3954147 * 2
def baseEnd_3954147 : Nat := 676792663177948705125905

theorem tailTrace_3954147 : CollatzResearch.WordTrace tailWord_3954147 prefixEnd_3954147 676792663177948705125905 := by
  unfold tailWord_3954147
  simp only [CollatzResearch.WordTrace]
  refine ⟨144219589205808208388172695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96146392803872138925448463 144219589205808208388172695)
  ·
    refine ⟨216329383808712312582259043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144219589205808208388172695 216329383808712312582259043)
    ·
      refine ⟨324494075713068468873388565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216329383808712312582259043 324494075713068468873388565)
      ·
        refine ⟨15210659799050084478440089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 324494075713068468873388565 15210659799050084478440089)
        ·
          refine ⟨11407994849287563358830067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15210659799050084478440089 11407994849287563358830067)
          ·
            refine ⟨17111992273931345038245101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11407994849287563358830067 17111992273931345038245101)
            ·
              refine ⟨6416997102724254389341913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17111992273931345038245101 6416997102724254389341913)
              ·
                refine ⟨4812747827043190792006435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6416997102724254389341913 4812747827043190792006435)
                ·
                  refine ⟨7219121740564786188009653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4812747827043190792006435 7219121740564786188009653)
                  ·
                    refine ⟨676792663177948705125905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7219121740564786188009653 676792663177948705125905)
                    ·
                      rfl

theorem cell23_3954147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 5].length) (baseStart_3954147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954147 prefixEnd_3954147 := by exact prefixLift 3954147
  have htrace : WordTrace (prefixWord ++ tailWord_3954147) baseStart_3954147 baseEnd_3954147 := by
    simpa [prefixWord, tailWord_3954147, baseEnd_3954147] using wordTrace_append hprefix tailTrace_3954147
  have hstable : (prefixWord ++ tailWord_3954147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954147).length < 2 ^ (prefixWord ++ tailWord_3954147).sum := by decide
  have hdescent : baseEnd_3954147 < baseStart_3954147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954160 : List Nat := [2, 1, 1, 1, 3, 5, 1, 2, 1, 6]
def baseStart_3954160 : Nat := 118140960795 + 3954160 * 2 ^ 59
def prefixEnd_3954160 : Nat := 4983230072969 + 3 ^ 40 * 3954160 * 2
def baseEnd_3954160 : Nat := 676794888260784854838385

theorem tailTrace_3954160 : CollatzResearch.WordTrace tailWord_3954160 prefixEnd_3954160 676794888260784854838385 := by
  unfold tailWord_3954160
  simp only [CollatzResearch.WordTrace]
  refine ⟨72110031677380555804197967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96146708903174074405597289 72110031677380555804197967)
  ·
    refine ⟨108165047516070833706296951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72110031677380555804197967 108165047516070833706296951)
    ·
      refine ⟨162247571274106250559445427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108165047516070833706296951 162247571274106250559445427)
      ·
        refine ⟨243371356911159375839168141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162247571274106250559445427 243371356911159375839168141)
        ·
          refine ⟨91264258841684765939688053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243371356911159375839168141 91264258841684765939688053)
          ·
            refine ⟨8556024266407946806845755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91264258841684765939688053 8556024266407946806845755)
            ·
              refine ⟨12834036399611920210268633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8556024266407946806845755 12834036399611920210268633)
              ·
                refine ⟨9625527299708940157701475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12834036399611920210268633 9625527299708940157701475)
                ·
                  refine ⟨14438290949563410236552213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9625527299708940157701475 14438290949563410236552213)
                  ·
                    refine ⟨676794888260784854838385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14438290949563410236552213 676794888260784854838385)
                    ·
                      rfl

theorem cell23_3954160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 1, 6].length) (baseStart_3954160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954160 prefixEnd_3954160 := by exact prefixLift 3954160
  have htrace : WordTrace (prefixWord ++ tailWord_3954160) baseStart_3954160 baseEnd_3954160 := by
    simpa [prefixWord, tailWord_3954160, baseEnd_3954160] using wordTrace_append hprefix tailTrace_3954160
  have hstable : (prefixWord ++ tailWord_3954160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954160).length < 2 ^ (prefixWord ++ tailWord_3954160).sum := by decide
  have hdescent : baseEnd_3954160 < baseStart_3954160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954163 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 6]
def baseStart_3954163 : Nat := 118140960795 + 3954163 * 2 ^ 59
def prefixEnd_3954163 : Nat := 4983230072969 + 3 ^ 40 * 3954163 * 2
def baseEnd_3954163 : Nat := 2030386205224318052777641

theorem tailTrace_3954163 : CollatzResearch.WordTrace tailWord_3954163 prefixEnd_3954163 2030386205224318052777641 := by
  unfold tailWord_3954163
  simp only [CollatzResearch.WordTrace]
  refine ⟨144220172773750243120755143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96146781849166828747170095 144220172773750243120755143)
  ·
    refine ⟨216330259160625364681132715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144220172773750243120755143 216330259160625364681132715)
    ·
      refine ⟨324495388740938047021699073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216330259160625364681132715 324495388740938047021699073)
      ·
        refine ⟨243371541555703535266274305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324495388740938047021699073 243371541555703535266274305)
        ·
          refine ⟨182528656166777651449705729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243371541555703535266274305 182528656166777651449705729)
          ·
            refine ⟨136896492125083238587279297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182528656166777651449705729 136896492125083238587279297)
            ·
              refine ⟨102672369093812428940459473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136896492125083238587279297 102672369093812428940459473)
              ·
                refine ⟨77004276820359321705344605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102672369093812428940459473 77004276820359321705344605)
                ·
                  refine ⟨28876603807634745639504227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77004276820359321705344605 28876603807634745639504227)
                  ·
                    refine ⟨43314905711452118459256341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28876603807634745639504227 43314905711452118459256341)
                    ·
                      refine ⟨2030386205224318052777641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43314905711452118459256341 2030386205224318052777641)
                      ·
                        rfl

theorem cell23_3954163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_3954163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954163 prefixEnd_3954163 := by exact prefixLift 3954163
  have htrace : WordTrace (prefixWord ++ tailWord_3954163) baseStart_3954163 baseEnd_3954163 := by
    simpa [prefixWord, tailWord_3954163, baseEnd_3954163] using wordTrace_append hprefix tailTrace_3954163
  have hstable : (prefixWord ++ tailWord_3954163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954163).length < 2 ^ (prefixWord ++ tailWord_3954163).sum := by decide
  have hdescent : baseEnd_3954163 < baseStart_3954163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954167 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 7, 2, 2]
def baseStart_3954167 : Nat := 118140960795 + 3954167 * 2 ^ 59
def prefixEnd_3954167 : Nat := 4983230072969 + 3 ^ 40 * 3954167 * 2
def baseEnd_3954167 : Nat := 2030388259146936037127623

theorem tailTrace_3954167 : CollatzResearch.WordTrace tailWord_3954167 prefixEnd_3954167 2030388259146936037127623 := by
  unfold tailWord_3954167
  simp only [CollatzResearch.WordTrace]
  refine ⟨144220318665735751803900755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96146879110490501202600503 144220318665735751803900755)
  ·
    refine ⟨216330477998603627705851133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144220318665735751803900755 216330477998603627705851133)
    ·
      refine ⟨81123929249476360389694175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216330477998603627705851133 81123929249476360389694175)
      ·
        refine ⟨121685893874214540584541263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81123929249476360389694175 121685893874214540584541263)
        ·
          refine ⟨182528840811321810876811895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121685893874214540584541263 182528840811321810876811895)
          ·
            refine ⟨273793261216982716315217843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182528840811321810876811895 273793261216982716315217843)
            ·
              refine ⟨410689891825474074472826765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273793261216982716315217843 410689891825474074472826765)
              ·
                refine ⟨154008709434552777927310037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410689891825474074472826765 154008709434552777927310037)
                ·
                  refine ⟨3609579127372330732671329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 154008709434552777927310037 3609579127372330732671329)
                  ·
                    refine ⟨2707184345529248049503497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3609579127372330732671329 2707184345529248049503497)
                    ·
                      refine ⟨2030388259146936037127623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2707184345529248049503497 2030388259146936037127623)
                      ·
                        rfl

theorem cell23_3954167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 2, 2].length) (baseStart_3954167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954167 prefixEnd_3954167 := by exact prefixLift 3954167
  have htrace : WordTrace (prefixWord ++ tailWord_3954167) baseStart_3954167 baseEnd_3954167 := by
    simpa [prefixWord, tailWord_3954167, baseEnd_3954167] using wordTrace_append hprefix tailTrace_3954167
  have hstable : (prefixWord ++ tailWord_3954167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954167).length < 2 ^ (prefixWord ++ tailWord_3954167).sum := by decide
  have hdescent : baseEnd_3954167 < baseStart_3954167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954173 : List Nat := [1, 4, 1, 1, 1, 15]
def baseStart_3954173 : Nat := 118140960795 + 3954173 * 2 ^ 59
def prefixEnd_3954173 : Nat := 4983230072969 + 3 ^ 40 * 3954173 * 2
def baseEnd_3954173 : Nat := 8355519917822481537665

theorem tailTrace_3954173 : CollatzResearch.WordTrace tailWord_3954173 prefixEnd_3954173 8355519917822481537665 := by
  unfold tailWord_3954173
  simp only [CollatzResearch.WordTrace]
  refine ⟨144220537503714014828619173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96147025002476009885746115 144220537503714014828619173)
  ·
    refine ⟨27041350781946377780366095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144220537503714014828619173 27041350781946377780366095)
    ·
      refine ⟨40562026172919566670549143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27041350781946377780366095 40562026172919566670549143)
      ·
        refine ⟨60843039259379350005823715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40562026172919566670549143 60843039259379350005823715)
        ·
          refine ⟨91264558889069025008735573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60843039259379350005823715 91264558889069025008735573)
          ·
            refine ⟨8355519917822481537665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 91264558889069025008735573 8355519917822481537665)
            ·
              rfl

theorem cell23_3954173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 15].length) (baseStart_3954173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954173 prefixEnd_3954173 := by exact prefixLift 3954173
  have htrace : WordTrace (prefixWord ++ tailWord_3954173) baseStart_3954173 baseEnd_3954173 := by
    simpa [prefixWord, tailWord_3954173, baseEnd_3954173] using wordTrace_append hprefix tailTrace_3954173
  have hstable : (prefixWord ++ tailWord_3954173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954173).length < 2 ^ (prefixWord ++ tailWord_3954173).sum := by decide
  have hdescent : baseEnd_3954173 < baseStart_3954173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954178 : List Nat := [3, 4, 1, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_3954178 : Nat := 118140960795 + 3954178 * 2 ^ 59
def prefixEnd_3954178 : Nat := 4983230072969 + 3 ^ 40 * 3954178 * 2
def baseEnd_3954178 : Nat := 2030393907434135494090073

theorem tailTrace_3954178 : CollatzResearch.WordTrace tailWord_3954178 prefixEnd_3954178 2030393907434135494090073 := by
  unfold tailWord_3954178
  simp only [CollatzResearch.WordTrace]
  refine ⟨36055179967173975170637797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96147146579130600455034125 36055179967173975170637797)
  ·
    refine ⟨6760346243845120344494587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36055179967173975170637797 6760346243845120344494587)
    ·
      refine ⟨10140519365767680516741881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6760346243845120344494587 10140519365767680516741881)
      ·
        refine ⟨7605389524325760387556411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10140519365767680516741881 7605389524325760387556411)
        ·
          refine ⟨11408084286488640581334617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7605389524325760387556411 11408084286488640581334617)
          ·
            refine ⟨8556063214866480436000963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11408084286488640581334617 8556063214866480436000963)
            ·
              refine ⟨12834094822299720654001445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8556063214866480436000963 12834094822299720654001445)
              ·
                refine ⟨2406392779181197622625271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12834094822299720654001445 2406392779181197622625271)
                ·
                  refine ⟨3609589168771796433937907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2406392779181197622625271 3609589168771796433937907)
                  ·
                    refine ⟨5414383753157694650906861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3609589168771796433937907 5414383753157694650906861)
                    ·
                      refine ⟨2030393907434135494090073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5414383753157694650906861 2030393907434135494090073)
                      ·
                        rfl

theorem cell23_3954178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_3954178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954178 prefixEnd_3954178 := by exact prefixLift 3954178
  have htrace : WordTrace (prefixWord ++ tailWord_3954178) baseStart_3954178 baseEnd_3954178 := by
    simpa [prefixWord, tailWord_3954178, baseEnd_3954178] using wordTrace_append hprefix tailTrace_3954178
  have hstable : (prefixWord ++ tailWord_3954178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954178).length < 2 ^ (prefixWord ++ tailWord_3954178).sum := by decide
  have hdescent : baseEnd_3954178 < baseStart_3954178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954197 : List Nat := [1, 3, 2, 1, 3, 3, 2, 1, 1, 2, 4]
def baseStart_3954197 : Nat := 118140960795 + 3954197 * 2 ^ 59
def prefixEnd_3954197 : Nat := 4983230072969 + 3 ^ 40 * 3954197 * 2
def baseEnd_3954197 : Nat := 2030403663566570919752485

theorem tailTrace_3954197 : CollatzResearch.WordTrace tailWord_3954197 prefixEnd_3954197 2030403663566570919752485 := by
  unfold tailWord_3954197
  simp only [CollatzResearch.WordTrace]
  refine ⟨144221412855627066927492845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96147608570418044618328563 144221412855627066927492845)
  ·
    refine ⟨54083029820860150097809817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144221412855627066927492845 54083029820860150097809817)
    ·
      refine ⟨40562272365645112573357363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54083029820860150097809817 40562272365645112573357363)
      ·
        refine ⟨60843408548467668860036045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40562272365645112573357363 60843408548467668860036045)
        ·
          refine ⟨22816278205675375822513517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60843408548467668860036045 22816278205675375822513517)
          ·
            refine ⟨8556104327128265933442569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22816278205675375822513517 8556104327128265933442569)
            ·
              refine ⟨6417078245346199450081927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8556104327128265933442569 6417078245346199450081927)
              ·
                refine ⟨9625617368019299175122891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6417078245346199450081927 9625617368019299175122891)
                ·
                  refine ⟨14438426052028948762684337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9625617368019299175122891 14438426052028948762684337)
                  ·
                    refine ⟨10828819539021711572013253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14438426052028948762684337 10828819539021711572013253)
                    ·
                      refine ⟨2030403663566570919752485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10828819539021711572013253 2030403663566570919752485)
                      ·
                        rfl

theorem cell23_3954197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_3954197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954197 prefixEnd_3954197 := by exact prefixLift 3954197
  have htrace : WordTrace (prefixWord ++ tailWord_3954197) baseStart_3954197 baseEnd_3954197 := by
    simpa [prefixWord, tailWord_3954197, baseEnd_3954197] using wordTrace_append hprefix tailTrace_3954197
  have hstable : (prefixWord ++ tailWord_3954197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954197).length < 2 ^ (prefixWord ++ tailWord_3954197).sum := by decide
  have hdescent : baseEnd_3954197 < baseStart_3954197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954218 : List Nat := [3, 1, 4, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_3954218 : Nat := 118140960795 + 3954218 * 2 ^ 59
def prefixEnd_3954218 : Nat := 4983230072969 + 3 ^ 40 * 3954218 * 2
def baseEnd_3954218 : Nat := 2030414446660315337589889

theorem tailTrace_3954218 : CollatzResearch.WordTrace tailWord_3954218 prefixEnd_3954218 2030414446660315337589889 := by
  unfold tailWord_3954218
  simp only [CollatzResearch.WordTrace]
  refine ⟨36055544697137746878501827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96148119192367325009338205 36055544697137746878501827)
  ·
    refine ⟨54083317045706620317752741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36055544697137746878501827 54083317045706620317752741)
    ·
      refine ⟨10140621946069991309578639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54083317045706620317752741 10140621946069991309578639)
      ·
        refine ⟨15210932919104986964367959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10140621946069991309578639 15210932919104986964367959)
        ·
          refine ⟨22816399378657480446551939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15210932919104986964367959 22816399378657480446551939)
          ·
            refine ⟨34224599067986220669827909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22816399378657480446551939 34224599067986220669827909)
            ·
              refine ⟨6417112325247416375592733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34224599067986220669827909 6417112325247416375592733)
              ·
                refine ⟨2406417121967781140847275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6417112325247416375592733 2406417121967781140847275)
                ·
                  refine ⟨3609625682951671711270913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2406417121967781140847275 3609625682951671711270913)
                  ·
                    refine ⟨2707219262213753783453185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3609625682951671711270913 2707219262213753783453185)
                    ·
                      refine ⟨2030414446660315337589889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2707219262213753783453185 2030414446660315337589889)
                      ·
                        rfl

theorem cell23_3954218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_3954218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954218 prefixEnd_3954218 := by exact prefixLift 3954218
  have htrace : WordTrace (prefixWord ++ tailWord_3954218) baseStart_3954218 baseEnd_3954218 := by
    simpa [prefixWord, tailWord_3954218, baseEnd_3954218] using wordTrace_append hprefix tailTrace_3954218
  have hstable : (prefixWord ++ tailWord_3954218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954218).length < 2 ^ (prefixWord ++ tailWord_3954218).sum := by decide
  have hdescent : baseEnd_3954218 < baseStart_3954218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954250 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 2, 6]
def baseStart_3954250 : Nat := 118140960795 + 3954250 * 2 ^ 59
def prefixEnd_3954250 : Nat := 4983230072969 + 3 ^ 40 * 3954250 * 2
def baseEnd_3954250 : Nat := 676810292680419737463247

theorem tailTrace_3954250 : CollatzResearch.WordTrace tailWord_3954250 prefixEnd_3954250 676810292680419737463247 := by
  unfold tailWord_3954250
  simp only [CollatzResearch.WordTrace]
  refine ⟨36055836481108764244793051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96148897282956704652781469 36055836481108764244793051)
  ·
    refine ⟨54083754721663146367189577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36055836481108764244793051 54083754721663146367189577)
    ·
      refine ⟨40562816041247359775392183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54083754721663146367189577 40562816041247359775392183)
      ·
        refine ⟨60844224061871039663088275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40562816041247359775392183 60844224061871039663088275)
        ·
          refine ⟨91266336092806559494632413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60844224061871039663088275 91266336092806559494632413)
          ·
            refine ⟨34224876034802459810487155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91266336092806559494632413 34224876034802459810487155)
            ·
              refine ⟨51337314052203689715730733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34224876034802459810487155 51337314052203689715730733)
              ·
                refine ⟨19251492769576383643399025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51337314052203689715730733 19251492769576383643399025)
                ·
                  refine ⟨14438619577182287732549269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19251492769576383643399025 14438619577182287732549269)
                  ·
                    refine ⟨676810292680419737463247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14438619577182287732549269 676810292680419737463247)
                    ·
                      rfl

theorem cell23_3954250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_3954250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954250 prefixEnd_3954250 := by exact prefixLift 3954250
  have htrace : WordTrace (prefixWord ++ tailWord_3954250) baseStart_3954250 baseEnd_3954250 := by
    simpa [prefixWord, tailWord_3954250, baseEnd_3954250] using wordTrace_append hprefix tailTrace_3954250
  have hstable : (prefixWord ++ tailWord_3954250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954250).length < 2 ^ (prefixWord ++ tailWord_3954250).sum := by decide
  have hdescent : baseEnd_3954250 < baseStart_3954250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954269 : List Nat := [1, 4, 4, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_3954269 : Nat := 118140960795 + 3954269 * 2 ^ 59
def prefixEnd_3954269 : Nat := 4983230072969 + 3 ^ 40 * 3954269 * 2
def baseEnd_3954269 : Nat := 2030440634173694638052155

theorem tailTrace_3954269 : CollatzResearch.WordTrace tailWord_3954269 prefixEnd_3954269 2030440634173694638052155 := by
  unfold tailWord_3954269
  simp only [CollatzResearch.WordTrace]
  refine ⟨144224038911366223224113861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96149359274244148816075907 144224038911366223224113861)
  ·
    refine ⟨27042007295881166854521349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144224038911366223224113861 27042007295881166854521349)
    ·
      refine ⟨5070376367977718785222753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27042007295881166854521349 5070376367977718785222753)
      ·
        refine ⟨3802782275983289088917065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5070376367977718785222753 3802782275983289088917065)
        ·
          refine ⟨2852086706987466816687799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3802782275983289088917065 2852086706987466816687799)
          ·
            refine ⟨4278130060481200225031699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2852086706987466816687799 4278130060481200225031699)
            ·
              refine ⟨6417195090721800337547549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4278130060481200225031699 6417195090721800337547549)
              ·
                refine ⟨2406448159020675126580331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6417195090721800337547549 2406448159020675126580331)
                ·
                  refine ⟨3609672238531012689870497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2406448159020675126580331 3609672238531012689870497)
                  ·
                    refine ⟨2707254178898259517402873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3609672238531012689870497 2707254178898259517402873)
                    ·
                      refine ⟨2030440634173694638052155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2707254178898259517402873 2030440634173694638052155)
                      ·
                        rfl

theorem cell23_3954269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_3954269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954269 prefixEnd_3954269 := by exact prefixLift 3954269
  have htrace : WordTrace (prefixWord ++ tailWord_3954269) baseStart_3954269 baseEnd_3954269 := by
    simpa [prefixWord, tailWord_3954269, baseEnd_3954269] using wordTrace_append hprefix tailTrace_3954269
  have hstable : (prefixWord ++ tailWord_3954269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954269).length < 2 ^ (prefixWord ++ tailWord_3954269).sum := by decide
  have hdescent : baseEnd_3954269 < baseStart_3954269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954277 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 2, 1, 5]
def baseStart_3954277 : Nat := 118140960795 + 3954277 * 2 ^ 59
def prefixEnd_3954277 : Nat := 4983230072969 + 3 ^ 40 * 3954277 * 2
def baseEnd_3954277 : Nat := 2030444742018930606752117

theorem tailTrace_3954277 : CollatzResearch.WordTrace tailWord_3954277 prefixEnd_3954277 2030444742018930606752117 := by
  unfold tailWord_3954277
  simp only [CollatzResearch.WordTrace]
  refine ⟨144224330695337240590405085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96149553796891493726936723 144224330695337240590405085)
  ·
    refine ⟨54084124010751465221401907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144224330695337240590405085 54084124010751465221401907)
    ·
      refine ⟨81126186016127197832102861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54084124010751465221401907 81126186016127197832102861)
      ·
        refine ⟨30422319756047699187038573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81126186016127197832102861 30422319756047699187038573)
        ·
          refine ⟨11408369908517887195139465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30422319756047699187038573 11408369908517887195139465)
          ·
            refine ⟨8556277431388415396354599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11408369908517887195139465 8556277431388415396354599)
            ·
              refine ⟨12834416147082623094531899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8556277431388415396354599 12834416147082623094531899)
              ·
                refine ⟨19251624220623934641797849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12834416147082623094531899 19251624220623934641797849)
                ·
                  refine ⟨14438718165467950981348387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19251624220623934641797849 14438718165467950981348387)
                  ·
                    refine ⟨21658077248201926472022581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14438718165467950981348387 21658077248201926472022581)
                    ·
                      refine ⟨2030444742018930606752117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21658077248201926472022581 2030444742018930606752117)
                      ·
                        rfl

theorem cell23_3954277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_3954277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954277 prefixEnd_3954277 := by exact prefixLift 3954277
  have htrace : WordTrace (prefixWord ++ tailWord_3954277) baseStart_3954277 baseEnd_3954277 := by
    simpa [prefixWord, tailWord_3954277, baseEnd_3954277] using wordTrace_append hprefix tailTrace_3954277
  have hstable : (prefixWord ++ tailWord_3954277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954277).length < 2 ^ (prefixWord ++ tailWord_3954277).sum := by decide
  have hdescent : baseEnd_3954277 < baseStart_3954277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954308 : List Nat := [2, 3, 2, 1, 4, 1, 1, 3, 2, 2, 2]
def baseStart_3954308 : Nat := 118140960795 + 3954308 * 2 ^ 59
def prefixEnd_3954308 : Nat := 4983230072969 + 3 ^ 40 * 3954308 * 2
def baseEnd_3954308 : Nat := 2030460659919219985464475

theorem tailTrace_3954308 : CollatzResearch.WordTrace tailWord_3954308 prefixEnd_3954308 2030460659919219985464475 := by
  unfold tailWord_3954308
  simp only [CollatzResearch.WordTrace]
  refine ⟨72112730679112466442391789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96150307572149955256522385 72112730679112466442391789)
  ·
    refine ⟨27042274004667174915896921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72112730679112466442391789 27042274004667174915896921)
    ·
      refine ⟨20281705503500381186922691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27042274004667174915896921 20281705503500381186922691)
      ·
        refine ⟨30422558255250571780384037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20281705503500381186922691 30422558255250571780384037)
        ·
          refine ⟨5704229672859482208822007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30422558255250571780384037 5704229672859482208822007)
          ·
            refine ⟨8556344509289223313233011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5704229672859482208822007 8556344509289223313233011)
            ·
              refine ⟨12834516763933834969849517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8556344509289223313233011 12834516763933834969849517)
              ·
                refine ⟨4812943786475188113693569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12834516763933834969849517 4812943786475188113693569)
                ·
                  refine ⟨3609707839856391085270177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4812943786475188113693569 3609707839856391085270177)
                  ·
                    refine ⟨2707280879892293313952633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3609707839856391085270177 2707280879892293313952633)
                    ·
                      refine ⟨2030460659919219985464475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2707280879892293313952633 2030460659919219985464475)
                      ·
                        rfl

theorem cell23_3954308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_3954308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954308 prefixEnd_3954308 := by exact prefixLift 3954308
  have htrace : WordTrace (prefixWord ++ tailWord_3954308) baseStart_3954308 baseEnd_3954308 := by
    simpa [prefixWord, tailWord_3954308, baseEnd_3954308] using wordTrace_append hprefix tailTrace_3954308
  have hstable : (prefixWord ++ tailWord_3954308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954308).length < 2 ^ (prefixWord ++ tailWord_3954308).sum := by decide
  have hdescent : baseEnd_3954308 < baseStart_3954308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954327 : List Nat := [1, 1, 3, 3, 2, 2, 1, 3, 2, 5]
def baseStart_3954327 : Nat := 118140960795 + 3954327 * 2 ^ 59
def prefixEnd_3954327 : Nat := 4983230072969 + 3 ^ 40 * 3954327 * 2
def baseEnd_3954327 : Nat := 676823472017218470375629

theorem tailTrace_3954327 : CollatzResearch.WordTrace tailWord_3954327 prefixEnd_3954327 676823472017218470375629 := by
  unfold tailWord_3954327
  simp only [CollatzResearch.WordTrace]
  refine ⟨144226154345156099129725235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96150769563437399419816823 144226154345156099129725235)
  ·
    refine ⟨216339231517734148694587853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144226154345156099129725235 216339231517734148694587853)
    ·
      refine ⟨81127211819150305760470445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216339231517734148694587853 81127211819150305760470445)
      ·
        refine ⟨30422704432181364660176417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81127211819150305760470445 30422704432181364660176417)
        ·
          refine ⟨22817028324136023495132313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30422704432181364660176417 22817028324136023495132313)
          ·
            refine ⟨17112771243102017621349235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22817028324136023495132313 17112771243102017621349235)
            ·
              refine ⟨25669156864653026432023853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17112771243102017621349235 25669156864653026432023853)
              ·
                refine ⟨9625933824244884912008945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25669156864653026432023853 9625933824244884912008945)
                ·
                  refine ⟨7219450368183663684006709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9625933824244884912008945 7219450368183663684006709)
                  ·
                    refine ⟨676823472017218470375629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7219450368183663684006709 676823472017218470375629)
                    ·
                      rfl

theorem cell23_3954327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_3954327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954327 prefixEnd_3954327 := by exact prefixLift 3954327
  have htrace : WordTrace (prefixWord ++ tailWord_3954327) baseStart_3954327 baseEnd_3954327 := by
    simpa [prefixWord, tailWord_3954327, baseEnd_3954327] using wordTrace_append hprefix tailTrace_3954327
  have hstable : (prefixWord ++ tailWord_3954327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954327).length < 2 ^ (prefixWord ++ tailWord_3954327).sum := by decide
  have hdescent : baseEnd_3954327 < baseStart_3954327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954337 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3954337 : Nat := 118140960795 + 3954337 * 2 ^ 59
def prefixEnd_3954337 : Nat := 4983230072969 + 3 ^ 40 * 3954337 * 2
def baseEnd_3954337 : Nat := 2030475550858200372001841

theorem tailTrace_3954337 : CollatzResearch.WordTrace tailWord_3954337 prefixEnd_3954337 2030475550858200372001841 := by
  unfold tailWord_3954337
  simp only [CollatzResearch.WordTrace]
  refine ⟨144226519075119870837589265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96151012716746580558392843 144226519075119870837589265)
  ·
    refine ⟨108169889306339903128191949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144226519075119870837589265 108169889306339903128191949)
    ·
      refine ⟨40563708489877463673071981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108169889306339903128191949 40563708489877463673071981)
      ·
        refine ⟨15211390683704048877401993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40563708489877463673071981 15211390683704048877401993)
        ·
          refine ⟨11408543012778036658051495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15211390683704048877401993 11408543012778036658051495)
          ·
            refine ⟨17112814519167054987077243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11408543012778036658051495 17112814519167054987077243)
            ·
              refine ⟨25669221778750582480615865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17112814519167054987077243 25669221778750582480615865)
              ·
                refine ⟨19251916334062936860461899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25669221778750582480615865 19251916334062936860461899)
                ·
                  refine ⟨28877874501094405290692849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19251916334062936860461899 28877874501094405290692849)
                  ·
                    refine ⟨21658405875820803968019637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28877874501094405290692849 21658405875820803968019637)
                    ·
                      refine ⟨2030475550858200372001841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21658405875820803968019637 2030475550858200372001841)
                      ·
                        rfl

theorem cell23_3954337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3954337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954337 prefixEnd_3954337 := by exact prefixLift 3954337
  have htrace : WordTrace (prefixWord ++ tailWord_3954337) baseStart_3954337 baseEnd_3954337 := by
    simpa [prefixWord, tailWord_3954337, baseEnd_3954337] using wordTrace_append hprefix tailTrace_3954337
  have hstable : (prefixWord ++ tailWord_3954337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954337).length < 2 ^ (prefixWord ++ tailWord_3954337).sum := by decide
  have hdescent : baseEnd_3954337 < baseStart_3954337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954364 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 1, 6, 2]
def baseStart_3954364 : Nat := 118140960795 + 3954364 * 2 ^ 59
def prefixEnd_3954364 : Nat := 4983230072969 + 3 ^ 40 * 3954364 * 2
def baseEnd_3954364 : Nat := 2030489414835871766364217

theorem tailTrace_3954364 : CollatzResearch.WordTrace tailWord_3954364 prefixEnd_3954364 2030489414835871766364217 := by
  unfold tailWord_3954364
  simp only [CollatzResearch.WordTrace]
  refine ⟨72113751923011027224411073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96151669230681369632548097 72113751923011027224411073)
  ·
    refine ⟨54085313942258270418308305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72113751923011027224411073 54085313942258270418308305)
    ·
      refine ⟨40563985456693702813731229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54085313942258270418308305 40563985456693702813731229)
      ·
        refine ⟨15211494546260138555149211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40563985456693702813731229 15211494546260138555149211)
        ·
          refine ⟨22817241819390207832723817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15211494546260138555149211 22817241819390207832723817)
          ·
            refine ⟨17112931364542655874542863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22817241819390207832723817 17112931364542655874542863)
            ·
              refine ⟨25669397046813983811814295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17112931364542655874542863 25669397046813983811814295)
              ·
                refine ⟨38504095570220975717721443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25669397046813983811814295 38504095570220975717721443)
                ·
                  refine ⟨57756143355331463576582165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38504095570220975717721443 57756143355331463576582165)
                  ·
                    refine ⟨2707319219781162355152289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57756143355331463576582165 2707319219781162355152289)
                    ·
                      refine ⟨2030489414835871766364217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2707319219781162355152289 2030489414835871766364217)
                      ·
                        rfl

theorem cell23_3954364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_3954364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954364 prefixEnd_3954364 := by exact prefixLift 3954364
  have htrace : WordTrace (prefixWord ++ tailWord_3954364) baseStart_3954364 baseEnd_3954364 := by
    simpa [prefixWord, tailWord_3954364, baseEnd_3954364] using wordTrace_append hprefix tailTrace_3954364
  have hstable : (prefixWord ++ tailWord_3954364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954364).length < 2 ^ (prefixWord ++ tailWord_3954364).sum := by decide
  have hdescent : baseEnd_3954364 < baseStart_3954364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954367 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 3]
def baseStart_3954367 : Nat := 118140960795 + 3954367 * 2 ^ 59
def prefixEnd_3954367 : Nat := 4983230072969 + 3 ^ 40 * 3954367 * 2
def baseEnd_3954367 : Nat := 2030490955277835254626703

theorem tailTrace_3954367 : CollatzResearch.WordTrace tailWord_3954367 prefixEnd_3954367 2030490955277835254626703 := by
  unfold tailWord_3954367
  simp only [CollatzResearch.WordTrace]
  refine ⟨144227613265011185961181355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96151742176674123974120903 144227613265011185961181355)
  ·
    refine ⟨216341419897516778941772033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144227613265011185961181355 216341419897516778941772033)
    ·
      refine ⟨162256064923137584206329025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216341419897516778941772033 162256064923137584206329025)
      ·
        refine ⟨121692048692353188154746769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162256064923137584206329025 121692048692353188154746769)
        ·
          refine ⟨91269036519264891116060077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121692048692353188154746769 91269036519264891116060077)
          ·
            refine ⟨34225888694724334168522529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91269036519264891116060077 34225888694724334168522529)
            ·
              refine ⟨25669416521043250626391897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34225888694724334168522529 25669416521043250626391897)
              ·
                refine ⟨19252062390782437969793923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25669416521043250626391897 19252062390782437969793923)
                ·
                  refine ⟨28878093586173656954690885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19252062390782437969793923 28878093586173656954690885)
                  ·
                    refine ⟨5414642547407560679004541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28878093586173656954690885 5414642547407560679004541)
                    ·
                      refine ⟨2030490955277835254626703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5414642547407560679004541 2030490955277835254626703)
                      ·
                        rfl

theorem cell23_3954367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_3954367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954367 prefixEnd_3954367 := by exact prefixLift 3954367
  have htrace : WordTrace (prefixWord ++ tailWord_3954367) baseStart_3954367 baseEnd_3954367 := by
    simpa [prefixWord, tailWord_3954367, baseEnd_3954367] using wordTrace_append hprefix tailTrace_3954367
  have hstable : (prefixWord ++ tailWord_3954367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954367).length < 2 ^ (prefixWord ++ tailWord_3954367).sum := by decide
  have hdescent : baseEnd_3954367 < baseStart_3954367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954381 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3954381 : Nat := 118140960795 + 3954381 * 2 ^ 59
def prefixEnd_3954381 : Nat := 4983230072969 + 3 ^ 40 * 3954381 * 2
def baseEnd_3954381 : Nat := 2030498144006998199851639

theorem tailTrace_3954381 : CollatzResearch.WordTrace tailWord_3954381 prefixEnd_3954381 2030498144006998199851639 := by
  unfold tailWord_3954381
  simp only [CollatzResearch.WordTrace]
  refine ⟨144228123886960466352190997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96152082591306977568127331 144228123886960466352190997)
  ·
    refine ⟨6760693307201271860258953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 144228123886960466352190997 6760693307201271860258953)
    ·
      refine ⟨5070519980400953895194215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6760693307201271860258953 5070519980400953895194215)
      ·
        refine ⟨7605779970601430842791323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5070519980400953895194215 7605779970601430842791323)
        ·
          refine ⟨11408669955902146264186985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7605779970601430842791323 11408669955902146264186985)
          ·
            refine ⟨8556502466926609698140239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11408669955902146264186985 8556502466926609698140239)
            ·
              refine ⟨12834753700389914547210359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8556502466926609698140239 12834753700389914547210359)
              ·
                refine ⟨19252130550584871820815539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12834753700389914547210359 19252130550584871820815539)
                ·
                  refine ⟨28878195825877307731223309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19252130550584871820815539 28878195825877307731223309)
                  ·
                    refine ⟨10829323434703990399208741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28878195825877307731223309 10829323434703990399208741)
                    ·
                      refine ⟨2030498144006998199851639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10829323434703990399208741 2030498144006998199851639)
                      ·
                        rfl

theorem cell23_3954381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3954381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954381 prefixEnd_3954381 := by exact prefixLift 3954381
  have htrace : WordTrace (prefixWord ++ tailWord_3954381) baseStart_3954381 baseEnd_3954381 := by
    simpa [prefixWord, tailWord_3954381, baseEnd_3954381] using wordTrace_append hprefix tailTrace_3954381
  have hstable : (prefixWord ++ tailWord_3954381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954381).length < 2 ^ (prefixWord ++ tailWord_3954381).sum := by decide
  have hdescent : baseEnd_3954381 < baseStart_3954381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954391 : List Nat := [1, 1, 3, 2, 1, 3, 4, 3, 1, 4]
def baseStart_3954391 : Nat := 118140960795 + 3954391 * 2 ^ 59
def prefixEnd_3954391 : Nat := 4983230072969 + 3 ^ 40 * 3954391 * 2
def baseEnd_3954391 : Nat := 676834426271181053575531

theorem tailTrace_3954391 : CollatzResearch.WordTrace tailWord_3954391 prefixEnd_3954391 676834426271181053575531 := by
  unfold tailWord_3954391
  simp only [CollatzResearch.WordTrace]
  refine ⟨144228488616924238060055027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96152325744616158706703351 144228488616924238060055027)
  ·
    refine ⟨216342732925386357090082541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144228488616924238060055027 216342732925386357090082541)
    ·
      refine ⟨81128524847019883908780953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216342732925386357090082541 81128524847019883908780953)
      ·
        refine ⟨60846393635264912931585715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81128524847019883908780953 60846393635264912931585715)
        ·
          refine ⟨91269590452897369397378573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60846393635264912931585715 91269590452897369397378573)
          ·
            refine ⟨34226096419836513524016965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91269590452897369397378573 34226096419836513524016965)
            ·
              refine ⟨6417393078719346285753181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34226096419836513524016965 6417393078719346285753181)
              ·
                refine ⟨2406522404519754857157443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6417393078719346285753181 2406522404519754857157443)
                ·
                  refine ⟨3609783606779632285736165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2406522404519754857157443 3609783606779632285736165)
                  ·
                    refine ⟨676834426271181053575531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3609783606779632285736165 676834426271181053575531)
                    ·
                      rfl

theorem cell23_3954391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 1, 4].length) (baseStart_3954391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954391 prefixEnd_3954391 := by exact prefixLift 3954391
  have htrace : WordTrace (prefixWord ++ tailWord_3954391) baseStart_3954391 baseEnd_3954391 := by
    simpa [prefixWord, tailWord_3954391, baseEnd_3954391] using wordTrace_append hprefix tailTrace_3954391
  have hstable : (prefixWord ++ tailWord_3954391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954391).length < 2 ^ (prefixWord ++ tailWord_3954391).sum := by decide
  have hdescent : baseEnd_3954391 < baseStart_3954391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954424 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 6, 3, 2]
def baseStart_3954424 : Nat := 118140960795 + 3954424 * 2 ^ 59
def prefixEnd_3954424 : Nat := 4983230072969 + 3 ^ 40 * 3954424 * 2
def baseEnd_3954424 : Nat := 2030520223675141531613941

theorem tailTrace_3954424 : CollatzResearch.WordTrace tailWord_3954424 prefixEnd_3954424 2030520223675141531613941 := by
  unfold tailWord_3954424
  simp only [CollatzResearch.WordTrace]
  refine ⟨72114846112902342348003163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96153128150536456464004217 72114846112902342348003163)
  ·
    refine ⟨108172269169353513522004745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72114846112902342348003163 108172269169353513522004745)
    ·
      refine ⟨81129201877015135141503559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108172269169353513522004745 81129201877015135141503559)
      ·
        refine ⟨121693802815522702712255339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81129201877015135141503559 121693802815522702712255339)
        ·
          refine ⟨182540704223284054068383009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121693802815522702712255339 182540704223284054068383009)
          ·
            refine ⟨136905528167463040551287257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182540704223284054068383009 136905528167463040551287257)
            ·
              refine ⟨102679146125597280413465443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136905528167463040551287257 102679146125597280413465443)
              ·
                refine ⟨154018719188395920620198165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102679146125597280413465443 154018719188395920620198165)
                ·
                  refine ⟨7219627461956058779071789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154018719188395920620198165 7219627461956058779071789)
                  ·
                    refine ⟨2707360298233522042151921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7219627461956058779071789 2707360298233522042151921)
                    ·
                      refine ⟨2030520223675141531613941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2707360298233522042151921 2030520223675141531613941)
                      ·
                        rfl

theorem cell23_3954424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 6, 3, 2].length) (baseStart_3954424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954424 prefixEnd_3954424 := by exact prefixLift 3954424
  have htrace : WordTrace (prefixWord ++ tailWord_3954424) baseStart_3954424 baseEnd_3954424 := by
    simpa [prefixWord, tailWord_3954424, baseEnd_3954424] using wordTrace_append hprefix tailTrace_3954424
  have hstable : (prefixWord ++ tailWord_3954424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954424).length < 2 ^ (prefixWord ++ tailWord_3954424).sum := by decide
  have hdescent : baseEnd_3954424 < baseStart_3954424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954457 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 1, 8, 3]
def baseStart_3954457 : Nat := 118140960795 + 3954457 * 2 ^ 59
def prefixEnd_3954457 : Nat := 4983230072969 + 3 ^ 40 * 3954457 * 2
def baseEnd_3954457 : Nat := 2030537168536739902501289

theorem tailTrace_3954457 : CollatzResearch.WordTrace tailWord_3954457 prefixEnd_3954457 2030537168536739902501289 := by
  unfold tailWord_3954457
  simp only [CollatzResearch.WordTrace]
  refine ⟨144230895834685131331957625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96153930556456754221305083 144230895834685131331957625)
  ·
    refine ⟨108173171876013848498968219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144230895834685131331957625 108173171876013848498968219)
    ·
      refine ⟨162259757814020772748452329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108173171876013848498968219 162259757814020772748452329)
      ·
        refine ⟨121694818360515579561339247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162259757814020772748452329 121694818360515579561339247)
        ·
          refine ⟨182542227540773369342008871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121694818360515579561339247 182542227540773369342008871)
          ·
            refine ⟨273813341311160054013013307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182542227540773369342008871 273813341311160054013013307)
            ·
              refine ⟨410720011966740081019519961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273813341311160054013013307 410720011966740081019519961)
              ·
                refine ⟨308040008975055060764639971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410720011966740081019519961 308040008975055060764639971)
                ·
                  refine ⟨462060013462582591146959957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308040008975055060764639971 462060013462582591146959957)
                  ·
                    refine ⟨5414765782764639740003437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 462060013462582591146959957 5414765782764639740003437)
                    ·
                      refine ⟨2030537168536739902501289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5414765782764639740003437 2030537168536739902501289)
                      ·
                        rfl

theorem cell23_3954457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_3954457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954457 prefixEnd_3954457 := by exact prefixLift 3954457
  have htrace : WordTrace (prefixWord ++ tailWord_3954457) baseStart_3954457 baseEnd_3954457 := by
    simpa [prefixWord, tailWord_3954457, baseEnd_3954457] using wordTrace_append hprefix tailTrace_3954457
  have hstable : (prefixWord ++ tailWord_3954457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954457).length < 2 ^ (prefixWord ++ tailWord_3954457).sum := by decide
  have hdescent : baseEnd_3954457 < baseStart_3954457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954464 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 4, 4]
def baseStart_3954464 : Nat := 118140960795 + 3954464 * 2 ^ 59
def prefixEnd_3954464 : Nat := 4983230072969 + 3 ^ 40 * 3954464 * 2
def baseEnd_3954464 : Nat := 676846920967107125037919

theorem tailTrace_3954464 : CollatzResearch.WordTrace tailWord_3954464 prefixEnd_3954464 676846920967107125037919 := by
  unfold tailWord_3954464
  simp only [CollatzResearch.WordTrace]
  refine ⟨72115575572829885763731223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96154100763773181018308297 72115575572829885763731223)
  ·
    refine ⟨108173363359244828645596835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72115575572829885763731223 108173363359244828645596835)
    ·
      refine ⟨162260045038867242968395253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108173363359244828645596835 162260045038867242968395253)
      ·
        refine ⟨15211879222393804028287055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162260045038867242968395253 15211879222393804028287055)
        ·
          refine ⟨22817818833590706042430583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15211879222393804028287055 22817818833590706042430583)
          ·
            refine ⟨34226728250386059063645875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22817818833590706042430583 34226728250386059063645875)
            ·
              refine ⟨51340092375579088595468813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34226728250386059063645875 51340092375579088595468813)
              ·
                refine ⟨19252534640842158223300805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51340092375579088595468813 19252534640842158223300805)
                ·
                  refine ⟨3609850245157904666868901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19252534640842158223300805 3609850245157904666868901)
                  ·
                    refine ⟨676846920967107125037919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3609850245157904666868901 676846920967107125037919)
                    ·
                      rfl

theorem cell23_3954464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 4, 4].length) (baseStart_3954464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954464 prefixEnd_3954464 := by exact prefixLift 3954464
  have htrace : WordTrace (prefixWord ++ tailWord_3954464) baseStart_3954464 baseEnd_3954464 := by
    simpa [prefixWord, tailWord_3954464, baseEnd_3954464] using wordTrace_append hprefix tailTrace_3954464
  have hstable : (prefixWord ++ tailWord_3954464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954464).length < 2 ^ (prefixWord ++ tailWord_3954464).sum := by decide
  have hdescent : baseEnd_3954464 < baseStart_3954464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954465 : List Nat := [1, 2, 3, 2, 1, 4, 3, 2, 1, 1, 3]
def baseStart_3954465 : Nat := 118140960795 + 3954465 * 2 ^ 59
def prefixEnd_3954465 : Nat := 4983230072969 + 3 ^ 40 * 3954465 * 2
def baseEnd_3954465 : Nat := 2030541276381975871201253

theorem tailTrace_3954465 : CollatzResearch.WordTrace tailWord_3954465 prefixEnd_3954465 2030541276381975871201253 := by
  unfold tailWord_3954465
  simp only [CollatzResearch.WordTrace]
  refine ⟨144231187618656148698248849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96154125079104099132165899 144231187618656148698248849)
  ·
    refine ⟨108173390713992111523686637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144231187618656148698248849 108173390713992111523686637)
    ·
      refine ⟨40565021517747041821382489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108173390713992111523686637 40565021517747041821382489)
      ·
        refine ⟨30423766138310281366036867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40565021517747041821382489 30423766138310281366036867)
        ·
          refine ⟨45635649207465422049055301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30423766138310281366036867 45635649207465422049055301)
          ·
            refine ⟨8556684226399766634197869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45635649207465422049055301 8556684226399766634197869)
            ·
              refine ⟨3208756584899912487824201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8556684226399766634197869 3208756584899912487824201)
              ·
                refine ⟨2406567438674934365868151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3208756584899912487824201 2406567438674934365868151)
                ·
                  refine ⟨3609851158012401548802227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2406567438674934365868151 3609851158012401548802227)
                  ·
                    refine ⟨5414776737018602323203341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3609851158012401548802227 5414776737018602323203341)
                    ·
                      refine ⟨2030541276381975871201253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5414776737018602323203341 2030541276381975871201253)
                      ·
                        rfl

theorem cell23_3954465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_3954465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954465 prefixEnd_3954465 := by exact prefixLift 3954465
  have htrace : WordTrace (prefixWord ++ tailWord_3954465) baseStart_3954465 baseEnd_3954465 := by
    simpa [prefixWord, tailWord_3954465, baseEnd_3954465] using wordTrace_append hprefix tailTrace_3954465
  have hstable : (prefixWord ++ tailWord_3954465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954465).length < 2 ^ (prefixWord ++ tailWord_3954465).sum := by decide
  have hdescent : baseEnd_3954465 < baseStart_3954465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954467 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 6]
def baseStart_3954467 : Nat := 118140960795 + 3954467 * 2 ^ 59
def prefixEnd_3954467 : Nat := 4983230072969 + 3 ^ 40 * 3954467 * 2
def baseEnd_3954467 : Nat := 2030542303343284863376243

theorem tailTrace_3954467 : CollatzResearch.WordTrace tailWord_3954467 prefixEnd_3954467 2030542303343284863376243 := by
  unfold tailWord_3954467
  simp only [CollatzResearch.WordTrace]
  refine ⟨144231260564648903039821655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96154173709765935359881103 144231260564648903039821655)
  ·
    refine ⟨216346890846973354559732483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144231260564648903039821655 216346890846973354559732483)
    ·
      refine ⟨324520336270460031839598725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216346890846973354559732483 324520336270460031839598725)
      ·
        refine ⟨60847563050711255969924761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324520336270460031839598725 60847563050711255969924761)
        ·
          refine ⟨45635672288033441977443571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60847563050711255969924761 45635672288033441977443571)
          ·
            refine ⟨68453508432050162966165357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45635672288033441977443571 68453508432050162966165357)
            ·
              refine ⟨25670065662018811112312009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68453508432050162966165357 25670065662018811112312009)
              ·
                refine ⟨19252549246514108334234007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25670065662018811112312009 19252549246514108334234007)
                ·
                  refine ⟨28878823869771162501351011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19252549246514108334234007 28878823869771162501351011)
                  ·
                    refine ⟨43318235804656743752026517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28878823869771162501351011 43318235804656743752026517)
                    ·
                      refine ⟨2030542303343284863376243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43318235804656743752026517 2030542303343284863376243)
                      ·
                        rfl

theorem cell23_3954467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_3954467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954467 prefixEnd_3954467 := by exact prefixLift 3954467
  have htrace : WordTrace (prefixWord ++ tailWord_3954467) baseStart_3954467 baseEnd_3954467 := by
    simpa [prefixWord, tailWord_3954467, baseEnd_3954467] using wordTrace_append hprefix tailTrace_3954467
  have hstable : (prefixWord ++ tailWord_3954467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954467).length < 2 ^ (prefixWord ++ tailWord_3954467).sum := by decide
  have hdescent : baseEnd_3954467 < baseStart_3954467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954481 : List Nat := [1, 2, 2, 3, 2, 3, 1, 3, 2, 4]
def baseStart_3954481 : Nat := 118140960795 + 3954481 * 2 ^ 59
def prefixEnd_3954481 : Nat := 4983230072969 + 3 ^ 40 * 3954481 * 2
def baseEnd_3954481 : Nat := 676849830690815936200393

theorem tailTrace_3954481 : CollatzResearch.WordTrace tailWord_3954481 prefixEnd_3954481 676849830690815936200393 := by
  unfold tailWord_3954481
  simp only [CollatzResearch.WordTrace]
  refine ⟨144231771186598183430831297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96154514124398788953887531 144231771186598183430831297)
  ·
    refine ⟨108173828389948637573123473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144231771186598183430831297 108173828389948637573123473)
    ·
      refine ⟨81130371292461478179842605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108173828389948637573123473 81130371292461478179842605)
      ·
        refine ⟨30423889234673054317440977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81130371292461478179842605 30423889234673054317440977)
        ·
          refine ⟨22817916926004790738080733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30423889234673054317440977 22817916926004790738080733)
          ·
            refine ⟨8556718847251796526780275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22817916926004790738080733 8556718847251796526780275)
            ·
              refine ⟨12835078270877694790170413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8556718847251796526780275 12835078270877694790170413)
              ·
                refine ⟨4813154351579135546313905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12835078270877694790170413 4813154351579135546313905)
                ·
                  refine ⟨3609865763684351659735429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4813154351579135546313905 3609865763684351659735429)
                  ·
                    refine ⟨676849830690815936200393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3609865763684351659735429 676849830690815936200393)
                    ·
                      rfl

theorem cell23_3954481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_3954481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954481 prefixEnd_3954481 := by exact prefixLift 3954481
  have htrace : WordTrace (prefixWord ++ tailWord_3954481) baseStart_3954481 baseEnd_3954481 := by
    simpa [prefixWord, tailWord_3954481, baseEnd_3954481] using wordTrace_append hprefix tailTrace_3954481
  have hstable : (prefixWord ++ tailWord_3954481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954481).length < 2 ^ (prefixWord ++ tailWord_3954481).sum := by decide
  have hdescent : baseEnd_3954481 < baseStart_3954481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954494 : List Nat := [4, 2, 1, 2, 2, 1, 2, 9]
def baseStart_3954494 : Nat := 118140960795 + 3954494 * 2 ^ 59
def prefixEnd_3954494 : Nat := 4983230072969 + 3 ^ 40 * 3954494 * 2
def baseEnd_3954494 : Nat := 75205783974850231768097

theorem tailTrace_3954494 : CollatzResearch.WordTrace tailWord_3954494 prefixEnd_3954494 75205783974850231768097 := by
  unfold tailWord_3954494
  simp only [CollatzResearch.WordTrace]
  refine ⟨18029030666943885831381817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96154830223700724434036357 18029030666943885831381817)
  ·
    refine ⟨13521773000207914373536363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18029030666943885831381817 13521773000207914373536363)
    ·
      refine ⟨20282659500311871560304545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13521773000207914373536363 20282659500311871560304545)
      ·
        refine ⟨15211994625233903670228409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20282659500311871560304545 15211994625233903670228409)
        ·
          refine ⟨11408995968925427752671307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15211994625233903670228409 11408995968925427752671307)
          ·
            refine ⟨17113493953388141629006961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11408995968925427752671307 17113493953388141629006961)
            ·
              refine ⟨12835120465041106221755221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17113493953388141629006961 12835120465041106221755221)
              ·
                refine ⟨75205783974850231768097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12835120465041106221755221 75205783974850231768097)
                ·
                  rfl

theorem cell23_3954494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 9].length) (baseStart_3954494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954494 prefixEnd_3954494 := by exact prefixLift 3954494
  have htrace : WordTrace (prefixWord ++ tailWord_3954494) baseStart_3954494 baseEnd_3954494 := by
    simpa [prefixWord, tailWord_3954494, baseEnd_3954494] using wordTrace_append hprefix tailTrace_3954494
  have hstable : (prefixWord ++ tailWord_3954494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954494).length < 2 ^ (prefixWord ++ tailWord_3954494).sum := by decide
  have hdescent : baseEnd_3954494 < baseStart_3954494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954504 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 3, 3, 3]
def baseStart_3954504 : Nat := 118140960795 + 3954504 * 2 ^ 59
def prefixEnd_3954504 : Nat := 4983230072969 + 3 ^ 40 * 3954504 * 2
def baseEnd_3954504 : Nat := 2030561302127501218613573

theorem tailTrace_3954504 : CollatzResearch.WordTrace tailWord_3954504 prefixEnd_3954504 2030561302127501218613573 := by
  unfold tailWord_3954504
  simp only [CollatzResearch.WordTrace]
  refine ⟨72116305032757429179459283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96155073377009905572612377 72116305032757429179459283)
  ·
    refine ⟨108174457549136143769188925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72116305032757429179459283 108174457549136143769188925)
    ·
      refine ⟨40565421580926053913445847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108174457549136143769188925 40565421580926053913445847)
      ·
        refine ⟨60848132371389080870168771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40565421580926053913445847 60848132371389080870168771)
        ·
          refine ⟨91272198557083621305253157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60848132371389080870168771 91272198557083621305253157)
          ·
            refine ⟨17113537229453178994734967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91272198557083621305253157 17113537229453178994734967)
            ·
              refine ⟨25670305844179768492102451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17113537229453178994734967 25670305844179768492102451)
              ·
                refine ⟨38505458766269652738153677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25670305844179768492102451 38505458766269652738153677)
                ·
                  refine ⟨14439547037351119776807629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38505458766269652738153677 14439547037351119776807629)
                  ·
                    refine ⟨5414830139006669916302861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14439547037351119776807629 5414830139006669916302861)
                    ·
                      refine ⟨2030561302127501218613573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5414830139006669916302861 2030561302127501218613573)
                      ·
                        rfl

theorem cell23_3954504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_3954504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954504 prefixEnd_3954504 := by exact prefixLift 3954504
  have htrace : WordTrace (prefixWord ++ tailWord_3954504) baseStart_3954504 baseEnd_3954504 := by
    simpa [prefixWord, tailWord_3954504, baseEnd_3954504] using wordTrace_append hprefix tailTrace_3954504
  have hstable : (prefixWord ++ tailWord_3954504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954504).length < 2 ^ (prefixWord ++ tailWord_3954504).sum := by decide
  have hdescent : baseEnd_3954504 < baseStart_3954504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954508 : List Nat := [2, 2, 1, 3, 5, 1, 1, 1, 1, 1, 5]
def baseStart_3954508 : Nat := 118140960795 + 3954508 * 2 ^ 59
def prefixEnd_3954508 : Nat := 4983230072969 + 3 ^ 40 * 3954508 * 2
def baseEnd_3954508 : Nat := 2030563356050119202963555

theorem tailTrace_3954508 : CollatzResearch.WordTrace tailWord_3954508 prefixEnd_3954508 2030563356050119202963555 := by
  unfold tailWord_3954508
  simp only [CollatzResearch.WordTrace]
  refine ⟨72116377978750183521032089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96155170638333578028042785 72116377978750183521032089)
  ·
    refine ⟨54087283484062637640774067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72116377978750183521032089 54087283484062637640774067)
    ·
      refine ⟨81130925226093956461161101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54087283484062637640774067 81130925226093956461161101)
      ·
        refine ⟨30424096959785233672935413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81130925226093956461161101 30424096959785233672935413)
        ·
          refine ⟨2852259089979865656837695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30424096959785233672935413 2852259089979865656837695)
          ·
            refine ⟨4278388634969798485256543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2852259089979865656837695 4278388634969798485256543)
            ·
              refine ⟨6417582952454697727884815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4278388634969798485256543 6417582952454697727884815)
              ·
                refine ⟨9626374428682046591827223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6417582952454697727884815 9626374428682046591827223)
                ·
                  refine ⟨14439561643023069887740835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9626374428682046591827223 14439561643023069887740835)
                  ·
                    refine ⟨21659342464534604831611253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14439561643023069887740835 21659342464534604831611253)
                    ·
                      refine ⟨2030563356050119202963555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21659342464534604831611253 2030563356050119202963555)
                      ·
                        rfl

theorem cell23_3954508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_3954508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954508 prefixEnd_3954508 := by exact prefixLift 3954508
  have htrace : WordTrace (prefixWord ++ tailWord_3954508) baseStart_3954508 baseEnd_3954508 := by
    simpa [prefixWord, tailWord_3954508, baseEnd_3954508] using wordTrace_append hprefix tailTrace_3954508
  have hstable : (prefixWord ++ tailWord_3954508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954508).length < 2 ^ (prefixWord ++ tailWord_3954508).sum := by decide
  have hdescent : baseEnd_3954508 < baseStart_3954508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954564 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_3954564 : Nat := 118140960795 + 3954564 * 2 ^ 59
def prefixEnd_3954564 : Nat := 4983230072969 + 3 ^ 40 * 3954564 * 2
def baseEnd_3954564 : Nat := 2030592110966770983863297

theorem tailTrace_3954564 : CollatzResearch.WordTrace tailWord_3954564 prefixEnd_3954564 2030592110966770983863297 := by
  unfold tailWord_3954564
  simp only [CollatzResearch.WordTrace]
  refine ⟨72117399222648744303051373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96156532296864992404068497 72117399222648744303051373)
  ·
    refine ⟨27044024708493279113644265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72117399222648744303051373 27044024708493279113644265)
    ·
      refine ⟨20283018531369959335233199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27044024708493279113644265 20283018531369959335233199)
      ·
        refine ⟨30424527797054939002849799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20283018531369959335233199 30424527797054939002849799)
        ·
          refine ⟨45636791695582408504274699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30424527797054939002849799 45636791695582408504274699)
          ·
            refine ⟨68455187543373612756412049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45636791695582408504274699 68455187543373612756412049)
            ·
              refine ⟨51341390657530209567309037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68455187543373612756412049 51341390657530209567309037)
              ·
                refine ⟨19253021496573828587740889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51341390657530209567309037 19253021496573828587740889)
                ·
                  refine ⟨14439766122430371440805667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19253021496573828587740889 14439766122430371440805667)
                  ·
                    refine ⟨21659649183645557161208501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14439766122430371440805667 21659649183645557161208501)
                    ·
                      refine ⟨2030592110966770983863297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21659649183645557161208501 2030592110966770983863297)
                      ·
                        rfl

theorem cell23_3954564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_3954564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954564 prefixEnd_3954564 := by exact prefixLift 3954564
  have htrace : WordTrace (prefixWord ++ tailWord_3954564) baseStart_3954564 baseEnd_3954564 := by
    simpa [prefixWord, tailWord_3954564, baseEnd_3954564] using wordTrace_append hprefix tailTrace_3954564
  have hstable : (prefixWord ++ tailWord_3954564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954564).length < 2 ^ (prefixWord ++ tailWord_3954564).sum := by decide
  have hdescent : baseEnd_3954564 < baseStart_3954564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954624 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 5]
def baseStart_3954624 : Nat := 118140960795 + 3954624 * 2 ^ 59
def prefixEnd_3954624 : Nat := 4983230072969 + 3 ^ 40 * 3954624 * 2
def baseEnd_3954624 : Nat := 2030622919806040749113021

theorem tailTrace_3954624 : CollatzResearch.WordTrace tailWord_3954624 prefixEnd_3954624 2030622919806040749113021 := by
  unfold tailWord_3954624
  simp only [CollatzResearch.WordTrace]
  refine ⟨72118493412540059426643463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96157991216720079235524617 72118493412540059426643463)
  ·
    refine ⟨108177740118810089139965195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72118493412540059426643463 108177740118810089139965195)
    ·
      refine ⟨162266610178215133709947793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108177740118810089139965195 162266610178215133709947793)
      ·
        refine ⟨121699957633661350282460845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162266610178215133709947793 121699957633661350282460845)
        ·
          refine ⟨45637484112623006355922817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121699957633661350282460845 45637484112623006355922817)
          ·
            refine ⟨34228113084467254766942113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45637484112623006355922817 34228113084467254766942113)
            ·
              refine ⟨25671084813350441075206585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34228113084467254766942113 25671084813350441075206585)
              ·
                refine ⟨19253313610012830806404939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25671084813350441075206585 19253313610012830806404939)
                ·
                  refine ⟨28879970415019246209607409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19253313610012830806404939 28879970415019246209607409)
                  ·
                    refine ⟨21659977811264434657205557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28879970415019246209607409 21659977811264434657205557)
                    ·
                      refine ⟨2030622919806040749113021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21659977811264434657205557 2030622919806040749113021)
                      ·
                        rfl

theorem cell23_3954624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_3954624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954624 prefixEnd_3954624 := by exact prefixLift 3954624
  have htrace : WordTrace (prefixWord ++ tailWord_3954624) baseStart_3954624 baseEnd_3954624 := by
    simpa [prefixWord, tailWord_3954624, baseEnd_3954624] using wordTrace_append hprefix tailTrace_3954624
  have hstable : (prefixWord ++ tailWord_3954624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954624).length < 2 ^ (prefixWord ++ tailWord_3954624).sum := by decide
  have hdescent : baseEnd_3954624 < baseStart_3954624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954646 : List Nat := [5, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_3954646 : Nat := 118140960795 + 3954646 * 2 ^ 59
def prefixEnd_3954646 : Nat := 4983230072969 + 3 ^ 40 * 3954646 * 2
def baseEnd_3954646 : Nat := 2030634216380439663037921

theorem tailTrace_3954646 : CollatzResearch.WordTrace tailWord_3954646 prefixEnd_3954646 2030634216380439663037921 := by
  unfold tailWord_3954646
  simp only [CollatzResearch.WordTrace]
  refine ⟨9014861826937526038161737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96158526154000277740391861 9014861826937526038161737)
  ·
    refine ⟨6761146370203144528621303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9014861826937526038161737 6761146370203144528621303)
    ·
      refine ⟨10141719555304716792931955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6761146370203144528621303 10141719555304716792931955)
      ·
        refine ⟨15212579332957075189397933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10141719555304716792931955 15212579332957075189397933)
        ·
          refine ⟨5704717249858903196024225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15212579332957075189397933 5704717249858903196024225)
          ·
            refine ⟨4278537937394177397018169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5704717249858903196024225 4278537937394177397018169)
            ·
              refine ⟨3208903453045633047763627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4278537937394177397018169 3208903453045633047763627)
              ·
                refine ⟨4813355179568449571645441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3208903453045633047763627 4813355179568449571645441)
                ·
                  refine ⟨3610016384676337178734081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4813355179568449571645441 3610016384676337178734081)
                  ·
                    refine ⟨2707512288507252884050561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3610016384676337178734081 2707512288507252884050561)
                    ·
                      refine ⟨2030634216380439663037921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2707512288507252884050561 2030634216380439663037921)
                      ·
                        rfl

theorem cell23_3954646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_3954646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954646 prefixEnd_3954646 := by exact prefixLift 3954646
  have htrace : WordTrace (prefixWord ++ tailWord_3954646) baseStart_3954646 baseEnd_3954646 := by
    simpa [prefixWord, tailWord_3954646, baseEnd_3954646] using wordTrace_append hprefix tailTrace_3954646
  have hstable : (prefixWord ++ tailWord_3954646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954646).length < 2 ^ (prefixWord ++ tailWord_3954646).sum := by decide
  have hdescent : baseEnd_3954646 < baseStart_3954646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954664 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_3954664 : Nat := 118140960795 + 3954664 * 2 ^ 59
def prefixEnd_3954664 : Nat := 4983230072969 + 3 ^ 40 * 3954664 * 2
def baseEnd_3954664 : Nat := 2030643459032220592612837

theorem tailTrace_3954664 : CollatzResearch.WordTrace tailWord_3954664 prefixEnd_3954664 2030643459032220592612837 := by
  unfold tailWord_3954664
  simp only [CollatzResearch.WordTrace]
  refine ⟨72119222872467602842371523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96158963829956803789828697 72119222872467602842371523)
  ·
    refine ⟨108178834308701404263557285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72119222872467602842371523 108178834308701404263557285)
    ·
      refine ⟨20283531432881513299416991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108178834308701404263557285 20283531432881513299416991)
      ·
        refine ⟨30425297149322269949125487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20283531432881513299416991 30425297149322269949125487)
        ·
          refine ⟨45637945723983404923688231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30425297149322269949125487 45637945723983404923688231)
          ·
            refine ⟨68456918585975107385532347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45637945723983404923688231 68456918585975107385532347)
            ·
              refine ⟨102685377878962661078298521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68456918585975107385532347 102685377878962661078298521)
              ·
                refine ⟨77014033409221995808723891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102685377878962661078298521 77014033409221995808723891)
                ·
                  refine ⟨115521050113832993713085837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77014033409221995808723891 115521050113832993713085837)
                  ·
                    refine ⟨43320393792687372642407189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115521050113832993713085837 43320393792687372642407189)
                    ·
                      refine ⟨2030643459032220592612837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43320393792687372642407189 2030643459032220592612837)
                      ·
                        rfl

theorem cell23_3954664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_3954664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954664 prefixEnd_3954664 := by exact prefixLift 3954664
  have htrace : WordTrace (prefixWord ++ tailWord_3954664) baseStart_3954664 baseEnd_3954664 := by
    simpa [prefixWord, tailWord_3954664, baseEnd_3954664] using wordTrace_append hprefix tailTrace_3954664
  have hstable : (prefixWord ++ tailWord_3954664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954664).length < 2 ^ (prefixWord ++ tailWord_3954664).sum := by decide
  have hdescent : baseEnd_3954664 < baseStart_3954664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954695 : List Nat := [1, 1, 4, 3, 1, 3, 1, 4, 1, 4]
def baseStart_3954695 : Nat := 118140960795 + 3954695 * 2 ^ 59
def prefixEnd_3954695 : Nat := 4983230072969 + 3 ^ 40 * 3954695 * 2
def baseEnd_3954695 : Nat := 676886458977503323775065

theorem tailTrace_3954695 : CollatzResearch.WordTrace tailWord_3954695 prefixEnd_3954695 676886458977503323775065 := by
  unfold tailWord_3954695
  simp only [CollatzResearch.WordTrace]
  refine ⟨144239576407822897979121539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96159717605215265319414359 144239576407822897979121539)
  ·
    refine ⟨216359364611734346968682309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144239576407822897979121539 216359364611734346968682309)
    ·
      refine ⟨40567380864700190056627933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216359364611734346968682309 40567380864700190056627933)
      ·
        refine ⟨15212767824262571271235475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40567380864700190056627933 15212767824262571271235475)
        ·
          refine ⟨22819151736393856906853213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15212767824262571271235475 22819151736393856906853213)
          ·
            refine ⟨8557181901147696340069955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22819151736393856906853213 8557181901147696340069955)
            ·
              refine ⟨12835772851721544510104933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8557181901147696340069955 12835772851721544510104933)
              ·
                refine ⟨2406707409697789595644675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12835772851721544510104933 2406707409697789595644675)
                ·
                  refine ⟨3610061114546684393467013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2406707409697789595644675 3610061114546684393467013)
                  ·
                    refine ⟨676886458977503323775065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3610061114546684393467013 676886458977503323775065)
                    ·
                      rfl

theorem cell23_3954695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_3954695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954695 prefixEnd_3954695 := by exact prefixLift 3954695
  have htrace : WordTrace (prefixWord ++ tailWord_3954695) baseStart_3954695 baseEnd_3954695 := by
    simpa [prefixWord, tailWord_3954695, baseEnd_3954695] using wordTrace_append hprefix tailTrace_3954695
  have hstable : (prefixWord ++ tailWord_3954695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954695).length < 2 ^ (prefixWord ++ tailWord_3954695).sum := by decide
  have hdescent : baseEnd_3954695 < baseStart_3954695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954738 : List Nat := [3, 2, 1, 1, 2, 4, 1, 3, 1, 5]
def baseStart_3954738 : Nat := 118140960795 + 3954738 * 2 ^ 59
def prefixEnd_3954738 : Nat := 4983230072969 + 3 ^ 40 * 3954738 * 2
def baseEnd_3954738 : Nat := 676893818866884434362499

theorem tailTrace_3954738 : CollatzResearch.WordTrace tailWord_3954738 prefixEnd_3954738 676893818866884434362499 := by
  unfold tailWord_3954738
  simp only [CollatzResearch.WordTrace]
  refine ⟨36060286186666779080734217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96160763164444744215291245 36060286186666779080734217)
  ·
    refine ⟨27045214640000084310550663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36060286186666779080734217 27045214640000084310550663)
    ·
      refine ⟨40567821960000126465825995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27045214640000084310550663 40567821960000126465825995)
      ·
        refine ⟨60851732940000189698738993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40567821960000126465825995 60851732940000189698738993)
        ·
          refine ⟨45638799705000142274054245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60851732940000189698738993 45638799705000142274054245)
          ·
            refine ⟨8557274944687526676385171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45638799705000142274054245 8557274944687526676385171)
            ·
              refine ⟨12835912417031290014577757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8557274944687526676385171 12835912417031290014577757)
              ·
                refine ⟨4813467156386733755466659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12835912417031290014577757 4813467156386733755466659)
                ·
                  refine ⟨7220200734580100633199989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4813467156386733755466659 7220200734580100633199989)
                  ·
                    refine ⟨676893818866884434362499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7220200734580100633199989 676893818866884434362499)
                    ·
                      rfl

theorem cell23_3954738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_3954738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954738 prefixEnd_3954738 := by exact prefixLift 3954738
  have htrace : WordTrace (prefixWord ++ tailWord_3954738) baseStart_3954738 baseEnd_3954738 := by
    simpa [prefixWord, tailWord_3954738, baseEnd_3954738] using wordTrace_append hprefix tailTrace_3954738
  have hstable : (prefixWord ++ tailWord_3954738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954738).length < 2 ^ (prefixWord ++ tailWord_3954738).sum := by decide
  have hdescent : baseEnd_3954738 < baseStart_3954738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954761 : List Nat := [1, 2, 1, 1, 2, 2, 5, 2, 1, 1, 5]
def baseStart_3954761 : Nat := 118140960795 + 3954761 * 2 ^ 59
def prefixEnd_3954761 : Nat := 4983230072969 + 3 ^ 40 * 3954761 * 2
def baseEnd_3954761 : Nat := 2030693266655706713099891

theorem tailTrace_3954761 : CollatzResearch.WordTrace tailWord_3954761 prefixEnd_3954761 2030693266655706713099891 := by
  unfold tailWord_3954761
  simp only [CollatzResearch.WordTrace]
  refine ⟨144241983625583791251024137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96161322417055860834016091 144241983625583791251024137)
  ·
    refine ⟨108181487719187843438268103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144241983625583791251024137 108181487719187843438268103)
    ·
      refine ⟨162272231578781765157402155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108181487719187843438268103 162272231578781765157402155)
      ·
        refine ⟨243408347368172647736103233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162272231578781765157402155 243408347368172647736103233)
        ·
          refine ⟨182556260526129485802077425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243408347368172647736103233 182556260526129485802077425)
          ·
            refine ⟨136917195394597114351558069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182556260526129485802077425 136917195394597114351558069)
            ·
              refine ⟨12835987068243479470458569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136917195394597114351558069 12835987068243479470458569)
              ·
                refine ⟨9626990301182609602843927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12835987068243479470458569 9626990301182609602843927)
                ·
                  refine ⟨14440485451773914404265891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9626990301182609602843927 14440485451773914404265891)
                  ·
                    refine ⟨21660728177660871606398837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14440485451773914404265891 21660728177660871606398837)
                    ·
                      refine ⟨2030693266655706713099891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21660728177660871606398837 2030693266655706713099891)
                      ·
                        rfl

theorem cell23_3954761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 1, 5].length) (baseStart_3954761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954761 prefixEnd_3954761 := by exact prefixLift 3954761
  have htrace : WordTrace (prefixWord ++ tailWord_3954761) baseStart_3954761 baseEnd_3954761 := by
    simpa [prefixWord, tailWord_3954761, baseEnd_3954761] using wordTrace_append hprefix tailTrace_3954761
  have hstable : (prefixWord ++ tailWord_3954761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954761).length < 2 ^ (prefixWord ++ tailWord_3954761).sum := by decide
  have hdescent : baseEnd_3954761 < baseStart_3954761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954775 : List Nat := [1, 1, 3, 2, 2, 1, 4, 2, 3, 2, 2]
def baseStart_3954775 : Nat := 118140960795 + 3954775 * 2 ^ 59
def prefixEnd_3954775 : Nat := 4983230072969 + 3 ^ 40 * 3954775 * 2
def baseEnd_3954775 : Nat := 2030700455384869658324827

theorem tailTrace_3954775 : CollatzResearch.WordTrace tailWord_3954775 prefixEnd_3954775 2030700455384869658324827 := by
  unfold tailWord_3954775
  simp only [CollatzResearch.WordTrace]
  refine ⟨144242494247533071642033779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96161662831688714428022519 144242494247533071642033779)
  ·
    refine ⟨216363741371299607463050669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144242494247533071642033779 216363741371299607463050669)
    ·
      refine ⟨81136403014237352798644001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216363741371299607463050669 81136403014237352798644001)
      ·
        refine ⟨60852302260678014598983001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81136403014237352798644001 60852302260678014598983001)
        ·
          refine ⟨45639226695508510949237251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60852302260678014598983001 45639226695508510949237251)
          ·
            refine ⟨68458840043262766423855877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45639226695508510949237251 68458840043262766423855877)
            ·
              refine ⟨12836032508111768704472977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68458840043262766423855877 12836032508111768704472977)
              ·
                refine ⟨9627024381083826528354733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12836032508111768704472977 9627024381083826528354733)
                ·
                  refine ⟨3610134142906434948133025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9627024381083826528354733 3610134142906434948133025)
                  ·
                    refine ⟨2707600607179826211099769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3610134142906434948133025 2707600607179826211099769)
                    ·
                      refine ⟨2030700455384869658324827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2707600607179826211099769 2030700455384869658324827)
                      ·
                        rfl

theorem cell23_3954775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_3954775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954775 prefixEnd_3954775 := by exact prefixLift 3954775
  have htrace : WordTrace (prefixWord ++ tailWord_3954775) baseStart_3954775 baseEnd_3954775 := by
    simpa [prefixWord, tailWord_3954775, baseEnd_3954775] using wordTrace_append hprefix tailTrace_3954775
  have hstable : (prefixWord ++ tailWord_3954775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954775).length < 2 ^ (prefixWord ++ tailWord_3954775).sum := by decide
  have hdescent : baseEnd_3954775 < baseStart_3954775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954786 : List Nat := [3, 3, 2, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_3954786 : Nat := 118140960795 + 3954786 * 2 ^ 59
def prefixEnd_3954786 : Nat := 4983230072969 + 3 ^ 40 * 3954786 * 2
def baseEnd_3954786 : Nat := 2030706103672069115287277

theorem tailTrace_3954786 : CollatzResearch.WordTrace tailWord_3954786 prefixEnd_3954786 2030706103672069115287277 := by
  unfold tailWord_3954786
  simp only [CollatzResearch.WordTrace]
  refine ⟨36060723862623305130171053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96161930300328813680456141 36060723862623305130171053)
  ·
    refine ⟨13522771448483739423814145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36060723862623305130171053 13522771448483739423814145)
    ·
      refine ⟨10142078586362804567860609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13522771448483739423814145 10142078586362804567860609)
      ·
        refine ⟨7606558939772103425895457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10142078586362804567860609 7606558939772103425895457)
        ·
          refine ⟨5704919204829077569421593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7606558939772103425895457 5704919204829077569421593)
          ·
            refine ⟨4278689403621808177066195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5704919204829077569421593 4278689403621808177066195)
            ·
              refine ⟨6418034105432712265599293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4278689403621808177066195 6418034105432712265599293)
              ·
                refine ⟨2406762789537267099599735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6418034105432712265599293 2406762789537267099599735)
                ·
                  refine ⟨3610144184305900649399603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2406762789537267099599735 3610144184305900649399603)
                  ·
                    refine ⟨5415216276458850974099405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3610144184305900649399603 5415216276458850974099405)
                    ·
                      refine ⟨2030706103672069115287277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5415216276458850974099405 2030706103672069115287277)
                      ·
                        rfl

theorem cell23_3954786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_3954786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954786 prefixEnd_3954786 := by exact prefixLift 3954786
  have htrace : WordTrace (prefixWord ++ tailWord_3954786) baseStart_3954786 baseEnd_3954786 := by
    simpa [prefixWord, tailWord_3954786, baseEnd_3954786] using wordTrace_append hprefix tailTrace_3954786
  have hstable : (prefixWord ++ tailWord_3954786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954786).length < 2 ^ (prefixWord ++ tailWord_3954786).sum := by decide
  have hdescent : baseEnd_3954786 < baseStart_3954786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954825 : List Nat := [1, 2, 1, 1, 4, 2, 3, 3, 2, 1, 3]
def baseStart_3954825 : Nat := 118140960795 + 3954825 * 2 ^ 59
def prefixEnd_3954825 : Nat := 4983230072969 + 3 ^ 40 * 3954825 * 2
def baseEnd_3954825 : Nat := 2030726129417594462699597

theorem tailTrace_3954825 : CollatzResearch.WordTrace tailWord_3954825 prefixEnd_3954825 2030726129417594462699597 := by
  unfold tailWord_3954825
  simp only [CollatzResearch.WordTrace]
  refine ⟨144244317897351930181353929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96162878598234620120902619 144244317897351930181353929)
  ·
    refine ⟨108183238423013947636015447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144244317897351930181353929 108183238423013947636015447)
    ·
      refine ⟨162274857634520921454023171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108183238423013947636015447 162274857634520921454023171)
      ·
        refine ⟨243412286451781382181034757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162274857634520921454023171 243412286451781382181034757)
        ·
          refine ⟨45639803709709009158944017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243412286451781382181034757 45639803709709009158944017)
          ·
            refine ⟨34229852782281756869208013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45639803709709009158944017 34229852782281756869208013)
            ·
              refine ⟨12836194793355658825953005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34229852782281756869208013 12836194793355658825953005)
              ·
                refine ⟨4813573047508372059732377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12836194793355658825953005 4813573047508372059732377)
                ·
                  refine ⟨3610179785631279044799283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4813573047508372059732377 3610179785631279044799283)
                  ·
                    refine ⟨5415269678446918567198925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3610179785631279044799283 5415269678446918567198925)
                    ·
                      refine ⟨2030726129417594462699597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5415269678446918567198925 2030726129417594462699597)
                      ·
                        rfl

theorem cell23_3954825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 1, 3].length) (baseStart_3954825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954825 prefixEnd_3954825 := by exact prefixLift 3954825
  have htrace : WordTrace (prefixWord ++ tailWord_3954825) baseStart_3954825 baseEnd_3954825 := by
    simpa [prefixWord, tailWord_3954825, baseEnd_3954825] using wordTrace_append hprefix tailTrace_3954825
  have hstable : (prefixWord ++ tailWord_3954825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954825).length < 2 ^ (prefixWord ++ tailWord_3954825).sum := by decide
  have hdescent : baseEnd_3954825 < baseStart_3954825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954938 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4]
def baseStart_3954938 : Nat := 118140960795 + 3954938 * 2 ^ 59
def prefixEnd_3954938 : Nat := 4983230072969 + 3 ^ 40 * 3954938 * 2
def baseEnd_3954938 : Nat := 2030784152731552520586577

theorem tailTrace_3954938 : CollatzResearch.WordTrace tailWord_3954938 prefixEnd_3954938 2030784152731552520586577 := by
  unfold tailWord_3954938
  simp only [CollatzResearch.WordTrace]
  refine ⟨36062109836485637620054367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96165626230628366986811645 36062109836485637620054367)
  ·
    refine ⟨54093164754728456430081551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36062109836485637620054367 54093164754728456430081551)
    ·
      refine ⟨81139747132092684645122327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54093164754728456430081551 81139747132092684645122327)
      ·
        refine ⟨121709620698139026967683491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81139747132092684645122327 121709620698139026967683491)
        ·
          refine ⟨182564431047208540451525237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121709620698139026967683491 182564431047208540451525237)
          ·
            refine ⟨17115415410675800667330491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182564431047208540451525237 17115415410675800667330491)
            ·
              refine ⟨25673123116013701000995737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17115415410675800667330491 25673123116013701000995737)
              ·
                refine ⟨19254842337010275750746803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25673123116013701000995737 19254842337010275750746803)
                ·
                  refine ⟨28882263505515413626120205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19254842337010275750746803 28882263505515413626120205)
                  ·
                    refine ⟨10830848814568280109795077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28882263505515413626120205 10830848814568280109795077)
                    ·
                      refine ⟨2030784152731552520586577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10830848814568280109795077 2030784152731552520586577)
                      ·
                        rfl

theorem cell23_3954938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_3954938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954938 prefixEnd_3954938 := by exact prefixLift 3954938
  have htrace : WordTrace (prefixWord ++ tailWord_3954938) baseStart_3954938 baseEnd_3954938 := by
    simpa [prefixWord, tailWord_3954938, baseEnd_3954938] using wordTrace_append hprefix tailTrace_3954938
  have hstable : (prefixWord ++ tailWord_3954938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954938).length < 2 ^ (prefixWord ++ tailWord_3954938).sum := by decide
  have hdescent : baseEnd_3954938 < baseStart_3954938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954975 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 3]
def baseStart_3954975 : Nat := 118140960795 + 3954975 * 2 ^ 59
def prefixEnd_3954975 : Nat := 4983230072969 + 3 ^ 40 * 3954975 * 2
def baseEnd_3954975 : Nat := 2030803151515768875823907

theorem tailTrace_3954975 : CollatzResearch.WordTrace tailWord_3954975 prefixEnd_3954975 2030803151515768875823907 := by
  unfold tailWord_3954975
  simp only [CollatzResearch.WordTrace]
  refine ⟨144249788846808505799314379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96166525897872337199542919 144249788846808505799314379)
  ·
    refine ⟨216374683270212758698971569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144249788846808505799314379 216374683270212758698971569)
    ·
      refine ⟨162281012452659569024228677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216374683270212758698971569 162281012452659569024228677)
      ·
        refine ⟨30427689834873669192042877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162281012452659569024228677 30427689834873669192042877)
        ·
          refine ⟨11410383688077625947016079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30427689834873669192042877 11410383688077625947016079)
          ·
            refine ⟨17115575532116438920524119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11410383688077625947016079 17115575532116438920524119)
            ·
              refine ⟨25673363298174658380786179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17115575532116438920524119 25673363298174658380786179)
              ·
                refine ⟨38510044947261987571179269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25673363298174658380786179 38510044947261987571179269)
                ·
                  refine ⟨7220633427611622669596113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38510044947261987571179269 7220633427611622669596113)
                  ·
                    refine ⟨5415475070708717002197085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7220633427611622669596113 5415475070708717002197085)
                    ·
                      refine ⟨2030803151515768875823907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5415475070708717002197085 2030803151515768875823907)
                      ·
                        rfl

theorem cell23_3954975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_3954975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3954975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3954975 prefixEnd_3954975 := by exact prefixLift 3954975
  have htrace : WordTrace (prefixWord ++ tailWord_3954975) baseStart_3954975 baseEnd_3954975 := by
    simpa [prefixWord, tailWord_3954975, baseEnd_3954975] using wordTrace_append hprefix tailTrace_3954975
  have hstable : (prefixWord ++ tailWord_3954975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954975).length < 2 ^ (prefixWord ++ tailWord_3954975).sum := by decide
  have hdescent : baseEnd_3954975 < baseStart_3954975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955009 : List Nat := [1, 2, 5, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_3955009 : Nat := 118140960795 + 3955009 * 2 ^ 59
def prefixEnd_3955009 : Nat := 4983230072969 + 3 ^ 40 * 3955009 * 2
def baseEnd_3955009 : Nat := 2030820609858021742798751

theorem tailTrace_3955009 : CollatzResearch.WordTrace tailWord_3955009 prefixEnd_3955009 2030820609858021742798751 := by
  unfold tailWord_3955009
  simp only [CollatzResearch.WordTrace]
  refine ⟨144251028928685329606052081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96167352619123553070701387 144251028928685329606052081)
  ·
    refine ⟨108188271696513997204539061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144251028928685329606052081 108188271696513997204539061)
    ·
      refine ⟨10142650471548187237925537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108188271696513997204539061 10142650471548187237925537)
      ·
        refine ⟨7606987853661140428444153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10142650471548187237925537 7606987853661140428444153)
        ·
          refine ⟨5705240890245855321333115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7606987853661140428444153 5705240890245855321333115)
          ·
            refine ⟨8557861335368782981999673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5705240890245855321333115 8557861335368782981999673)
            ·
              refine ⟨6418396001526587236499755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8557861335368782981999673 6418396001526587236499755)
              ·
                refine ⟨9627594002289880854749633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418396001526587236499755 9627594002289880854749633)
                ·
                  refine ⟨7220695501717410641062225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9627594002289880854749633 7220695501717410641062225)
                  ·
                    refine ⟨5415521626288057980796669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7220695501717410641062225 5415521626288057980796669)
                    ·
                      refine ⟨2030820609858021742798751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5415521626288057980796669 2030820609858021742798751)
                      ·
                        rfl

theorem cell23_3955009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_3955009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955009 prefixEnd_3955009 := by exact prefixLift 3955009
  have htrace : WordTrace (prefixWord ++ tailWord_3955009) baseStart_3955009 baseEnd_3955009 := by
    simpa [prefixWord, tailWord_3955009, baseEnd_3955009] using wordTrace_append hprefix tailTrace_3955009
  have hstable : (prefixWord ++ tailWord_3955009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955009).length < 2 ^ (prefixWord ++ tailWord_3955009).sum := by decide
  have hdescent : baseEnd_3955009 < baseStart_3955009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955045 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 3, 1, 4]
def baseStart_3955045 : Nat := 118140960795 + 3955045 * 2 ^ 59
def prefixEnd_3955045 : Nat := 4983230072969 + 3 ^ 40 * 3955045 * 2
def baseEnd_3955045 : Nat := 2030839095161583601948585

theorem tailTrace_3955045 : CollatzResearch.WordTrace tailWord_3955045 prefixEnd_3955045 2030839095161583601948585 := by
  unfold tailWord_3955045
  simp only [CollatzResearch.WordTrace]
  refine ⟨144252341956554907754362589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96168227971036605169575059 144252341956554907754362589)
  ·
    refine ⟨54094628233708090407885971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144252341956554907754362589 54094628233708090407885971)
    ·
      refine ⟨81141942350562135611828957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54094628233708090407885971 81141942350562135611828957)
      ·
        refine ⟨30428228381460800854435859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81141942350562135611828957 30428228381460800854435859)
        ·
          refine ⟨45642342572191201281653789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30428228381460800854435859 45642342572191201281653789)
          ·
            refine ⟨17115878464571700480620171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45642342572191201281653789 17115878464571700480620171)
            ·
              refine ⟨25673817696857550720930257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17115878464571700480620171 25673817696857550720930257)
              ·
                refine ⟨19255363272643163040697693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25673817696857550720930257 19255363272643163040697693)
                ·
                  refine ⟨7220761227241186140261635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19255363272643163040697693 7220761227241186140261635)
                  ·
                    refine ⟨10831141840861779210392453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7220761227241186140261635 10831141840861779210392453)
                    ·
                      refine ⟨2030839095161583601948585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10831141840861779210392453 2030839095161583601948585)
                      ·
                        rfl

theorem cell23_3955045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_3955045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955045 prefixEnd_3955045 := by exact prefixLift 3955045
  have htrace : WordTrace (prefixWord ++ tailWord_3955045) baseStart_3955045 baseEnd_3955045 := by
    simpa [prefixWord, tailWord_3955045, baseEnd_3955045] using wordTrace_append hprefix tailTrace_3955045
  have hstable : (prefixWord ++ tailWord_3955045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955045).length < 2 ^ (prefixWord ++ tailWord_3955045).sum := by decide
  have hdescent : baseEnd_3955045 < baseStart_3955045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955095 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 3]
def baseStart_3955095 : Nat := 118140960795 + 3955095 * 2 ^ 59
def prefixEnd_3955095 : Nat := 4983230072969 + 3 ^ 40 * 3955095 * 2
def baseEnd_3955095 : Nat := 2030864769194308406323355

theorem tailTrace_3955095 : CollatzResearch.WordTrace tailWord_3955095 prefixEnd_3955095 2030864769194308406323355 := by
  unfold tailWord_3955095
  simp only [CollatzResearch.WordTrace]
  refine ⟨144254165606373766293682739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96169443737582510862455159 144254165606373766293682739)
  ·
    refine ⟨216381248409560649440524109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144254165606373766293682739 216381248409560649440524109)
    ·
      refine ⟨81142968153585243540196541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216381248409560649440524109 81142968153585243540196541)
      ·
        refine ⟨30428613057594466327573703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81142968153585243540196541 30428613057594466327573703)
        ·
          refine ⟨45642919586391699491360555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30428613057594466327573703 45642919586391699491360555)
          ·
            refine ⟨68464379379587549237040833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45642919586391699491360555 68464379379587549237040833)
            ·
              refine ⟨51348284534690661927780625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68464379379587549237040833 51348284534690661927780625)
              ·
                refine ⟨38511213401017996445835469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51348284534690661927780625 38511213401017996445835469)
                ·
                  refine ⟨14441705025381748667188301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38511213401017996445835469 14441705025381748667188301)
                  ·
                    refine ⟨5415639384518155750195613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14441705025381748667188301 5415639384518155750195613)
                    ·
                      refine ⟨2030864769194308406323355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5415639384518155750195613 2030864769194308406323355)
                      ·
                        rfl

theorem cell23_3955095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_3955095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955095 prefixEnd_3955095 := by exact prefixLift 3955095
  have htrace : WordTrace (prefixWord ++ tailWord_3955095) baseStart_3955095 baseEnd_3955095 := by
    simpa [prefixWord, tailWord_3955095, baseEnd_3955095] using wordTrace_append hprefix tailTrace_3955095
  have hstable : (prefixWord ++ tailWord_3955095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955095).length < 2 ^ (prefixWord ++ tailWord_3955095).sum := by decide
  have hdescent : baseEnd_3955095 < baseStart_3955095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955096 : List Nat := [2, 1, 2, 5, 1, 2, 2, 1, 3, 2, 2]
def baseStart_3955096 : Nat := 118140960795 + 3955096 * 2 ^ 59
def prefixEnd_3955096 : Nat := 4983230072969 + 3 ^ 40 * 3955096 * 2
def baseEnd_3955096 : Nat := 2030865282674962902410851

theorem tailTrace_3955096 : CollatzResearch.WordTrace tailWord_3955096 prefixEnd_3955096 2030865282674962902410851 := by
  unfold tailWord_3955096
  simp only [CollatzResearch.WordTrace]
  refine ⟨72127101039685071732234571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96169468052913428976312761 72127101039685071732234571)
  ·
    refine ⟨108190651559527607598351857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72127101039685071732234571 108190651559527607598351857)
    ·
      refine ⟨81142988669645705698763893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108190651559527607598351857 81142988669645705698763893)
      ·
        refine ⟨7607155187779284909259115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81142988669645705698763893 7607155187779284909259115)
        ·
          refine ⟨11410732781668927363888673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7607155187779284909259115 11410732781668927363888673)
          ·
            refine ⟨8558049586251695522916505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11410732781668927363888673 8558049586251695522916505)
            ·
              refine ⟨6418537189688771642187379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8558049586251695522916505 6418537189688771642187379)
              ·
                refine ⟨9627805784533157463281069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418537189688771642187379 9627805784533157463281069)
                ·
                  refine ⟨3610427169199934048730401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9627805784533157463281069 3610427169199934048730401)
                  ·
                    refine ⟨2707820376899950536547801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3610427169199934048730401 2707820376899950536547801)
                    ·
                      refine ⟨2030865282674962902410851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2707820376899950536547801 2030865282674962902410851)
                      ·
                        rfl

theorem cell23_3955096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_3955096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955096 prefixEnd_3955096 := by exact prefixLift 3955096
  have htrace : WordTrace (prefixWord ++ tailWord_3955096) baseStart_3955096 baseEnd_3955096 := by
    simpa [prefixWord, tailWord_3955096, baseEnd_3955096] using wordTrace_append hprefix tailTrace_3955096
  have hstable : (prefixWord ++ tailWord_3955096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955096).length < 2 ^ (prefixWord ++ tailWord_3955096).sum := by decide
  have hdescent : baseEnd_3955096 < baseStart_3955096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955173 : List Nat := [1, 3, 1, 5, 2, 2, 1, 2, 1, 3, 2]
def baseStart_3955173 : Nat := 118140960795 + 3955173 * 2 ^ 59
def prefixEnd_3955173 : Nat := 4983230072969 + 3 ^ 40 * 3955173 * 2
def baseEnd_3955173 : Nat := 2030904820685359101147997

theorem tailTrace_3955173 : CollatzResearch.WordTrace tailWord_3955173 prefixEnd_3955173 2030904820685359101147997 := by
  unfold tailWord_3955173
  simp only [CollatzResearch.WordTrace]
  refine ⟨144257010500091185615022173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96171340333394123743348115 144257010500091185615022173)
  ·
    refine ⟨54096378937534194605633315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144257010500091185615022173 54096378937534194605633315)
    ·
      refine ⟨81144568406301291908449973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54096378937534194605633315 81144568406301291908449973)
      ·
        refine ⟨7607303288090746116417185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81144568406301291908449973 7607303288090746116417185)
        ·
          refine ⟨5705477466068059587312889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7607303288090746116417185 5705477466068059587312889)
          ·
            refine ⟨4279108099551044690484667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5705477466068059587312889 4279108099551044690484667)
            ·
              refine ⟨6418662149326567035727001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4279108099551044690484667 6418662149326567035727001)
              ·
                refine ⟨4813996611994925276795251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6418662149326567035727001 4813996611994925276795251)
                ·
                  refine ⟨7220994917992387915192877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4813996611994925276795251 7220994917992387915192877)
                  ·
                    refine ⟨2707873094247145468197329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7220994917992387915192877 2707873094247145468197329)
                    ·
                      refine ⟨2030904820685359101147997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2707873094247145468197329 2030904820685359101147997)
                      ·
                        rfl

theorem cell23_3955173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_3955173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955173 prefixEnd_3955173 := by exact prefixLift 3955173
  have htrace : WordTrace (prefixWord ++ tailWord_3955173) baseStart_3955173 baseEnd_3955173 := by
    simpa [prefixWord, tailWord_3955173, baseEnd_3955173] using wordTrace_append hprefix tailTrace_3955173
  have hstable : (prefixWord ++ tailWord_3955173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955173).length < 2 ^ (prefixWord ++ tailWord_3955173).sum := by decide
  have hdescent : baseEnd_3955173 < baseStart_3955173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955175 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 9]
def baseStart_3955175 : Nat := 118140960795 + 3955175 * 2 ^ 59
def prefixEnd_3955175 : Nat := 4983230072969 + 3 ^ 40 * 3955175 * 2
def baseEnd_3955175 : Nat := 225656205294074232591443

theorem tailTrace_3955175 : CollatzResearch.WordTrace tailWord_3955175 prefixEnd_3955175 225656205294074232591443 := by
  unfold tailWord_3955175
  simp only [CollatzResearch.WordTrace]
  refine ⟨144257083446083939956594979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96171388964055959971063319 144257083446083939956594979)
  ·
    refine ⟨216385625169125909934892469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144257083446083939956594979 216385625169125909934892469)
    ·
      refine ⟨20286152359605554056396169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216385625169125909934892469 20286152359605554056396169)
      ·
        refine ⟨15214614269704165542297127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20286152359605554056396169 15214614269704165542297127)
        ·
          refine ⟨22821921404556248313445691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15214614269704165542297127 22821921404556248313445691)
          ·
            refine ⟨34232882106834372470168537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22821921404556248313445691 34232882106834372470168537)
            ·
              refine ⟨25674661580125779352626403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34232882106834372470168537 25674661580125779352626403)
              ·
                refine ⟨38511992370188669028939605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25674661580125779352626403 38511992370188669028939605)
                ·
                  refine ⟨225656205294074232591443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38511992370188669028939605 225656205294074232591443)
                  ·
                    rfl

theorem cell23_3955175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 9].length) (baseStart_3955175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955175 prefixEnd_3955175 := by exact prefixLift 3955175
  have htrace : WordTrace (prefixWord ++ tailWord_3955175) baseStart_3955175 baseEnd_3955175 := by
    simpa [prefixWord, tailWord_3955175, baseEnd_3955175] using wordTrace_append hprefix tailTrace_3955175
  have hstable : (prefixWord ++ tailWord_3955175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955175).length < 2 ^ (prefixWord ++ tailWord_3955175).sum := by decide
  have hdescent : baseEnd_3955175 < baseStart_3955175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955186 : List Nat := [3, 2, 1, 4, 2, 1, 1, 2, 1, 4, 2]
def baseStart_3955186 : Nat := 118140960795 + 3955186 * 2 ^ 59
def prefixEnd_3955186 : Nat := 4983230072969 + 3 ^ 40 * 3955186 * 2
def baseEnd_3955186 : Nat := 2030911495933867550285437

theorem tailTrace_3955186 : CollatzResearch.WordTrace tailWord_3955186 prefixEnd_3955186 2030911495933867550285437 := by
  unfold tailWord_3955186
  simp only [CollatzResearch.WordTrace]
  refine ⟨36064371162261022208811353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96171656432696059223496941 36064371162261022208811353)
  ·
    refine ⟨27048278371695766656608515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36064371162261022208811353 27048278371695766656608515)
    ·
      refine ⟨40572417557543649984912773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27048278371695766656608515 40572417557543649984912773)
      ·
        refine ⟨7607328292039434372171145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40572417557543649984912773 7607328292039434372171145)
        ·
          refine ⟨5705496219029575779128359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7607328292039434372171145 5705496219029575779128359)
          ·
            refine ⟨8558244328544363668692539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5705496219029575779128359 8558244328544363668692539)
            ·
              refine ⟨12837366492816545503038809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8558244328544363668692539 12837366492816545503038809)
              ·
                refine ⟨9628024869612409127279107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12837366492816545503038809 9628024869612409127279107)
                ·
                  refine ⟨14442037304418613690918661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9628024869612409127279107 14442037304418613690918661)
                  ·
                    refine ⟨2707881994578490067047249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14442037304418613690918661 2707881994578490067047249)
                    ·
                      refine ⟨2030911495933867550285437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2707881994578490067047249 2030911495933867550285437)
                      ·
                        rfl

theorem cell23_3955186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_3955186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955186 prefixEnd_3955186 := by exact prefixLift 3955186
  have htrace : WordTrace (prefixWord ++ tailWord_3955186) baseStart_3955186 baseEnd_3955186 := by
    simpa [prefixWord, tailWord_3955186, baseEnd_3955186] using wordTrace_append hprefix tailTrace_3955186
  have hstable : (prefixWord ++ tailWord_3955186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955186).length < 2 ^ (prefixWord ++ tailWord_3955186).sum := by decide
  have hdescent : baseEnd_3955186 < baseStart_3955186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955192 : List Nat := [2, 1, 2, 1, 1, 4, 2, 5, 5]
def baseStart_3955192 : Nat := 118140960795 + 3955192 * 2 ^ 59
def prefixEnd_3955192 : Nat := 4983230072969 + 3 ^ 40 * 3955192 * 2
def baseEnd_3955192 : Nat := 225657175201977169645601

theorem tailTrace_3955192 : CollatzResearch.WordTrace tailWord_3955192 prefixEnd_3955192 225657175201977169645601 := by
  unfold tailWord_3955192
  simp only [CollatzResearch.WordTrace]
  refine ⟨72128851743511175929981915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96171802324681567906642553 72128851743511175929981915)
  ·
    refine ⟨108193277615266763894972873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72128851743511175929981915 108193277615266763894972873)
    ·
      refine ⟨81144958211450072921229655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108193277615266763894972873 81144958211450072921229655)
      ·
        refine ⟨121717437317175109381844483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81144958211450072921229655 121717437317175109381844483)
        ·
          refine ⟨182576155975762664072766725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121717437317175109381844483 182576155975762664072766725)
          ·
            refine ⟨34233029245455499513643761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182576155975762664072766725 34233029245455499513643761)
            ·
              refine ⟨25674771934091624635232821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34233029245455499513643761 25674771934091624635232821)
              ·
                refine ⟨2407009868821089809553077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25674771934091624635232821 2407009868821089809553077)
                ·
                  refine ⟨225657175201977169645601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2407009868821089809553077 225657175201977169645601)
                  ·
                    rfl

theorem cell23_3955192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 5].length) (baseStart_3955192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955192 prefixEnd_3955192 := by exact prefixLift 3955192
  have htrace : WordTrace (prefixWord ++ tailWord_3955192) baseStart_3955192 baseEnd_3955192 := by
    simpa [prefixWord, tailWord_3955192, baseEnd_3955192] using wordTrace_append hprefix tailTrace_3955192
  have hstable : (prefixWord ++ tailWord_3955192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955192).length < 2 ^ (prefixWord ++ tailWord_3955192).sum := by decide
  have hdescent : baseEnd_3955192 < baseStart_3955192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955225 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 3, 3, 4]
def baseStart_3955225 : Nat := 118140960795 + 3955225 * 2 ^ 59
def prefixEnd_3955225 : Nat := 4983230072969 + 3 ^ 40 * 3955225 * 2
def baseEnd_3955225 : Nat := 2030931521679392897697757

theorem tailTrace_3955225 : CollatzResearch.WordTrace tailWord_3955225 prefixEnd_3955225 2030931521679392897697757 := by
  unfold tailWord_3955225
  simp only [CollatzResearch.WordTrace]
  refine ⟨144258907095902798495915129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96172604730601865663943419 144258907095902798495915129)
  ·
    refine ⟨108194180321927098871936347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144258907095902798495915129 108194180321927098871936347)
    ·
      refine ⟨162291270482890648307904521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108194180321927098871936347 162291270482890648307904521)
      ·
        refine ⟨121718452862167986230928391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162291270482890648307904521 121718452862167986230928391)
        ·
          refine ⟨182577679293251979346392587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121718452862167986230928391 182577679293251979346392587)
          ·
            refine ⟨273866518939877969019588881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182577679293251979346392587 273866518939877969019588881)
            ·
              refine ⟨205399889204908476764691661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273866518939877969019588881 205399889204908476764691661)
              ·
                refine ⟨77024958451840678786759373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205399889204908476764691661 77024958451840678786759373)
                ·
                  refine ⟨28884359419440254545034765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77024958451840678786759373 28884359419440254545034765)
                  ·
                    refine ⟨10831634782290095454388037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28884359419440254545034765 10831634782290095454388037)
                    ·
                      refine ⟨2030931521679392897697757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10831634782290095454388037 2030931521679392897697757)
                      ·
                        rfl

theorem cell23_3955225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_3955225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955225 prefixEnd_3955225 := by exact prefixLift 3955225
  have htrace : WordTrace (prefixWord ++ tailWord_3955225) baseStart_3955225 baseEnd_3955225 := by
    simpa [prefixWord, tailWord_3955225, baseEnd_3955225] using wordTrace_append hprefix tailTrace_3955225
  have hstable : (prefixWord ++ tailWord_3955225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955225).length < 2 ^ (prefixWord ++ tailWord_3955225).sum := by decide
  have hdescent : baseEnd_3955225 < baseStart_3955225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955255 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 6]
def baseStart_3955255 : Nat := 118140960795 + 3955255 * 2 ^ 59
def prefixEnd_3955255 : Nat := 4983230072969 + 3 ^ 40 * 3955255 * 2
def baseEnd_3955255 : Nat := 2030946926099027780322619

theorem tailTrace_3955255 : CollatzResearch.WordTrace tailWord_3955255 prefixEnd_3955255 2030946926099027780322619 := by
  unfold tailWord_3955255
  simp only [CollatzResearch.WordTrace]
  refine ⟨144260001285794113619507219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96173334190529409079671479 144260001285794113619507219)
  ·
    refine ⟨216390001928691170429260829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144260001285794113619507219 216390001928691170429260829)
    ·
      refine ⟨81146250723259188910972811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216390001928691170429260829 81146250723259188910972811)
      ·
        refine ⟨121719376084888783366459217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81146250723259188910972811 121719376084888783366459217)
        ·
          refine ⟨91289532063666587524844413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121719376084888783366459217 91289532063666587524844413)
          ·
            refine ⟨34233574523874970321816655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91289532063666587524844413 34233574523874970321816655)
            ·
              refine ⟨51350361785812455482724983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34233574523874970321816655 51350361785812455482724983)
              ·
                refine ⟨77025542678718683224087475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51350361785812455482724983 77025542678718683224087475)
                ·
                  refine ⟨115538314018078024836131213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77025542678718683224087475 115538314018078024836131213)
                  ·
                    refine ⟨43326867756779259313549205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115538314018078024836131213 43326867756779259313549205)
                    ·
                      refine ⟨2030946926099027780322619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43326867756779259313549205 2030946926099027780322619)
                      ·
                        rfl

theorem cell23_3955255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_3955255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955255 prefixEnd_3955255 := by exact prefixLift 3955255
  have htrace : WordTrace (prefixWord ++ tailWord_3955255) baseStart_3955255 baseEnd_3955255 := by
    simpa [prefixWord, tailWord_3955255, baseEnd_3955255] using wordTrace_append hprefix tailTrace_3955255
  have hstable : (prefixWord ++ tailWord_3955255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955255).length < 2 ^ (prefixWord ++ tailWord_3955255).sum := by decide
  have hdescent : baseEnd_3955255 < baseStart_3955255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955269 : List Nat := [1, 3, 1, 1, 1, 6, 2, 1, 3, 4]
def baseStart_3955269 : Nat := 118140960795 + 3955269 * 2 ^ 59
def prefixEnd_3955269 : Nat := 4983230072969 + 3 ^ 40 * 3955269 * 2
def baseEnd_3955269 : Nat := 676984704942730241849185

theorem tailTrace_3955269 : CollatzResearch.WordTrace tailWord_3955269 prefixEnd_3955269 676984704942730241849185 := by
  unfold tailWord_3955269
  simp only [CollatzResearch.WordTrace]
  refine ⟨144260511907743394010516861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96173674605162262673677907 144260511907743394010516861)
  ·
    refine ⟨54097691965403772753943823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144260511907743394010516861 54097691965403772753943823)
    ·
      refine ⟨81146537948105659130915735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54097691965403772753943823 81146537948105659130915735)
      ·
        refine ⟨121719806922158488696373603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81146537948105659130915735 121719806922158488696373603)
        ·
          refine ⟨182579710383237733044560405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121719806922158488696373603 182579710383237733044560405)
          ·
            refine ⟨8558423924214268736463769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182579710383237733044560405 8558423924214268736463769)
            ·
              refine ⟨6418817943160701552347827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8558423924214268736463769 6418817943160701552347827)
              ·
                refine ⟨9628226914741052328521741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418817943160701552347827 9628226914741052328521741)
                ·
                  refine ⟨3610585093027894623195653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9628226914741052328521741 3610585093027894623195653)
                  ·
                    refine ⟨676984704942730241849185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3610585093027894623195653 676984704942730241849185)
                    ·
                      rfl

theorem cell23_3955269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_3955269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955269 prefixEnd_3955269 := by exact prefixLift 3955269
  have htrace : WordTrace (prefixWord ++ tailWord_3955269) baseStart_3955269 baseEnd_3955269 := by
    simpa [prefixWord, tailWord_3955269, baseEnd_3955269] using wordTrace_append hprefix tailTrace_3955269
  have hstable : (prefixWord ++ tailWord_3955269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955269).length < 2 ^ (prefixWord ++ tailWord_3955269).sum := by decide
  have hdescent : baseEnd_3955269 < baseStart_3955269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955295 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 2, 9]
def baseStart_3955295 : Nat := 118140960795 + 3955295 * 2 ^ 59
def prefixEnd_3955295 : Nat := 4983230072969 + 3 ^ 40 * 3955295 * 2
def baseEnd_3955295 : Nat := 676989155108402541274145

theorem tailTrace_3955295 : CollatzResearch.WordTrace tailWord_3955295 prefixEnd_3955295 676989155108402541274145 := by
  unfold tailWord_3955295
  simp only [CollatzResearch.WordTrace]
  refine ⟨144261460205649200450963339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96174306803766133633975559 144261460205649200450963339)
  ·
    refine ⟨216392190308473800676445009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144261460205649200450963339 216392190308473800676445009)
    ·
      refine ⟨162294142731355350507333757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216392190308473800676445009 162294142731355350507333757)
      ·
        refine ⟨60860303524258256440250159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162294142731355350507333757 60860303524258256440250159)
        ·
          refine ⟨91290455286387384660375239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60860303524258256440250159 91290455286387384660375239)
          ·
            refine ⟨136935682929581076990562859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91290455286387384660375239 136935682929581076990562859)
            ·
              refine ⟨205403524394371615485844289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136935682929581076990562859 205403524394371615485844289)
              ·
                refine ⟨154052643295778711614383217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205403524394371615485844289 154052643295778711614383217)
                ·
                  refine ⟨115539482471834033710787413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154052643295778711614383217 115539482471834033710787413)
                  ·
                    refine ⟨676989155108402541274145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 115539482471834033710787413 676989155108402541274145)
                    ·
                      rfl

theorem cell23_3955295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 9].length) (baseStart_3955295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955295 prefixEnd_3955295 := by exact prefixLift 3955295
  have htrace : WordTrace (prefixWord ++ tailWord_3955295) baseStart_3955295 baseEnd_3955295 := by
    simpa [prefixWord, tailWord_3955295, baseEnd_3955295] using wordTrace_append hprefix tailTrace_3955295
  have hstable : (prefixWord ++ tailWord_3955295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955295).length < 2 ^ (prefixWord ++ tailWord_3955295).sum := by decide
  have hdescent : baseEnd_3955295 < baseStart_3955295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955319 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 4, 3, 2]
def baseStart_3955319 : Nat := 118140960795 + 3955319 * 2 ^ 59
def prefixEnd_3955319 : Nat := 4983230072969 + 3 ^ 40 * 3955319 * 2
def baseEnd_3955319 : Nat := 2030979788860915529922325

theorem tailTrace_3955319 : CollatzResearch.WordTrace tailWord_3955319 prefixEnd_3955319 2030979788860915529922325 := by
  unfold tailWord_3955319
  simp only [CollatzResearch.WordTrace]
  refine ⟨144262335557562252549837011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96174890371708168366558007 144262335557562252549837011)
  ·
    refine ⟨216393503336343378824755517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144262335557562252549837011 216393503336343378824755517)
    ·
      refine ⟨81147563751128767059283319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216393503336343378824755517 81147563751128767059283319)
      ·
        refine ⟨121721345626693150588924979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81147563751128767059283319 121721345626693150588924979)
        ·
          refine ⟨182582018440039725883387469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121721345626693150588924979 182582018440039725883387469)
          ·
            refine ⟨68468256915014897206270301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182582018440039725883387469 68468256915014897206270301)
            ·
              refine ⟨25675596343130586452351363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68468256915014897206270301 25675596343130586452351363)
              ·
                refine ⟨38513394514695879678527045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25675596343130586452351363 38513394514695879678527045)
                ·
                  refine ⟨7221261471505477439723821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38513394514695879678527045 7221261471505477439723821)
                  ·
                    refine ⟨2707973051814554039896433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7221261471505477439723821 2707973051814554039896433)
                    ·
                      refine ⟨2030979788860915529922325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2707973051814554039896433 2030979788860915529922325)
                      ·
                        rfl

theorem cell23_3955319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 3, 2].length) (baseStart_3955319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955319 prefixEnd_3955319 := by exact prefixLift 3955319
  have htrace : WordTrace (prefixWord ++ tailWord_3955319) baseStart_3955319 baseEnd_3955319 := by
    simpa [prefixWord, tailWord_3955319, baseEnd_3955319] using wordTrace_append hprefix tailTrace_3955319
  have hstable : (prefixWord ++ tailWord_3955319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955319).length < 2 ^ (prefixWord ++ tailWord_3955319).sum := by decide
  have hdescent : baseEnd_3955319 < baseStart_3955319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955346 : List Nat := [3, 2, 3, 1, 2, 1, 3, 2, 1, 5]
def baseStart_3955346 : Nat := 118140960795 + 3955346 * 2 ^ 59
def prefixEnd_3955346 : Nat := 4983230072969 + 3 ^ 40 * 3955346 * 2
def baseEnd_3955346 : Nat := 676997884279528974761567

theorem tailTrace_3955346 : CollatzResearch.WordTrace tailWord_3955346 prefixEnd_3955346 676997884279528974761567 := by
  unfold tailWord_3955346
  simp only [CollatzResearch.WordTrace]
  refine ⟨36065830082116109040267473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96175546885642957440713261 36065830082116109040267473)
  ·
    refine ⟨27049372561587081780200605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36065830082116109040267473 27049372561587081780200605)
    ·
      refine ⟨10143514710595155667575227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27049372561587081780200605 10143514710595155667575227)
      ·
        refine ⟨15215272065892733501362841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10143514710595155667575227 15215272065892733501362841)
        ·
          refine ⟨11411454049419550126022131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15215272065892733501362841 11411454049419550126022131)
          ·
            refine ⟨17117181074129325189033197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11411454049419550126022131 17117181074129325189033197)
            ·
              refine ⟨6418942902798496945887449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17117181074129325189033197 6418942902798496945887449)
              ·
                refine ⟨4814207177098872709415587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6418942902798496945887449 4814207177098872709415587)
                ·
                  refine ⟨7221310765648309064123381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4814207177098872709415587 7221310765648309064123381)
                  ·
                    refine ⟨676997884279528974761567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7221310765648309064123381 676997884279528974761567)
                    ·
                      rfl

theorem cell23_3955346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_3955346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955346 prefixEnd_3955346 := by exact prefixLift 3955346
  have htrace : WordTrace (prefixWord ++ tailWord_3955346) baseStart_3955346 baseEnd_3955346 := by
    simpa [prefixWord, tailWord_3955346, baseEnd_3955346] using wordTrace_append hprefix tailTrace_3955346
  have hstable : (prefixWord ++ tailWord_3955346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955346).length < 2 ^ (prefixWord ++ tailWord_3955346).sum := by decide
  have hdescent : baseEnd_3955346 < baseStart_3955346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955389 : List Nat := [1, 4, 1, 2, 1, 5, 1, 8]
def baseStart_3955389 : Nat := 118140960795 + 3955389 * 2 ^ 59
def prefixEnd_3955389 : Nat := 4983230072969 + 3 ^ 40 * 3955389 * 2
def baseEnd_3955389 : Nat := 75222804907656676149889

theorem tailTrace_3955389 : CollatzResearch.WordTrace tailWord_3955389 prefixEnd_3955389 75222804907656676149889 := by
  unfold tailWord_3955389
  simp only [CollatzResearch.WordTrace]
  refine ⟨144264888667308654504885221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96176592444872436336590147 144264888667308654504885221)
  ·
    refine ⟨27049666625120372719665979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144264888667308654504885221 27049666625120372719665979)
    ·
      refine ⟨40574499937680559079498969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27049666625120372719665979 40574499937680559079498969)
      ·
        refine ⟨30430874953260419309624227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40574499937680559079498969 30430874953260419309624227)
        ·
          refine ⟨45646312429890628964436341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30430874953260419309624227 45646312429890628964436341)
          ·
            refine ⟨4279341790302246465415907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45646312429890628964436341 4279341790302246465415907)
            ·
              refine ⟨6419012685453369698123861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4279341790302246465415907 6419012685453369698123861)
              ·
                refine ⟨75222804907656676149889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6419012685453369698123861 75222804907656676149889)
                ·
                  rfl

theorem cell23_3955389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 8].length) (baseStart_3955389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955389 prefixEnd_3955389 := by exact prefixLift 3955389
  have htrace : WordTrace (prefixWord ++ tailWord_3955389) baseStart_3955389 baseEnd_3955389 := by
    simpa [prefixWord, tailWord_3955389, baseEnd_3955389] using wordTrace_append hprefix tailTrace_3955389
  have hstable : (prefixWord ++ tailWord_3955389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955389).length < 2 ^ (prefixWord ++ tailWord_3955389).sum := by decide
  have hdescent : baseEnd_3955389 < baseStart_3955389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955393 : List Nat := [1, 2, 6, 2, 1, 1, 2, 1, 1, 6]
def baseStart_3955393 : Nat := 118140960795 + 3955393 * 2 ^ 59
def prefixEnd_3955393 : Nat := 4983230072969 + 3 ^ 40 * 3955393 * 2
def baseEnd_3955393 : Nat := 677005928809782746798995

theorem tailTrace_3955393 : CollatzResearch.WordTrace tailWord_3955393 prefixEnd_3955393 677005928809782746798995 := by
  unfold tailWord_3955393
  simp only [CollatzResearch.WordTrace]
  refine ⟨144265034559294163188030833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96176689706196108792020555 144265034559294163188030833)
  ·
    refine ⟨108198775919470622391023125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144265034559294163188030833 108198775919470622391023125)
    ·
      refine ⟨5071817621225185424579209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108198775919470622391023125 5071817621225185424579209)
      ·
        refine ⟨3803863215918889068434407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5071817621225185424579209 3803863215918889068434407)
        ·
          refine ⟨5705794823878333602651611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3803863215918889068434407 5705794823878333602651611)
          ·
            refine ⟨8558692235817500403977417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5705794823878333602651611 8558692235817500403977417)
            ·
              refine ⟨6419019176863125302983063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8558692235817500403977417 6419019176863125302983063)
              ·
                refine ⟨9628528765294687954474595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6419019176863125302983063 9628528765294687954474595)
                ·
                  refine ⟨14442793147942031931711893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9628528765294687954474595 14442793147942031931711893)
                  ·
                    refine ⟨677005928809782746798995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14442793147942031931711893 677005928809782746798995)
                    ·
                      rfl

theorem cell23_3955393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_3955393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955393 prefixEnd_3955393 := by exact prefixLift 3955393
  have htrace : WordTrace (prefixWord ++ tailWord_3955393) baseStart_3955393 baseEnd_3955393 := by
    simpa [prefixWord, tailWord_3955393, baseEnd_3955393] using wordTrace_append hprefix tailTrace_3955393
  have hstable : (prefixWord ++ tailWord_3955393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955393).length < 2 ^ (prefixWord ++ tailWord_3955393).sum := by decide
  have hdescent : baseEnd_3955393 < baseStart_3955393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955396 : List Nat := [2, 3, 3, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_3955396 : Nat := 118140960795 + 3955396 * 2 ^ 59
def prefixEnd_3955396 : Nat := 4983230072969 + 3 ^ 40 * 3955396 * 2
def baseEnd_3955396 : Nat := 2031019326871311728659471

theorem tailTrace_3955396 : CollatzResearch.WordTrace tailWord_3955396 prefixEnd_3955396 2031019326871311728659471 := by
  unfold tailWord_3955396
  simp only [CollatzResearch.WordTrace]
  refine ⟨72132571989141647350195021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96176762652188863133593361 72132571989141647350195021)
  ·
    refine ⟨27049714495928117756323133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72132571989141647350195021 27049714495928117756323133)
    ·
      refine ⟨10143642935973044158621175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27049714495928117756323133 10143642935973044158621175)
      ·
        refine ⟨15215464403959566237931763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10143642935973044158621175 15215464403959566237931763)
        ·
          refine ⟨22823196605939349356897645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15215464403959566237931763 22823196605939349356897645)
          ·
            refine ⟨8558698727227256008836617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22823196605939349356897645 8558698727227256008836617)
            ·
              refine ⟨6419024045420442006627463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8558698727227256008836617 6419024045420442006627463)
              ·
                refine ⟨9628536068130663009941195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6419024045420442006627463 9628536068130663009941195)
                ·
                  refine ⟨14442804102195994514911793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9628536068130663009941195 14442804102195994514911793)
                  ·
                    refine ⟨10832103076646995886183845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14442804102195994514911793 10832103076646995886183845)
                    ·
                      refine ⟨2031019326871311728659471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10832103076646995886183845 2031019326871311728659471)
                      ·
                        rfl

theorem cell23_3955396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_3955396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955396 prefixEnd_3955396 := by exact prefixLift 3955396
  have htrace : WordTrace (prefixWord ++ tailWord_3955396) baseStart_3955396 baseEnd_3955396 := by
    simpa [prefixWord, tailWord_3955396, baseEnd_3955396] using wordTrace_append hprefix tailTrace_3955396
  have hstable : (prefixWord ++ tailWord_3955396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955396).length < 2 ^ (prefixWord ++ tailWord_3955396).sum := by decide
  have hdescent : baseEnd_3955396 < baseStart_3955396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955420 : List Nat := [2, 2, 5, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_3955420 : Nat := 118140960795 + 3955420 * 2 ^ 59
def prefixEnd_3955420 : Nat := 4983230072969 + 3 ^ 40 * 3955420 * 2
def baseEnd_3955420 : Nat := 2031031650407019634759361

theorem tailTrace_3955420 : CollatzResearch.WordTrace tailWord_3955420 prefixEnd_3955420 2031031650407019634759361 := by
  unfold tailWord_3955420
  simp only [CollatzResearch.WordTrace]
  refine ⟨72133009665098173399631857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96177346220130897866175809 72133009665098173399631857)
  ·
    refine ⟨54099757248823630049723893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72133009665098173399631857 54099757248823630049723893)
    ·
      refine ⟨5071852242077215317161615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54099757248823630049723893 5071852242077215317161615)
      ·
        refine ⟨7607778363115822975742423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5071852242077215317161615 7607778363115822975742423)
        ·
          refine ⟨11411667544673734463613635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7607778363115822975742423 11411667544673734463613635)
          ·
            refine ⟨17117501317010601695420453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11411667544673734463613635 17117501317010601695420453)
            ·
              refine ⟨3209531496939487817891335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17117501317010601695420453 3209531496939487817891335)
              ·
                refine ⟨4814297245409231726837003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3209531496939487817891335 4814297245409231726837003)
                ·
                  refine ⟨7221445868113847590255505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4814297245409231726837003 7221445868113847590255505)
                  ·
                    refine ⟨5416084401085385692691629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7221445868113847590255505 5416084401085385692691629)
                    ·
                      refine ⟨2031031650407019634759361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5416084401085385692691629 2031031650407019634759361)
                      ·
                        rfl

theorem cell23_3955420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_3955420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955420 prefixEnd_3955420 := by exact prefixLift 3955420
  have htrace : WordTrace (prefixWord ++ tailWord_3955420) baseStart_3955420 baseEnd_3955420 := by
    simpa [prefixWord, tailWord_3955420, baseEnd_3955420] using wordTrace_append hprefix tailTrace_3955420
  have hstable : (prefixWord ++ tailWord_3955420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955420).length < 2 ^ (prefixWord ++ tailWord_3955420).sum := by decide
  have hdescent : baseEnd_3955420 < baseStart_3955420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955456 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 8, 2, 2]
def baseStart_3955456 : Nat := 118140960795 + 3955456 * 2 ^ 59
def prefixEnd_3955456 : Nat := 4983230072969 + 3 ^ 40 * 3955456 * 2
def baseEnd_3955456 : Nat := 2031050135710581493909195

theorem tailTrace_3955456 : CollatzResearch.WordTrace tailWord_3955456 prefixEnd_3955456 2031050135710581493909195 := by
  unfold tailWord_3955456
  simp only [CollatzResearch.WordTrace]
  refine ⟨72133666179032962473787111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96178221572043949965049481 72133666179032962473787111)
  ·
    refine ⟨108200499268549443710680667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72133666179032962473787111 108200499268549443710680667)
    ·
      refine ⟨162300748902824165566021001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108200499268549443710680667 162300748902824165566021001)
      ·
        refine ⟨121725561677118124174515751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162300748902824165566021001 121725561677118124174515751)
        ·
          refine ⟨182588342515677186261773627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121725561677118124174515751 182588342515677186261773627)
          ·
            refine ⟨273882513773515779392660441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182588342515677186261773627 273882513773515779392660441)
            ·
              refine ⟨205411885330136834544495331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273882513773515779392660441 205411885330136834544495331)
              ·
                refine ⟨308117827995205251816742997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205411885330136834544495331 308117827995205251816742997)
                ·
                  refine ⟨3610755796818811544727457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 308117827995205251816742997 3610755796818811544727457)
                  ·
                    refine ⟨2708066847614108658545593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3610755796818811544727457 2708066847614108658545593)
                    ·
                      refine ⟨2031050135710581493909195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2708066847614108658545593 2031050135710581493909195)
                      ·
                        rfl

theorem cell23_3955456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 8, 2, 2].length) (baseStart_3955456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955456 prefixEnd_3955456 := by exact prefixLift 3955456
  have htrace : WordTrace (prefixWord ++ tailWord_3955456) baseStart_3955456 baseEnd_3955456 := by
    simpa [prefixWord, tailWord_3955456, baseEnd_3955456] using wordTrace_append hprefix tailTrace_3955456
  have hstable : (prefixWord ++ tailWord_3955456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955456).length < 2 ^ (prefixWord ++ tailWord_3955456).sum := by decide
  have hdescent : baseEnd_3955456 < baseStart_3955456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955501 : List Nat := [1, 5, 3, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_3955501 : Nat := 118140960795 + 3955501 * 2 ^ 59
def prefixEnd_3955501 : Nat := 4983230072969 + 3 ^ 40 * 3955501 * 2
def baseEnd_3955501 : Nat := 2031073242340033817846489

theorem tailTrace_3955501 : CollatzResearch.WordTrace tailWord_3955501 prefixEnd_3955501 2031073242340033817846489 := by
  unfold tailWord_3955501
  simp only [CollatzResearch.WordTrace]
  refine ⟨144268973642902897632962357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96179315761935265088641571 144268973642902897632962357)
  ·
    refine ⟨13525216279022146653090221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144268973642902897632962357 13525216279022146653090221)
    ·
      refine ⟨5071956104633304994908833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13525216279022146653090221 5071956104633304994908833)
      ·
        refine ⟨3803967078474978746181625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5071956104633304994908833 3803967078474978746181625)
        ·
          refine ⟨2852975308856234059636219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3803967078474978746181625 2852975308856234059636219)
          ·
            refine ⟨4279462963284351089454329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2852975308856234059636219 4279462963284351089454329)
            ·
              refine ⟨3209597222463263317090747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4279462963284351089454329 3209597222463263317090747)
              ·
                refine ⟨4814395833694894975636121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3209597222463263317090747 4814395833694894975636121)
                ·
                  refine ⟨3610796875271171231727091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4814395833694894975636121 3610796875271171231727091)
                  ·
                    refine ⟨5416195312906756847590637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3610796875271171231727091 5416195312906756847590637)
                    ·
                      refine ⟨2031073242340033817846489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5416195312906756847590637 2031073242340033817846489)
                      ·
                        rfl

theorem cell23_3955501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_3955501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955501 prefixEnd_3955501 := by exact prefixLift 3955501
  have htrace : WordTrace (prefixWord ++ tailWord_3955501) baseStart_3955501 baseEnd_3955501 := by
    simpa [prefixWord, tailWord_3955501, baseEnd_3955501] using wordTrace_append hprefix tailTrace_3955501
  have hstable : (prefixWord ++ tailWord_3955501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955501).length < 2 ^ (prefixWord ++ tailWord_3955501).sum := by decide
  have hdescent : baseEnd_3955501 < baseStart_3955501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955507 : List Nat := [1, 1, 1, 2, 6, 3, 2, 1, 2, 2, 2]
def baseStart_3955507 : Nat := 118140960795 + 3955507 * 2 ^ 59
def prefixEnd_3955507 : Nat := 4983230072969 + 3 ^ 40 * 3955507 * 2
def baseEnd_3955507 : Nat := 2031076323223960794371461

theorem tailTrace_3955507 : CollatzResearch.WordTrace tailWord_3955507 prefixEnd_3955507 2031076323223960794371461 := by
  unfold tailWord_3955507
  simp only [CollatzResearch.WordTrace]
  refine ⟨144269192480881160657680775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96179461653920773771787183 144269192480881160657680775)
  ·
    refine ⟨216403788721321740986521163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144269192480881160657680775 216403788721321740986521163)
    ·
      refine ⟨324605683081982611479781745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216403788721321740986521163 324605683081982611479781745)
      ·
        refine ⟨243454262311486958609836309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324605683081982611479781745 243454262311486958609836309)
        ·
          refine ⟨11411918545850951184836077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 243454262311486958609836309 11411918545850951184836077)
          ·
            refine ⟨4279469454694106694313529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11411918545850951184836077 4279469454694106694313529)
            ·
              refine ⟨3209602091020580020735147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4279469454694106694313529 3209602091020580020735147)
              ·
                refine ⟨4814403136530870031102721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3209602091020580020735147 4814403136530870031102721)
                ·
                  refine ⟨3610802352398152523327041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4814403136530870031102721 3610802352398152523327041)
                  ·
                    refine ⟨2708101764298614392495281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3610802352398152523327041 2708101764298614392495281)
                    ·
                      refine ⟨2031076323223960794371461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2708101764298614392495281 2031076323223960794371461)
                      ·
                        rfl

theorem cell23_3955507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 2, 2, 2].length) (baseStart_3955507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955507 prefixEnd_3955507 := by exact prefixLift 3955507
  have htrace : WordTrace (prefixWord ++ tailWord_3955507) baseStart_3955507 baseEnd_3955507 := by
    simpa [prefixWord, tailWord_3955507, baseEnd_3955507] using wordTrace_append hprefix tailTrace_3955507
  have hstable : (prefixWord ++ tailWord_3955507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955507).length < 2 ^ (prefixWord ++ tailWord_3955507).sum := by decide
  have hdescent : baseEnd_3955507 < baseStart_3955507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955546 : List Nat := [3, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4]
def baseStart_3955546 : Nat := 118140960795 + 3955546 * 2 ^ 59
def prefixEnd_3955546 : Nat := 4983230072969 + 3 ^ 40 * 3955546 * 2
def baseEnd_3955546 : Nat := 2031096348969486141783781

theorem tailTrace_3955546 : CollatzResearch.WordTrace tailWord_3955546 prefixEnd_3955546 2031096348969486141783781 := by
  unfold tailWord_3955546
  simp only [CollatzResearch.WordTrace]
  refine ⟨36067653731934967579587623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96180409951826580212233661 36067653731934967579587623)
  ·
    refine ⟨54101480597902451369381435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36067653731934967579587623 54101480597902451369381435)
    ·
      refine ⟨81152220896853677054072153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54101480597902451369381435 81152220896853677054072153)
      ·
        refine ⟨60864165672640257790554115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81152220896853677054072153 60864165672640257790554115)
        ·
          refine ⟨91296248508960386685831173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60864165672640257790554115 91296248508960386685831173)
          ·
            refine ⟨17118046595430072503593345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91296248508960386685831173 17118046595430072503593345)
            ·
              refine ⟨12838534946572554377695009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17118046595430072503593345 12838534946572554377695009)
              ·
                refine ⟨9628901209929415783271257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12838534946572554377695009 9628901209929415783271257)
                ·
                  refine ⟨7221675907447061837453443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9628901209929415783271257 7221675907447061837453443)
                  ·
                    refine ⟨10832513861170592756180165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7221675907447061837453443 10832513861170592756180165)
                    ·
                      refine ⟨2031096348969486141783781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10832513861170592756180165 2031096348969486141783781)
                      ·
                        rfl

theorem cell23_3955546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_3955546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955546 prefixEnd_3955546 := by exact prefixLift 3955546
  have htrace : WordTrace (prefixWord ++ tailWord_3955546) baseStart_3955546 baseEnd_3955546 := by
    simpa [prefixWord, tailWord_3955546, baseEnd_3955546] using wordTrace_append hprefix tailTrace_3955546
  have hstable : (prefixWord ++ tailWord_3955546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955546).length < 2 ^ (prefixWord ++ tailWord_3955546).sum := by decide
  have hdescent : baseEnd_3955546 < baseStart_3955546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955573 : List Nat := [1, 3, 4, 1, 1, 3, 1, 2, 3, 4]
def baseStart_3955573 : Nat := 118140960795 + 3955573 * 2 ^ 59
def prefixEnd_3955573 : Nat := 4983230072969 + 3 ^ 40 * 3955573 * 2
def baseEnd_3955573 : Nat := 677036737649052512048719

theorem tailTrace_3955573 : CollatzResearch.WordTrace tailWord_3955573 prefixEnd_3955573 677036737649052512048719 := by
  unfold tailWord_3955573
  simp only [CollatzResearch.WordTrace]
  refine ⟨144271599698642053929583373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96181066465761369286388915 144271599698642053929583373)
  ·
    refine ⟨54101849886990770223593765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144271599698642053929583373 54101849886990770223593765)
    ·
      refine ⟨10144096853810769416923831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54101849886990770223593765 10144096853810769416923831)
      ·
        refine ⟨15216145280716154125385747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10144096853810769416923831 15216145280716154125385747)
        ·
          refine ⟨22824217921074231188078621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15216145280716154125385747 22824217921074231188078621)
          ·
            refine ⟨8559081720402836695529483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22824217921074231188078621 8559081720402836695529483)
            ·
              refine ⟨12838622580604255043294225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8559081720402836695529483 12838622580604255043294225)
              ·
                refine ⟨9628966935453191282470669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12838622580604255043294225 9628966935453191282470669)
                ·
                  refine ⟨3610862600794946730926501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9628966935453191282470669 3610862600794946730926501)
                  ·
                    refine ⟨677036737649052512048719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3610862600794946730926501 677036737649052512048719)
                    ·
                      rfl

theorem cell23_3955573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_3955573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955573 prefixEnd_3955573 := by exact prefixLift 3955573
  have htrace : WordTrace (prefixWord ++ tailWord_3955573) baseStart_3955573 baseEnd_3955573 := by
    simpa [prefixWord, tailWord_3955573, baseEnd_3955573] using wordTrace_append hprefix tailTrace_3955573
  have hstable : (prefixWord ++ tailWord_3955573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955573).length < 2 ^ (prefixWord ++ tailWord_3955573).sum := by decide
  have hdescent : baseEnd_3955573 < baseStart_3955573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955646 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_3955646 : Nat := 118140960795 + 3955646 * 2 ^ 59
def prefixEnd_3955646 : Nat := 4983230072969 + 3 ^ 40 * 3955646 * 2
def baseEnd_3955646 : Nat := 677049232344978583511107

theorem tailTrace_3955646 : CollatzResearch.WordTrace tailWord_3955646 prefixEnd_3955646 677049232344978583511107 := by
  unfold tailWord_3955646
  simp only [CollatzResearch.WordTrace]
  refine ⟨18034282778422198424623849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96182841484918391597993861 18034282778422198424623849)
  ·
    refine ⟨13525712083816648818467887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18034282778422198424623849 13525712083816648818467887)
    ·
      refine ⟨20288568125724973227701831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13525712083816648818467887 20288568125724973227701831)
      ·
        refine ⟨30432852188587459841552747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20288568125724973227701831 30432852188587459841552747)
        ·
          refine ⟨45649278282881189762329121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30432852188587459841552747 45649278282881189762329121)
          ·
            refine ⟨34236958712160892321746841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45649278282881189762329121 34236958712160892321746841)
            ·
              refine ⟨25677719034120669241310131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34236958712160892321746841 25677719034120669241310131)
              ·
                refine ⟨38516578551181003861965197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25677719034120669241310131 38516578551181003861965197)
                ·
                  refine ⟨14443716956692876448236949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38516578551181003861965197 14443716956692876448236949)
                  ·
                    refine ⟨677049232344978583511107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14443716956692876448236949 677049232344978583511107)
                    ·
                      rfl

theorem cell23_3955646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_3955646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955646 prefixEnd_3955646 := by exact prefixLift 3955646
  have htrace : WordTrace (prefixWord ++ tailWord_3955646) baseStart_3955646 baseEnd_3955646 := by
    simpa [prefixWord, tailWord_3955646, baseEnd_3955646] using wordTrace_append hprefix tailTrace_3955646
  have hstable : (prefixWord ++ tailWord_3955646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955646).length < 2 ^ (prefixWord ++ tailWord_3955646).sum := by decide
  have hdescent : baseEnd_3955646 < baseStart_3955646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955659 : List Nat := [1, 1, 1, 1, 3, 5, 11]
def baseStart_3955659 : Nat := 118140960795 + 3955659 * 2 ^ 59
def prefixEnd_3955659 : Nat := 4983230072969 + 3 ^ 40 * 3955659 * 2
def baseEnd_3955659 : Nat := 25075979904733879008281

theorem tailTrace_3955659 : CollatzResearch.WordTrace tailWord_3955659 prefixEnd_3955659 25075979904733879008281 := by
  unfold tailWord_3955659
  simp only [CollatzResearch.WordTrace]
  refine ⟨144274736376330490617214031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96183157584220327078142687 144274736376330490617214031)
  ·
    refine ⟨216412104564495735925821047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144274736376330490617214031 216412104564495735925821047)
    ·
      refine ⟨324618156846743603888731571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216412104564495735925821047 324618156846743603888731571)
      ·
        refine ⟨486927235270115405833097357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324618156846743603888731571 486927235270115405833097357)
        ·
          refine ⟨182597713226293277187411509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 486927235270115405833097357 182597713226293277187411509)
          ·
            refine ⟨17118535614964994736319829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182597713226293277187411509 17118535614964994736319829)
            ·
              refine ⟨25075979904733879008281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17118535614964994736319829 25075979904733879008281)
              ·
                rfl

theorem cell23_3955659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 11].length) (baseStart_3955659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955659 prefixEnd_3955659 := by exact prefixLift 3955659
  have htrace : WordTrace (prefixWord ++ tailWord_3955659) baseStart_3955659 baseEnd_3955659 := by
    simpa [prefixWord, tailWord_3955659, baseEnd_3955659] using wordTrace_append hprefix tailTrace_3955659
  have hstable : (prefixWord ++ tailWord_3955659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955659).length < 2 ^ (prefixWord ++ tailWord_3955659).sum := by decide
  have hdescent : baseEnd_3955659 < baseStart_3955659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955690 : List Nat := [3, 1, 3, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_3955690 : Nat := 118140960795 + 3955690 * 2 ^ 59
def prefixEnd_3955690 : Nat := 4983230072969 + 3 ^ 40 * 3955690 * 2
def baseEnd_3955690 : Nat := 2031170290183733578383119

theorem tailTrace_3955690 : CollatzResearch.WordTrace tailWord_3955690 prefixEnd_3955690 2031170290183733578383119 := by
  unfold tailWord_3955690
  simp only [CollatzResearch.WordTrace]
  refine ⟨36068966759804545727898131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96183911359478788607728349 36068966759804545727898131)
  ·
    refine ⟨54103450139706818591847197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36068966759804545727898131 54103450139706818591847197)
    ·
      refine ⟨20288793802390056971942699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54103450139706818591847197 20288793802390056971942699)
      ·
        refine ⟨30433190703585085457914049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20288793802390056971942699 30433190703585085457914049)
        ·
          refine ⟨22824893027688814093435537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30433190703585085457914049 22824893027688814093435537)
          ·
            refine ⟨17118669770766610570076653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22824893027688814093435537 17118669770766610570076653)
            ·
              refine ⟨6419501164037478963778745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17118669770766610570076653 6419501164037478963778745)
              ·
                refine ⟨4814625873028109222834059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6419501164037478963778745 4814625873028109222834059)
                ·
                  refine ⟨7221938809542163834251089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4814625873028109222834059 7221938809542163834251089)
                  ·
                    refine ⟨5416454107156622875688317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7221938809542163834251089 5416454107156622875688317)
                    ·
                      refine ⟨2031170290183733578383119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5416454107156622875688317 2031170290183733578383119)
                      ·
                        rfl

theorem cell23_3955690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_3955690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3955690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3955690 prefixEnd_3955690 := by exact prefixLift 3955690
  have htrace : WordTrace (prefixWord ++ tailWord_3955690) baseStart_3955690 baseEnd_3955690 := by
    simpa [prefixWord, tailWord_3955690, baseEnd_3955690] using wordTrace_append hprefix tailTrace_3955690
  have hstable : (prefixWord ++ tailWord_3955690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955690).length < 2 ^ (prefixWord ++ tailWord_3955690).sum := by decide
  have hdescent : baseEnd_3955690 < baseStart_3955690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
