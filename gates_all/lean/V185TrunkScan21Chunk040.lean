import V185TrunkScan21Chunk039

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_483649 : List Nat := [1, 2, 5, 2, 3, 1, 1, 3, 3]
def baseStart_483649 : Nat := 118140960795 + 483649 * 2 ^ 59
def prefixEnd_483649 : Nat := 4983230072969 + 3 ^ 40 * 483649 * 2
def baseEnd_483649 : Nat := 110375291140659313228109

theorem tailTrace_483649 : CollatzResearch.WordTrace tailWord_483649 prefixEnd_483649 110375291140659313228109 := by
  unfold tailWord_483649
  simp only [CollatzResearch.WordTrace]
  refine ⟨17640128224829748518134001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11760085483219832345422667 17640128224829748518134001)
  ·
    refine ⟨13230096168622311388600501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17640128224829748518134001 13230096168622311388600501)
    ·
      refine ⟨1240321515808341692681297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13230096168622311388600501 1240321515808341692681297)
      ·
        refine ⟨930241136856256269510973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1240321515808341692681297 930241136856256269510973)
        ·
          refine ⟨348840426321096101066615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 930241136856256269510973 348840426321096101066615)
          ·
            refine ⟨523260639481644151599923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348840426321096101066615 523260639481644151599923)
            ·
              refine ⟨784890959222466227399885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523260639481644151599923 784890959222466227399885)
              ·
                refine ⟨294334109708424835274957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 784890959222466227399885 294334109708424835274957)
                ·
                  refine ⟨110375291140659313228109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294334109708424835274957 110375291140659313228109)
                  ·
                    rfl

theorem cell21_483649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 3].length) (baseStart_483649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_483649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_483649 prefixEnd_483649 := by exact prefixLift 483649
  have htrace : WordTrace (prefixWord ++ tailWord_483649) baseStart_483649 baseEnd_483649 := by
    simpa [prefixWord, tailWord_483649, baseEnd_483649] using wordTrace_append hprefix tailTrace_483649
  have hstable : (prefixWord ++ tailWord_483649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483649).length < 2 ^ (prefixWord ++ tailWord_483649).sum := by decide
  have hdescent : baseEnd_483649 < baseStart_483649 := by decide
  rcases family_descends (prefixWord ++ tailWord_483649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483671 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 6]
def baseStart_483671 : Nat := 118140960795 + 483671 * 2 ^ 59
def prefixEnd_483671 : Nat := 4983230072969 + 3 ^ 40 * 483671 * 2
def baseEnd_483671 : Nat := 110380311840392163861397

theorem tailTrace_483671 : CollatzResearch.WordTrace tailWord_483671 prefixEnd_483671 110380311840392163861397 := by
  unfold tailWord_483671
  simp only [CollatzResearch.WordTrace]
  refine ⟨17640930630750046275434867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11760620420500030850289911 17640930630750046275434867)
  ·
    refine ⟨26461395946125069413152301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17640930630750046275434867 26461395946125069413152301)
    ·
      refine ⟨9923023479796901029932113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26461395946125069413152301 9923023479796901029932113)
      ·
        refine ⟨7442267609847675772449085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9923023479796901029932113 7442267609847675772449085)
        ·
          refine ⟨2790850353692878414668407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7442267609847675772449085 2790850353692878414668407)
          ·
            refine ⟨4186275530539317622002611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2790850353692878414668407 4186275530539317622002611)
            ·
              refine ⟨6279413295808976433003917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4186275530539317622002611 6279413295808976433003917)
              ·
                refine ⟨2354779985928366162376469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6279413295808976433003917 2354779985928366162376469)
                ·
                  refine ⟨110380311840392163861397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2354779985928366162376469 110380311840392163861397)
                  ·
                    rfl

theorem cell21_483671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 6].length) (baseStart_483671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_483671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_483671 prefixEnd_483671 := by exact prefixLift 483671
  have htrace : WordTrace (prefixWord ++ tailWord_483671) baseStart_483671 baseEnd_483671 := by
    simpa [prefixWord, tailWord_483671, baseEnd_483671] using wordTrace_append hprefix tailTrace_483671
  have hstable : (prefixWord ++ tailWord_483671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483671).length < 2 ^ (prefixWord ++ tailWord_483671).sum := by decide
  have hdescent : baseEnd_483671 < baseStart_483671 := by decide
  rcases family_descends (prefixWord ++ tailWord_483671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483722 : List Nat := [3, 1, 2, 5, 1, 1, 2, 2, 4]
def baseStart_483722 : Nat := 118140960795 + 483722 * 2 ^ 59
def prefixEnd_483722 : Nat := 4983230072969 + 3 ^ 40 * 483722 * 2
def baseEnd_483722 : Nat := 110391950735227408511293

theorem tailTrace_483722 : CollatzResearch.WordTrace tailWord_483722 prefixEnd_483722 110391950735227408511293 := by
  unfold tailWord_483722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4410697688391320496385355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11761860502376854657027613 4410697688391320496385355)
  ·
    refine ⟨6616046532586980744578033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4410697688391320496385355 6616046532586980744578033)
    ·
      refine ⟨4962034899440235558433525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6616046532586980744578033 4962034899440235558433525)
      ·
        refine ⟨465190771822522083603143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4962034899440235558433525 465190771822522083603143)
        ·
          refine ⟨697786157733783125404715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465190771822522083603143 697786157733783125404715)
          ·
            refine ⟨1046679236600674688107073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697786157733783125404715 1046679236600674688107073)
            ·
              refine ⟨785009427450506016080305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046679236600674688107073 785009427450506016080305)
              ·
                refine ⟨588757070587879512060229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785009427450506016080305 588757070587879512060229)
                ·
                  refine ⟨110391950735227408511293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 588757070587879512060229 110391950735227408511293)
                  ·
                    rfl

theorem cell21_483722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_483722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_483722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_483722 prefixEnd_483722 := by exact prefixLift 483722
  have htrace : WordTrace (prefixWord ++ tailWord_483722) baseStart_483722 baseEnd_483722 := by
    simpa [prefixWord, tailWord_483722, baseEnd_483722] using wordTrace_append hprefix tailTrace_483722
  have hstable : (prefixWord ++ tailWord_483722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483722).length < 2 ^ (prefixWord ++ tailWord_483722).sum := by decide
  have hdescent : baseEnd_483722 < baseStart_483722 := by decide
  rcases family_descends (prefixWord ++ tailWord_483722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483798 : List Nat := [5, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_483798 : Nat := 118140960795 + 483798 * 2 ^ 59
def prefixEnd_483798 : Nat := 4983230072969 + 3 ^ 40 * 483798 * 2
def baseEnd_483798 : Nat := 110409294970668165244471

theorem tailTrace_483798 : CollatzResearch.WordTrace tailWord_483798 prefixEnd_483798 110409294970668165244471 := by
  unfold tailWord_483798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1102847668830621685331753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11763708467526631310205365 1102847668830621685331753)
  ·
    refine ⟨827135751622966263998815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1102847668830621685331753 827135751622966263998815)
    ·
      refine ⟨1240703627434449395998223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 827135751622966263998815 1240703627434449395998223)
      ·
        refine ⟨1861055441151674093997335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240703627434449395998223 1861055441151674093997335)
        ·
          refine ⟨2791583161727511140996003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1861055441151674093997335 2791583161727511140996003)
          ·
            refine ⟨4187374742591266711494005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791583161727511140996003 4187374742591266711494005)
            ·
              refine ⟨392566382117931254202563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4187374742591266711494005 392566382117931254202563)
              ·
                refine ⟨588849573176896881303845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392566382117931254202563 588849573176896881303845)
                ·
                  refine ⟨110409294970668165244471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 588849573176896881303845 110409294970668165244471)
                  ·
                    rfl

theorem cell21_483798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_483798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_483798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_483798 prefixEnd_483798 := by exact prefixLift 483798
  have htrace : WordTrace (prefixWord ++ tailWord_483798) baseStart_483798 baseEnd_483798 := by
    simpa [prefixWord, tailWord_483798, baseEnd_483798] using wordTrace_append hprefix tailTrace_483798
  have hstable : (prefixWord ++ tailWord_483798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483798).length < 2 ^ (prefixWord ++ tailWord_483798).sum := by decide
  have hdescent : baseEnd_483798 < baseStart_483798 := by decide
  rcases family_descends (prefixWord ++ tailWord_483798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483854 : List Nat := [4, 1, 1, 2, 3, 1, 1, 8]
def baseStart_483854 : Nat := 118140960795 + 483854 * 2 ^ 59
def prefixEnd_483854 : Nat := 4983230072969 + 3 ^ 40 * 483854 * 2
def baseEnd_483854 : Nat := 36807358311208170770341

theorem tailTrace_483854 : CollatzResearch.WordTrace tailWord_483854 prefixEnd_483854 36807358311208170770341 := by
  unfold tailWord_483854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2205950648635883566168327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11765070126058045686231077 2205950648635883566168327)
  ·
    refine ⟨3308925972953825349252491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2205950648635883566168327 3308925972953825349252491)
    ·
      refine ⟨4963388959430738023878737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3308925972953825349252491 4963388959430738023878737)
      ·
        refine ⟨3722541719573053517909053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4963388959430738023878737 3722541719573053517909053)
        ·
          refine ⟨1395953144839895069215895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3722541719573053517909053 1395953144839895069215895)
          ·
            refine ⟨2093929717259842603823843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395953144839895069215895 2093929717259842603823843)
            ·
              refine ⟨3140894575889763905735765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093929717259842603823843 3140894575889763905735765)
              ·
                refine ⟨36807358311208170770341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3140894575889763905735765 36807358311208170770341)
                ·
                  rfl

theorem cell21_483854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_483854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_483854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_483854 prefixEnd_483854 := by exact prefixLift 483854
  have htrace : WordTrace (prefixWord ++ tailWord_483854) baseStart_483854 baseEnd_483854 := by
    simpa [prefixWord, tailWord_483854, baseEnd_483854] using wordTrace_append hprefix tailTrace_483854
  have hstable : (prefixWord ++ tailWord_483854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483854).length < 2 ^ (prefixWord ++ tailWord_483854).sum := by decide
  have hdescent : baseEnd_483854 < baseStart_483854 := by decide
  rcases family_descends (prefixWord ++ tailWord_483854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_483961 : List Nat := [1, 2, 1, 3, 3, 3, 2, 1, 5]
def baseStart_483961 : Nat := 118140960795 + 483961 * 2 ^ 59
def prefixEnd_483961 : Nat := 4983230072969 + 3 ^ 40 * 483961 * 2
def baseEnd_483961 : Nat := 110446493791416104027471

theorem tailTrace_483961 : CollatzResearch.WordTrace tailWord_483961 prefixEnd_483961 110446493791416104027471 := by
  unfold tailWord_483961
  simp only [CollatzResearch.WordTrace]
  refine ⟨17651507799699425803491737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11767671866466283868994491 17651507799699425803491737)
  ·
    refine ⟨13238630849774569352618803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17651507799699425803491737 13238630849774569352618803)
    ·
      refine ⟨19857946274661854028928205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13238630849774569352618803 19857946274661854028928205)
      ·
        refine ⟨7446729852998195260848077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19857946274661854028928205 7446729852998195260848077)
        ·
          refine ⟨2792523694874323222818029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7446729852998195260848077 2792523694874323222818029)
          ·
            refine ⟨1047196385577871208556761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2792523694874323222818029 1047196385577871208556761)
            ·
              refine ⟨785397289183403406417571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1047196385577871208556761 785397289183403406417571)
              ·
                refine ⟨1178095933775105109626357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785397289183403406417571 1178095933775105109626357)
                ·
                  refine ⟨110446493791416104027471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1178095933775105109626357 110446493791416104027471)
                  ·
                    rfl

theorem cell21_483961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_483961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_483961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_483961 prefixEnd_483961 := by exact prefixLift 483961
  have htrace : WordTrace (prefixWord ++ tailWord_483961) baseStart_483961 baseEnd_483961 := by
    simpa [prefixWord, tailWord_483961, baseEnd_483961] using wordTrace_append hprefix tailTrace_483961
  have hstable : (prefixWord ++ tailWord_483961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_483961).length < 2 ^ (prefixWord ++ tailWord_483961).sum := by decide
  have hdescent : baseEnd_483961 < baseStart_483961 := by decide
  rcases family_descends (prefixWord ++ tailWord_483961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484065 : List Nat := [1, 2, 3, 1, 4, 10]
def baseStart_484065 : Nat := 118140960795 + 484065 * 2 ^ 59
def prefixEnd_484065 : Nat := 4983230072969 + 3 ^ 40 * 484065 * 2
def baseEnd_484065 : Nat := 4091489926234630899775

theorem tailTrace_484065 : CollatzResearch.WordTrace tailWord_484065 prefixEnd_484065 4091489926234630899775 := by
  unfold tailWord_484065
  simp only [CollatzResearch.WordTrace]
  refine ⟨17655300991322651565277649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11770200660881767710185099 17655300991322651565277649)
  ·
    refine ⟨13241475743491988673958237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17655300991322651565277649 13241475743491988673958237)
    ·
      refine ⟨4965553403809495752734339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13241475743491988673958237 4965553403809495752734339)
      ·
        refine ⟨7448330105714243629101509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4965553403809495752734339 7448330105714243629101509)
        ·
          refine ⟨1396561894821420680456533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7448330105714243629101509 1396561894821420680456533)
          ·
            refine ⟨4091489926234630899775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1396561894821420680456533 4091489926234630899775)
            ·
              rfl

theorem cell21_484065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 10].length) (baseStart_484065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484065 prefixEnd_484065 := by exact prefixLift 484065
  have htrace : WordTrace (prefixWord ++ tailWord_484065) baseStart_484065 baseEnd_484065 := by
    simpa [prefixWord, tailWord_484065, baseEnd_484065] using wordTrace_append hprefix tailTrace_484065
  have hstable : (prefixWord ++ tailWord_484065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484065).length < 2 ^ (prefixWord ++ tailWord_484065).sum := by decide
  have hdescent : baseEnd_484065 < baseStart_484065 := by decide
  rcases family_descends (prefixWord ++ tailWord_484065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484068 : List Nat := [2, 3, 1, 1, 1, 5, 2, 2, 4]
def baseStart_484068 : Nat := 118140960795 + 484068 * 2 ^ 59
def prefixEnd_484068 : Nat := 4983230072969 + 3 ^ 40 * 484068 * 2
def baseEnd_484068 : Nat := 110470912649207695743919

theorem tailTrace_484068 : CollatzResearch.WordTrace tailWord_484068 prefixEnd_484068 110470912649207695743919 := by
  unfold tailWord_484068
  simp only [CollatzResearch.WordTrace]
  refine ⟨8827705205155891538818429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11770273606874522051757905 8827705205155891538818429)
  ·
    refine ⟨3310389451933459327056911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8827705205155891538818429 3310389451933459327056911)
    ·
      refine ⟨4965584177900188990585367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3310389451933459327056911 4965584177900188990585367)
      ·
        refine ⟨7448376266850283485878051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4965584177900188990585367 7448376266850283485878051)
        ·
          refine ⟨11172564400275425228817077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7448376266850283485878051 11172564400275425228817077)
          ·
            refine ⟨1047427912525821115201601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11172564400275425228817077 1047427912525821115201601)
            ·
              refine ⟨785570934394365836401201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1047427912525821115201601 785570934394365836401201)
              ·
                refine ⟨589178200795774377300901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785570934394365836401201 589178200795774377300901)
                ·
                  refine ⟨110470912649207695743919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 589178200795774377300901 110470912649207695743919)
                  ·
                    rfl

theorem cell21_484068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_484068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484068 prefixEnd_484068 := by exact prefixLift 484068
  have htrace : WordTrace (prefixWord ++ tailWord_484068) baseStart_484068 baseEnd_484068 := by
    simpa [prefixWord, tailWord_484068, baseEnd_484068] using wordTrace_append hprefix tailTrace_484068
  have hstable : (prefixWord ++ tailWord_484068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484068).length < 2 ^ (prefixWord ++ tailWord_484068).sum := by decide
  have hdescent : baseEnd_484068 < baseStart_484068 := by decide
  rcases family_descends (prefixWord ++ tailWord_484068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484082 : List Nat := [3, 2, 1, 3, 1, 2, 3, 6]
def baseStart_484082 : Nat := 118140960795 + 484082 * 2 ^ 59
def prefixEnd_484082 : Nat := 4983230072969 + 3 ^ 40 * 484082 * 2
def baseEnd_484082 : Nat := 36824702546648927503519

theorem tailTrace_484082 : CollatzResearch.WordTrace tailWord_484082 prefixEnd_484082 36824702546648927503519 := by
  unfold tailWord_484082
  simp only [CollatzResearch.WordTrace]
  refine ⟨4413980258065265867161625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11770614021507375645764333 4413980258065265867161625)
  ·
    refine ⟨3310485193548949400371219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4413980258065265867161625 3310485193548949400371219)
    ·
      refine ⟨4965727790323424100556829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3310485193548949400371219 4965727790323424100556829)
      ·
        refine ⟨1862147921371284037708811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4965727790323424100556829 1862147921371284037708811)
        ·
          refine ⟨2793221882056926056563217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1862147921371284037708811 2793221882056926056563217)
          ·
            refine ⟨2094916411542694542422413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2793221882056926056563217 2094916411542694542422413)
            ·
              refine ⟨785593654328510453408405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2094916411542694542422413 785593654328510453408405)
              ·
                refine ⟨36824702546648927503519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 785593654328510453408405 36824702546648927503519)
                ·
                  rfl

theorem cell21_484082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_484082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484082 prefixEnd_484082 := by exact prefixLift 484082
  have htrace : WordTrace (prefixWord ++ tailWord_484082) baseStart_484082 baseEnd_484082 := by
    simpa [prefixWord, tailWord_484082, baseEnd_484082] using wordTrace_append hprefix tailTrace_484082
  have hstable : (prefixWord ++ tailWord_484082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484082).length < 2 ^ (prefixWord ++ tailWord_484082).sum := by decide
  have hdescent : baseEnd_484082 < baseStart_484082 := by decide
  rcases family_descends (prefixWord ++ tailWord_484082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484113 : List Nat := [1, 2, 2, 1, 1, 3, 3, 5, 3]
def baseStart_484113 : Nat := 118140960795 + 484113 * 2 ^ 59
def prefixEnd_484113 : Nat := 4983230072969 + 3 ^ 40 * 484113 * 2
def baseEnd_484113 : Nat := 110481182262297617493827

theorem tailTrace_484113 : CollatzResearch.WordTrace tailWord_484113 prefixEnd_484113 110481182262297617493827 := by
  unfold tailWord_484113
  simp only [CollatzResearch.WordTrace]
  refine ⟨17657051695148755763024993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11771367796765837175349995 17657051695148755763024993)
  ·
    refine ⟨13242788771361566822268745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17657051695148755763024993 13242788771361566822268745)
    ·
      refine ⟨9932091578521175116701559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13242788771361566822268745 9932091578521175116701559)
      ·
        refine ⟨14898137367781762675052339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9932091578521175116701559 14898137367781762675052339)
        ·
          refine ⟨22347206051672644012578509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14898137367781762675052339 22347206051672644012578509)
          ·
            refine ⟨8380202269377241504716941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22347206051672644012578509 8380202269377241504716941)
            ·
              refine ⟨3142575851016465564268853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8380202269377241504716941 3142575851016465564268853)
              ·
                refine ⟨294616486032793646650205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3142575851016465564268853 294616486032793646650205)
                ·
                  refine ⟨110481182262297617493827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294616486032793646650205 110481182262297617493827)
                  ·
                    rfl

theorem cell21_484113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 3].length) (baseStart_484113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484113 prefixEnd_484113 := by exact prefixLift 484113
  have htrace : WordTrace (prefixWord ++ tailWord_484113) baseStart_484113 baseEnd_484113 := by
    simpa [prefixWord, tailWord_484113, baseEnd_484113] using wordTrace_append hprefix tailTrace_484113
  have hstable : (prefixWord ++ tailWord_484113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484113).length < 2 ^ (prefixWord ++ tailWord_484113).sum := by decide
  have hdescent : baseEnd_484113 < baseStart_484113 := by decide
  rcases family_descends (prefixWord ++ tailWord_484113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484127 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 6]
def baseStart_484127 : Nat := 118140960795 + 484127 * 2 ^ 59
def prefixEnd_484127 : Nat := 4983230072969 + 3 ^ 40 * 484127 * 2
def baseEnd_484127 : Nat := 110484377253036704260465

theorem tailTrace_484127 : CollatzResearch.WordTrace tailWord_484127 prefixEnd_484127 110484377253036704260465 := by
  unfold tailWord_484127
  simp only [CollatzResearch.WordTrace]
  refine ⟨17657562317098036154034635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11771708211398690769356423 17657562317098036154034635)
  ·
    refine ⟨26486343475647054231051953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17657562317098036154034635 26486343475647054231051953)
    ·
      refine ⟨19864757606735290673288965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26486343475647054231051953 19864757606735290673288965)
      ·
        refine ⟨3724642051262867001241681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19864757606735290673288965 3724642051262867001241681)
        ·
          refine ⟨2793481538447150250931261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3724642051262867001241681 2793481538447150250931261)
          ·
            refine ⟨1047555576917681344099223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2793481538447150250931261 1047555576917681344099223)
            ·
              refine ⟨1571333365376522016148835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1047555576917681344099223 1571333365376522016148835)
              ·
                refine ⟨2357000048064783024223253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1571333365376522016148835 2357000048064783024223253)
                ·
                  refine ⟨110484377253036704260465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2357000048064783024223253 110484377253036704260465)
                  ·
                    rfl

theorem cell21_484127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 6].length) (baseStart_484127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484127 prefixEnd_484127 := by exact prefixLift 484127
  have htrace : WordTrace (prefixWord ++ tailWord_484127) baseStart_484127 baseEnd_484127 := by
    simpa [prefixWord, tailWord_484127, baseEnd_484127] using wordTrace_append hprefix tailTrace_484127
  have hstable : (prefixWord ++ tailWord_484127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484127).length < 2 ^ (prefixWord ++ tailWord_484127).sum := by decide
  have hdescent : baseEnd_484127 < baseStart_484127 := by decide
  rcases family_descends (prefixWord ++ tailWord_484127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484130 : List Nat := [3, 3, 1, 1, 2, 2, 2, 4, 3]
def baseStart_484130 : Nat := 118140960795 + 484130 * 2 ^ 59
def prefixEnd_484130 : Nat := 4983230072969 + 3 ^ 40 * 484130 * 2
def baseEnd_484130 : Nat := 110485061893909365710459

theorem tailTrace_484130 : CollatzResearch.WordTrace tailWord_484130 prefixEnd_484130 110485061893909365710459 := by
  unfold tailWord_484130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4414417934021791916598461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11771781157391445110929229 4414417934021791916598461)
  ·
    refine ⟨1655406725258171968724423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4414417934021791916598461 1655406725258171968724423)
    ·
      refine ⟨2483110087887257953086635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1655406725258171968724423 2483110087887257953086635)
      ·
        refine ⟨3724665131830886929629953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2483110087887257953086635 3724665131830886929629953)
        ·
          refine ⟨2793498848873165197222465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3724665131830886929629953 2793498848873165197222465)
          ·
            refine ⟨2095124136654873897916849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2793498848873165197222465 2095124136654873897916849)
            ·
              refine ⟨1571343102491155423437637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2095124136654873897916849 1571343102491155423437637)
              ·
                refine ⟨294626831717091641894557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1571343102491155423437637 294626831717091641894557)
                ·
                  refine ⟨110485061893909365710459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294626831717091641894557 110485061893909365710459)
                  ·
                    rfl

theorem cell21_484130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_484130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484130 prefixEnd_484130 := by exact prefixLift 484130
  have htrace : WordTrace (prefixWord ++ tailWord_484130) baseStart_484130 baseEnd_484130 := by
    simpa [prefixWord, tailWord_484130, baseEnd_484130] using wordTrace_append hprefix tailTrace_484130
  have hstable : (prefixWord ++ tailWord_484130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484130).length < 2 ^ (prefixWord ++ tailWord_484130).sum := by decide
  have hdescent : baseEnd_484130 < baseStart_484130 := by decide
  rcases family_descends (prefixWord ++ tailWord_484130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484217 : List Nat := [1, 2, 1, 3, 2, 3, 2, 7]
def baseStart_484217 : Nat := 118140960795 + 484217 * 2 ^ 59
def prefixEnd_484217 : Nat := 4983230072969 + 3 ^ 40 * 484217 * 2
def baseEnd_484217 : Nat := 36834972159738849253427

theorem tailTrace_484217 : CollatzResearch.WordTrace tailWord_484217 prefixEnd_484217 36834972159738849253427 := by
  unfold tailWord_484217
  simp only [CollatzResearch.WordTrace]
  refine ⟨17660844886771981524810905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11773896591181321016540603 17660844886771981524810905)
  ·
    refine ⟨13245633665078986143608179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17660844886771981524810905 13245633665078986143608179)
    ·
      refine ⟨19868450497618479215412269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13245633665078986143608179 19868450497618479215412269)
      ·
        refine ⟨7450668936606929705779601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19868450497618479215412269 7450668936606929705779601)
        ·
          refine ⟨5588001702455197279334701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7450668936606929705779601 5588001702455197279334701)
          ·
            refine ⟨2095500638420698979750513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5588001702455197279334701 2095500638420698979750513)
            ·
              refine ⟨1571625478815524234812885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2095500638420698979750513 1571625478815524234812885)
              ·
                refine ⟨36834972159738849253427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1571625478815524234812885 36834972159738849253427)
                ·
                  rfl

theorem cell21_484217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 7].length) (baseStart_484217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484217 prefixEnd_484217 := by exact prefixLift 484217
  have htrace : WordTrace (prefixWord ++ tailWord_484217) baseStart_484217 baseEnd_484217 := by
    simpa [prefixWord, tailWord_484217, baseEnd_484217] using wordTrace_append hprefix tailTrace_484217
  have hstable : (prefixWord ++ tailWord_484217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484217).length < 2 ^ (prefixWord ++ tailWord_484217).sum := by decide
  have hdescent : baseEnd_484217 < baseStart_484217 := by decide
  rcases family_descends (prefixWord ++ tailWord_484217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484327 : List Nat := [1, 1, 5, 2, 2, 3, 2, 5]
def baseStart_484327 : Nat := 118140960795 + 484327 * 2 ^ 59
def prefixEnd_484327 : Nat := 4983230072969 + 3 ^ 40 * 484327 * 2
def baseEnd_484327 : Nat := 36843339992626933642241

theorem tailTrace_484327 : CollatzResearch.WordTrace tailWord_484327 prefixEnd_484327 36843339992626933642241 := by
  unfold tailWord_484327
  simp only [CollatzResearch.WordTrace]
  refine ⟨17664856916373470311315235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11776571277582313540876823 17664856916373470311315235)
  ·
    refine ⟨26497285374560205466972853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17664856916373470311315235 26497285374560205466972853)
    ·
      refine ⟨2484120503865019262528705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26497285374560205466972853 2484120503865019262528705)
      ·
        refine ⟨1863090377898764446896529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2484120503865019262528705 1863090377898764446896529)
        ·
          refine ⟨1397317783424073335172397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1863090377898764446896529 1397317783424073335172397)
          ·
            refine ⟨523994168784027500689649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1397317783424073335172397 523994168784027500689649)
            ·
              refine ⟨392995626588020625517237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523994168784027500689649 392995626588020625517237)
              ·
                refine ⟨36843339992626933642241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 392995626588020625517237 36843339992626933642241)
                ·
                  rfl

theorem cell21_484327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 5].length) (baseStart_484327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484327 prefixEnd_484327 := by exact prefixLift 484327
  have htrace : WordTrace (prefixWord ++ tailWord_484327) baseStart_484327 baseEnd_484327 := by
    simpa [prefixWord, tailWord_484327, baseEnd_484327] using wordTrace_append hprefix tailTrace_484327
  have hstable : (prefixWord ++ tailWord_484327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484327).length < 2 ^ (prefixWord ++ tailWord_484327).sum := by decide
  have hdescent : baseEnd_484327 < baseStart_484327 := by decide
  rcases family_descends (prefixWord ++ tailWord_484327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484476 : List Nat := [2, 2, 2, 1, 1, 3, 4, 1, 5]
def baseStart_484476 : Nat := 118140960795 + 484476 * 2 ^ 59
def prefixEnd_484476 : Nat := 4983230072969 + 3 ^ 40 * 484476 * 2
def baseEnd_484476 : Nat := 110564023807889652943085

theorem tailTrace_484476 : CollatzResearch.WordTrace tailWord_484476 prefixEnd_484476 110564023807889652943085 := by
  unfold tailWord_484476
  simp only [CollatzResearch.WordTrace]
  refine ⟨8835145696416834379244641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11780194261889112505659521 8835145696416834379244641)
  ·
    refine ⟨6626359272312625784433481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8835145696416834379244641 6626359272312625784433481)
    ·
      refine ⟨4969769454234469338325111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6626359272312625784433481 4969769454234469338325111)
      ·
        refine ⟨7454654181351704007487667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4969769454234469338325111 7454654181351704007487667)
        ·
          refine ⟨11181981272027556011231501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7454654181351704007487667 11181981272027556011231501)
          ·
            refine ⟨4193242977010333504211813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11181981272027556011231501 4193242977010333504211813)
            ·
              refine ⟨786233058189437532039715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4193242977010333504211813 786233058189437532039715)
              ·
                refine ⟨1179349587284156298059573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 786233058189437532039715 1179349587284156298059573)
                ·
                  refine ⟨110564023807889652943085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1179349587284156298059573 110564023807889652943085)
                  ·
                    rfl

theorem cell21_484476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_484476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484476 prefixEnd_484476 := by exact prefixLift 484476
  have htrace : WordTrace (prefixWord ++ tailWord_484476) baseStart_484476 baseEnd_484476 := by
    simpa [prefixWord, tailWord_484476, baseEnd_484476] using wordTrace_append hprefix tailTrace_484476
  have hstable : (prefixWord ++ tailWord_484476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484476).length < 2 ^ (prefixWord ++ tailWord_484476).sum := by decide
  have hdescent : baseEnd_484476 < baseStart_484476 := by decide
  rcases family_descends (prefixWord ++ tailWord_484476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484586 : List Nat := [3, 1, 3, 1, 1, 3, 4, 2, 3]
def baseStart_484586 : Nat := 118140960795 + 484586 * 2 ^ 59
def prefixEnd_484586 : Nat := 4983230072969 + 3 ^ 40 * 484586 * 2
def baseEnd_484586 : Nat := 110589127306553906109527

theorem tailTrace_484586 : CollatzResearch.WordTrace tailWord_484586 prefixEnd_484586 110589127306553906109527 := by
  unfold tailWord_484586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4418575855608789386248403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11782868948290105029995741 4418575855608789386248403)
  ·
    refine ⟨6627863783413184079372605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4418575855608789386248403 6627863783413184079372605)
    ·
      refine ⟨2485448918779944029764727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6627863783413184079372605 2485448918779944029764727)
      ·
        refine ⟨3728173378169916044647091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2485448918779944029764727 3728173378169916044647091)
        ·
          refine ⟨5592260067254874066970637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3728173378169916044647091 5592260067254874066970637)
          ·
            refine ⟨2097097525220577775113989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5592260067254874066970637 2097097525220577775113989)
            ·
              refine ⟨393205785978858332833873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2097097525220577775113989 393205785978858332833873)
              ·
                refine ⟨294904339484143749625405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393205785978858332833873 294904339484143749625405)
                ·
                  refine ⟨110589127306553906109527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294904339484143749625405 110589127306553906109527)
                  ·
                    rfl

theorem cell21_484586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_484586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484586 prefixEnd_484586 := by exact prefixLift 484586
  have htrace : WordTrace (prefixWord ++ tailWord_484586) baseStart_484586 baseEnd_484586 := by
    simpa [prefixWord, tailWord_484586, baseEnd_484586] using wordTrace_append hprefix tailTrace_484586
  have hstable : (prefixWord ++ tailWord_484586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484586).length < 2 ^ (prefixWord ++ tailWord_484586).sum := by decide
  have hdescent : baseEnd_484586 < baseStart_484586 := by decide
  rcases family_descends (prefixWord ++ tailWord_484586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484611 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 7]
def baseStart_484611 : Nat := 118140960795 + 484611 * 2 ^ 59
def prefixEnd_484611 : Nat := 4983230072969 + 3 ^ 40 * 484611 * 2
def baseEnd_484611 : Nat := 110594832647159418192809

theorem tailTrace_484611 : CollatzResearch.WordTrace tailWord_484611 prefixEnd_484611 110594832647159418192809 := by
  unfold tailWord_484611
  simp only [CollatzResearch.WordTrace]
  refine ⟨17675215247344586814653687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11783476831563057876435791 17675215247344586814653687)
  ·
    refine ⟨26512822871016880221980531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17675215247344586814653687 26512822871016880221980531)
    ·
      refine ⟨39769234306525320332970797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26512822871016880221980531 39769234306525320332970797)
      ·
        refine ⟨14913462864946995124864049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39769234306525320332970797 14913462864946995124864049)
        ·
          refine ⟨11185097148710246343648037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14913462864946995124864049 11185097148710246343648037)
          ·
            refine ⟨2097205715383171189434007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11185097148710246343648037 2097205715383171189434007)
            ·
              refine ⟨3145808573074756784151011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2097205715383171189434007 3145808573074756784151011)
              ·
                refine ⟨4718712859612135176226517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145808573074756784151011 4718712859612135176226517)
                ·
                  refine ⟨110594832647159418192809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4718712859612135176226517 110594832647159418192809)
                  ·
                    rfl

theorem cell21_484611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 7].length) (baseStart_484611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484611 prefixEnd_484611 := by exact prefixLift 484611
  have htrace : WordTrace (prefixWord ++ tailWord_484611) baseStart_484611 baseEnd_484611 := by
    simpa [prefixWord, tailWord_484611, baseEnd_484611] using wordTrace_append hprefix tailTrace_484611
  have hstable : (prefixWord ++ tailWord_484611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484611).length < 2 ^ (prefixWord ++ tailWord_484611).sum := by decide
  have hdescent : baseEnd_484611 < baseStart_484611 := by decide
  rcases family_descends (prefixWord ++ tailWord_484611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484645 : List Nat := [1, 3, 1, 2, 4, 1, 2, 4, 3]
def baseStart_484645 : Nat := 118140960795 + 484645 * 2 ^ 59
def prefixEnd_484645 : Nat := 4983230072969 + 3 ^ 40 * 484645 * 2
def baseEnd_484645 : Nat := 110602591910382914626073

theorem tailTrace_484645 : CollatzResearch.WordTrace tailWord_484645 prefixEnd_484645 110602591910382914626073 := by
  unfold tailWord_484645
  simp only [CollatzResearch.WordTrace]
  refine ⟨17676455329221410621391389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11784303552814273747594259 17676455329221410621391389)
  ·
    refine ⟨6628670748458028983021771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17676455329221410621391389 6628670748458028983021771)
    ·
      refine ⟨9943006122687043474532657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6628670748458028983021771 9943006122687043474532657)
      ·
        refine ⟨7457254592015282605899493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9943006122687043474532657 7457254592015282605899493)
        ·
          refine ⟨1398235236002865488606155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7457254592015282605899493 1398235236002865488606155)
          ·
            refine ⟨2097352854004298232909233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398235236002865488606155 2097352854004298232909233)
            ·
              refine ⟨1573014640503223674681925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2097352854004298232909233 1573014640503223674681925)
              ·
                refine ⟨294940245094354439002861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1573014640503223674681925 294940245094354439002861)
                ·
                  refine ⟨110602591910382914626073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294940245094354439002861 110602591910382914626073)
                  ·
                    rfl

theorem cell21_484645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_484645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484645 prefixEnd_484645 := by exact prefixLift 484645
  have htrace : WordTrace (prefixWord ++ tailWord_484645) baseStart_484645 baseEnd_484645 := by
    simpa [prefixWord, tailWord_484645, baseEnd_484645] using wordTrace_append hprefix tailTrace_484645
  have hstable : (prefixWord ++ tailWord_484645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484645).length < 2 ^ (prefixWord ++ tailWord_484645).sum := by decide
  have hdescent : baseEnd_484645 < baseStart_484645 := by decide
  rcases family_descends (prefixWord ++ tailWord_484645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484656 : List Nat := [2, 1, 1, 1, 2, 2, 4, 8]
def baseStart_484656 : Nat := 118140960795 + 484656 * 2 ^ 59
def prefixEnd_484656 : Nat := 4983230072969 + 3 ^ 40 * 484656 * 2
def baseEnd_484656 : Nat := 36868367420083113314239

theorem tailTrace_484656 : CollatzResearch.WordTrace tailWord_484656 prefixEnd_484656 36868367420083113314239 := by
  unfold tailWord_484656
  simp only [CollatzResearch.WordTrace]
  refine ⟨8838428266090779750020911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11784571021454373000027881 8838428266090779750020911)
  ·
    refine ⟨13257642399136169625031367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8838428266090779750020911 13257642399136169625031367)
    ·
      refine ⟨19886463598704254437547051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13257642399136169625031367 19886463598704254437547051)
      ·
        refine ⟨29829695398056381656320577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19886463598704254437547051 29829695398056381656320577)
        ·
          refine ⟨22372271548542286242240433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29829695398056381656320577 22372271548542286242240433)
          ·
            refine ⟨16779203661406714681680325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22372271548542286242240433 16779203661406714681680325)
            ·
              refine ⟨3146100686513759002815061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16779203661406714681680325 3146100686513759002815061)
              ·
                refine ⟨36868367420083113314239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3146100686513759002815061 36868367420083113314239)
                ·
                  rfl

theorem cell21_484656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 8].length) (baseStart_484656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484656 prefixEnd_484656 := by exact prefixLift 484656
  have htrace : WordTrace (prefixWord ++ tailWord_484656) baseStart_484656 baseEnd_484656 := by
    simpa [prefixWord, tailWord_484656, baseEnd_484656] using wordTrace_append hprefix tailTrace_484656
  have hstable : (prefixWord ++ tailWord_484656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484656).length < 2 ^ (prefixWord ++ tailWord_484656).sum := by decide
  have hdescent : baseEnd_484656 < baseStart_484656 := by decide
  rcases family_descends (prefixWord ++ tailWord_484656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484704 : List Nat := [2, 1, 1, 3, 4, 1, 3, 1, 5]
def baseStart_484704 : Nat := 118140960795 + 484704 * 2 ^ 59
def prefixEnd_484704 : Nat := 4983230072969 + 3 ^ 40 * 484704 * 2
def baseEnd_484704 : Nat := 110616056514211923142619

theorem tailTrace_484704 : CollatzResearch.WordTrace tailWord_484704 prefixEnd_484704 110616056514211923142619 := by
  unfold tailWord_484704
  simp only [CollatzResearch.WordTrace]
  refine ⟨8839303618003831848894583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11785738157338442465192777 8839303618003831848894583)
  ·
    refine ⟨13258955427005747773341875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8839303618003831848894583 13258955427005747773341875)
    ·
      refine ⟨19888433140508621660012813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13258955427005747773341875 19888433140508621660012813)
      ·
        refine ⟨7458162427690733122504805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19888433140508621660012813 7458162427690733122504805)
        ·
          refine ⟨1398405455192012460469651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7458162427690733122504805 1398405455192012460469651)
          ·
            refine ⟨2097608182788018690704477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398405455192012460469651 2097608182788018690704477)
            ·
              refine ⟨786603068545507009014179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2097608182788018690704477 786603068545507009014179)
              ·
                refine ⟨1179904602818260513521269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 786603068545507009014179 1179904602818260513521269)
                ·
                  refine ⟨110616056514211923142619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1179904602818260513521269 110616056514211923142619)
                  ·
                    rfl

theorem cell21_484704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_484704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484704 prefixEnd_484704 := by exact prefixLift 484704
  have htrace : WordTrace (prefixWord ++ tailWord_484704) baseStart_484704 baseEnd_484704 := by
    simpa [prefixWord, tailWord_484704, baseEnd_484704] using wordTrace_append hprefix tailTrace_484704
  have hstable : (prefixWord ++ tailWord_484704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484704).length < 2 ^ (prefixWord ++ tailWord_484704).sum := by decide
  have hdescent : baseEnd_484704 < baseStart_484704 := by decide
  rcases family_descends (prefixWord ++ tailWord_484704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484732 : List Nat := [2, 2, 2, 1, 1, 1, 3, 9]
def baseStart_484732 : Nat := 118140960795 + 484732 * 2 ^ 59
def prefixEnd_484732 : Nat := 4983230072969 + 3 ^ 40 * 484732 * 2
def baseEnd_484732 : Nat := 36874148831896698891965

theorem tailTrace_484732 : CollatzResearch.WordTrace tailWord_484732 prefixEnd_484732 36874148831896698891965 := by
  unfold tailWord_484732
  simp only [CollatzResearch.WordTrace]
  refine ⟨8839814239953112239904225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11786418986604149653205633 8839814239953112239904225)
  ·
    refine ⟨6629860679964834179928169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8839814239953112239904225 6629860679964834179928169)
    ·
      refine ⟨4972395509973625634946127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6629860679964834179928169 4972395509973625634946127)
      ·
        refine ⟨7458593264960438452419191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4972395509973625634946127 7458593264960438452419191)
        ·
          refine ⟨11187889897440657678628787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7458593264960438452419191 11187889897440657678628787)
          ·
            refine ⟨16781834846160986517943181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11187889897440657678628787 16781834846160986517943181)
            ·
              refine ⟨6293188067310369944228693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16781834846160986517943181 6293188067310369944228693)
              ·
                refine ⟨36874148831896698891965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6293188067310369944228693 36874148831896698891965)
                ·
                  rfl

theorem cell21_484732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 9].length) (baseStart_484732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484732 prefixEnd_484732 := by exact prefixLift 484732
  have htrace : WordTrace (prefixWord ++ tailWord_484732) baseStart_484732 baseEnd_484732 := by
    simpa [prefixWord, tailWord_484732, baseEnd_484732] using wordTrace_append hprefix tailTrace_484732
  have hstable : (prefixWord ++ tailWord_484732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484732).length < 2 ^ (prefixWord ++ tailWord_484732).sum := by decide
  have hdescent : baseEnd_484732 < baseStart_484732 := by decide
  rcases family_descends (prefixWord ++ tailWord_484732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484777 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 10]
def baseStart_484777 : Nat := 118140960795 + 484777 * 2 ^ 59
def prefixEnd_484777 : Nat := 4983230072969 + 3 ^ 40 * 484777 * 2
def baseEnd_484777 : Nat := 110632716108780018425803

theorem tailTrace_484777 : CollatzResearch.WordTrace tailWord_484777 prefixEnd_484777 110632716108780018425803 := by
  unfold tailWord_484777
  simp only [CollatzResearch.WordTrace]
  refine ⟨17681269764743197165196585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11787513176495464776797723 17681269764743197165196585)
  ·
    refine ⟨13260952323557397873897439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17681269764743197165196585 13260952323557397873897439)
    ·
      refine ⟨19891428485336096810846159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13260952323557397873897439 19891428485336096810846159)
      ·
        refine ⟨29837142728004145216269239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19891428485336096810846159 29837142728004145216269239)
        ·
          refine ⟨44755714092006217824403859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29837142728004145216269239 44755714092006217824403859)
          ·
            refine ⟨67133571138009326736605789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44755714092006217824403859 67133571138009326736605789)
            ·
              refine ⟨25175089176753497526227171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67133571138009326736605789 25175089176753497526227171)
              ·
                refine ⟨37762633765130246289340757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25175089176753497526227171 37762633765130246289340757)
                ·
                  refine ⟨110632716108780018425803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 37762633765130246289340757 110632716108780018425803)
                  ·
                    rfl

theorem cell21_484777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_484777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484777 prefixEnd_484777 := by exact prefixLift 484777
  have htrace : WordTrace (prefixWord ++ tailWord_484777) baseStart_484777 baseEnd_484777 := by
    simpa [prefixWord, tailWord_484777, baseEnd_484777] using wordTrace_append hprefix tailTrace_484777
  have hstable : (prefixWord ++ tailWord_484777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484777).length < 2 ^ (prefixWord ++ tailWord_484777).sum := by decide
  have hdescent : baseEnd_484777 < baseStart_484777 := by decide
  rcases family_descends (prefixWord ++ tailWord_484777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484797 : List Nat := [1, 4, 1, 2, 2, 1, 4, 3, 3]
def baseStart_484797 : Nat := 118140960795 + 484797 * 2 ^ 59
def prefixEnd_484797 : Nat := 4983230072969 + 3 ^ 40 * 484797 * 2
def baseEnd_484797 : Nat := 110637280381264428092429

theorem tailTrace_484797 : CollatzResearch.WordTrace tailWord_484797 prefixEnd_484797 110637280381264428092429 := by
  unfold tailWord_484797
  simp only [CollatzResearch.WordTrace]
  refine ⟨17681999224670740580924645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11787999483113827053949763 17681999224670740580924645)
  ·
    refine ⟨3315374854625763858923371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17681999224670740580924645 3315374854625763858923371)
    ·
      refine ⟨4973062281938645788385057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3315374854625763858923371 4973062281938645788385057)
      ·
        refine ⟨3729796711453984341288793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4973062281938645788385057 3729796711453984341288793)
        ·
          refine ⟨2797347533590488255966595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3729796711453984341288793 2797347533590488255966595)
          ·
            refine ⟨4196021300385732383949893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797347533590488255966595 4196021300385732383949893)
            ·
              refine ⟨786753993822324821990605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4196021300385732383949893 786753993822324821990605)
              ·
                refine ⟨295032747683371808246477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 786753993822324821990605 295032747683371808246477)
                ·
                  refine ⟨110637280381264428092429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295032747683371808246477 110637280381264428092429)
                  ·
                    rfl

theorem cell21_484797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_484797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484797 prefixEnd_484797 := by exact prefixLift 484797
  have htrace : WordTrace (prefixWord ++ tailWord_484797) baseStart_484797 baseEnd_484797 := by
    simpa [prefixWord, tailWord_484797, baseEnd_484797] using wordTrace_append hprefix tailTrace_484797
  have hstable : (prefixWord ++ tailWord_484797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484797).length < 2 ^ (prefixWord ++ tailWord_484797).sum := by decide
  have hdescent : baseEnd_484797 < baseStart_484797 := by decide
  rcases family_descends (prefixWord ++ tailWord_484797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484808 : List Nat := [2, 1, 3, 1, 3, 1, 10]
def baseStart_484808 : Nat := 118140960795 + 484808 * 2 ^ 59
def prefixEnd_484808 : Nat := 4983230072969 + 3 ^ 40 * 484808 * 2
def baseEnd_484808 : Nat := 12293310081236761489897

theorem tailTrace_484808 : CollatzResearch.WordTrace tailWord_484808 prefixEnd_484808 12293310081236761489897 := by
  unfold tailWord_484808
  simp only [CollatzResearch.WordTrace]
  refine ⟨8841200213815444729787539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11788266951753926306383385 8841200213815444729787539)
  ·
    refine ⟨13261800320723167094681309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8841200213815444729787539 13261800320723167094681309)
    ·
      refine ⟨4973175120271187660505491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13261800320723167094681309 4973175120271187660505491)
      ·
        refine ⟨7459762680406781490758237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4973175120271187660505491 7459762680406781490758237)
        ·
          refine ⟨2797411005152543059034339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7459762680406781490758237 2797411005152543059034339)
          ·
            refine ⟨4196116507728814588551509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797411005152543059034339 4196116507728814588551509)
            ·
              refine ⟨12293310081236761489897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4196116507728814588551509 12293310081236761489897)
              ·
                rfl

theorem cell21_484808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 10].length) (baseStart_484808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484808 prefixEnd_484808 := by exact prefixLift 484808
  have htrace : WordTrace (prefixWord ++ tailWord_484808) baseStart_484808 baseEnd_484808 := by
    simpa [prefixWord, tailWord_484808, baseEnd_484808] using wordTrace_append hprefix tailTrace_484808
  have hstable : (prefixWord ++ tailWord_484808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484808).length < 2 ^ (prefixWord ++ tailWord_484808).sum := by decide
  have hdescent : baseEnd_484808 < baseStart_484808 := by decide
  rcases family_descends (prefixWord ++ tailWord_484808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484873 : List Nat := [1, 2, 1, 1, 3, 1, 7, 2, 3]
def baseStart_484873 : Nat := 118140960795 + 484873 * 2 ^ 59
def prefixEnd_484873 : Nat := 4983230072969 + 3 ^ 40 * 484873 * 2
def baseEnd_484873 : Nat := 110654624616705184825607

theorem tailTrace_484873 : CollatzResearch.WordTrace tailWord_484873 prefixEnd_484873 110654624616705184825607 := by
  unfold tailWord_484873
  simp only [CollatzResearch.WordTrace]
  refine ⟨17684771172395405560691273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11789847448263603707127515 17684771172395405560691273)
  ·
    refine ⟨13263578379296554170518455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17684771172395405560691273 13263578379296554170518455)
    ·
      refine ⟨19895367568944831255777683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13263578379296554170518455 19895367568944831255777683)
      ·
        refine ⟨29843051353417246883666525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19895367568944831255777683 29843051353417246883666525)
        ·
          refine ⟨11191144257531467581374947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29843051353417246883666525 11191144257531467581374947)
          ·
            refine ⟨16786716386297201372062421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11191144257531467581374947 16786716386297201372062421)
            ·
              refine ⟨393438665303840657157713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16786716386297201372062421 393438665303840657157713)
              ·
                refine ⟨295078998977880492868285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393438665303840657157713 295078998977880492868285)
                ·
                  refine ⟨110654624616705184825607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295078998977880492868285 110654624616705184825607)
                  ·
                    rfl

theorem cell21_484873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 3].length) (baseStart_484873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484873 prefixEnd_484873 := by exact prefixLift 484873
  have htrace : WordTrace (prefixWord ++ tailWord_484873) baseStart_484873 baseEnd_484873 := by
    simpa [prefixWord, tailWord_484873, baseEnd_484873] using wordTrace_append hprefix tailTrace_484873
  have hstable : (prefixWord ++ tailWord_484873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484873).length < 2 ^ (prefixWord ++ tailWord_484873).sum := by decide
  have hdescent : baseEnd_484873 < baseStart_484873 := by decide
  rcases family_descends (prefixWord ++ tailWord_484873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_484918 : List Nat := [5, 1, 2, 1, 4, 8]
def baseStart_484918 : Nat := 118140960795 + 484918 * 2 ^ 59
def prefixEnd_484918 : Nat := 4983230072969 + 3 ^ 40 * 484918 * 2
def baseEnd_484918 : Nat := 4098699786288707650945

theorem tailTrace_484918 : CollatzResearch.WordTrace tailWord_484918 prefixEnd_484918 4098699786288707650945 := by
  unfold tailWord_484918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1105400778577023640379963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11790941638154918830719605 1105400778577023640379963)
  ·
    refine ⟨1658101167865535460569945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1105400778577023640379963 1658101167865535460569945)
    ·
      refine ⟨1243575875899151595427459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1658101167865535460569945 1243575875899151595427459)
      ·
        refine ⟨1865363813848727393141189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1243575875899151595427459 1865363813848727393141189)
        ·
          refine ⟨349755715096636386213973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1865363813848727393141189 349755715096636386213973)
          ·
            refine ⟨4098699786288707650945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 349755715096636386213973 4098699786288707650945)
            ·
              rfl

theorem cell21_484918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 8].length) (baseStart_484918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_484918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_484918 prefixEnd_484918 := by exact prefixLift 484918
  have htrace : WordTrace (prefixWord ++ tailWord_484918) baseStart_484918 baseEnd_484918 := by
    simpa [prefixWord, tailWord_484918, baseEnd_484918] using wordTrace_append hprefix tailTrace_484918
  have hstable : (prefixWord ++ tailWord_484918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_484918).length < 2 ^ (prefixWord ++ tailWord_484918).sum := by decide
  have hdescent : baseEnd_484918 < baseStart_484918 := by decide
  rcases family_descends (prefixWord ++ tailWord_484918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485025 : List Nat := [1, 2, 3, 3, 2, 1, 3, 3, 3]
def baseStart_485025 : Nat := 118140960795 + 485025 * 2 ^ 59
def prefixEnd_485025 : Nat := 4983230072969 + 3 ^ 40 * 485025 * 2
def baseEnd_485025 : Nat := 110689313087586698291963

theorem tailTrace_485025 : CollatzResearch.WordTrace tailWord_485025 prefixEnd_485025 110689313087586698291963 := by
  unfold tailWord_485025
  simp only [CollatzResearch.WordTrace]
  refine ⟨17690315067844735520224529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11793543378563157013483019 17690315067844735520224529)
  ·
    refine ⟨13267736300883551640168397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17690315067844735520224529 13267736300883551640168397)
    ·
      refine ⟨4975401112831331865063149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13267736300883551640168397 4975401112831331865063149)
      ·
        refine ⟨1865775417311749449398681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4975401112831331865063149 1865775417311749449398681)
        ·
          refine ⟨1399331562983812087049011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1865775417311749449398681 1399331562983812087049011)
          ·
            refine ⟨2098997344475718130573517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399331562983812087049011 2098997344475718130573517)
            ·
              refine ⟨787124004178394298965069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2098997344475718130573517 787124004178394298965069)
              ·
                refine ⟨295171501566897862111901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 787124004178394298965069 295171501566897862111901)
                ·
                  refine ⟨110689313087586698291963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295171501566897862111901 110689313087586698291963)
                  ·
                    rfl

theorem cell21_485025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 3].length) (baseStart_485025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485025 prefixEnd_485025 := by exact prefixLift 485025
  have htrace : WordTrace (prefixWord ++ tailWord_485025) baseStart_485025 baseEnd_485025 := by
    simpa [prefixWord, tailWord_485025, baseEnd_485025] using wordTrace_append hprefix tailTrace_485025
  have hstable : (prefixWord ++ tailWord_485025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485025).length < 2 ^ (prefixWord ++ tailWord_485025).sum := by decide
  have hdescent : baseEnd_485025 < baseStart_485025 := by decide
  rcases family_descends (prefixWord ++ tailWord_485025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485098 : List Nat := [3, 1, 3, 1, 1, 1, 3, 4, 4]
def baseStart_485098 : Nat := 118140960795 + 485098 * 2 ^ 59
def prefixEnd_485098 : Nat := 4983230072969 + 3 ^ 40 * 485098 * 2
def baseEnd_485098 : Nat := 110705972682154793575147

theorem tailTrace_485098 : CollatzResearch.WordTrace tailWord_485098 prefixEnd_485098 110705972682154793575147 := by
  unfold tailWord_485098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4423244399145067246907987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11795318397720179325087965 4423244399145067246907987)
  ·
    refine ⟨6634866598717600870361981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4423244399145067246907987 6634866598717600870361981)
    ·
      refine ⟨2488074974519100326385743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6634866598717600870361981 2488074974519100326385743)
      ·
        refine ⟨3732112461778650489578615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2488074974519100326385743 3732112461778650489578615)
        ·
          refine ⟨5598168692667975734367923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3732112461778650489578615 5598168692667975734367923)
          ·
            refine ⟨8397253039001963601551885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5598168692667975734367923 8397253039001963601551885)
            ·
              refine ⟨3148969889625736350581957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8397253039001963601551885 3148969889625736350581957)
              ·
                refine ⟨590431854304825565734117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3148969889625736350581957 590431854304825565734117)
                ·
                  refine ⟨110705972682154793575147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 590431854304825565734117 110705972682154793575147)
                  ·
                    rfl

theorem cell21_485098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_485098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485098 prefixEnd_485098 := by exact prefixLift 485098
  have htrace : WordTrace (prefixWord ++ tailWord_485098) baseStart_485098 baseEnd_485098 := by
    simpa [prefixWord, tailWord_485098, baseEnd_485098] using wordTrace_append hprefix tailTrace_485098
  have hstable : (prefixWord ++ tailWord_485098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485098).length < 2 ^ (prefixWord ++ tailWord_485098).sum := by decide
  have hdescent : baseEnd_485098 < baseStart_485098 := by decide
  rcases family_descends (prefixWord ++ tailWord_485098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485101 : List Nat := [1, 5, 1, 2, 1, 3, 1, 4, 3]
def baseStart_485101 : Nat := 118140960795 + 485101 * 2 ^ 59
def prefixEnd_485101 : Nat := 4983230072969 + 3 ^ 40 * 485101 * 2
def baseEnd_485101 : Nat := 110706657323027455025141

theorem tailTrace_485101 : CollatzResearch.WordTrace tailWord_485101 prefixEnd_485101 110706657323027455025141 := by
  unfold tailWord_485101
  simp only [CollatzResearch.WordTrace]
  refine ⟨17693087015569400499991157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11795391343712933666660771 17693087015569400499991157)
  ·
    refine ⟨1658726907709631296874171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17693087015569400499991157 1658726907709631296874171)
    ·
      refine ⟨2488090361564446945311257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1658726907709631296874171 2488090361564446945311257)
      ·
        refine ⟨1866067771173335208983443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2488090361564446945311257 1866067771173335208983443)
        ·
          refine ⟨2799101656760002813475165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1866067771173335208983443 2799101656760002813475165)
          ·
            refine ⟨1049663121285001055053187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2799101656760002813475165 1049663121285001055053187)
            ·
              refine ⟨1574494681927501582579781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049663121285001055053187 1574494681927501582579781)
              ·
                refine ⟨295217752861406546733709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1574494681927501582579781 295217752861406546733709)
                ·
                  refine ⟨110706657323027455025141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295217752861406546733709 110706657323027455025141)
                  ·
                    rfl

theorem cell21_485101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_485101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485101 prefixEnd_485101 := by exact prefixLift 485101
  have htrace : WordTrace (prefixWord ++ tailWord_485101) baseStart_485101 baseEnd_485101 := by
    simpa [prefixWord, tailWord_485101, baseEnd_485101] using wordTrace_append hprefix tailTrace_485101
  have hstable : (prefixWord ++ tailWord_485101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485101).length < 2 ^ (prefixWord ++ tailWord_485101).sum := by decide
  have hdescent : baseEnd_485101 < baseStart_485101 := by decide
  rcases family_descends (prefixWord ++ tailWord_485101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485160 : List Nat := [2, 1, 5, 1, 1, 3, 2, 1, 5]
def baseStart_485160 : Nat := 118140960795 + 485160 * 2 ^ 59
def prefixEnd_485160 : Nat := 4983230072969 + 3 ^ 40 * 485160 * 2
def baseEnd_485160 : Nat := 110720121926856463541687

theorem tailTrace_485160 : CollatzResearch.WordTrace tailWord_485160 prefixEnd_485160 110720121926856463541687 := by
  unfold tailWord_485160
  simp only [CollatzResearch.WordTrace]
  refine ⟨8847619461177826788194467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11796825948237102384259289 8847619461177826788194467)
  ·
    refine ⟨13271429191766740182291701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8847619461177826788194467 13271429191766740182291701)
    ·
      refine ⟨1244196486728131892089847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13271429191766740182291701 1244196486728131892089847)
      ·
        refine ⟨1866294730092197838134771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244196486728131892089847 1866294730092197838134771)
        ·
          refine ⟨2799442095138296757202157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1866294730092197838134771 2799442095138296757202157)
          ·
            refine ⟨1049790785676861283950809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2799442095138296757202157 1049790785676861283950809)
            ·
              refine ⟨787343089257645962963107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1049790785676861283950809 787343089257645962963107)
              ·
                refine ⟨1181014633886468944444661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787343089257645962963107 1181014633886468944444661)
                ·
                  refine ⟨110720121926856463541687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1181014633886468944444661 110720121926856463541687)
                  ·
                    rfl

theorem cell21_485160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_485160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485160 prefixEnd_485160 := by exact prefixLift 485160
  have htrace : WordTrace (prefixWord ++ tailWord_485160) baseStart_485160 baseEnd_485160 := by
    simpa [prefixWord, tailWord_485160, baseEnd_485160] using wordTrace_append hprefix tailTrace_485160
  have hstable : (prefixWord ++ tailWord_485160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485160).length < 2 ^ (prefixWord ++ tailWord_485160).sum := by decide
  have hdescent : baseEnd_485160 < baseStart_485160 := by decide
  rcases family_descends (prefixWord ++ tailWord_485160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485312 : List Nat := [2, 1, 1, 2, 3, 2, 4, 3, 3]
def baseStart_485312 : Nat := 118140960795 + 485312 * 2 ^ 59
def prefixEnd_485312 : Nat := 4983230072969 + 3 ^ 40 * 485312 * 2
def baseEnd_485312 : Nat := 110754810397737977008043

theorem tailTrace_485312 : CollatzResearch.WordTrace tailWord_485312 prefixEnd_485312 110754810397737977008043 := by
  unfold tailWord_485312
  simp only [CollatzResearch.WordTrace]
  refine ⟨8850391408902491767961095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11800521878536655690614793 8850391408902491767961095)
  ·
    refine ⟨13275587113353737651941643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8850391408902491767961095 13275587113353737651941643)
    ·
      refine ⟨19913380670030606477912465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13275587113353737651941643 19913380670030606477912465)
      ·
        refine ⟨14935035502522954858434349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19913380670030606477912465 14935035502522954858434349)
        ·
          refine ⟨5600638313446108071912881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14935035502522954858434349 5600638313446108071912881)
          ·
            refine ⟨4200478735084581053934661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5600638313446108071912881 4200478735084581053934661)
            ·
              refine ⟨787589762828358947612749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4200478735084581053934661 787589762828358947612749)
              ·
                refine ⟨295346161060634605354781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 787589762828358947612749 295346161060634605354781)
                ·
                  refine ⟨110754810397737977008043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295346161060634605354781 110754810397737977008043)
                  ·
                    rfl

theorem cell21_485312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 3].length) (baseStart_485312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485312 prefixEnd_485312 := by exact prefixLift 485312
  have htrace : WordTrace (prefixWord ++ tailWord_485312) baseStart_485312 baseEnd_485312 := by
    simpa [prefixWord, tailWord_485312, baseEnd_485312] using wordTrace_append hprefix tailTrace_485312
  have hstable : (prefixWord ++ tailWord_485312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485312).length < 2 ^ (prefixWord ++ tailWord_485312).sum := by decide
  have hdescent : baseEnd_485312 < baseStart_485312 := by decide
  rcases family_descends (prefixWord ++ tailWord_485312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485323 : List Nat := [1, 1, 1, 1, 3, 4, 10]
def baseStart_485323 : Nat := 118140960795 + 485323 * 2 ^ 59
def prefixEnd_485323 : Nat := 4983230072969 + 3 ^ 40 * 485323 * 2
def baseEnd_485323 : Nat := 12306368971956044702743

theorem tailTrace_485323 : CollatzResearch.WordTrace tailWord_485323 prefixEnd_485323 12306368971956044702743 := by
  unfold tailWord_485323
  simp only [CollatzResearch.WordTrace]
  refine ⟨17701184020765132414572623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11800789347176754943048415 17701184020765132414572623)
  ·
    refine ⟨26551776031147698621858935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17701184020765132414572623 26551776031147698621858935)
    ·
      refine ⟨39827664046721547932788403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26551776031147698621858935 39827664046721547932788403)
      ·
        refine ⟨59741496070082321899182605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39827664046721547932788403 59741496070082321899182605)
        ·
          refine ⟨22403061026280870712193477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59741496070082321899182605 22403061026280870712193477)
          ·
            refine ⟨4200573942427663258536277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22403061026280870712193477 4200573942427663258536277)
            ·
              refine ⟨12306368971956044702743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4200573942427663258536277 12306368971956044702743)
              ·
                rfl

theorem cell21_485323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 10].length) (baseStart_485323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485323 prefixEnd_485323 := by exact prefixLift 485323
  have htrace : WordTrace (prefixWord ++ tailWord_485323) baseStart_485323 baseEnd_485323 := by
    simpa [prefixWord, tailWord_485323, baseEnd_485323] using wordTrace_append hprefix tailTrace_485323
  have hstable : (prefixWord ++ tailWord_485323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485323).length < 2 ^ (prefixWord ++ tailWord_485323).sum := by decide
  have hdescent : baseEnd_485323 < baseStart_485323 := by decide
  rcases family_descends (prefixWord ++ tailWord_485323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485343 : List Nat := [1, 1, 2, 3, 4, 2, 3, 1, 4]
def baseStart_485343 : Nat := 118140960795 + 485343 * 2 ^ 59
def prefixEnd_485343 : Nat := 4983230072969 + 3 ^ 40 * 485343 * 2
def baseEnd_485343 : Nat := 110761885020088811991313

theorem tailTrace_485343 : CollatzResearch.WordTrace tailWord_485343 prefixEnd_485343 110761885020088811991313 := by
  unfold tailWord_485343
  simp only [CollatzResearch.WordTrace]
  refine ⟨17701913480692675830300683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11801275653795117220200455 17701913480692675830300683)
  ·
    refine ⟨26552870221039013745451025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17701913480692675830300683 26552870221039013745451025)
    ·
      refine ⟨19914652665779260309088269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26552870221039013745451025 19914652665779260309088269)
      ·
        refine ⟨7467994749667222615908101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19914652665779260309088269 7467994749667222615908101)
        ·
          refine ⟨1400249015562604240482769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7467994749667222615908101 1400249015562604240482769)
          ·
            refine ⟨1050186761671953180362077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1400249015562604240482769 1050186761671953180362077)
            ·
              refine ⟨393820035626982442635779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1050186761671953180362077 393820035626982442635779)
              ·
                refine ⟨590730053440473663953669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393820035626982442635779 590730053440473663953669)
                ·
                  refine ⟨110761885020088811991313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 590730053440473663953669 110761885020088811991313)
                  ·
                    rfl

theorem cell21_485343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 4].length) (baseStart_485343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485343 prefixEnd_485343 := by exact prefixLift 485343
  have htrace : WordTrace (prefixWord ++ tailWord_485343) baseStart_485343 baseEnd_485343 := by
    simpa [prefixWord, tailWord_485343, baseEnd_485343] using wordTrace_append hprefix tailTrace_485343
  have hstable : (prefixWord ++ tailWord_485343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485343).length < 2 ^ (prefixWord ++ tailWord_485343).sum := by decide
  have hdescent : baseEnd_485343 < baseStart_485343 := by decide
  rcases family_descends (prefixWord ++ tailWord_485343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485402 : List Nat := [3, 1, 1, 3, 1, 4, 1, 3, 4]
def baseStart_485402 : Nat := 118140960795 + 485402 * 2 ^ 59
def prefixEnd_485402 : Nat := 4983230072969 + 3 ^ 40 * 485402 * 2
def baseEnd_485402 : Nat := 110775349623917820507859

theorem tailTrace_485402 : CollatzResearch.WordTrace tailWord_485402 prefixEnd_485402 110775349623917820507859 := by
  unfold tailWord_485402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4426016346869732226674615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11802710258319285937798973 4426016346869732226674615)
  ·
    refine ⟨6639024520304598340011923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4426016346869732226674615 6639024520304598340011923)
    ·
      refine ⟨9958536780456897510017885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6639024520304598340011923 9958536780456897510017885)
      ·
        refine ⟨3734451292671336566256707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9958536780456897510017885 3734451292671336566256707)
        ·
          refine ⟨5601676939007004849385061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3734451292671336566256707 5601676939007004849385061)
          ·
            refine ⟨1050314426063813409259699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5601676939007004849385061 1050314426063813409259699)
            ·
              refine ⟨1575471639095720113889549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050314426063813409259699 1575471639095720113889549)
              ·
                refine ⟨590801864660895042708581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1575471639095720113889549 590801864660895042708581)
                ·
                  refine ⟨110775349623917820507859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 590801864660895042708581 110775349623917820507859)
                  ·
                    rfl

theorem cell21_485402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_485402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485402 prefixEnd_485402 := by exact prefixLift 485402
  have htrace : WordTrace (prefixWord ++ tailWord_485402) baseStart_485402 baseEnd_485402 := by
    simpa [prefixWord, tailWord_485402, baseEnd_485402] using wordTrace_append hprefix tailTrace_485402
  have hstable : (prefixWord ++ tailWord_485402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485402).length < 2 ^ (prefixWord ++ tailWord_485402).sum := by decide
  have hdescent : baseEnd_485402 < baseStart_485402 := by decide
  rcases family_descends (prefixWord ++ tailWord_485402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485475 : List Nat := [1, 1, 1, 5, 1, 1, 2, 9]
def baseStart_485475 : Nat := 118140960795 + 485475 * 2 ^ 59
def prefixEnd_485475 : Nat := 4983230072969 + 3 ^ 40 * 485475 * 2
def baseEnd_485475 : Nat := 36930669739495305263681

theorem tailTrace_485475 : CollatzResearch.WordTrace tailWord_485475 prefixEnd_485475 36930669739495305263681 := by
  unfold tailWord_485475
  simp only [CollatzResearch.WordTrace]
  refine ⟨17706727916214462374105879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11804485277476308249403919 17706727916214462374105879)
  ·
    refine ⟨26560091874321693561158819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17706727916214462374105879 26560091874321693561158819)
    ·
      refine ⟨39840137811482540341738229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26560091874321693561158819 39840137811482540341738229)
      ·
        refine ⟨3735012919826488157037959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39840137811482540341738229 3735012919826488157037959)
        ·
          refine ⟨5602519379739732235556939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3735012919826488157037959 5602519379739732235556939)
          ·
            refine ⟨8403779069609598353335409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5602519379739732235556939 8403779069609598353335409)
            ·
              refine ⟨6302834302207198765001557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8403779069609598353335409 6302834302207198765001557)
              ·
                refine ⟨36930669739495305263681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6302834302207198765001557 36930669739495305263681)
                ·
                  rfl

theorem cell21_485475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 9].length) (baseStart_485475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485475 prefixEnd_485475 := by exact prefixLift 485475
  have htrace : WordTrace (prefixWord ++ tailWord_485475) baseStart_485475 baseEnd_485475 := by
    simpa [prefixWord, tailWord_485475, baseEnd_485475] using wordTrace_append hprefix tailTrace_485475
  have hstable : (prefixWord ++ tailWord_485475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485475).length < 2 ^ (prefixWord ++ tailWord_485475).sum := by decide
  have hdescent : baseEnd_485475 < baseStart_485475 := by decide
  rcases family_descends (prefixWord ++ tailWord_485475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485537 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 6]
def baseStart_485537 : Nat := 118140960795 + 485537 * 2 ^ 59
def prefixEnd_485537 : Nat := 4983230072969 + 3 ^ 40 * 485537 * 2
def baseEnd_485537 : Nat := 110806158463187585757583

theorem tailTrace_485537 : CollatzResearch.WordTrace tailWord_485537 prefixEnd_485537 110806158463187585757583 := by
  unfold tailWord_485537
  simp only [CollatzResearch.WordTrace]
  refine ⟨17708989241989846962862865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11805992827993231308575243 17708989241989846962862865)
  ·
    refine ⟨13281741931492385222147149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17708989241989846962862865 13281741931492385222147149)
    ·
      refine ⟨4980653224309644458305181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13281741931492385222147149 4980653224309644458305181)
      ·
        refine ⟨1867744959116116671864443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4980653224309644458305181 1867744959116116671864443)
        ·
          refine ⟨2801617438674175007796665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1867744959116116671864443 2801617438674175007796665)
          ·
            refine ⟨2101213079005631255847499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2801617438674175007796665 2101213079005631255847499)
            ·
              refine ⟨3151819618508446883771249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2101213079005631255847499 3151819618508446883771249)
              ·
                refine ⟨2363864713881335162828437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3151819618508446883771249 2363864713881335162828437)
                ·
                  refine ⟨110806158463187585757583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2363864713881335162828437 110806158463187585757583)
                  ·
                    rfl

theorem cell21_485537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_485537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485537 prefixEnd_485537 := by exact prefixLift 485537
  have htrace : WordTrace (prefixWord ++ tailWord_485537) baseStart_485537 baseEnd_485537 := by
    simpa [prefixWord, tailWord_485537, baseEnd_485537] using wordTrace_append hprefix tailTrace_485537
  have hstable : (prefixWord ++ tailWord_485537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485537).length < 2 ^ (prefixWord ++ tailWord_485537).sum := by decide
  have hdescent : baseEnd_485537 < baseStart_485537 := by decide
  rcases family_descends (prefixWord ++ tailWord_485537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485557 : List Nat := [1, 3, 3, 4, 1, 2, 1, 1, 5]
def baseStart_485557 : Nat := 118140960795 + 485557 * 2 ^ 59
def prefixEnd_485557 : Nat := 4983230072969 + 3 ^ 40 * 485557 * 2
def baseEnd_485557 : Nat := 110810722735671995424209

theorem tailTrace_485557 : CollatzResearch.WordTrace tailWord_485557 prefixEnd_485557 110810722735671995424209 := by
  unfold tailWord_485557
  simp only [CollatzResearch.WordTrace]
  refine ⟨17709718701917390378590925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11806479134611593585727283 17709718701917390378590925)
  ·
    refine ⟨6641144513219021391971597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17709718701917390378590925 6641144513219021391971597)
    ·
      refine ⟨2490429192457133021989349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6641144513219021391971597 2490429192457133021989349)
      ·
        refine ⟨466955473585712441623003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2490429192457133021989349 466955473585712441623003)
        ·
          refine ⟨700433210378568662434505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466955473585712441623003 700433210378568662434505)
          ·
            refine ⟨525324907783926496825879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 700433210378568662434505 525324907783926496825879)
            ·
              refine ⟨787987361675889745238819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525324907783926496825879 787987361675889745238819)
              ·
                refine ⟨1181981042513834617858229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787987361675889745238819 1181981042513834617858229)
                ·
                  refine ⟨110810722735671995424209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1181981042513834617858229 110810722735671995424209)
                  ·
                    rfl

theorem cell21_485557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_485557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485557 prefixEnd_485557 := by exact prefixLift 485557
  have htrace : WordTrace (prefixWord ++ tailWord_485557) baseStart_485557 baseEnd_485557 := by
    simpa [prefixWord, tailWord_485557, baseEnd_485557] using wordTrace_append hprefix tailTrace_485557
  have hstable : (prefixWord ++ tailWord_485557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485557).length < 2 ^ (prefixWord ++ tailWord_485557).sum := by decide
  have hdescent : baseEnd_485557 < baseStart_485557 := by decide
  rcases family_descends (prefixWord ++ tailWord_485557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485568 : List Nat := [2, 1, 1, 2, 5, 2, 2, 6]
def baseStart_485568 : Nat := 118140960795 + 485568 * 2 ^ 59
def prefixEnd_485568 : Nat := 4983230072969 + 3 ^ 40 * 485568 * 2
def baseEnd_485568 : Nat := 36937744361846140246951

theorem tailTrace_485568 : CollatzResearch.WordTrace tailWord_485568 prefixEnd_485568 36937744361846140246951 := by
  unfold tailWord_485568
  simp only [CollatzResearch.WordTrace]
  refine ⟨8855059952438769628620679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11806746603251692838160905 8855059952438769628620679)
  ·
    refine ⟨13282589928658154442931019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8855059952438769628620679 13282589928658154442931019)
    ·
      refine ⟨19923884892987231664396529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13282589928658154442931019 19923884892987231664396529)
      ·
        refine ⟨14942913669740423748297397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19923884892987231664396529 14942913669740423748297397)
        ·
          refine ⟨1400898156538164726402881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14942913669740423748297397 1400898156538164726402881)
          ·
            refine ⟨1050673617403623544802161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1400898156538164726402881 1050673617403623544802161)
            ·
              refine ⟨788005213052717658601621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1050673617403623544802161 788005213052717658601621)
              ·
                refine ⟨36937744361846140246951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 788005213052717658601621 36937744361846140246951)
                ·
                  rfl

theorem cell21_485568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 6].length) (baseStart_485568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485568 prefixEnd_485568 := by exact prefixLift 485568
  have htrace : WordTrace (prefixWord ++ tailWord_485568) baseStart_485568 baseEnd_485568 := by
    simpa [prefixWord, tailWord_485568, baseEnd_485568] using wordTrace_append hprefix tailTrace_485568
  have hstable : (prefixWord ++ tailWord_485568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485568).length < 2 ^ (prefixWord ++ tailWord_485568).sum := by decide
  have hdescent : baseEnd_485568 < baseStart_485568 := by decide
  rcases family_descends (prefixWord ++ tailWord_485568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485599 : List Nat := [1, 1, 2, 3, 2, 1, 1, 7, 3]
def baseStart_485599 : Nat := 118140960795 + 485599 * 2 ^ 59
def prefixEnd_485599 : Nat := 4983230072969 + 3 ^ 40 * 485599 * 2
def baseEnd_485599 : Nat := 110820307707889255724123

theorem tailTrace_485599 : CollatzResearch.WordTrace tailWord_485599 prefixEnd_485599 110820307707889255724123 := by
  unfold tailWord_485599
  simp only [CollatzResearch.WordTrace]
  refine ⟨17711250567765231551619851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11807500378510154367746567 17711250567765231551619851)
  ·
    refine ⟨26566875851647847327429777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17711250567765231551619851 26566875851647847327429777)
    ·
      refine ⟨19925156888735885495572333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26566875851647847327429777 19925156888735885495572333)
      ·
        refine ⟨7471933833275957060839625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19925156888735885495572333 7471933833275957060839625)
        ·
          refine ⟨5603950374956967795629719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7471933833275957060839625 5603950374956967795629719)
          ·
            refine ⟨8405925562435451693444579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5603950374956967795629719 8405925562435451693444579)
            ·
              refine ⟨12608888343653177540166869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8405925562435451693444579 12608888343653177540166869)
              ·
                refine ⟨295520820554371348597661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12608888343653177540166869 295520820554371348597661)
                ·
                  refine ⟨110820307707889255724123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295520820554371348597661 110820307707889255724123)
                  ·
                    rfl

theorem cell21_485599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 3].length) (baseStart_485599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485599 prefixEnd_485599 := by exact prefixLift 485599
  have htrace : WordTrace (prefixWord ++ tailWord_485599) baseStart_485599 baseEnd_485599 := by
    simpa [prefixWord, tailWord_485599, baseEnd_485599] using wordTrace_append hprefix tailTrace_485599
  have hstable : (prefixWord ++ tailWord_485599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485599).length < 2 ^ (prefixWord ++ tailWord_485599).sum := by decide
  have hdescent : baseEnd_485599 < baseStart_485599 := by decide
  rcases family_descends (prefixWord ++ tailWord_485599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485602 : List Nat := [3, 3, 4, 1, 1, 9]
def baseStart_485602 : Nat := 118140960795 + 485602 * 2 ^ 59
def prefixEnd_485602 : Nat := 4983230072969 + 3 ^ 40 * 485602 * 2
def baseEnd_485602 : Nat := 4104481198102293228671

theorem tailTrace_485602 : CollatzResearch.WordTrace tailWord_485602 prefixEnd_485602 4104481198102293228671 := by
  unfold tailWord_485602
  simp only [CollatzResearch.WordTrace]
  refine ⟨4427839996688590765994765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11807573324502908709319373 4427839996688590765994765)
  ·
    refine ⟨1660439998758221537248037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4427839996688590765994765 1660439998758221537248037)
    ·
      refine ⟨311332499767166538234007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1660439998758221537248037 311332499767166538234007)
      ·
        refine ⟨466998749650749807351011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311332499767166538234007 466998749650749807351011)
        ·
          refine ⟨700498124476124711026517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466998749650749807351011 700498124476124711026517)
          ·
            refine ⟨4104481198102293228671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 700498124476124711026517 4104481198102293228671)
            ·
              rfl

theorem cell21_485602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 9].length) (baseStart_485602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485602 prefixEnd_485602 := by exact prefixLift 485602
  have htrace : WordTrace (prefixWord ++ tailWord_485602) baseStart_485602 baseEnd_485602 := by
    simpa [prefixWord, tailWord_485602, baseEnd_485602] using wordTrace_append hprefix tailTrace_485602
  have hstable : (prefixWord ++ tailWord_485602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485602).length < 2 ^ (prefixWord ++ tailWord_485602).sum := by decide
  have hdescent : baseEnd_485602 < baseStart_485602 := by decide
  rcases family_descends (prefixWord ++ tailWord_485602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485630 : List Nat := [4, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_485630 : Nat := 118140960795 + 485630 * 2 ^ 59
def prefixEnd_485630 : Nat := 4983230072969 + 3 ^ 40 * 485630 * 2
def baseEnd_485630 : Nat := 110827382330240090707393

theorem tailTrace_485630 : CollatzResearch.WordTrace tailWord_485630 prefixEnd_485630 110827382330240090707393 := by
  unfold tailWord_485630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2214047653831615480749793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11808254153768615897332229 2214047653831615480749793)
  ·
    refine ⟨1660535740373711610562345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2214047653831615480749793 1660535740373711610562345)
    ·
      refine ⟨1245401805280283707921759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1660535740373711610562345 1245401805280283707921759)
      ·
        refine ⟨1868102707920425561882639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245401805280283707921759 1868102707920425561882639)
        ·
          refine ⟨2802154061880638342823959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1868102707920425561882639 2802154061880638342823959)
          ·
            refine ⟨4203231092820957514235939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802154061880638342823959 4203231092820957514235939)
            ·
              refine ⟨6304846639231436271353909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4203231092820957514235939 6304846639231436271353909)
              ·
                refine ⟨591079372427947150439429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6304846639231436271353909 591079372427947150439429)
                ·
                  refine ⟨110827382330240090707393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 591079372427947150439429 110827382330240090707393)
                  ·
                    rfl

theorem cell21_485630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_485630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485630 prefixEnd_485630 := by exact prefixLift 485630
  have htrace : WordTrace (prefixWord ++ tailWord_485630) baseStart_485630 baseEnd_485630 := by
    simpa [prefixWord, tailWord_485630, baseEnd_485630] using wordTrace_append hprefix tailTrace_485630
  have hstable : (prefixWord ++ tailWord_485630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485630).length < 2 ^ (prefixWord ++ tailWord_485630).sum := by decide
  have hdescent : baseEnd_485630 < baseStart_485630 := by decide
  rcases family_descends (prefixWord ++ tailWord_485630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485644 : List Nat := [2, 2, 1, 2, 2, 2, 5, 5]
def baseStart_485644 : Nat := 118140960795 + 485644 * 2 ^ 59
def prefixEnd_485644 : Nat := 4983230072969 + 3 ^ 40 * 485644 * 2
def baseEnd_485644 : Nat := 36943525773659725824677

theorem tailTrace_485644 : CollatzResearch.WordTrace tailWord_485644 prefixEnd_485644 36943525773659725824677 := by
  unfold tailWord_485644
  simp only [CollatzResearch.WordTrace]
  refine ⟨8856445926301102118503993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11808594568401469491338657 8856445926301102118503993)
  ·
    refine ⟨6642334444725826588877995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8856445926301102118503993 6642334444725826588877995)
    ·
      refine ⟨9963501667088739883316993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6642334444725826588877995 9963501667088739883316993)
      ·
        refine ⟨7472626250316554912487745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9963501667088739883316993 7472626250316554912487745)
        ·
          refine ⟨5604469687737416184365809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7472626250316554912487745 5604469687737416184365809)
          ·
            refine ⟨4203352265803062138274357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5604469687737416184365809 4203352265803062138274357)
            ·
              refine ⟨394064274919037075463221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4203352265803062138274357 394064274919037075463221)
              ·
                refine ⟨36943525773659725824677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 394064274919037075463221 36943525773659725824677)
                ·
                  rfl

theorem cell21_485644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 5].length) (baseStart_485644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485644 prefixEnd_485644 := by exact prefixLift 485644
  have htrace : WordTrace (prefixWord ++ tailWord_485644) baseStart_485644 baseEnd_485644 := by
    simpa [prefixWord, tailWord_485644, baseEnd_485644] using wordTrace_append hprefix tailTrace_485644
  have hstable : (prefixWord ++ tailWord_485644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485644).length < 2 ^ (prefixWord ++ tailWord_485644).sum := by decide
  have hdescent : baseEnd_485644 < baseStart_485644 := by decide
  rcases family_descends (prefixWord ++ tailWord_485644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485703 : List Nat := [1, 1, 4, 1, 2, 2, 3, 7]
def baseStart_485703 : Nat := 118140960795 + 485703 * 2 ^ 59
def prefixEnd_485703 : Nat := 4983230072969 + 3 ^ 40 * 485703 * 2
def baseEnd_485703 : Nat := 36948013974936061996859

theorem tailTrace_485703 : CollatzResearch.WordTrace tailWord_485703 prefixEnd_485703 36948013974936061996859 := by
  unfold tailWord_485703
  simp only [CollatzResearch.WordTrace]
  refine ⟨17715043759388457313405763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11810029172925638208937175 17715043759388457313405763)
  ·
    refine ⟨26572565639082685970108645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17715043759388457313405763 26572565639082685970108645)
    ·
      refine ⟨4982356057328003619395371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26572565639082685970108645 4982356057328003619395371)
      ·
        refine ⟨7473534085992005429093057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4982356057328003619395371 7473534085992005429093057)
        ·
          refine ⟨5605150564494004071819793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7473534085992005429093057 5605150564494004071819793)
          ·
            refine ⟨4203862923370503053864845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5605150564494004071819793 4203862923370503053864845)
            ·
              refine ⟨1576448596263938645199317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4203862923370503053864845 1576448596263938645199317)
              ·
                refine ⟨36948013974936061996859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1576448596263938645199317 36948013974936061996859)
                ·
                  rfl

theorem cell21_485703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 7].length) (baseStart_485703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485703 prefixEnd_485703 := by exact prefixLift 485703
  have htrace : WordTrace (prefixWord ++ tailWord_485703) baseStart_485703 baseEnd_485703 := by
    simpa [prefixWord, tailWord_485703, baseEnd_485703] using wordTrace_append hprefix tailTrace_485703
  have hstable : (prefixWord ++ tailWord_485703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485703).length < 2 ^ (prefixWord ++ tailWord_485703).sum := by decide
  have hdescent : baseEnd_485703 < baseStart_485703 := by decide
  rcases family_descends (prefixWord ++ tailWord_485703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485740 : List Nat := [2, 2, 1, 1, 7, 1, 2, 1, 4]
def baseStart_485740 : Nat := 118140960795 + 485740 * 2 ^ 59
def prefixEnd_485740 : Nat := 4983230072969 + 3 ^ 40 * 485740 * 2
def baseEnd_485740 : Nat := 110852485828904343873835

theorem tailTrace_485740 : CollatzResearch.WordTrace tailWord_485740 prefixEnd_485740 110852485828904343873835 := by
  unfold tailWord_485740
  simp only [CollatzResearch.WordTrace]
  refine ⟨8858196630127206316251337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11810928840169608421668449 8858196630127206316251337)
  ·
    refine ⟨6643647472595404737188503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8858196630127206316251337 6643647472595404737188503)
    ·
      refine ⟨9965471208893107105782755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6643647472595404737188503 9965471208893107105782755)
      ·
        refine ⟨14948206813339660658674133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9965471208893107105782755 14948206813339660658674133)
        ·
          refine ⟨350348597187648296687675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 14948206813339660658674133 350348597187648296687675)
          ·
            refine ⟨525522895781472445031513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350348597187648296687675 525522895781472445031513)
            ·
              refine ⟨394142171836104333773635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525522895781472445031513 394142171836104333773635)
              ·
                refine ⟨591213257754156500660453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394142171836104333773635 591213257754156500660453)
                ·
                  refine ⟨110852485828904343873835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 591213257754156500660453 110852485828904343873835)
                  ·
                    rfl

theorem cell21_485740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_485740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485740 prefixEnd_485740 := by exact prefixLift 485740
  have htrace : WordTrace (prefixWord ++ tailWord_485740) baseStart_485740 baseEnd_485740 := by
    simpa [prefixWord, tailWord_485740, baseEnd_485740] using wordTrace_append hprefix tailTrace_485740
  have hstable : (prefixWord ++ tailWord_485740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485740).length < 2 ^ (prefixWord ++ tailWord_485740).sum := by decide
  have hdescent : baseEnd_485740 < baseStart_485740 := by decide
  rcases family_descends (prefixWord ++ tailWord_485740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485810 : List Nat := [3, 2, 1, 1, 1, 1, 5, 2, 5]
def baseStart_485810 : Nat := 118140960795 + 485810 * 2 ^ 59
def prefixEnd_485810 : Nat := 4983230072969 + 3 ^ 40 * 485810 * 2
def baseEnd_485810 : Nat := 110868460782599777707025

theorem tailTrace_485810 : CollatzResearch.WordTrace tailWord_485810 prefixEnd_485810 110868460782599777707025 := by
  unfold tailWord_485810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4429736592500203646887721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11812630913333876391700589 4429736592500203646887721)
  ·
    refine ⟨3322302444375152735165791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4429736592500203646887721 3322302444375152735165791)
    ·
      refine ⟨4983453666562729102748687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3322302444375152735165791 4983453666562729102748687)
      ·
        refine ⟨7475180499844093654123031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4983453666562729102748687 7475180499844093654123031)
        ·
          refine ⟨11212770749766140481184547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7475180499844093654123031 11212770749766140481184547)
          ·
            refine ⟨16819156124649210721776821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11212770749766140481184547 16819156124649210721776821)
            ·
              refine ⟨1576795886685863505166577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16819156124649210721776821 1576795886685863505166577)
              ·
                refine ⟨1182596915014397628874933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576795886685863505166577 1182596915014397628874933)
                ·
                  refine ⟨110868460782599777707025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1182596915014397628874933 110868460782599777707025)
                  ·
                    rfl

theorem cell21_485810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_485810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485810 prefixEnd_485810 := by exact prefixLift 485810
  have htrace : WordTrace (prefixWord ++ tailWord_485810) baseStart_485810 baseEnd_485810 := by
    simpa [prefixWord, tailWord_485810, baseEnd_485810] using wordTrace_append hprefix tailTrace_485810
  have hstable : (prefixWord ++ tailWord_485810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485810).length < 2 ^ (prefixWord ++ tailWord_485810).sum := by decide
  have hdescent : baseEnd_485810 < baseStart_485810 := by decide
  rcases family_descends (prefixWord ++ tailWord_485810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485813 : List Nat := [1, 3, 3, 2, 3, 1, 3, 5]
def baseStart_485813 : Nat := 118140960795 + 485813 * 2 ^ 59
def prefixEnd_485813 : Nat := 4983230072969 + 3 ^ 40 * 485813 * 2
def baseEnd_485813 : Nat := 36956381807824146385673

theorem tailTrace_485813 : CollatzResearch.WordTrace tailWord_485813 prefixEnd_485813 36956381807824146385673 := by
  unfold tailWord_485813
  simp only [CollatzResearch.WordTrace]
  refine ⟨17719055788989946099910093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11812703859326630733273395 17719055788989946099910093)
  ·
    refine ⟨6644645920871229787466285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17719055788989946099910093 6644645920871229787466285)
    ·
      refine ⟨2491742220326711170299857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6644645920871229787466285 2491742220326711170299857)
      ·
        refine ⟨1868806665245033377724893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2491742220326711170299857 1868806665245033377724893)
        ·
          refine ⟨700802499466887516646835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1868806665245033377724893 700802499466887516646835)
          ·
            refine ⟨1051203749200331274970253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700802499466887516646835 1051203749200331274970253)
            ·
              refine ⟨394201405950124228113845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1051203749200331274970253 394201405950124228113845)
              ·
                refine ⟨36956381807824146385673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 394201405950124228113845 36956381807824146385673)
                ·
                  rfl

theorem cell21_485813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 5].length) (baseStart_485813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485813 prefixEnd_485813 := by exact prefixLift 485813
  have htrace : WordTrace (prefixWord ++ tailWord_485813) baseStart_485813 baseEnd_485813 := by
    simpa [prefixWord, tailWord_485813, baseEnd_485813] using wordTrace_append hprefix tailTrace_485813
  have hstable : (prefixWord ++ tailWord_485813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485813).length < 2 ^ (prefixWord ++ tailWord_485813).sum := by decide
  have hdescent : baseEnd_485813 < baseStart_485813 := by decide
  rcases family_descends (prefixWord ++ tailWord_485813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485824 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 6]
def baseStart_485824 : Nat := 118140960795 + 485824 * 2 ^ 59
def prefixEnd_485824 : Nat := 4983230072969 + 3 ^ 40 * 485824 * 2
def baseEnd_485824 : Nat := 110871655773338864473663

theorem tailTrace_485824 : CollatzResearch.WordTrace tailWord_485824 prefixEnd_485824 110871655773338864473663 := by
  unfold tailWord_485824
  simp only [CollatzResearch.WordTrace]
  refine ⟨8859728495975047489280263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11812971327966729985707017 8859728495975047489280263)
  ·
    refine ⟨13289592743962571233920395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8859728495975047489280263 13289592743962571233920395)
    ·
      refine ⟨19934389115943856850880593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13289592743962571233920395 19934389115943856850880593)
      ·
        refine ⟨14950791836957892638160445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19934389115943856850880593 14950791836957892638160445)
        ·
          refine ⟨5606546938859209739310167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14950791836957892638160445 5606546938859209739310167)
          ·
            refine ⟨8409820408288814608965251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5606546938859209739310167 8409820408288814608965251)
            ·
              refine ⟨12614730612433221913447877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8409820408288814608965251 12614730612433221913447877)
              ·
                refine ⟨2365261989831229108771477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12614730612433221913447877 2365261989831229108771477)
                ·
                  refine ⟨110871655773338864473663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2365261989831229108771477 110871655773338864473663)
                  ·
                    rfl

theorem cell21_485824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_485824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485824 prefixEnd_485824 := by exact prefixLift 485824
  have htrace : WordTrace (prefixWord ++ tailWord_485824) baseStart_485824 baseEnd_485824 := by
    simpa [prefixWord, tailWord_485824, baseEnd_485824] using wordTrace_append hprefix tailTrace_485824
  have hstable : (prefixWord ++ tailWord_485824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485824).length < 2 ^ (prefixWord ++ tailWord_485824).sum := by decide
  have hdescent : baseEnd_485824 < baseStart_485824 := by decide
  rcases family_descends (prefixWord ++ tailWord_485824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485844 : List Nat := [2, 4, 1, 2, 2, 1, 2, 4, 3]
def baseStart_485844 : Nat := 118140960795 + 485844 * 2 ^ 59
def prefixEnd_485844 : Nat := 4983230072969 + 3 ^ 40 * 485844 * 2
def baseEnd_485844 : Nat := 110876220045823274140289

theorem tailTrace_485844 : CollatzResearch.WordTrace tailWord_485844 prefixEnd_485844 110876220045823274140289 := by
  unfold tailWord_485844
  simp only [CollatzResearch.WordTrace]
  refine ⟨8860093225938819197144293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11813457634585092262859057 8860093225938819197144293)
  ·
    refine ⟨1661267479863528599464555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8860093225938819197144293 1661267479863528599464555)
    ·
      refine ⟨2491901219795292899196833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1661267479863528599464555 2491901219795292899196833)
      ·
        refine ⟨1868925914846469674397625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2491901219795292899196833 1868925914846469674397625)
        ·
          refine ⟨1401694436134852255798219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1868925914846469674397625 1401694436134852255798219)
          ·
            refine ⟨2102541654202278383697329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401694436134852255798219 2102541654202278383697329)
            ·
              refine ⟨1576906240651708787772997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2102541654202278383697329 1576906240651708787772997)
              ·
                refine ⟨295669920122195397707437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1576906240651708787772997 295669920122195397707437)
                ·
                  refine ⟨110876220045823274140289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295669920122195397707437 110876220045823274140289)
                  ·
                    rfl

theorem cell21_485844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_485844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485844 prefixEnd_485844 := by exact prefixLift 485844
  have htrace : WordTrace (prefixWord ++ tailWord_485844) baseStart_485844 baseEnd_485844 := by
    simpa [prefixWord, tailWord_485844, baseEnd_485844] using wordTrace_append hprefix tailTrace_485844
  have hstable : (prefixWord ++ tailWord_485844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485844).length < 2 ^ (prefixWord ++ tailWord_485844).sum := by decide
  have hdescent : baseEnd_485844 < baseStart_485844 := by decide
  rcases family_descends (prefixWord ++ tailWord_485844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_485965 : List Nat := [1, 6, 1, 1, 2, 3, 1, 6]
def baseStart_485965 : Nat := 118140960795 + 485965 * 2 ^ 59
def prefixEnd_485965 : Nat := 4983230072969 + 3 ^ 40 * 485965 * 2
def baseEnd_485965 : Nat := 36967944631451317541125

theorem tailTrace_485965 : CollatzResearch.WordTrace tailWord_485965 prefixEnd_485965 36967944631451317541125 := by
  unfold tailWord_485965
  simp only [CollatzResearch.WordTrace]
  refine ⟨17724599684439276059443349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11816399789626184039628899 17724599684439276059443349)
  ·
    refine ⟨830840610208091065286407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17724599684439276059443349 830840610208091065286407)
    ·
      refine ⟨1246260915312136597929611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 830840610208091065286407 1246260915312136597929611)
      ·
        refine ⟨1869391372968204896894417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246260915312136597929611 1869391372968204896894417)
        ·
          refine ⟨1402043529726153672670813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1869391372968204896894417 1402043529726153672670813)
          ·
            refine ⟨525766323647307627251555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1402043529726153672670813 525766323647307627251555)
            ·
              refine ⟨788649485470961440877333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525766323647307627251555 788649485470961440877333)
              ·
                refine ⟨36967944631451317541125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 788649485470961440877333 36967944631451317541125)
                ·
                  rfl

theorem cell21_485965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 6].length) (baseStart_485965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_485965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_485965 prefixEnd_485965 := by exact prefixLift 485965
  have htrace : WordTrace (prefixWord ++ tailWord_485965) baseStart_485965 baseEnd_485965 := by
    simpa [prefixWord, tailWord_485965, baseEnd_485965] using wordTrace_append hprefix tailTrace_485965
  have hstable : (prefixWord ++ tailWord_485965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_485965).length < 2 ^ (prefixWord ++ tailWord_485965).sum := by decide
  have hdescent : baseEnd_485965 < baseStart_485965 := by decide
  rcases family_descends (prefixWord ++ tailWord_485965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486052 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 8]
def baseStart_486052 : Nat := 118140960795 + 486052 * 2 ^ 59
def prefixEnd_486052 : Nat := 4983230072969 + 3 ^ 40 * 486052 * 2
def baseEnd_486052 : Nat := 110923688479661134673197

theorem tailTrace_486052 : CollatzResearch.WordTrace tailWord_486052 prefixEnd_486052 110923688479661134673197 := by
  unfold tailWord_486052
  simp only [CollatzResearch.WordTrace]
  refine ⟨8863886417562044958930205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11818515223416059945240273 8863886417562044958930205)
  ·
    refine ⟨3323957406585766859598827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8863886417562044958930205 3323957406585766859598827)
    ·
      refine ⟨4985936109878650289398241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3323957406585766859598827 4985936109878650289398241)
      ·
        refine ⟨3739452082408987717048681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4985936109878650289398241 3739452082408987717048681)
        ·
          refine ⟨2804589061806740787786511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3739452082408987717048681 2804589061806740787786511)
          ·
            refine ⟨4206883592710111181679767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2804589061806740787786511 4206883592710111181679767)
            ·
              refine ⟨6310325389065166772519651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206883592710111181679767 6310325389065166772519651)
              ·
                refine ⟨9465488083597750158779477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6310325389065166772519651 9465488083597750158779477)
                ·
                  refine ⟨110923688479661134673197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9465488083597750158779477 110923688479661134673197)
                  ·
                    rfl

theorem cell21_486052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_486052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_486052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_486052 prefixEnd_486052 := by exact prefixLift 486052
  have htrace : WordTrace (prefixWord ++ tailWord_486052) baseStart_486052 baseEnd_486052 := by
    simpa [prefixWord, tailWord_486052, baseEnd_486052] using wordTrace_append hprefix tailTrace_486052
  have hstable : (prefixWord ++ tailWord_486052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486052).length < 2 ^ (prefixWord ++ tailWord_486052).sum := by decide
  have hdescent : baseEnd_486052 < baseStart_486052 := by decide
  rcases family_descends (prefixWord ++ tailWord_486052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486058 : List Nat := [3, 1, 5, 2, 2, 1, 7]
def baseStart_486058 : Nat := 118140960795 + 486058 * 2 ^ 59
def prefixEnd_486058 : Nat := 4983230072969 + 3 ^ 40 * 486058 * 2
def baseEnd_486058 : Nat := 12325006417934050841465

theorem tailTrace_486058 : CollatzResearch.WordTrace tailWord_486058 prefixEnd_486058 12325006417934050841465 := by
  unfold tailWord_486058
  simp only [CollatzResearch.WordTrace]
  refine ⟨4431997918275588235644707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11818661115401568628385885 4431997918275588235644707)
  ·
    refine ⟨6647996877413382353467061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4431997918275588235644707 6647996877413382353467061)
    ·
      refine ⟨623249707257504595637537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6647996877413382353467061 623249707257504595637537)
      ·
        refine ⟨467437280443128446728153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623249707257504595637537 467437280443128446728153)
        ·
          refine ⟨350577960332346335046115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467437280443128446728153 350577960332346335046115)
          ·
            refine ⟨525866940498519502569173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350577960332346335046115 525866940498519502569173)
            ·
              refine ⟨12325006417934050841465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 525866940498519502569173 12325006417934050841465)
              ·
                rfl

theorem cell21_486058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 7].length) (baseStart_486058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_486058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_486058 prefixEnd_486058 := by exact prefixLift 486058
  have htrace : WordTrace (prefixWord ++ tailWord_486058) baseStart_486058 baseEnd_486058 := by
    simpa [prefixWord, tailWord_486058, baseEnd_486058] using wordTrace_append hprefix tailTrace_486058
  have hstable : (prefixWord ++ tailWord_486058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486058).length < 2 ^ (prefixWord ++ tailWord_486058).sum := by decide
  have hdescent : baseEnd_486058 < baseStart_486058 := by decide
  rcases family_descends (prefixWord ++ tailWord_486058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486069 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 6]
def baseStart_486069 : Nat := 118140960795 + 486069 * 2 ^ 59
def prefixEnd_486069 : Nat := 4983230072969 + 3 ^ 40 * 486069 * 2
def baseEnd_486069 : Nat := 110927568111272882889829

theorem tailTrace_486069 : CollatzResearch.WordTrace tailWord_486069 prefixEnd_486069 110927568111272882889829 := by
  unfold tailWord_486069
  simp only [CollatzResearch.WordTrace]
  refine ⟨17728392876062501821229261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11818928584041667880819507 17728392876062501821229261)
  ·
    refine ⟨6648147328523438182960973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17728392876062501821229261 6648147328523438182960973)
    ·
      refine ⟨2493055248196289318610365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6648147328523438182960973 2493055248196289318610365)
      ·
        refine ⟨934895718073608494478887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2493055248196289318610365 934895718073608494478887)
        ·
          refine ⟨1402343577110412741718331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934895718073608494478887 1402343577110412741718331)
          ·
            refine ⟨2103515365665619112577497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402343577110412741718331 2103515365665619112577497)
            ·
              refine ⟨1577636524249214334433123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2103515365665619112577497 1577636524249214334433123)
              ·
                refine ⟨2366454786373821501649685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577636524249214334433123 2366454786373821501649685)
                ·
                  refine ⟨110927568111272882889829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2366454786373821501649685 110927568111272882889829)
                  ·
                    rfl

theorem cell21_486069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_486069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_486069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_486069 prefixEnd_486069 := by exact prefixLift 486069
  have htrace : WordTrace (prefixWord ++ tailWord_486069) baseStart_486069 baseEnd_486069 := by
    simpa [prefixWord, tailWord_486069, baseEnd_486069] using wordTrace_append hprefix tailTrace_486069
  have hstable : (prefixWord ++ tailWord_486069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486069).length < 2 ^ (prefixWord ++ tailWord_486069).sum := by decide
  have hdescent : baseEnd_486069 < baseStart_486069 := by decide
  rcases family_descends (prefixWord ++ tailWord_486069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486097 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 7]
def baseStart_486097 : Nat := 118140960795 + 486097 * 2 ^ 59
def prefixEnd_486097 : Nat := 4983230072969 + 3 ^ 40 * 486097 * 2
def baseEnd_486097 : Nat := 110933958092751056423105

theorem tailTrace_486097 : CollatzResearch.WordTrace tailWord_486097 prefixEnd_486097 110933958092751056423105 := by
  unfold tailWord_486097
  simp only [CollatzResearch.WordTrace]
  refine ⟨17729414119961062603248545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11819609413307375068832363 17729414119961062603248545)
  ·
    refine ⟨13297060589970796952436409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17729414119961062603248545 13297060589970796952436409)
    ·
      refine ⟨9972795442478097714327307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13297060589970796952436409 9972795442478097714327307)
      ·
        refine ⟨14959193163717146571490961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9972795442478097714327307 14959193163717146571490961)
        ·
          refine ⟨11219394872787859928618221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14959193163717146571490961 11219394872787859928618221)
          ·
            refine ⟨4207273077295447473231833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11219394872787859928618221 4207273077295447473231833)
            ·
              refine ⟨3155454807971585604923875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4207273077295447473231833 3155454807971585604923875)
              ·
                refine ⟨4733182211957378407385813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3155454807971585604923875 4733182211957378407385813)
                ·
                  refine ⟨110933958092751056423105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4733182211957378407385813 110933958092751056423105)
                  ·
                    rfl

theorem cell21_486097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_486097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_486097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_486097 prefixEnd_486097 := by exact prefixLift 486097
  have htrace : WordTrace (prefixWord ++ tailWord_486097) baseStart_486097 baseEnd_486097 := by
    simpa [prefixWord, tailWord_486097, baseEnd_486097] using wordTrace_append hprefix tailTrace_486097
  have hstable : (prefixWord ++ tailWord_486097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486097).length < 2 ^ (prefixWord ++ tailWord_486097).sum := by decide
  have hdescent : baseEnd_486097 < baseStart_486097 := by decide
  rcases family_descends (prefixWord ++ tailWord_486097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486159 : List Nat := [1, 1, 2, 1, 1, 1, 9, 5]
def baseStart_486159 : Nat := 118140960795 + 486159 * 2 ^ 59
def prefixEnd_486159 : Nat := 4983230072969 + 3 ^ 40 * 486159 * 2
def baseEnd_486159 : Nat := 36982702445817575463215

theorem tailTrace_486159 : CollatzResearch.WordTrace tailWord_486159 prefixEnd_486159 36982702445817575463215 := by
  unfold tailWord_486159
  simp only [CollatzResearch.WordTrace]
  refine ⟨17731675445736447192005531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11821116963824298128003687 17731675445736447192005531)
  ·
    refine ⟨26597513168604670788008297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17731675445736447192005531 26597513168604670788008297)
    ·
      refine ⟨19948134876453503091006223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26597513168604670788008297 19948134876453503091006223)
      ·
        refine ⟨29922202314680254636509335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19948134876453503091006223 29922202314680254636509335)
        ·
          refine ⟨44883303472020381954764003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29922202314680254636509335 44883303472020381954764003)
          ·
            refine ⟨67324955208030572932146005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44883303472020381954764003 67324955208030572932146005)
            ·
              refine ⟨394482159422054138274293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 67324955208030572932146005 394482159422054138274293)
              ·
                refine ⟨36982702445817575463215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 394482159422054138274293 36982702445817575463215)
                ·
                  rfl

theorem cell21_486159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 5].length) (baseStart_486159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_486159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_486159 prefixEnd_486159 := by exact prefixLift 486159
  have htrace : WordTrace (prefixWord ++ tailWord_486159) baseStart_486159 baseEnd_486159 := by
    simpa [prefixWord, tailWord_486159, baseEnd_486159] using wordTrace_append hprefix tailTrace_486159
  have hstable : (prefixWord ++ tailWord_486159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486159).length < 2 ^ (prefixWord ++ tailWord_486159).sum := by decide
  have hdescent : baseEnd_486159 < baseStart_486159 := by decide
  rcases family_descends (prefixWord ++ tailWord_486159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486300 : List Nat := [2, 2, 3, 3, 2, 1, 1, 4, 3]
def baseStart_486300 : Nat := 118140960795 + 486300 * 2 ^ 59
def prefixEnd_486300 : Nat := 4983230072969 + 3 ^ 40 * 486300 * 2
def baseEnd_486300 : Nat := 110980285458467814539357

theorem tailTrace_486300 : CollatzResearch.WordTrace tailWord_486300 prefixEnd_486300 110980285458467814539357 := by
  unfold tailWord_486300
  simp only [CollatzResearch.WordTrace]
  refine ⟨8868409069112814136444177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11824545425483752181925569 8868409069112814136444177)
  ·
    refine ⟨6651306801834610602333133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8868409069112814136444177 6651306801834610602333133)
    ·
      refine ⟨2494240050687978975874925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6651306801834610602333133 2494240050687978975874925)
      ·
        refine ⟨935340019007992115953097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2494240050687978975874925 935340019007992115953097)
        ·
          refine ⟨701505014255994086964823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 935340019007992115953097 701505014255994086964823)
          ·
            refine ⟨1052257521383991130447235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701505014255994086964823 1052257521383991130447235)
            ·
              refine ⟨1578386282075986695670853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052257521383991130447235 1578386282075986695670853)
              ·
                refine ⟨295947427889247505438285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1578386282075986695670853 295947427889247505438285)
                ·
                  refine ⟨110980285458467814539357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295947427889247505438285 110980285458467814539357)
                  ·
                    rfl

theorem cell21_486300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_486300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_486300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_486300 prefixEnd_486300 := by exact prefixLift 486300
  have htrace : WordTrace (prefixWord ++ tailWord_486300) baseStart_486300 baseEnd_486300 := by
    simpa [prefixWord, tailWord_486300, baseEnd_486300] using wordTrace_append hprefix tailTrace_486300
  have hstable : (prefixWord ++ tailWord_486300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486300).length < 2 ^ (prefixWord ++ tailWord_486300).sum := by decide
  have hdescent : baseEnd_486300 < baseStart_486300 := by decide
  rcases family_descends (prefixWord ++ tailWord_486300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486339 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 8]
def baseStart_486339 : Nat := 118140960795 + 486339 * 2 ^ 59
def prefixEnd_486339 : Nat := 4983230072969 + 3 ^ 40 * 486339 * 2
def baseEnd_486339 : Nat := 110989185789812413389277

theorem tailTrace_486339 : CollatzResearch.WordTrace tailWord_486339 prefixEnd_486339 110989185789812413389277 := by
  unfold tailWord_486339
  simp only [CollatzResearch.WordTrace]
  refine ⟨17738240585084337933558071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11825493723389558622372047 17738240585084337933558071)
  ·
    refine ⟨26607360877626506900337107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17738240585084337933558071 26607360877626506900337107)
    ·
      refine ⟨39911041316439760350505661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26607360877626506900337107 39911041316439760350505661)
      ·
        refine ⟨14966640493664910131439623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39911041316439760350505661 14966640493664910131439623)
        ·
          refine ⟨22449960740497365197159435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14966640493664910131439623 22449960740497365197159435)
          ·
            refine ⟨33674941110746047795739153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22449960740497365197159435 33674941110746047795739153)
            ·
              refine ⟨25256205833059535846804365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33674941110746047795739153 25256205833059535846804365)
              ·
                refine ⟨9471077187397325942551637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25256205833059535846804365 9471077187397325942551637)
                ·
                  refine ⟨110989185789812413389277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9471077187397325942551637 110989185789812413389277)
                  ·
                    rfl

theorem cell21_486339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 8].length) (baseStart_486339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_486339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_486339 prefixEnd_486339 := by exact prefixLift 486339
  have htrace : WordTrace (prefixWord ++ tailWord_486339) baseStart_486339 baseEnd_486339 := by
    simpa [prefixWord, tailWord_486339, baseEnd_486339] using wordTrace_append hprefix tailTrace_486339
  have hstable : (prefixWord ++ tailWord_486339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486339).length < 2 ^ (prefixWord ++ tailWord_486339).sum := by decide
  have hdescent : baseEnd_486339 < baseStart_486339 := by decide
  rcases family_descends (prefixWord ++ tailWord_486339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486542 : List Nat := [4, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_486542 : Nat := 118140960795 + 486542 * 2 ^ 59
def prefixEnd_486542 : Nat := 4983230072969 + 3 ^ 40 * 486542 * 2
def baseEnd_486542 : Nat := 111035513155529171505529

theorem tailTrace_486542 : CollatzResearch.WordTrace tailWord_486542 prefixEnd_486542 111035513155529171505529 := by
  unfold tailWord_486542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2218205575418612950399735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11830429735565935735465253 2218205575418612950399735)
  ·
    refine ⟨3327308363127919425599603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2218205575418612950399735 3327308363127919425599603)
    ·
      refine ⟨4990962544691879138399405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3327308363127919425599603 4990962544691879138399405)
      ·
        refine ⟨1871610954259454676899777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4990962544691879138399405 1871610954259454676899777)
        ·
          refine ⟨1403708215694591007674833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1871610954259454676899777 1403708215694591007674833)
          ·
            refine ⟨1052781161770943255756125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1403708215694591007674833 1052781161770943255756125)
            ·
              refine ⟨394792935664103720908547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1052781161770943255756125 394792935664103720908547)
              ·
                refine ⟨592189403496155581362821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394792935664103720908547 592189403496155581362821)
                ·
                  refine ⟨111035513155529171505529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 592189403496155581362821 111035513155529171505529)
                  ·
                    rfl

theorem cell21_486542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_486542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_486542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_486542 prefixEnd_486542 := by exact prefixLift 486542
  have htrace : WordTrace (prefixWord ++ tailWord_486542) baseStart_486542 baseEnd_486542 := by
    simpa [prefixWord, tailWord_486542, baseEnd_486542] using wordTrace_append hprefix tailTrace_486542
  have hstable : (prefixWord ++ tailWord_486542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486542).length < 2 ^ (prefixWord ++ tailWord_486542).sum := by decide
  have hdescent : baseEnd_486542 < baseStart_486542 := by decide
  rcases family_descends (prefixWord ++ tailWord_486542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486556 : List Nat := [2, 2, 3, 2, 1, 4, 2, 5]
def baseStart_486556 : Nat := 118140960795 + 486556 * 2 ^ 59
def prefixEnd_486556 : Nat := 4983230072969 + 3 ^ 40 * 486556 * 2
def baseEnd_486556 : Nat := 37012902715422752757389

theorem tailTrace_486556 : CollatzResearch.WordTrace tailWord_486556 prefixEnd_486556 37012902715422752757389 := by
  unfold tailWord_486556
  simp only [CollatzResearch.WordTrace]
  refine ⟨8873077612649091997103761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11830770150198789329471681 8873077612649091997103761)
  ·
    refine ⟨6654808209486818997827821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8873077612649091997103761 6654808209486818997827821)
    ·
      refine ⟨2495553078557557124185433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6654808209486818997827821 2495553078557557124185433)
      ·
        refine ⟨1871664808918167843139075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2495553078557557124185433 1871664808918167843139075)
        ·
          refine ⟨2807497213377251764708613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1871664808918167843139075 2807497213377251764708613)
          ·
            refine ⟨526405727508234705882865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2807497213377251764708613 526405727508234705882865)
            ·
              refine ⟨394804295631176029412149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526405727508234705882865 394804295631176029412149)
              ·
                refine ⟨37012902715422752757389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 394804295631176029412149 37012902715422752757389)
                ·
                  rfl

theorem cell21_486556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 5].length) (baseStart_486556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_486556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_486556 prefixEnd_486556 := by exact prefixLift 486556
  have htrace : WordTrace (prefixWord ++ tailWord_486556) baseStart_486556 baseEnd_486556 := by
    simpa [prefixWord, tailWord_486556, baseEnd_486556] using wordTrace_append hprefix tailTrace_486556
  have hstable : (prefixWord ++ tailWord_486556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486556).length < 2 ^ (prefixWord ++ tailWord_486556).sum := by decide
  have hdescent : baseEnd_486556 < baseStart_486556 := by decide
  rcases family_descends (prefixWord ++ tailWord_486556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486705 : List Nat := [1, 2, 2, 3, 3, 1, 1, 3, 5]
def baseStart_486705 : Nat := 118140960795 + 486705 * 2 ^ 59
def prefixEnd_486705 : Nat := 4983230072969 + 3 ^ 40 * 486705 * 2
def baseEnd_486705 : Nat := 111072711976277110288529

theorem tailTrace_486705 : CollatzResearch.WordTrace tailWord_486705 prefixEnd_486705 111072711976277110288529 := by
  unfold tailWord_486705
  simp only [CollatzResearch.WordTrace]
  refine ⟨17751589701758382441381569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11834393134505588294254379 17751589701758382441381569)
  ·
    refine ⟨13313692276318786831036177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17751589701758382441381569 13313692276318786831036177)
    ·
      refine ⟨9985269207239090123277133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13313692276318786831036177 9985269207239090123277133)
      ·
        refine ⟨3744475952714658796228925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9985269207239090123277133 3744475952714658796228925)
        ·
          refine ⟨1404178482267997048585847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3744475952714658796228925 1404178482267997048585847)
          ·
            refine ⟨2106267723401995572878771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1404178482267997048585847 2106267723401995572878771)
            ·
              refine ⟨3159401585102993359318157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2106267723401995572878771 3159401585102993359318157)
              ·
                refine ⟨1184775594413622509744309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3159401585102993359318157 1184775594413622509744309)
                ·
                  refine ⟨111072711976277110288529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1184775594413622509744309 111072711976277110288529)
                  ·
                    rfl

theorem cell21_486705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_486705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_486705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_486705 prefixEnd_486705 := by exact prefixLift 486705
  have htrace : WordTrace (prefixWord ++ tailWord_486705) baseStart_486705 baseEnd_486705 := by
    simpa [prefixWord, tailWord_486705, baseEnd_486705] using wordTrace_append hprefix tailTrace_486705
  have hstable : (prefixWord ++ tailWord_486705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486705).length < 2 ^ (prefixWord ++ tailWord_486705).sum := by decide
  have hdescent : baseEnd_486705 < baseStart_486705 := by decide
  rcases family_descends (prefixWord ++ tailWord_486705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486742 : List Nat := [5, 2, 3, 1, 1, 2, 7]
def baseStart_486742 : Nat := 118140960795 + 486742 * 2 ^ 59
def prefixEnd_486742 : Nat := 4983230072969 + 3 ^ 40 * 486742 * 2
def baseEnd_486742 : Nat := 12342350653374807574643

theorem tailTrace_486742 : CollatzResearch.WordTrace tailWord_486742 prefixEnd_486742 12342350653374807574643 := by
  unfold tailWord_486742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1109558700164021110029905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11835292801749558506985653 1109558700164021110029905)
  ·
    refine ⟨832169025123015832522429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1109558700164021110029905 832169025123015832522429)
    ·
      refine ⟨312063384421130937195911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 832169025123015832522429 312063384421130937195911)
      ·
        refine ⟨468095076631696405793867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312063384421130937195911 468095076631696405793867)
        ·
          refine ⟨702142614947544608690801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468095076631696405793867 702142614947544608690801)
          ·
            refine ⟨526606961210658456518101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 702142614947544608690801 526606961210658456518101)
            ·
              refine ⟨12342350653374807574643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 526606961210658456518101 12342350653374807574643)
              ·
                rfl

theorem cell21_486742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 7].length) (baseStart_486742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_486742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_486742 prefixEnd_486742 := by exact prefixLift 486742
  have htrace : WordTrace (prefixWord ++ tailWord_486742) baseStart_486742 baseEnd_486742 := by
    simpa [prefixWord, tailWord_486742, baseEnd_486742] using wordTrace_append hprefix tailTrace_486742
  have hstable : (prefixWord ++ tailWord_486742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486742).length < 2 ^ (prefixWord ++ tailWord_486742).sum := by decide
  have hdescent : baseEnd_486742 < baseStart_486742 := by decide
  rcases family_descends (prefixWord ++ tailWord_486742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486809 : List Nat := [1, 2, 1, 2, 1, 14]
def baseStart_486809 : Nat := 118140960795 + 486809 * 2 ^ 59
def prefixEnd_486809 : Nat := 4983230072969 + 3 ^ 40 * 486809 * 2
def baseEnd_486809 : Nat := 4114683192340594094629

theorem tailTrace_486809 : CollatzResearch.WordTrace tailWord_486809 prefixEnd_486809 4114683192340594094629 := by
  unfold tailWord_486809
  simp only [CollatzResearch.WordTrace]
  refine ⟨17755382893381608203167481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11836921928921072135444987 17755382893381608203167481)
  ·
    refine ⟨13316537170036206152375611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17755382893381608203167481 13316537170036206152375611)
    ·
      refine ⟨19974805755054309228563417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13316537170036206152375611 19974805755054309228563417)
      ·
        refine ⟨14981104316290731921422563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19974805755054309228563417 14981104316290731921422563)
        ·
          refine ⟨22471656474436097882133845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14981104316290731921422563 22471656474436097882133845)
          ·
            refine ⟨4114683192340594094629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 22471656474436097882133845 4114683192340594094629)
            ·
              rfl

theorem cell21_486809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 14].length) (baseStart_486809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_486809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_486809 prefixEnd_486809 := by exact prefixLift 486809
  have htrace : WordTrace (prefixWord ++ tailWord_486809) baseStart_486809 baseEnd_486809 := by
    simpa [prefixWord, tailWord_486809, baseEnd_486809] using wordTrace_append hprefix tailTrace_486809
  have hstable : (prefixWord ++ tailWord_486809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486809).length < 2 ^ (prefixWord ++ tailWord_486809).sum := by decide
  have hdescent : baseEnd_486809 < baseStart_486809 := by decide
  rcases family_descends (prefixWord ++ tailWord_486809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486815 : List Nat := [1, 1, 2, 5, 1, 2, 4, 2, 3]
def baseStart_486815 : Nat := 118140960795 + 486815 * 2 ^ 59
def prefixEnd_486815 : Nat := 4983230072969 + 3 ^ 40 * 486815 * 2
def baseEnd_486815 : Nat := 111097815474941363454971

theorem tailTrace_486815 : CollatzResearch.WordTrace tailWord_486815 prefixEnd_486815 111097815474941363454971 := by
  unfold tailWord_486815
  simp only [CollatzResearch.WordTrace]
  refine ⟨17755601731359871227885899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11837067820906580818590599 17755601731359871227885899)
  ·
    refine ⟨26633402597039806841828849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17755601731359871227885899 26633402597039806841828849)
    ·
      refine ⟨19975051947779855131371637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26633402597039806841828849 19975051947779855131371637)
      ·
        refine ⟨1872661120104361418566091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19975051947779855131371637 1872661120104361418566091)
        ·
          refine ⟨2808991680156542127849137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1872661120104361418566091 2808991680156542127849137)
          ·
            refine ⟨2106743760117406595886853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2808991680156542127849137 2106743760117406595886853)
            ·
              refine ⟨395014455022013736728785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2106743760117406595886853 395014455022013736728785)
              ·
                refine ⟨296260841266510302546589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395014455022013736728785 296260841266510302546589)
                ·
                  refine ⟨111097815474941363454971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 296260841266510302546589 111097815474941363454971)
                  ·
                    rfl

theorem cell21_486815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 3].length) (baseStart_486815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_486815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_486815 prefixEnd_486815 := by exact prefixLift 486815
  have htrace : WordTrace (prefixWord ++ tailWord_486815) baseStart_486815 baseEnd_486815 := by
    simpa [prefixWord, tailWord_486815, baseEnd_486815] using wordTrace_append hprefix tailTrace_486815
  have hstable : (prefixWord ++ tailWord_486815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486815).length < 2 ^ (prefixWord ++ tailWord_486815).sum := by decide
  have hdescent : baseEnd_486815 < baseStart_486815 := by decide
  rcases family_descends (prefixWord ++ tailWord_486815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486829 : List Nat := [1, 5, 2, 2, 1, 1, 2, 3, 4]
def baseStart_486829 : Nat := 118140960795 + 486829 * 2 ^ 59
def prefixEnd_486829 : Nat := 4983230072969 + 3 ^ 40 * 486829 * 2
def baseEnd_486829 : Nat := 111101010465680450221609

theorem tailTrace_486829 : CollatzResearch.WordTrace tailWord_486829 prefixEnd_486829 111101010465680450221609 := by
  unfold tailWord_486829
  simp only [CollatzResearch.WordTrace]
  refine ⟨17756112353309151618895541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11837408235539434412597027 17756112353309151618895541)
  ·
    refine ⟨1664635533122732964271457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17756112353309151618895541 1664635533122732964271457)
    ·
      refine ⟨1248476649842049723203593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1664635533122732964271457 1248476649842049723203593)
      ·
        refine ⟨936357487381537292402695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1248476649842049723203593 936357487381537292402695)
        ·
          refine ⟨1404536231072305938604043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936357487381537292402695 1404536231072305938604043)
          ·
            refine ⟨2106804346608458907906065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1404536231072305938604043 2106804346608458907906065)
            ·
              refine ⟨1580103259956344180929549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2106804346608458907906065 1580103259956344180929549)
              ·
                refine ⟨592538722483629067848581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1580103259956344180929549 592538722483629067848581)
                ·
                  refine ⟨111101010465680450221609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 592538722483629067848581 111101010465680450221609)
                  ·
                    rfl

theorem cell21_486829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_486829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_486829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_486829 prefixEnd_486829 := by exact prefixLift 486829
  have htrace : WordTrace (prefixWord ++ tailWord_486829) baseStart_486829 baseEnd_486829 := by
    simpa [prefixWord, tailWord_486829, baseEnd_486829] using wordTrace_append hprefix tailTrace_486829
  have hstable : (prefixWord ++ tailWord_486829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486829).length < 2 ^ (prefixWord ++ tailWord_486829).sum := by decide
  have hdescent : baseEnd_486829 < baseStart_486829 := by decide
  rcases family_descends (prefixWord ++ tailWord_486829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486840 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 7]
def baseStart_486840 : Nat := 118140960795 + 486840 * 2 ^ 59
def prefixEnd_486840 : Nat := 4983230072969 + 3 ^ 40 * 486840 * 2
def baseEnd_486840 : Nat := 111103520815546875538253

theorem tailTrace_486840 : CollatzResearch.WordTrace tailWord_486840 prefixEnd_486840 111103520815546875538253 := by
  unfold tailWord_486840
  simp only [CollatzResearch.WordTrace]
  refine ⟨8878256778134650248772987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11837675704179533665030649 8878256778134650248772987)
  ·
    refine ⟨13317385167201975373159481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8878256778134650248772987 13317385167201975373159481)
    ·
      refine ⟨9988038875401481529869611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13317385167201975373159481 9988038875401481529869611)
      ·
        refine ⟨14982058313102222294804417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9988038875401481529869611 14982058313102222294804417)
        ·
          refine ⟨11236543734826666721103313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14982058313102222294804417 11236543734826666721103313)
          ·
            refine ⟨8427407801120000040827485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11236543734826666721103313 8427407801120000040827485)
            ·
              refine ⟨3160277925420000015310307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8427407801120000040827485 3160277925420000015310307)
              ·
                refine ⟨4740416888130000022965461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3160277925420000015310307 4740416888130000022965461)
                ·
                  refine ⟨111103520815546875538253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4740416888130000022965461 111103520815546875538253)
                  ·
                    rfl

theorem cell21_486840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_486840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_486840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_486840 prefixEnd_486840 := by exact prefixLift 486840
  have htrace : WordTrace (prefixWord ++ tailWord_486840) baseStart_486840 baseEnd_486840 := by
    simpa [prefixWord, tailWord_486840, baseEnd_486840] using wordTrace_append hprefix tailTrace_486840
  have hstable : (prefixWord ++ tailWord_486840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486840).length < 2 ^ (prefixWord ++ tailWord_486840).sum := by decide
  have hdescent : baseEnd_486840 < baseStart_486840 := by decide
  rcases family_descends (prefixWord ++ tailWord_486840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486874 : List Nat := [3, 1, 1, 2, 3, 2, 2, 4, 3]
def baseStart_486874 : Nat := 118140960795 + 486874 * 2 ^ 59
def prefixEnd_486874 : Nat := 4983230072969 + 3 ^ 40 * 486874 * 2
def baseEnd_486874 : Nat := 111111280078770371971517

theorem tailTrace_486874 : CollatzResearch.WordTrace tailWord_486874 prefixEnd_486874 111111280078770371971517 := by
  unfold tailWord_486874
  simp only [CollatzResearch.WordTrace]
  refine ⟨4439438409536531076070919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11838502425430749536189117 4439438409536531076070919)
  ·
    refine ⟨6659157614304796614106379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4439438409536531076070919 6659157614304796614106379)
    ·
      refine ⟨9988736421457194921159569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6659157614304796614106379 9988736421457194921159569)
      ·
        refine ⟨7491552316092896190869677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9988736421457194921159569 7491552316092896190869677)
        ·
          refine ⟨2809332118534836071576129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7491552316092896190869677 2809332118534836071576129)
          ·
            refine ⟨2106999088901127053682097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2809332118534836071576129 2106999088901127053682097)
            ·
              refine ⟨1580249316675845290261573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2106999088901127053682097 1580249316675845290261573)
              ·
                refine ⟨296296746876720991924045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1580249316675845290261573 296296746876720991924045)
                ·
                  refine ⟨111111280078770371971517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 296296746876720991924045 111111280078770371971517)
                  ·
                    rfl

theorem cell21_486874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_486874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_486874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_486874 prefixEnd_486874 := by exact prefixLift 486874
  have htrace : WordTrace (prefixWord ++ tailWord_486874) baseStart_486874 baseEnd_486874 := by
    simpa [prefixWord, tailWord_486874, baseEnd_486874] using wordTrace_append hprefix tailTrace_486874
  have hstable : (prefixWord ++ tailWord_486874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486874).length < 2 ^ (prefixWord ++ tailWord_486874).sum := by decide
  have hdescent : baseEnd_486874 < baseStart_486874 := by decide
  rcases family_descends (prefixWord ++ tailWord_486874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486925 : List Nat := [1, 7, 1, 1, 3, 1, 1, 1, 5]
def baseStart_486925 : Nat := 118140960795 + 486925 * 2 ^ 59
def prefixEnd_486925 : Nat := 4983230072969 + 3 ^ 40 * 486925 * 2
def baseEnd_486925 : Nat := 111122918973605616621413

theorem tailTrace_486925 : CollatzResearch.WordTrace tailWord_486925 prefixEnd_486925 111122918973605616621413 := by
  unfold tailWord_486925
  simp only [CollatzResearch.WordTrace]
  refine ⟨17759613760961360014390229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11839742507307573342926819 17759613760961360014390229)
  ·
    refine ⟨416240947522531875337271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17759613760961360014390229 416240947522531875337271)
    ·
      refine ⟨624361421283797813005907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416240947522531875337271 624361421283797813005907)
      ·
        refine ⟨936542131925696719508861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624361421283797813005907 936542131925696719508861)
        ·
          refine ⟨351203299472136269815823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 936542131925696719508861 351203299472136269815823)
          ·
            refine ⟨526804949208204404723735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351203299472136269815823 526804949208204404723735)
            ·
              refine ⟨790207423812306607085603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526804949208204404723735 790207423812306607085603)
              ·
                refine ⟨1185311135718459910628405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790207423812306607085603 1185311135718459910628405)
                ·
                  refine ⟨111122918973605616621413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1185311135718459910628405 111122918973605616621413)
                  ·
                    rfl

theorem cell21_486925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_486925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_486925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_486925 prefixEnd_486925 := by exact prefixLift 486925
  have htrace : WordTrace (prefixWord ++ tailWord_486925) baseStart_486925 baseEnd_486925 := by
    simpa [prefixWord, tailWord_486925, baseEnd_486925] using wordTrace_append hprefix tailTrace_486925
  have hstable : (prefixWord ++ tailWord_486925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486925).length < 2 ^ (prefixWord ++ tailWord_486925).sum := by decide
  have hdescent : baseEnd_486925 < baseStart_486925 := by decide
  rcases family_descends (prefixWord ++ tailWord_486925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486933 : List Nat := [1, 3, 2, 1, 3, 2, 3, 1, 5]
def baseStart_486933 : Nat := 118140960795 + 486933 * 2 ^ 59
def prefixEnd_486933 : Nat := 4983230072969 + 3 ^ 40 * 486933 * 2
def baseEnd_486933 : Nat := 111124744682599380488063

theorem tailTrace_486933 : CollatzResearch.WordTrace tailWord_486933 prefixEnd_486933 111124744682599380488063 := by
  unfold tailWord_486933
  simp only [CollatzResearch.WordTrace]
  refine ⟨17759905544932377380681453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11839937029954918253787635 17759905544932377380681453)
  ·
    refine ⟨6659964579349641517755545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17759905544932377380681453 6659964579349641517755545)
    ·
      refine ⟨4994973434512231138316659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6659964579349641517755545 4994973434512231138316659)
      ·
        refine ⟨7492460151768346707474989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4994973434512231138316659 7492460151768346707474989)
        ·
          refine ⟨2809672556913130015303121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7492460151768346707474989 2809672556913130015303121)
          ·
            refine ⟨2107254417684847511477341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2809672556913130015303121 2107254417684847511477341)
            ·
              refine ⟨790220406631817816804003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2107254417684847511477341 790220406631817816804003)
              ·
                refine ⟨1185330609947726725206005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790220406631817816804003 1185330609947726725206005)
                ·
                  refine ⟨111124744682599380488063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1185330609947726725206005 111124744682599380488063)
                  ·
                    rfl

theorem cell21_486933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_486933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_486933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_486933 prefixEnd_486933 := by exact prefixLift 486933
  have htrace : WordTrace (prefixWord ++ tailWord_486933) baseStart_486933 baseEnd_486933 := by
    simpa [prefixWord, tailWord_486933, baseEnd_486933] using wordTrace_append hprefix tailTrace_486933
  have hstable : (prefixWord ++ tailWord_486933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486933).length < 2 ^ (prefixWord ++ tailWord_486933).sum := by decide
  have hdescent : baseEnd_486933 < baseStart_486933 := by decide
  rcases family_descends (prefixWord ++ tailWord_486933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_486992 : List Nat := [2, 1, 1, 1, 1, 3, 4, 3, 5]
def baseStart_486992 : Nat := 118140960795 + 486992 * 2 ^ 59
def prefixEnd_486992 : Nat := 4983230072969 + 3 ^ 40 * 486992 * 2
def baseEnd_486992 : Nat := 111138209286428389004609

theorem tailTrace_486992 : CollatzResearch.WordTrace tailWord_486992 prefixEnd_486992 111138209286428389004609 := by
  unfold tailWord_486992
  simp only [CollatzResearch.WordTrace]
  refine ⟨8881028725859315228539615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11841371634479086971386153 8881028725859315228539615)
  ·
    refine ⟨13321543088788972842809423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8881028725859315228539615 13321543088788972842809423)
    ·
      refine ⟨19982314633183459264214135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13321543088788972842809423 19982314633183459264214135)
      ·
        refine ⟨29973471949775188896321203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19982314633183459264214135 29973471949775188896321203)
        ·
          refine ⟨44960207924662783344481805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29973471949775188896321203 44960207924662783344481805)
          ·
            refine ⟨16860077971748543754180677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44960207924662783344481805 16860077971748543754180677)
            ·
              refine ⟨3161264619702851953908877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16860077971748543754180677 3161264619702851953908877)
              ·
                refine ⟨1185474232388569482715829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3161264619702851953908877 1185474232388569482715829)
                ·
                  refine ⟨111138209286428389004609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1185474232388569482715829 111138209286428389004609)
                  ·
                    rfl

theorem cell21_486992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_486992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_486992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_486992 prefixEnd_486992 := by exact prefixLift 486992
  have htrace : WordTrace (prefixWord ++ tailWord_486992) baseStart_486992 baseEnd_486992 := by
    simpa [prefixWord, tailWord_486992, baseEnd_486992] using wordTrace_append hprefix tailTrace_486992
  have hstable : (prefixWord ++ tailWord_486992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_486992).length < 2 ^ (prefixWord ++ tailWord_486992).sum := by decide
  have hdescent : baseEnd_486992 < baseStart_486992 := by decide
  rcases family_descends (prefixWord ++ tailWord_486992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487026 : List Nat := [3, 2, 1, 2, 3, 1, 1, 5, 3]
def baseStart_487026 : Nat := 118140960795 + 487026 * 2 ^ 59
def prefixEnd_487026 : Nat := 4983230072969 + 3 ^ 40 * 487026 * 2
def baseEnd_487026 : Nat := 111145968549651885437873

theorem tailTrace_487026 : CollatzResearch.WordTrace tailWord_487026 prefixEnd_487026 111145968549651885437873 := by
  unfold tailWord_487026
  simp only [CollatzResearch.WordTrace]
  refine ⟨4440824383398863565954233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11842198355730302842544621 4440824383398863565954233)
  ·
    refine ⟨3330618287549147674465675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4440824383398863565954233 3330618287549147674465675)
    ·
      refine ⟨4995927431323721511698513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3330618287549147674465675 4995927431323721511698513)
      ·
        refine ⟨3746945573492791133773885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4995927431323721511698513 3746945573492791133773885)
        ·
          refine ⟨1405104590059796675165207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3746945573492791133773885 1405104590059796675165207)
          ·
            refine ⟨2107656885089695012747811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405104590059796675165207 2107656885089695012747811)
            ·
              refine ⟨3161485327634542519121717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2107656885089695012747811 3161485327634542519121717)
              ·
                refine ⟨296389249465738361167661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3161485327634542519121717 296389249465738361167661)
                ·
                  refine ⟨111145968549651885437873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 296389249465738361167661 111145968549651885437873)
                  ·
                    rfl

theorem cell21_487026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_487026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_487026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_487026 prefixEnd_487026 := by exact prefixLift 487026
  have htrace : WordTrace (prefixWord ++ tailWord_487026) baseStart_487026 baseEnd_487026 := by
    simpa [prefixWord, tailWord_487026, baseEnd_487026] using wordTrace_append hprefix tailTrace_487026
  have hstable : (prefixWord ++ tailWord_487026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487026).length < 2 ^ (prefixWord ++ tailWord_487026).sum := by decide
  have hdescent : baseEnd_487026 < baseStart_487026 := by decide
  rcases family_descends (prefixWord ++ tailWord_487026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487071 : List Nat := [1, 1, 2, 7, 1, 1, 1, 7]
def baseStart_487071 : Nat := 118140960795 + 487071 * 2 ^ 59
def prefixEnd_487071 : Nat := 4983230072969 + 3 ^ 40 * 487071 * 2
def baseEnd_487071 : Nat := 37052079387580602395927

theorem tailTrace_487071 : CollatzResearch.WordTrace tailWord_487071 prefixEnd_487071 37052079387580602395927 := by
  unfold tailWord_487071
  simp only [CollatzResearch.WordTrace]
  refine ⟨17764938818432426949205067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11843292545621617966136711 17764938818432426949205067)
  ·
    refine ⟨26647408227648640423807601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17764938818432426949205067 26647408227648640423807601)
    ·
      refine ⟨19985556170736480317855701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26647408227648640423807601 19985556170736480317855701)
      ·
        refine ⟨468411472751636257449743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 19985556170736480317855701 468411472751636257449743)
        ·
          refine ⟨702617209127454386174615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468411472751636257449743 702617209127454386174615)
          ·
            refine ⟨1053925813691181579261923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702617209127454386174615 1053925813691181579261923)
            ·
              refine ⟨1580888720536772368892885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053925813691181579261923 1580888720536772368892885)
              ·
                refine ⟨37052079387580602395927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1580888720536772368892885 37052079387580602395927)
                ·
                  rfl

theorem cell21_487071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 7].length) (baseStart_487071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_487071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_487071 prefixEnd_487071 := by exact prefixLift 487071
  have htrace : WordTrace (prefixWord ++ tailWord_487071) baseStart_487071 baseEnd_487071 := by
    simpa [prefixWord, tailWord_487071, baseEnd_487071] using wordTrace_append hprefix tailTrace_487071
  have hstable : (prefixWord ++ tailWord_487071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487071).length < 2 ^ (prefixWord ++ tailWord_487071).sum := by decide
  have hdescent : baseEnd_487071 < baseStart_487071 := by decide
  rcases family_descends (prefixWord ++ tailWord_487071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487102 : List Nat := [4, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_487102 : Nat := 118140960795 + 487102 * 2 ^ 59
def prefixEnd_487102 : Nat := 4983230072969 + 3 ^ 40 * 487102 * 2
def baseEnd_487102 : Nat := 111163312785092642171051

theorem tailTrace_487102 : CollatzResearch.WordTrace tailWord_487102 prefixEnd_487102 111163312785092642171051 := by
  unfold tailWord_487102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2220758685165014905447945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11844046320880079495722373 2220758685165014905447945)
  ·
    refine ⟨1665569013873761179085959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2220758685165014905447945 1665569013873761179085959)
    ·
      refine ⟨2498353520810641768628939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1665569013873761179085959 2498353520810641768628939)
      ·
        refine ⟨3747530281215962652943409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2498353520810641768628939 3747530281215962652943409)
        ·
          refine ⟨2810647710911971989707557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3747530281215962652943409 2810647710911971989707557)
          ·
            refine ⟨526996445795994748070167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2810647710911971989707557 526996445795994748070167)
            ·
              refine ⟨790494668693992122105251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526996445795994748070167 790494668693992122105251)
              ·
                refine ⟨1185742003040988183157877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790494668693992122105251 1185742003040988183157877)
                ·
                  refine ⟨111163312785092642171051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1185742003040988183157877 111163312785092642171051)
                  ·
                    rfl

theorem cell21_487102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_487102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_487102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_487102 prefixEnd_487102 := by exact prefixLift 487102
  have htrace : WordTrace (prefixWord ++ tailWord_487102) baseStart_487102 baseEnd_487102 := by
    simpa [prefixWord, tailWord_487102, baseEnd_487102] using wordTrace_append hprefix tailTrace_487102
  have hstable : (prefixWord ++ tailWord_487102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487102).length < 2 ^ (prefixWord ++ tailWord_487102).sum := by decide
  have hdescent : baseEnd_487102 < baseStart_487102 := by decide
  rcases family_descends (prefixWord ++ tailWord_487102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487355 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 7]
def baseStart_487355 : Nat := 118140960795 + 487355 * 2 ^ 59
def prefixEnd_487355 : Nat := 4983230072969 + 3 ^ 40 * 487355 * 2
def baseEnd_487355 : Nat := 111221050832020424453867

theorem tailTrace_487355 : CollatzResearch.WordTrace tailWord_487355 prefixEnd_487355 111221050832020424453867 := by
  unfold tailWord_487355
  simp only [CollatzResearch.WordTrace]
  refine ⟨17775297149403543452543519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11850198099602362301695679 17775297149403543452543519)
  ·
    refine ⟨26662945724105315178815279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17775297149403543452543519 26662945724105315178815279)
    ·
      refine ⟨39994418586157972768222919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26662945724105315178815279 39994418586157972768222919)
      ·
        refine ⟨59991627879236959152334379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39994418586157972768222919 59991627879236959152334379)
        ·
          refine ⟨89987441818855438728501569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59991627879236959152334379 89987441818855438728501569)
          ·
            refine ⟨67490581364141579046376177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89987441818855438728501569 67490581364141579046376177)
            ·
              refine ⟨50617936023106184284782133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67490581364141579046376177 50617936023106184284782133)
              ·
                refine ⟨4745431502166204776698325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50617936023106184284782133 4745431502166204776698325)
                ·
                  refine ⟨111221050832020424453867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4745431502166204776698325 111221050832020424453867)
                  ·
                    rfl

theorem cell21_487355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 7].length) (baseStart_487355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_487355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_487355 prefixEnd_487355 := by exact prefixLift 487355
  have htrace : WordTrace (prefixWord ++ tailWord_487355) baseStart_487355 baseEnd_487355 := by
    simpa [prefixWord, tailWord_487355, baseEnd_487355] using wordTrace_append hprefix tailTrace_487355
  have hstable : (prefixWord ++ tailWord_487355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487355).length < 2 ^ (prefixWord ++ tailWord_487355).sum := by decide
  have hdescent : baseEnd_487355 < baseStart_487355 := by decide
  rcases family_descends (prefixWord ++ tailWord_487355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487378 : List Nat := [3, 2, 2, 3, 3, 1, 1, 2, 4]
def baseStart_487378 : Nat := 118140960795 + 487378 * 2 ^ 59
def prefixEnd_487378 : Nat := 4983230072969 + 3 ^ 40 * 487378 * 2
def baseEnd_487378 : Nat := 111226299745377495570487

theorem tailTrace_487378 : CollatzResearch.WordTrace tailWord_487378 prefixEnd_487378 111226299745377495570487 := by
  unfold tailWord_487378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4444034007080054595157697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11850757352213478920420525 4444034007080054595157697)
  ·
    refine ⟨3333025505310040946368273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4444034007080054595157697 3333025505310040946368273)
    ·
      refine ⟨2499769128982530709776205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3333025505310040946368273 2499769128982530709776205)
      ·
        refine ⟨937413423368449016166077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2499769128982530709776205 937413423368449016166077)
        ·
          refine ⟨351530033763168381062279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 937413423368449016166077 351530033763168381062279)
          ·
            refine ⟨527295050644752571593419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351530033763168381062279 527295050644752571593419)
            ·
              refine ⟨790942575967128857390129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527295050644752571593419 790942575967128857390129)
              ·
                refine ⟨593206931975346643042597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790942575967128857390129 593206931975346643042597)
                ·
                  refine ⟨111226299745377495570487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 593206931975346643042597 111226299745377495570487)
                  ·
                    rfl

theorem cell21_487378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_487378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_487378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_487378 prefixEnd_487378 := by exact prefixLift 487378
  have htrace : WordTrace (prefixWord ++ tailWord_487378) baseStart_487378 baseEnd_487378 := by
    simpa [prefixWord, tailWord_487378, baseEnd_487378] using wordTrace_append hprefix tailTrace_487378
  have hstable : (prefixWord ++ tailWord_487378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487378).length < 2 ^ (prefixWord ++ tailWord_487378).sum := by decide
  have hdescent : baseEnd_487378 < baseStart_487378 := by decide
  rcases family_descends (prefixWord ++ tailWord_487378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487417 : List Nat := [1, 2, 1, 3, 1, 5, 1, 7]
def baseStart_487417 : Nat := 118140960795 + 487417 * 2 ^ 59
def prefixEnd_487417 : Nat := 4983230072969 + 3 ^ 40 * 487417 * 2
def baseEnd_487417 : Nat := 37078400025574031473469

theorem tailTrace_487417 : CollatzResearch.WordTrace tailWord_487417 prefixEnd_487417 37078400025574031473469 := by
  unfold tailWord_487417
  simp only [CollatzResearch.WordTrace]
  refine ⟨17777558475178928041300505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11851705650119285360867003 17777558475178928041300505)
  ·
    refine ⟨13333168856384196030975379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17777558475178928041300505 13333168856384196030975379)
    ·
      refine ⟨19999753284576294046463069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13333168856384196030975379 19999753284576294046463069)
      ·
        refine ⟨7499907481716110267423651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19999753284576294046463069 7499907481716110267423651)
        ·
          refine ⟨11249861222574165401135477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7499907481716110267423651 11249861222574165401135477)
          ·
            refine ⟨1054674489616328006356451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11249861222574165401135477 1054674489616328006356451)
            ·
              refine ⟨1582011734424492009534677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054674489616328006356451 1582011734424492009534677)
              ·
                refine ⟨37078400025574031473469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1582011734424492009534677 37078400025574031473469)
                ·
                  rfl

theorem cell21_487417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 7].length) (baseStart_487417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_487417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_487417 prefixEnd_487417 := by exact prefixLift 487417
  have htrace : WordTrace (prefixWord ++ tailWord_487417) baseStart_487417 baseEnd_487417 := by
    simpa [prefixWord, tailWord_487417, baseEnd_487417] using wordTrace_append hprefix tailTrace_487417
  have hstable : (prefixWord ++ tailWord_487417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487417).length < 2 ^ (prefixWord ++ tailWord_487417).sum := by decide
  have hdescent : baseEnd_487417 < baseStart_487417 := by decide
  rcases family_descends (prefixWord ++ tailWord_487417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487434 : List Nat := [3, 1, 2, 2, 4, 2, 7]
def baseStart_487434 : Nat := 118140960795 + 487434 * 2 ^ 59
def prefixEnd_487434 : Nat := 4983230072969 + 3 ^ 40 * 487434 * 2
def baseEnd_487434 : Nat := 12359897745370426959671

theorem tailTrace_487434 : CollatzResearch.WordTrace tailWord_487434 prefixEnd_487434 12359897745370426959671 := by
  unfold tailWord_487434
  simp only [CollatzResearch.WordTrace]
  refine ⟨4444544629029334986167339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11852119010744893296446237 4444544629029334986167339)
  ·
    refine ⟨6666816943544002479251009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4444544629029334986167339 6666816943544002479251009)
    ·
      refine ⟨5000112707658001859438257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6666816943544002479251009 5000112707658001859438257)
      ·
        refine ⟨3750084530743501394578693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5000112707658001859438257 3750084530743501394578693)
        ·
          refine ⟨703140849514406511483505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3750084530743501394578693 703140849514406511483505)
          ·
            refine ⟨527355637135804883612629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 703140849514406511483505 527355637135804883612629)
            ·
              refine ⟨12359897745370426959671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 527355637135804883612629 12359897745370426959671)
              ·
                rfl

theorem cell21_487434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 7].length) (baseStart_487434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_487434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_487434 prefixEnd_487434 := by exact prefixLift 487434
  have htrace : WordTrace (prefixWord ++ tailWord_487434) baseStart_487434 baseEnd_487434 := by
    simpa [prefixWord, tailWord_487434, baseEnd_487434] using wordTrace_append hprefix tailTrace_487434
  have hstable : (prefixWord ++ tailWord_487434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487434).length < 2 ^ (prefixWord ++ tailWord_487434).sum := by decide
  have hdescent : baseEnd_487434 < baseStart_487434 := by decide
  rcases family_descends (prefixWord ++ tailWord_487434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487555 : List Nat := [1, 1, 1, 3, 3, 3, 3, 2, 4]
def baseStart_487555 : Nat := 118140960795 + 487555 * 2 ^ 59
def prefixEnd_487555 : Nat := 4983230072969 + 3 ^ 40 * 487555 * 2
def baseEnd_487555 : Nat := 111266693556864521120125

theorem tailTrace_487555 : CollatzResearch.WordTrace tailWord_487555 prefixEnd_487555 111266693556864521120125 := by
  unfold tailWord_487555
  simp only [CollatzResearch.WordTrace]
  refine ⟨17782591748678977609824119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11855061165785985073216079 17782591748678977609824119)
  ·
    refine ⟨26673887623018466414736179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17782591748678977609824119 26673887623018466414736179)
    ·
      refine ⟨40010831434527699622104269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26673887623018466414736179 40010831434527699622104269)
      ·
        refine ⟨15004061787947887358289101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40010831434527699622104269 15004061787947887358289101)
        ·
          refine ⟨5626523170480457759358413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15004061787947887358289101 5626523170480457759358413)
          ·
            refine ⟨2109946188930171659759405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5626523170480457759358413 2109946188930171659759405)
            ·
              refine ⟨791229820848814372409777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2109946188930171659759405 791229820848814372409777)
              ·
                refine ⟨593422365636610779307333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791229820848814372409777 593422365636610779307333)
                ·
                  refine ⟨111266693556864521120125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 593422365636610779307333 111266693556864521120125)
                  ·
                    rfl

theorem cell21_487555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 4].length) (baseStart_487555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_487555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_487555 prefixEnd_487555 := by exact prefixLift 487555
  have htrace : WordTrace (prefixWord ++ tailWord_487555) baseStart_487555 baseEnd_487555 := by
    simpa [prefixWord, tailWord_487555, baseEnd_487555] using wordTrace_append hprefix tailTrace_487555
  have hstable : (prefixWord ++ tailWord_487555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487555).length < 2 ^ (prefixWord ++ tailWord_487555).sum := by decide
  have hdescent : baseEnd_487555 < baseStart_487555 := by decide
  rcases family_descends (prefixWord ++ tailWord_487555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487586 : List Nat := [3, 3, 1, 3, 1, 2, 1, 7]
def baseStart_487586 : Nat := 118140960795 + 487586 * 2 ^ 59
def prefixEnd_487586 : Nat := 4983230072969 + 3 ^ 40 * 487586 * 2
def baseEnd_487586 : Nat := 37091256059738452034465

theorem tailTrace_487586 : CollatzResearch.WordTrace tailWord_487586 prefixEnd_487586 37091256059738452034465 := by
  unfold tailWord_487586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4445930602891667476050653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11855814941044446602801741 4445930602891667476050653)
  ·
    refine ⟨1667223976084375303518995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4445930602891667476050653 1667223976084375303518995)
    ·
      refine ⟨2500835964126562955278493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1667223976084375303518995 2500835964126562955278493)
      ·
        refine ⟨937813486547461108229435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2500835964126562955278493 937813486547461108229435)
        ·
          refine ⟨1406720229821191662344153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 937813486547461108229435 1406720229821191662344153)
          ·
            refine ⟨1055040172365893746758115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1406720229821191662344153 1055040172365893746758115)
            ·
              refine ⟨1582560258548840620137173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055040172365893746758115 1582560258548840620137173)
              ·
                refine ⟨37091256059738452034465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1582560258548840620137173 37091256059738452034465)
                ·
                  rfl

theorem cell21_487586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_487586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_487586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_487586 prefixEnd_487586 := by exact prefixLift 487586
  have htrace : WordTrace (prefixWord ++ tailWord_487586) baseStart_487586 baseEnd_487586 := by
    simpa [prefixWord, tailWord_487586, baseEnd_487586] using wordTrace_append hprefix tailTrace_487586
  have hstable : (prefixWord ++ tailWord_487586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487586).length < 2 ^ (prefixWord ++ tailWord_487586).sum := by decide
  have hdescent : baseEnd_487586 < baseStart_487586 := by decide
  rcases family_descends (prefixWord ++ tailWord_487586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487797 : List Nat := [1, 3, 4, 1, 2, 1, 1, 8]
def baseStart_487797 : Nat := 118140960795 + 487797 * 2 ^ 59
def prefixEnd_487797 : Nat := 4983230072969 + 3 ^ 40 * 487797 * 2
def baseEnd_487797 : Nat := 37107307084641959362099

theorem tailTrace_487797 : CollatzResearch.WordTrace tailWord_487797 prefixEnd_487797 37107307084641959362099 := by
  unfold tailWord_487797
  simp only [CollatzResearch.WordTrace]
  refine ⟨17791418213802252940133645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11860945475868168626755763 17791418213802252940133645)
  ·
    refine ⟨6671781830175844852550117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17791418213802252940133645 6671781830175844852550117)
    ·
      refine ⟨1250959093157970909853147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6671781830175844852550117 1250959093157970909853147)
      ·
        refine ⟨1876438639736956364779721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1250959093157970909853147 1876438639736956364779721)
        ·
          refine ⟨1407328979802717273584791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1876438639736956364779721 1407328979802717273584791)
          ·
            refine ⟨2110993469704075910377187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407328979802717273584791 2110993469704075910377187)
            ·
              refine ⟨3166490204556113865565781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110993469704075910377187 3166490204556113865565781)
              ·
                refine ⟨37107307084641959362099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3166490204556113865565781 37107307084641959362099)
                ·
                  rfl

theorem cell21_487797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 8].length) (baseStart_487797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_487797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_487797 prefixEnd_487797 := by exact prefixLift 487797
  have htrace : WordTrace (prefixWord ++ tailWord_487797) baseStart_487797 baseEnd_487797 := by
    simpa [prefixWord, tailWord_487797, baseEnd_487797] using wordTrace_append hprefix tailTrace_487797
  have hstable : (prefixWord ++ tailWord_487797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487797).length < 2 ^ (prefixWord ++ tailWord_487797).sum := by decide
  have hdescent : baseEnd_487797 < baseStart_487797 := by decide
  rcases family_descends (prefixWord ++ tailWord_487797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487890 : List Nat := [3, 2, 2, 4, 1, 1, 8]
def baseStart_487890 : Nat := 118140960795 + 487890 * 2 ^ 59
def prefixEnd_487890 : Nat := 4983230072969 + 3 ^ 40 * 487890 * 2
def baseEnd_487890 : Nat := 12371460568997598115123

theorem tailTrace_487890 : CollatzResearch.WordTrace tailWord_487890 prefixEnd_487890 12371460568997598115123 := by
  unfold tailWord_487890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4448702550616332455817281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11863206801643553215512749 4448702550616332455817281)
  ·
    refine ⟨3336526912962249341862961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4448702550616332455817281 3336526912962249341862961)
    ·
      refine ⟨2502395184721687006397221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3336526912962249341862961 2502395184721687006397221)
      ·
        refine ⟨469199097135316313699479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2502395184721687006397221 469199097135316313699479)
        ·
          refine ⟨703798645702974470549219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469199097135316313699479 703798645702974470549219)
          ·
            refine ⟨1055697968554461705823829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703798645702974470549219 1055697968554461705823829)
            ·
              refine ⟨12371460568997598115123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1055697968554461705823829 12371460568997598115123)
              ·
                rfl

theorem cell21_487890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 8].length) (baseStart_487890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_487890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_487890 prefixEnd_487890 := by exact prefixLift 487890
  have htrace : WordTrace (prefixWord ++ tailWord_487890) baseStart_487890 baseEnd_487890 := by
    simpa [prefixWord, tailWord_487890, baseEnd_487890] using wordTrace_append hprefix tailTrace_487890
  have hstable : (prefixWord ++ tailWord_487890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487890).length < 2 ^ (prefixWord ++ tailWord_487890).sum := by decide
  have hdescent : baseEnd_487890 < baseStart_487890 := by decide
  rcases family_descends (prefixWord ++ tailWord_487890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_487904 : List Nat := [2, 1, 1, 3, 1, 1, 3, 6, 3]
def baseStart_487904 : Nat := 118140960795 + 487904 * 2 ^ 59
def prefixEnd_487904 : Nat := 4983230072969 + 3 ^ 40 * 487904 * 2
def baseEnd_487904 : Nat := 111346340111717469802745

theorem tailTrace_487904 : CollatzResearch.WordTrace tailWord_487904 prefixEnd_487904 111346340111717469802745 := by
  unfold tailWord_487904
  simp only [CollatzResearch.WordTrace]
  refine ⟨8897660412207305107139383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11863547216276406809519177 8897660412207305107139383)
  ·
    refine ⟨13346490618310957660709075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8897660412207305107139383 13346490618310957660709075)
    ·
      refine ⟨20019735927466436491063613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13346490618310957660709075 20019735927466436491063613)
      ·
        refine ⟨7507400972799913684148855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20019735927466436491063613 7507400972799913684148855)
        ·
          refine ⟨11261101459199870526223283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7507400972799913684148855 11261101459199870526223283)
          ·
            refine ⟨16891652188799805789334925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11261101459199870526223283 16891652188799805789334925)
            ·
              refine ⟨6334369570799927171000597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16891652188799805789334925 6334369570799927171000597)
              ·
                refine ⟨296923573631246586140653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6334369570799927171000597 296923573631246586140653)
                ·
                  refine ⟨111346340111717469802745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 296923573631246586140653 111346340111717469802745)
                  ·
                    rfl

theorem cell21_487904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 3].length) (baseStart_487904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_487904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_487904 prefixEnd_487904 := by exact prefixLift 487904
  have htrace : WordTrace (prefixWord ++ tailWord_487904) baseStart_487904 baseEnd_487904 := by
    simpa [prefixWord, tailWord_487904, baseEnd_487904] using wordTrace_append hprefix tailTrace_487904
  have hstable : (prefixWord ++ tailWord_487904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_487904).length < 2 ^ (prefixWord ++ tailWord_487904).sum := by decide
  have hdescent : baseEnd_487904 < baseStart_487904 := by decide
  rcases family_descends (prefixWord ++ tailWord_487904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488087 : List Nat := [1, 1, 3, 3, 2, 1, 5, 1, 4]
def baseStart_488087 : Nat := 118140960795 + 488087 * 2 ^ 59
def prefixEnd_488087 : Nat := 4983230072969 + 3 ^ 40 * 488087 * 2
def baseEnd_488087 : Nat := 111388103204949818252371

theorem tailTrace_488087 : CollatzResearch.WordTrace tailWord_488087 prefixEnd_488087 111388103204949818252371 := by
  unfold tailWord_488087
  simp only [CollatzResearch.WordTrace]
  refine ⟨17801995382751632468190515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11867996921834421645460343 17801995382751632468190515)
  ·
    refine ⟨26702993074127448702285773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17801995382751632468190515 26702993074127448702285773)
    ·
      refine ⟨10013622402797793263357165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26702993074127448702285773 10013622402797793263357165)
      ·
        refine ⟨3755108401049172473758937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10013622402797793263357165 3755108401049172473758937)
        ·
          refine ⟨2816331300786879355319203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3755108401049172473758937 2816331300786879355319203)
          ·
            refine ⟨4224496951180319032978805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816331300786879355319203 4224496951180319032978805)
            ·
              refine ⟨396046589173154909341763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4224496951180319032978805 396046589173154909341763)
              ·
                refine ⟨594069883759732364012645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396046589173154909341763 594069883759732364012645)
                ·
                  refine ⟨111388103204949818252371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 594069883759732364012645 111388103204949818252371)
                  ·
                    rfl

theorem cell21_488087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 4].length) (baseStart_488087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_488087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_488087 prefixEnd_488087 := by exact prefixLift 488087
  have htrace : WordTrace (prefixWord ++ tailWord_488087) baseStart_488087 baseEnd_488087 := by
    simpa [prefixWord, tailWord_488087, baseEnd_488087] using wordTrace_append hprefix tailTrace_488087
  have hstable : (prefixWord ++ tailWord_488087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488087).length < 2 ^ (prefixWord ++ tailWord_488087).sum := by decide
  have hdescent : baseEnd_488087 < baseStart_488087 := by decide
  rcases family_descends (prefixWord ++ tailWord_488087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488132 : List Nat := [2, 3, 3, 1, 1, 2, 3, 1, 5]
def baseStart_488132 : Nat := 118140960795 + 488132 * 2 ^ 59
def prefixEnd_488132 : Nat := 4983230072969 + 3 ^ 40 * 488132 * 2
def baseEnd_488132 : Nat := 111398372818039740002279

theorem tailTrace_488132 : CollatzResearch.WordTrace tailWord_488132 prefixEnd_488132 111398372818039740002279 := by
  unfold tailWord_488132
  simp only [CollatzResearch.WordTrace]
  refine ⟨8901818333794302576789325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11869091111725736769052433 8901818333794302576789325)
  ·
    refine ⟨3338181875172863466295997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8901818333794302576789325 3338181875172863466295997)
    ·
      refine ⟨1251818203189823799860999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3338181875172863466295997 1251818203189823799860999)
      ·
        refine ⟨1877727304784735699791499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1251818203189823799860999 1877727304784735699791499)
        ·
          refine ⟨2816590957177103549687249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877727304784735699791499 2816590957177103549687249)
          ·
            refine ⟨2112443217882827662265437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2816590957177103549687249 2112443217882827662265437)
            ·
              refine ⟨792166206706060373349539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2112443217882827662265437 792166206706060373349539)
              ·
                refine ⟨1188249310059090560024309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792166206706060373349539 1188249310059090560024309)
                ·
                  refine ⟨111398372818039740002279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1188249310059090560024309 111398372818039740002279)
                  ·
                    rfl

theorem cell21_488132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_488132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_488132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_488132 prefixEnd_488132 := by exact prefixLift 488132
  have htrace : WordTrace (prefixWord ++ tailWord_488132) baseStart_488132 baseEnd_488132 := by
    simpa [prefixWord, tailWord_488132, baseEnd_488132] using wordTrace_append hprefix tailTrace_488132
  have hstable : (prefixWord ++ tailWord_488132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488132).length < 2 ^ (prefixWord ++ tailWord_488132).sum := by decide
  have hdescent : baseEnd_488132 < baseStart_488132 := by decide
  rcases family_descends (prefixWord ++ tailWord_488132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488194 : List Nat := [3, 4, 1, 1, 1, 4, 1, 6]
def baseStart_488194 : Nat := 118140960795 + 488194 * 2 ^ 59
def prefixEnd_488194 : Nat := 4983230072969 + 3 ^ 40 * 488194 * 2
def baseEnd_488194 : Nat := 37137507354247136656273

theorem tailTrace_488194 : CollatzResearch.WordTrace tailWord_488194 prefixEnd_488194 37137507354247136656273 := by
  unfold tailWord_488194
  simp only [CollatzResearch.WordTrace]
  refine ⟨4451474498340997435583909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11870598662242659828223757 4451474498340997435583909)
  ·
    refine ⟨834651468438937019171983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4451474498340997435583909 834651468438937019171983)
    ·
      refine ⟨1251977202658405528757975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 834651468438937019171983 1251977202658405528757975)
      ·
        refine ⟨1877965803987608293136963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1251977202658405528757975 1877965803987608293136963)
        ·
          refine ⟨2816948705981412439705445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877965803987608293136963 2816948705981412439705445)
          ·
            refine ⟨528177882371514832444771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2816948705981412439705445 528177882371514832444771)
            ·
              refine ⟨792266823557272248667157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528177882371514832444771 792266823557272248667157)
              ·
                refine ⟨37137507354247136656273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 792266823557272248667157 37137507354247136656273)
                ·
                  rfl

theorem cell21_488194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_488194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_488194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_488194 prefixEnd_488194 := by exact prefixLift 488194
  have htrace : WordTrace (prefixWord ++ tailWord_488194) baseStart_488194 baseEnd_488194 := by
    simpa [prefixWord, tailWord_488194, baseEnd_488194] using wordTrace_append hprefix tailTrace_488194
  have hstable : (prefixWord ++ tailWord_488194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488194).length < 2 ^ (prefixWord ++ tailWord_488194).sum := by decide
  have hdescent : baseEnd_488194 < baseStart_488194 := by decide
  rcases family_descends (prefixWord ++ tailWord_488194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488281 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 6]
def baseStart_488281 : Nat := 118140960795 + 488281 * 2 ^ 59
def prefixEnd_488281 : Nat := 4983230072969 + 3 ^ 40 * 488281 * 2
def baseEnd_488281 : Nat := 111432376648048592018641

theorem tailTrace_488281 : CollatzResearch.WordTrace tailWord_488281 prefixEnd_488281 111432376648048592018641 := by
  unfold tailWord_488281
  simp only [CollatzResearch.WordTrace]
  refine ⟨17809071144048803600752697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11872714096032535733835131 17809071144048803600752697)
  ·
    refine ⟨13356803358036602700564523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17809071144048803600752697 13356803358036602700564523)
    ·
      refine ⟨20035205037054904050846785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13356803358036602700564523 20035205037054904050846785)
      ·
        refine ⟨15026403777791178038135089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20035205037054904050846785 15026403777791178038135089)
        ·
          refine ⟨11269802833343383528601317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15026403777791178038135089 11269802833343383528601317)
          ·
            refine ⟨2113088031251884411612747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11269802833343383528601317 2113088031251884411612747)
            ·
              refine ⟨3169632046877826617419121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113088031251884411612747 3169632046877826617419121)
              ·
                refine ⟨2377224035158369963064341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3169632046877826617419121 2377224035158369963064341)
                ·
                  refine ⟨111432376648048592018641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2377224035158369963064341 111432376648048592018641)
                  ·
                    rfl

theorem cell21_488281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_488281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_488281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_488281 prefixEnd_488281 := by exact prefixLift 488281
  have htrace : WordTrace (prefixWord ++ tailWord_488281) baseStart_488281 baseEnd_488281 := by
    simpa [prefixWord, tailWord_488281, baseEnd_488281] using wordTrace_append hprefix tailTrace_488281
  have hstable : (prefixWord ++ tailWord_488281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488281).length < 2 ^ (prefixWord ++ tailWord_488281).sum := by decide
  have hdescent : baseEnd_488281 < baseStart_488281 := by decide
  rcases family_descends (prefixWord ++ tailWord_488281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488371 : List Nat := [1, 1, 1, 2, 3, 1, 2, 10]
def baseStart_488371 : Nat := 118140960795 + 488371 * 2 ^ 59
def prefixEnd_488371 : Nat := 4983230072969 + 3 ^ 40 * 488371 * 2
def baseEnd_488371 : Nat := 37150971958076145172819

theorem tailTrace_488371 : CollatzResearch.WordTrace tailWord_488371 prefixEnd_488371 37150971958076145172819 := by
  unfold tailWord_488371
  simp only [CollatzResearch.WordTrace]
  refine ⟨17812353713722748971528967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11874902475815165981019311 17812353713722748971528967)
  ·
    refine ⟨26718530570584123457293451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17812353713722748971528967 26718530570584123457293451)
    ·
      refine ⟨40077795855876185185940177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26718530570584123457293451 40077795855876185185940177)
      ·
        refine ⟨30058346891907138889455133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40077795855876185185940177 30058346891907138889455133)
        ·
          refine ⟨11271880084465177083545675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30058346891907138889455133 11271880084465177083545675)
          ·
            refine ⟨16907820126697765625318513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11271880084465177083545675 16907820126697765625318513)
            ·
              refine ⟨12680865095023324218988885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16907820126697765625318513 12680865095023324218988885)
              ·
                refine ⟨37150971958076145172819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12680865095023324218988885 37150971958076145172819)
                ·
                  rfl

theorem cell21_488371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 10].length) (baseStart_488371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_488371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_488371 prefixEnd_488371 := by exact prefixLift 488371
  have htrace : WordTrace (prefixWord ++ tailWord_488371) baseStart_488371 baseEnd_488371 := by
    simpa [prefixWord, tailWord_488371, baseEnd_488371] using wordTrace_append hprefix tailTrace_488371
  have hstable : (prefixWord ++ tailWord_488371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488371).length < 2 ^ (prefixWord ++ tailWord_488371).sum := by decide
  have hdescent : baseEnd_488371 < baseStart_488371 := by decide
  rcases family_descends (prefixWord ++ tailWord_488371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488419 : List Nat := [1, 1, 1, 6, 1, 1, 4, 1, 5]
def baseStart_488419 : Nat := 118140960795 + 488419 * 2 ^ 59
def prefixEnd_488419 : Nat := 4983230072969 + 3 ^ 40 * 488419 * 2
def baseEnd_488419 : Nat := 111463870128191018718359

theorem tailTrace_488419 : CollatzResearch.WordTrace tailWord_488419 prefixEnd_488419 111463870128191018718359 := by
  unfold tailWord_488419
  simp only [CollatzResearch.WordTrace]
  refine ⟨17814104417548853169276311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11876069611699235446184207 17814104417548853169276311)
  ·
    refine ⟨26721156626323279753914467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17814104417548853169276311 26721156626323279753914467)
    ·
      refine ⟨40081734939484919630871701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26721156626323279753914467 40081734939484919630871701)
      ·
        refine ⟨1878831325288355607697111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40081734939484919630871701 1878831325288355607697111)
        ·
          refine ⟨2818246987932533411545667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1878831325288355607697111 2818246987932533411545667)
          ·
            refine ⟨4227370481898800117318501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2818246987932533411545667 4227370481898800117318501)
            ·
              refine ⟨792631965356025021997219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4227370481898800117318501 792631965356025021997219)
              ·
                refine ⟨1188947948034037532995829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792631965356025021997219 1188947948034037532995829)
                ·
                  refine ⟨111463870128191018718359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1188947948034037532995829 111463870128191018718359)
                  ·
                    rfl

theorem cell21_488419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 5].length) (baseStart_488419 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_488419 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_488419 prefixEnd_488419 := by exact prefixLift 488419
  have htrace : WordTrace (prefixWord ++ tailWord_488419) baseStart_488419 baseEnd_488419 := by
    simpa [prefixWord, tailWord_488419, baseEnd_488419] using wordTrace_append hprefix tailTrace_488419
  have hstable : (prefixWord ++ tailWord_488419).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488419).length < 2 ^ (prefixWord ++ tailWord_488419).sum := by decide
  have hdescent : baseEnd_488419 < baseStart_488419 := by decide
  rcases family_descends (prefixWord ++ tailWord_488419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488484 : List Nat := [2, 3, 1, 4, 1, 3, 2, 1, 4]
def baseStart_488484 : Nat := 118140960795 + 488484 * 2 ^ 59
def prefixEnd_488484 : Nat := 4983230072969 + 3 ^ 40 * 488484 * 2
def baseEnd_488484 : Nat := 111478704013765350134893

theorem tailTrace_488484 : CollatzResearch.WordTrace tailWord_488484 prefixEnd_488484 111478704013765350134893 := by
  unfold tailWord_488484
  simp only [CollatzResearch.WordTrace]
  refine ⟨8908237581156684635196253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11877650108208912846928337 8908237581156684635196253)
  ·
    refine ⟨3340589092933756738198595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8908237581156684635196253 3340589092933756738198595)
    ·
      refine ⟨5010883639400635107297893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3340589092933756738198595 5010883639400635107297893)
      ·
        refine ⟨939540682387619082618355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5010883639400635107297893 939540682387619082618355)
        ·
          refine ⟨1409311023581428623927533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939540682387619082618355 1409311023581428623927533)
          ·
            refine ⟨528491633843035733972825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1409311023581428623927533 528491633843035733972825)
            ·
              refine ⟨396368725382276800479619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528491633843035733972825 396368725382276800479619)
              ·
                refine ⟨594553088073415200719429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396368725382276800479619 594553088073415200719429)
                ·
                  refine ⟨111478704013765350134893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 594553088073415200719429 111478704013765350134893)
                  ·
                    rfl

theorem cell21_488484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_488484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_488484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_488484 prefixEnd_488484 := by exact prefixLift 488484
  have htrace : WordTrace (prefixWord ++ tailWord_488484) baseStart_488484 baseEnd_488484 := by
    simpa [prefixWord, tailWord_488484, baseEnd_488484] using wordTrace_append hprefix tailTrace_488484
  have hstable : (prefixWord ++ tailWord_488484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488484).length < 2 ^ (prefixWord ++ tailWord_488484).sum := by decide
  have hdescent : baseEnd_488484 < baseStart_488484 := by decide
  rcases family_descends (prefixWord ++ tailWord_488484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488526 : List Nat := [4, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_488526 : Nat := 118140960795 + 488526 * 2 ^ 59
def prefixEnd_488526 : Nat := 4983230072969 + 3 ^ 40 * 488526 * 2
def baseEnd_488526 : Nat := 111488288985982610434807

theorem tailTrace_488526 : CollatzResearch.WordTrace tailWord_488526 prefixEnd_488526 111488288985982610434807 := by
  unfold tailWord_488526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2227250878520151305427679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11878671352107473628947621 2227250878520151305427679)
  ·
    refine ⟨3340876317780226958141519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2227250878520151305427679 3340876317780226958141519)
    ·
      refine ⟨5011314476670340437212279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3340876317780226958141519 5011314476670340437212279)
      ·
        refine ⟨7516971715005510655818419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5011314476670340437212279 7516971715005510655818419)
        ·
          refine ⟨11275457572508265983727629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7516971715005510655818419 11275457572508265983727629)
          ·
            refine ⟨4228296589690599743897861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11275457572508265983727629 4228296589690599743897861)
            ·
              refine ⟨792805610566987451980849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4228296589690599743897861 792805610566987451980849)
              ·
                refine ⟨594604207925240588985637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792805610566987451980849 594604207925240588985637)
                ·
                  refine ⟨111488288985982610434807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 594604207925240588985637 111488288985982610434807)
                  ·
                    rfl

theorem cell21_488526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_488526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_488526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_488526 prefixEnd_488526 := by exact prefixLift 488526
  have htrace : WordTrace (prefixWord ++ tailWord_488526) baseStart_488526 baseEnd_488526 := by
    simpa [prefixWord, tailWord_488526, baseEnd_488526] using wordTrace_append hprefix tailTrace_488526
  have hstable : (prefixWord ++ tailWord_488526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488526).length < 2 ^ (prefixWord ++ tailWord_488526).sum := by decide
  have hdescent : baseEnd_488526 < baseStart_488526 := by decide
  rcases family_descends (prefixWord ++ tailWord_488526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488557 : List Nat := [1, 5, 1, 1, 2, 3, 3, 5]
def baseStart_488557 : Nat := 118140960795 + 488557 * 2 ^ 59
def prefixEnd_488557 : Nat := 4983230072969 + 3 ^ 40 * 488557 * 2
def baseEnd_488557 : Nat := 37165121202777815139359

theorem tailTrace_488557 : CollatzResearch.WordTrace tailWord_488557 prefixEnd_488557 37165121202777815139359 := by
  unfold tailWord_488557
  simp only [CollatzResearch.WordTrace]
  refine ⟨17819137691048902737799925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11879425127365935158533283 17819137691048902737799925)
  ·
    refine ⟨1670544158535834631668743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17819137691048902737799925 1670544158535834631668743)
    ·
      refine ⟨2505816237803751947503115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1670544158535834631668743 2505816237803751947503115)
      ·
        refine ⟨3758724356705627921254673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2505816237803751947503115 3758724356705627921254673)
        ·
          refine ⟨2819043267529220940941005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3758724356705627921254673 2819043267529220940941005)
          ·
            refine ⟨1057141225323457852852877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2819043267529220940941005 1057141225323457852852877)
            ·
              refine ⟨396427959496296694819829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1057141225323457852852877 396427959496296694819829)
              ·
                refine ⟨37165121202777815139359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 396427959496296694819829 37165121202777815139359)
                ·
                  rfl

theorem cell21_488557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 5].length) (baseStart_488557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_488557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_488557 prefixEnd_488557 := by exact prefixLift 488557
  have htrace : WordTrace (prefixWord ++ tailWord_488557) baseStart_488557 baseEnd_488557 := by
    simpa [prefixWord, tailWord_488557, baseEnd_488557] using wordTrace_append hprefix tailTrace_488557
  have hstable : (prefixWord ++ tailWord_488557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488557).length < 2 ^ (prefixWord ++ tailWord_488557).sum := by decide
  have hdescent : baseEnd_488557 < baseStart_488557 := by decide
  rcases family_descends (prefixWord ++ tailWord_488557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488585 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 6]
def baseStart_488585 : Nat := 118140960795 + 488585 * 2 ^ 59
def prefixEnd_488585 : Nat := 4983230072969 + 3 ^ 40 * 488585 * 2
def baseEnd_488585 : Nat := 111501753589811618951353

theorem tailTrace_488585 : CollatzResearch.WordTrace tailWord_488585 prefixEnd_488585 111501753589811618951353 := by
  unfold tailWord_488585
  simp only [CollatzResearch.WordTrace]
  refine ⟨17820158934947463519819209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11880105956631642346546139 17820158934947463519819209)
  ·
    refine ⟨13365119201210597639864407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17820158934947463519819209 13365119201210597639864407)
    ·
      refine ⟨20047678801815896459796611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13365119201210597639864407 20047678801815896459796611)
      ·
        refine ⟨30071518202723844689694917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20047678801815896459796611 30071518202723844689694917)
        ·
          refine ⟨5638409663010720879317797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30071518202723844689694917 5638409663010720879317797)
          ·
            refine ⟨1057201811814510164872087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5638409663010720879317797 1057201811814510164872087)
            ·
              refine ⟨1585802717721765247308131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1057201811814510164872087 1585802717721765247308131)
              ·
                refine ⟨2378704076582647870962197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1585802717721765247308131 2378704076582647870962197)
                ·
                  refine ⟨111501753589811618951353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2378704076582647870962197 111501753589811618951353)
                  ·
                    rfl

theorem cell21_488585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_488585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_488585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_488585 prefixEnd_488585 := by exact prefixLift 488585
  have htrace : WordTrace (prefixWord ++ tailWord_488585) baseStart_488585 baseEnd_488585 := by
    simpa [prefixWord, tailWord_488585, baseEnd_488585] using wordTrace_append hprefix tailTrace_488585
  have hstable : (prefixWord ++ tailWord_488585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488585).length < 2 ^ (prefixWord ++ tailWord_488585).sum := by decide
  have hdescent : baseEnd_488585 < baseStart_488585 := by decide
  rcases family_descends (prefixWord ++ tailWord_488585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488647 : List Nat := [1, 1, 4, 1, 1, 1, 1, 8, 3]
def baseStart_488647 : Nat := 118140960795 + 488647 * 2 ^ 59
def prefixEnd_488647 : Nat := 4983230072969 + 3 ^ 40 * 488647 * 2
def baseEnd_488647 : Nat := 111515902834513288917893

theorem tailTrace_488647 : CollatzResearch.WordTrace tailWord_488647 prefixEnd_488647 111515902834513288917893 := by
  unfold tailWord_488647
  simp only [CollatzResearch.WordTrace]
  refine ⟨17822420260722848108576195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11881613507148565405717463 17822420260722848108576195)
  ·
    refine ⟨26733630391084272162864293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17822420260722848108576195 26733630391084272162864293)
    ·
      refine ⟨5012555698328301030537055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26733630391084272162864293 5012555698328301030537055)
      ·
        refine ⟨7518833547492451545805583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5012555698328301030537055 7518833547492451545805583)
        ·
          refine ⟨11278250321238677318708375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7518833547492451545805583 11278250321238677318708375)
          ·
            refine ⟨16917375481858015978062563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11278250321238677318708375 16917375481858015978062563)
            ·
              refine ⟨25376063222787023967093845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16917375481858015978062563 25376063222787023967093845)
              ·
                refine ⟨297375740892035437114381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 25376063222787023967093845 297375740892035437114381)
                ·
                  refine ⟨111515902834513288917893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297375740892035437114381 111515902834513288917893)
                  ·
                    rfl

theorem cell21_488647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 3].length) (baseStart_488647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_488647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_488647 prefixEnd_488647 := by exact prefixLift 488647
  have htrace : WordTrace (prefixWord ++ tailWord_488647) baseStart_488647 baseEnd_488647 := by
    simpa [prefixWord, tailWord_488647, baseEnd_488647] using wordTrace_append hprefix tailTrace_488647
  have hstable : (prefixWord ++ tailWord_488647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488647).length < 2 ^ (prefixWord ++ tailWord_488647).sum := by decide
  have hdescent : baseEnd_488647 < baseStart_488647 := by decide
  rcases family_descends (prefixWord ++ tailWord_488647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488740 : List Nat := [2, 3, 1, 3, 1, 1, 4, 3, 3]
def baseStart_488740 : Nat := 118140960795 + 488740 * 2 ^ 59
def prefixEnd_488740 : Nat := 4983230072969 + 3 ^ 40 * 488740 * 2
def baseEnd_488740 : Nat := 111537126701565793867703

theorem tailTrace_488740 : CollatzResearch.WordTrace tailWord_488740 prefixEnd_488740 111537126701565793867703 := by
  unfold tailWord_488740
  simp only [CollatzResearch.WordTrace]
  refine ⟨8912906124692962495855837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11883874832923949994474449 8912906124692962495855837)
  ·
    refine ⟨3342339796759860935945939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8912906124692962495855837 3342339796759860935945939)
    ·
      refine ⟨5013509695139791403918909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3342339796759860935945939 5013509695139791403918909)
      ·
        refine ⟨1880066135677421776469591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5013509695139791403918909 1880066135677421776469591)
        ·
          refine ⟨2820099203516132664704387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1880066135677421776469591 2820099203516132664704387)
          ·
            refine ⟨4230148805274198997056581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2820099203516132664704387 4230148805274198997056581)
            ·
              refine ⟨793152900988912311948109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4230148805274198997056581 793152900988912311948109)
              ·
                refine ⟨297432337870842116980541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 793152900988912311948109 297432337870842116980541)
                ·
                  refine ⟨111537126701565793867703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297432337870842116980541 111537126701565793867703)
                  ·
                    rfl

theorem cell21_488740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_488740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_488740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_488740 prefixEnd_488740 := by exact prefixLift 488740
  have htrace : WordTrace (prefixWord ++ tailWord_488740) baseStart_488740 baseEnd_488740 := by
    simpa [prefixWord, tailWord_488740, baseEnd_488740] using wordTrace_append hprefix tailTrace_488740
  have hstable : (prefixWord ++ tailWord_488740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488740).length < 2 ^ (prefixWord ++ tailWord_488740).sum := by decide
  have hdescent : baseEnd_488740 < baseStart_488740 := by decide
  rcases family_descends (prefixWord ++ tailWord_488740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488754 : List Nat := [3, 2, 1, 1, 4, 1, 3, 2, 4]
def baseStart_488754 : Nat := 118140960795 + 488754 * 2 ^ 59
def prefixEnd_488754 : Nat := 4983230072969 + 3 ^ 40 * 488754 * 2
def baseEnd_488754 : Nat := 111540321692304880634341

theorem tailTrace_488754 : CollatzResearch.WordTrace tailWord_488754 prefixEnd_488754 111540321692304880634341 := by
  unfold tailWord_488754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4456580717833801345680329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11884215247556803588480877 4456580717833801345680329)
  ·
    refine ⟨3342435538375351009260247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4456580717833801345680329 3342435538375351009260247)
    ·
      refine ⟨5013653307563026513890371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3342435538375351009260247 5013653307563026513890371)
      ·
        refine ⟨7520479961344539770835557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5013653307563026513890371 7520479961344539770835557)
        ·
          refine ⟨1410089992752101207031667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7520479961344539770835557 1410089992752101207031667)
          ·
            refine ⟨2115134989128151810547501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410089992752101207031667 2115134989128151810547501)
            ·
              refine ⟨793175620923056928955313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2115134989128151810547501 793175620923056928955313)
              ·
                refine ⟨594881715692292696716485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793175620923056928955313 594881715692292696716485)
                ·
                  refine ⟨111540321692304880634341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 594881715692292696716485 111540321692304880634341)
                  ·
                    rfl

theorem cell21_488754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_488754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_488754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_488754 prefixEnd_488754 := by exact prefixLift 488754
  have htrace : WordTrace (prefixWord ++ tailWord_488754) baseStart_488754 baseEnd_488754 := by
    simpa [prefixWord, tailWord_488754, baseEnd_488754] using wordTrace_append hprefix tailTrace_488754
  have hstable : (prefixWord ++ tailWord_488754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488754).length < 2 ^ (prefixWord ++ tailWord_488754).sum := by decide
  have hdescent : baseEnd_488754 < baseStart_488754 := by decide
  rcases family_descends (prefixWord ++ tailWord_488754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488782 : List Nat := [4, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_488782 : Nat := 118140960795 + 488782 * 2 ^ 59
def prefixEnd_488782 : Nat := 4983230072969 + 3 ^ 40 * 488782 * 2
def baseEnd_488782 : Nat := 111546711673783054167617

theorem tailTrace_488782 : CollatzResearch.WordTrace tailWord_488782 prefixEnd_488782 111546711673783054167617 := by
  unfold tailWord_488782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2228418014404220770592575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11884896076822510776493733 2228418014404220770592575)
  ·
    refine ⟨3342627021606331155888863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2228418014404220770592575 3342627021606331155888863)
    ·
      refine ⟨5013940532409496733833295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3342627021606331155888863 5013940532409496733833295)
      ·
        refine ⟨7520910798614245100749943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5013940532409496733833295 7520910798614245100749943)
        ·
          refine ⟨11281366197921367651124915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7520910798614245100749943 11281366197921367651124915)
          ·
            refine ⟨16922049296882051476687373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11281366197921367651124915 16922049296882051476687373)
            ·
              refine ⟨6345768486330769303757765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16922049296882051476687373 6345768486330769303757765)
              ·
                refine ⟨1189831591187019244454581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6345768486330769303757765 1189831591187019244454581)
                ·
                  refine ⟨111546711673783054167617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1189831591187019244454581 111546711673783054167617)
                  ·
                    rfl

theorem cell21_488782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_488782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_488782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_488782 prefixEnd_488782 := by exact prefixLift 488782
  have htrace : WordTrace (prefixWord ++ tailWord_488782) baseStart_488782 baseEnd_488782 := by
    simpa [prefixWord, tailWord_488782, baseEnd_488782] using wordTrace_append hprefix tailTrace_488782
  have hstable : (prefixWord ++ tailWord_488782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488782).length < 2 ^ (prefixWord ++ tailWord_488782).sum := by decide
  have hdescent : baseEnd_488782 < baseStart_488782 := by decide
  rcases family_descends (prefixWord ++ tailWord_488782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488813 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 6]
def baseStart_488813 : Nat := 118140960795 + 488813 * 2 ^ 59
def prefixEnd_488813 : Nat := 4983230072969 + 3 ^ 40 * 488813 * 2
def baseEnd_488813 : Nat := 111553786296133889150887

theorem tailTrace_488813 : CollatzResearch.WordTrace tailWord_488813 prefixEnd_488813 111553786296133889150887 := by
  unfold tailWord_488813
  simp only [CollatzResearch.WordTrace]
  refine ⟨17828474778121458459119093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11885649852080972306079395 17828474778121458459119093)
  ·
    refine ⟨1671419510448886730542415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17828474778121458459119093 1671419510448886730542415)
    ·
      refine ⟨2507129265673330095813623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1671419510448886730542415 2507129265673330095813623)
      ·
        refine ⟨3760693898509995143720435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2507129265673330095813623 3760693898509995143720435)
        ·
          refine ⟨5641040847764992715580653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3760693898509995143720435 5641040847764992715580653)
          ·
            refine ⟨2115390317911872268342745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5641040847764992715580653 2115390317911872268342745)
            ·
              refine ⟨1586542738433904201257059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2115390317911872268342745 1586542738433904201257059)
              ·
                refine ⟨2379814107650856301885589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1586542738433904201257059 2379814107650856301885589)
                ·
                  refine ⟨111553786296133889150887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2379814107650856301885589 111553786296133889150887)
                  ·
                    rfl

theorem cell21_488813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_488813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_488813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_488813 prefixEnd_488813 := by exact prefixLift 488813
  have htrace : WordTrace (prefixWord ++ tailWord_488813) baseStart_488813 baseEnd_488813 := by
    simpa [prefixWord, tailWord_488813, baseEnd_488813] using wordTrace_append hprefix tailTrace_488813
  have hstable : (prefixWord ++ tailWord_488813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488813).length < 2 ^ (prefixWord ++ tailWord_488813).sum := by decide
  have hdescent : baseEnd_488813 < baseStart_488813 := by decide
  rcases family_descends (prefixWord ++ tailWord_488813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488816 : List Nat := [2, 1, 1, 1, 4, 2, 5, 2, 3]
def baseStart_488816 : Nat := 118140960795 + 488816 * 2 ^ 59
def prefixEnd_488816 : Nat := 4983230072969 + 3 ^ 40 * 488816 * 2
def baseEnd_488816 : Nat := 111554470937006550600881

theorem tailTrace_488816 : CollatzResearch.WordTrace tailWord_488816 prefixEnd_488816 111554470937006550600881 := by
  unfold tailWord_488816
  simp only [CollatzResearch.WordTrace]
  refine ⟨8914292098555294985739151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11885722798073726647652201 8914292098555294985739151)
  ·
    refine ⟨13371438147832942478608727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8914292098555294985739151 13371438147832942478608727)
    ·
      refine ⟨20057157221749413717913091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13371438147832942478608727 20057157221749413717913091)
      ·
        refine ⟨30085735832624120576869637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20057157221749413717913091 30085735832624120576869637)
        ·
          refine ⟨5641075468617022608163057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30085735832624120576869637 5641075468617022608163057)
          ·
            refine ⟨4230806601462766956122293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5641075468617022608163057 4230806601462766956122293)
            ·
              refine ⟨396638118887134402136465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4230806601462766956122293 396638118887134402136465)
              ·
                refine ⟨297478589165350801602349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396638118887134402136465 297478589165350801602349)
                ·
                  refine ⟨111554470937006550600881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297478589165350801602349 111554470937006550600881)
                  ·
                    rfl

theorem cell21_488816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 3].length) (baseStart_488816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_488816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_488816 prefixEnd_488816 := by exact prefixLift 488816
  have htrace : WordTrace (prefixWord ++ tailWord_488816) baseStart_488816 baseEnd_488816 := by
    simpa [prefixWord, tailWord_488816, baseEnd_488816] using wordTrace_append hprefix tailTrace_488816
  have hstable : (prefixWord ++ tailWord_488816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488816).length < 2 ^ (prefixWord ++ tailWord_488816).sum := by decide
  have hdescent : baseEnd_488816 < baseStart_488816 := by decide
  rcases family_descends (prefixWord ++ tailWord_488816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488827 : List Nat := [1, 1, 1, 1, 1, 6, 4, 6]
def baseStart_488827 : Nat := 118140960795 + 488827 * 2 ^ 59
def prefixEnd_488827 : Nat := 4983230072969 + 3 ^ 40 * 488827 * 2
def baseEnd_488827 : Nat := 37185660428957658639175

theorem tailTrace_488827 : CollatzResearch.WordTrace tailWord_488827 prefixEnd_488827 37185660428957658639175 := by
  unfold tailWord_488827
  simp only [CollatzResearch.WordTrace]
  refine ⟨17828985400070738850128735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11885990266713825900085823 17828985400070738850128735)
  ·
    refine ⟨26743478100106108275193103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17828985400070738850128735 26743478100106108275193103)
    ·
      refine ⟨40115217150159162412789655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26743478100106108275193103 40115217150159162412789655)
      ·
        refine ⟨60172825725238743619184483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40115217150159162412789655 60172825725238743619184483)
        ·
          refine ⟨90259238587858115428776725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60172825725238743619184483 90259238587858115428776725)
          ·
            refine ⟨4230901808805849160723909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90259238587858115428776725 4230901808805849160723909)
            ·
              refine ⟨793294089151096717635733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4230901808805849160723909 793294089151096717635733)
              ·
                refine ⟨37185660428957658639175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 793294089151096717635733 37185660428957658639175)
                ·
                  rfl

theorem cell21_488827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 6].length) (baseStart_488827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_488827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_488827 prefixEnd_488827 := by exact prefixLift 488827
  have htrace : WordTrace (prefixWord ++ tailWord_488827) baseStart_488827 baseEnd_488827 := by
    simpa [prefixWord, tailWord_488827, baseEnd_488827] using wordTrace_append hprefix tailTrace_488827
  have hstable : (prefixWord ++ tailWord_488827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488827).length < 2 ^ (prefixWord ++ tailWord_488827).sum := by decide
  have hdescent : baseEnd_488827 < baseStart_488827 := by decide
  rcases family_descends (prefixWord ++ tailWord_488827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_488979 : List Nat := [1, 1, 1, 2, 1, 8, 7]
def baseStart_488979 : Nat := 118140960795 + 488979 * 2 ^ 59
def prefixEnd_488979 : Nat := 4983230072969 + 3 ^ 40 * 488979 * 2
def baseEnd_488979 : Nat := 12399074417528276598209

theorem tailTrace_488979 : CollatzResearch.WordTrace tailWord_488979 prefixEnd_488979 12399074417528276598209 := by
  unfold tailWord_488979
  simp only [CollatzResearch.WordTrace]
  refine ⟨17834529295520068809661991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11889686197013379206441327 17834529295520068809661991)
  ·
    refine ⟨26751793943280103214492987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17834529295520068809661991 26751793943280103214492987)
    ·
      refine ⟨40127690914920154821739481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26751793943280103214492987 40127690914920154821739481)
      ·
        refine ⟨30095768186190116116304611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40127690914920154821739481 30095768186190116116304611)
        ·
          refine ⟨45143652279285174174456917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30095768186190116116304611 45143652279285174174456917)
          ·
            refine ⟨529027175147873134856917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 45143652279285174174456917 529027175147873134856917)
            ·
              refine ⟨12399074417528276598209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 529027175147873134856917 12399074417528276598209)
              ·
                rfl

theorem cell21_488979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 7].length) (baseStart_488979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_488979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_488979 prefixEnd_488979 := by exact prefixLift 488979
  have htrace : WordTrace (prefixWord ++ tailWord_488979) baseStart_488979 baseEnd_488979 := by
    simpa [prefixWord, tailWord_488979, baseEnd_488979] using wordTrace_append hprefix tailTrace_488979
  have hstable : (prefixWord ++ tailWord_488979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_488979).length < 2 ^ (prefixWord ++ tailWord_488979).sum := by decide
  have hdescent : baseEnd_488979 < baseStart_488979 := by decide
  rcases family_descends (prefixWord ++ tailWord_488979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489041 : List Nat := [1, 2, 2, 1, 3, 2, 4, 2, 4]
def baseStart_489041 : Nat := 118140960795 + 489041 * 2 ^ 59
def prefixEnd_489041 : Nat := 4983230072969 + 3 ^ 40 * 489041 * 2
def baseEnd_489041 : Nat := 111605819002456159350421

theorem tailTrace_489041 : CollatzResearch.WordTrace tailWord_489041 prefixEnd_489041 111605819002456159350421 := by
  unfold tailWord_489041
  simp only [CollatzResearch.WordTrace]
  refine ⟨17836790621295453398418977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11891193747530302265612651 17836790621295453398418977)
  ·
    refine ⟨13377592965971590048814233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17836790621295453398418977 13377592965971590048814233)
    ·
      refine ⟨10033194724478692536610675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13377592965971590048814233 10033194724478692536610675)
      ·
        refine ⟨15049792086718038804916013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10033194724478692536610675 15049792086718038804916013)
        ·
          refine ⟨5643672032519264551843505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15049792086718038804916013 5643672032519264551843505)
          ·
            refine ⟨4232754024389448413882629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5643672032519264551843505 4232754024389448413882629)
            ·
              refine ⟨793641379573021577602993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4232754024389448413882629 793641379573021577602993)
              ·
                refine ⟨595231034679766183202245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793641379573021577602993 595231034679766183202245)
                ·
                  refine ⟨111605819002456159350421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 595231034679766183202245 111605819002456159350421)
                  ·
                    rfl

theorem cell21_489041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_489041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489041 prefixEnd_489041 := by exact prefixLift 489041
  have htrace : WordTrace (prefixWord ++ tailWord_489041) baseStart_489041 baseEnd_489041 := by
    simpa [prefixWord, tailWord_489041, baseEnd_489041] using wordTrace_append hprefix tailTrace_489041
  have hstable : (prefixWord ++ tailWord_489041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489041).length < 2 ^ (prefixWord ++ tailWord_489041).sum := by decide
  have hdescent : baseEnd_489041 < baseStart_489041 := by decide
  rcases family_descends (prefixWord ++ tailWord_489041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489072 : List Nat := [2, 1, 1, 1, 6, 2, 3, 5]
def baseStart_489072 : Nat := 118140960795 + 489072 * 2 ^ 59
def prefixEnd_489072 : Nat := 4983230072969 + 3 ^ 40 * 489072 * 2
def baseEnd_489072 : Nat := 37204297874935664777897

theorem tailTrace_489072 : CollatzResearch.WordTrace tailWord_489072 prefixEnd_489072 37204297874935664777897 := by
  unfold tailWord_489072
  simp only [CollatzResearch.WordTrace]
  refine ⟨8918960642091572846398735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11891947522788763795198313 8918960642091572846398735)
  ·
    refine ⟨13378440963137359269598103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8918960642091572846398735 13378440963137359269598103)
    ·
      refine ⟨20067661444706038904397155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13378440963137359269598103 20067661444706038904397155)
      ·
        refine ⟨30101492167059058356595733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20067661444706038904397155 30101492167059058356595733)
        ·
          refine ⟨1411007445330893360465425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30101492167059058356595733 1411007445330893360465425)
          ·
            refine ⟨1058255583998170020349069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1411007445330893360465425 1058255583998170020349069)
            ·
              refine ⟨396845843999313757630901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1058255583998170020349069 396845843999313757630901)
              ·
                refine ⟨37204297874935664777897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 396845843999313757630901 37204297874935664777897)
                ·
                  rfl

theorem cell21_489072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 5].length) (baseStart_489072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489072 prefixEnd_489072 := by exact prefixLift 489072
  have htrace : WordTrace (prefixWord ++ tailWord_489072) baseStart_489072 baseEnd_489072 := by
    simpa [prefixWord, tailWord_489072, baseEnd_489072] using wordTrace_append hprefix tailTrace_489072
  have hstable : (prefixWord ++ tailWord_489072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489072).length < 2 ^ (prefixWord ++ tailWord_489072).sum := by decide
  have hdescent : baseEnd_489072 < baseStart_489072 := by decide
  rcases family_descends (prefixWord ++ tailWord_489072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489100 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 6]
def baseStart_489100 : Nat := 118140960795 + 489100 * 2 ^ 59
def prefixEnd_489100 : Nat := 4983230072969 + 3 ^ 40 * 489100 * 2
def baseEnd_489100 : Nat := 111619283606285167866967

theorem tailTrace_489100 : CollatzResearch.WordTrace tailWord_489100 prefixEnd_489100 111619283606285167866967 := by
  unfold tailWord_489100
  simp only [CollatzResearch.WordTrace]
  refine ⟨8919471264040853237408377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11892628352054470983211169 8919471264040853237408377)
  ·
    refine ⟨6689603448030639928056283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8919471264040853237408377 6689603448030639928056283)
    ·
      refine ⟨10034405172045959892084425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6689603448030639928056283 10034405172045959892084425)
      ·
        refine ⟨7525803879034469919063319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10034405172045959892084425 7525803879034469919063319)
        ·
          refine ⟨11288705818551704878594979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7525803879034469919063319 11288705818551704878594979)
          ·
            refine ⟨16933058727827557317892469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11288705818551704878594979 16933058727827557317892469)
            ·
              refine ⟨1587474255733833498552419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16933058727827557317892469 1587474255733833498552419)
              ·
                refine ⟨2381211383600750247828629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587474255733833498552419 2381211383600750247828629)
                ·
                  refine ⟨111619283606285167866967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2381211383600750247828629 111619283606285167866967)
                  ·
                    rfl

theorem cell21_489100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_489100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489100 prefixEnd_489100 := by exact prefixLift 489100
  have htrace : WordTrace (prefixWord ++ tailWord_489100) baseStart_489100 baseEnd_489100 := by
    simpa [prefixWord, tailWord_489100, baseEnd_489100] using wordTrace_append hprefix tailTrace_489100
  have hstable : (prefixWord ++ tailWord_489100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489100).length < 2 ^ (prefixWord ++ tailWord_489100).sum := by decide
  have hdescent : baseEnd_489100 < baseStart_489100 := by decide
  rcases family_descends (prefixWord ++ tailWord_489100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489145 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 7]
def baseStart_489145 : Nat := 118140960795 + 489145 * 2 ^ 59
def prefixEnd_489145 : Nat := 4983230072969 + 3 ^ 40 * 489145 * 2
def baseEnd_489145 : Nat := 111629553219375089616875

theorem tailTrace_489145 : CollatzResearch.WordTrace tailWord_489145 prefixEnd_489145 111629553219375089616875 := by
  unfold tailWord_489145
  simp only [CollatzResearch.WordTrace]
  refine ⟨17840583812918679160204889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11893722541945786106803259 17840583812918679160204889)
  ·
    refine ⟨13380437859689009370153667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17840583812918679160204889 13380437859689009370153667)
    ·
      refine ⟨20070656789533514055230501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13380437859689009370153667 20070656789533514055230501)
      ·
        refine ⟨3763248148037533885355719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20070656789533514055230501 3763248148037533885355719)
        ·
          refine ⟨5644872222056300828033579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3763248148037533885355719 5644872222056300828033579)
          ·
            refine ⟨8467308333084451242050369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5644872222056300828033579 8467308333084451242050369)
            ·
              refine ⟨6350481249813338431537777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8467308333084451242050369 6350481249813338431537777)
              ·
                refine ⟨4762860937360003823653333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6350481249813338431537777 4762860937360003823653333)
                ·
                  refine ⟨111629553219375089616875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4762860937360003823653333 111629553219375089616875)
                  ·
                    rfl

theorem cell21_489145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_489145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489145 prefixEnd_489145 := by exact prefixLift 489145
  have htrace : WordTrace (prefixWord ++ tailWord_489145) baseStart_489145 baseEnd_489145 := by
    simpa [prefixWord, tailWord_489145, baseEnd_489145] using wordTrace_append hprefix tailTrace_489145
  have hstable : (prefixWord ++ tailWord_489145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489145).length < 2 ^ (prefixWord ++ tailWord_489145).sum := by decide
  have hdescent : baseEnd_489145 < baseStart_489145 := by decide
  rcases family_descends (prefixWord ++ tailWord_489145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489154 : List Nat := [3, 5, 1, 2, 1, 2, 1, 1, 5]
def baseStart_489154 : Nat := 118140960795 + 489154 * 2 ^ 59
def prefixEnd_489154 : Nat := 4983230072969 + 3 ^ 40 * 489154 * 2
def baseEnd_489154 : Nat := 111631607141993073966857

theorem tailTrace_489154 : CollatzResearch.WordTrace tailWord_489154 prefixEnd_489154 111631607141993073966857 := by
  unfold tailWord_489154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4460228017471518424320629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11893941379924049131521677 4460228017471518424320629)
  ·
    refine ⟨418146376637954852280059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4460228017471518424320629 418146376637954852280059)
    ·
      refine ⟨627219564956932278420089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418146376637954852280059 627219564956932278420089)
      ·
        refine ⟨470414673717699208815067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627219564956932278420089 470414673717699208815067)
        ·
          refine ⟨705622010576548813222601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470414673717699208815067 705622010576548813222601)
          ·
            refine ⟨529216507932411609916951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705622010576548813222601 529216507932411609916951)
            ·
              refine ⟨793824761898617414875427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529216507932411609916951 793824761898617414875427)
              ·
                refine ⟨1190737142847926122313141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 793824761898617414875427 1190737142847926122313141)
                ·
                  refine ⟨111631607141993073966857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1190737142847926122313141 111631607141993073966857)
                  ·
                    rfl

theorem cell21_489154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_489154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489154 prefixEnd_489154 := by exact prefixLift 489154
  have htrace : WordTrace (prefixWord ++ tailWord_489154) baseStart_489154 baseEnd_489154 := by
    simpa [prefixWord, tailWord_489154, baseEnd_489154] using wordTrace_append hprefix tailTrace_489154
  have hstable : (prefixWord ++ tailWord_489154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489154).length < 2 ^ (prefixWord ++ tailWord_489154).sum := by decide
  have hdescent : baseEnd_489154 < baseStart_489154 := by decide
  rcases family_descends (prefixWord ++ tailWord_489154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489165 : List Nat := [1, 6, 2, 1, 1, 2, 2, 6]
def baseStart_489165 : Nat := 118140960795 + 489165 * 2 ^ 59
def prefixEnd_489165 : Nat := 4983230072969 + 3 ^ 40 * 489165 * 2
def baseEnd_489165 : Nat := 37211372497286499761167

theorem tailTrace_489165 : CollatzResearch.WordTrace tailWord_489165 prefixEnd_489165 37211372497286499761167 := by
  unfold tailWord_489165
  simp only [CollatzResearch.WordTrace]
  refine ⟨17841313272846222575932949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11894208848564148383955299 17841313272846222575932949)
  ·
    refine ⟨836311559664666683246857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17841313272846222575932949 836311559664666683246857)
    ·
      refine ⟨627233669748500012435143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 836311559664666683246857 627233669748500012435143)
      ·
        refine ⟨940850504622750018652715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627233669748500012435143 940850504622750018652715)
        ·
          refine ⟨1411275756934125027979073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940850504622750018652715 1411275756934125027979073)
          ·
            refine ⟨1058456817700593770984305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1411275756934125027979073 1058456817700593770984305)
            ·
              refine ⟨793842613275445328238229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1058456817700593770984305 793842613275445328238229)
              ·
                refine ⟨37211372497286499761167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 793842613275445328238229 37211372497286499761167)
                ·
                  rfl

theorem cell21_489165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 6].length) (baseStart_489165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489165 prefixEnd_489165 := by exact prefixLift 489165
  have htrace : WordTrace (prefixWord ++ tailWord_489165) baseStart_489165 baseEnd_489165 := by
    simpa [prefixWord, tailWord_489165, baseEnd_489165] using wordTrace_append hprefix tailTrace_489165
  have hstable : (prefixWord ++ tailWord_489165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489165).length < 2 ^ (prefixWord ++ tailWord_489165).sum := by decide
  have hdescent : baseEnd_489165 < baseStart_489165 := by decide
  rcases family_descends (prefixWord ++ tailWord_489165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489269 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 6]
def baseStart_489269 : Nat := 118140960795 + 489269 * 2 ^ 59
def prefixEnd_489269 : Nat := 4983230072969 + 3 ^ 40 * 489269 * 2
def baseEnd_489269 : Nat := 111657851708778429549955

theorem tailTrace_489269 : CollatzResearch.WordTrace tailWord_489269 prefixEnd_489269 111657851708778429549955 := by
  unfold tailWord_489269
  simp only [CollatzResearch.WordTrace]
  refine ⟨17845106464469448337718861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11896737642979632225145907 17845106464469448337718861)
  ·
    refine ⟨6691914924176043126644573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17845106464469448337718861 6691914924176043126644573)
    ·
      refine ⟨2509468096566016172491715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6691914924176043126644573 2509468096566016172491715)
      ·
        refine ⟨3764202144849024258737573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2509468096566016172491715 3764202144849024258737573)
        ·
          refine ⟨705787902159192048513295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3764202144849024258737573 705787902159192048513295)
          ·
            refine ⟨1058681853238788072769943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705787902159192048513295 1058681853238788072769943)
            ·
              refine ⟨1588022779858182109154915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058681853238788072769943 1588022779858182109154915)
              ·
                refine ⟨2382034169787273163732373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588022779858182109154915 2382034169787273163732373)
                ·
                  refine ⟨111657851708778429549955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2382034169787273163732373 111657851708778429549955)
                  ·
                    rfl

theorem cell21_489269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_489269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489269 prefixEnd_489269 := by exact prefixLift 489269
  have htrace : WordTrace (prefixWord ++ tailWord_489269) baseStart_489269 baseEnd_489269 := by
    simpa [prefixWord, tailWord_489269, baseEnd_489269] using wordTrace_append hprefix tailTrace_489269
  have hstable : (prefixWord ++ tailWord_489269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489269).length < 2 ^ (prefixWord ++ tailWord_489269).sum := by decide
  have hdescent : baseEnd_489269 < baseStart_489269 := by decide
  rcases family_descends (prefixWord ++ tailWord_489269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489300 : List Nat := [2, 4, 1, 1, 3, 1, 4, 5]
def baseStart_489300 : Nat := 118140960795 + 489300 * 2 ^ 59
def prefixEnd_489300 : Nat := 4983230072969 + 3 ^ 40 * 489300 * 2
def baseEnd_489300 : Nat := 37221642110376421511075

theorem tailTrace_489300 : CollatzResearch.WordTrace tailWord_489300 prefixEnd_489300 37221642110376421511075 := by
  unfold tailWord_489300
  simp only [CollatzResearch.WordTrace]
  refine ⟨8923118563678570316048677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11897491418238093754731569 8923118563678570316048677)
  ·
    refine ⟨1673084730689731934259127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8923118563678570316048677 1673084730689731934259127)
    ·
      refine ⟨2509627096034597901388691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1673084730689731934259127 2509627096034597901388691)
      ·
        refine ⟨3764440644051896852083037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2509627096034597901388691 3764440644051896852083037)
        ·
          refine ⟨1411665241519461319531139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3764440644051896852083037 1411665241519461319531139)
          ·
            refine ⟨2117497862279191979296709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411665241519461319531139 2117497862279191979296709)
            ·
              refine ⟨397030849177348496118133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2117497862279191979296709 397030849177348496118133)
              ·
                refine ⟨37221642110376421511075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 397030849177348496118133 37221642110376421511075)
                ·
                  rfl

theorem cell21_489300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 5].length) (baseStart_489300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489300 prefixEnd_489300 := by exact prefixLift 489300
  have htrace : WordTrace (prefixWord ++ tailWord_489300) baseStart_489300 baseEnd_489300 := by
    simpa [prefixWord, tailWord_489300, baseEnd_489300] using wordTrace_append hprefix tailTrace_489300
  have hstable : (prefixWord ++ tailWord_489300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489300).length < 2 ^ (prefixWord ++ tailWord_489300).sum := by decide
  have hdescent : baseEnd_489300 < baseStart_489300 := by decide
  rcases family_descends (prefixWord ++ tailWord_489300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489328 : List Nat := [2, 1, 1, 1, 4, 1, 1, 6, 4]
def baseStart_489328 : Nat := 118140960795 + 489328 * 2 ^ 59
def prefixEnd_489328 : Nat := 4983230072969 + 3 ^ 40 * 489328 * 2
def baseEnd_489328 : Nat := 111671316312607438066501

theorem tailTrace_489328 : CollatzResearch.WordTrace tailWord_489328 prefixEnd_489328 111671316312607438066501 := by
  unfold tailWord_489328
  simp only [CollatzResearch.WordTrace]
  refine ⟨8923629185627850707058319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11898172247503800942744425 8923629185627850707058319)
  ·
    refine ⟨13385443778441776060587479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8923629185627850707058319 13385443778441776060587479)
    ·
      refine ⟨20078165667662664090881219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13385443778441776060587479 20078165667662664090881219)
      ·
        refine ⟨30117248501493996136321829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20078165667662664090881219 30117248501493996136321829)
        ·
          refine ⟨5646984094030124275560343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30117248501493996136321829 5646984094030124275560343)
          ·
            refine ⟨8470476141045186413340515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5646984094030124275560343 8470476141045186413340515)
            ·
              refine ⟨12705714211567779620010773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8470476141045186413340515 12705714211567779620010773)
              ·
                refine ⟨595580353667239669688005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12705714211567779620010773 595580353667239669688005)
                ·
                  refine ⟨111671316312607438066501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 595580353667239669688005 111671316312607438066501)
                  ·
                    rfl

theorem cell21_489328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_489328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489328 prefixEnd_489328 := by exact prefixLift 489328
  have htrace : WordTrace (prefixWord ++ tailWord_489328) baseStart_489328 baseEnd_489328 := by
    simpa [prefixWord, tailWord_489328, baseEnd_489328] using wordTrace_append hprefix tailTrace_489328
  have hstable : (prefixWord ++ tailWord_489328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489328).length < 2 ^ (prefixWord ++ tailWord_489328).sum := by decide
  have hdescent : baseEnd_489328 < baseStart_489328 := by decide
  rcases family_descends (prefixWord ++ tailWord_489328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489418 : List Nat := [3, 1, 2, 1, 2, 1, 2, 9]
def baseStart_489418 : Nat := 118140960795 + 489418 * 2 ^ 59
def prefixEnd_489418 : Nat := 4983230072969 + 3 ^ 40 * 489418 * 2
def baseEnd_489418 : Nat := 37230618512929093855439

theorem tailTrace_489418 : CollatzResearch.WordTrace tailWord_489418 prefixEnd_489418 37230618512929093855439 := by
  unfold tailWord_489418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4462635235232411696223227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11900360627286431189928605 4462635235232411696223227)
  ·
    refine ⟨6693952852848617544334841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4462635235232411696223227 6693952852848617544334841)
    ·
      refine ⟨5020464639636463158251131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6693952852848617544334841 5020464639636463158251131)
      ·
        refine ⟨7530696959454694737376697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5020464639636463158251131 7530696959454694737376697)
        ·
          refine ⟨5648022719591021053032523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7530696959454694737376697 5648022719591021053032523)
          ·
            refine ⟨8472034079386531579548785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5648022719591021053032523 8472034079386531579548785)
            ·
              refine ⟨6354025559539898684661589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8472034079386531579548785 6354025559539898684661589)
              ·
                refine ⟨37230618512929093855439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6354025559539898684661589 37230618512929093855439)
                ·
                  rfl

theorem cell21_489418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_489418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489418 prefixEnd_489418 := by exact prefixLift 489418
  have htrace : WordTrace (prefixWord ++ tailWord_489418) baseStart_489418 baseEnd_489418 := by
    simpa [prefixWord, tailWord_489418, baseEnd_489418] using wordTrace_append hprefix tailTrace_489418
  have hstable : (prefixWord ++ tailWord_489418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489418).length < 2 ^ (prefixWord ++ tailWord_489418).sum := by decide
  have hdescent : baseEnd_489418 < baseStart_489418 := by decide
  rcases family_descends (prefixWord ++ tailWord_489418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489500 : List Nat := [2, 2, 3, 1, 3, 2, 3, 2, 3]
def baseStart_489500 : Nat := 118140960795 + 489500 * 2 ^ 59
def prefixEnd_489500 : Nat := 4983230072969 + 3 ^ 40 * 489500 * 2
def baseEnd_489500 : Nat := 111710569055973361199483

theorem tailTrace_489500 : CollatzResearch.WordTrace tailWord_489500 prefixEnd_489500 111710569055973361199483 := by
  unfold tailWord_489500
  simp only [CollatzResearch.WordTrace]
  refine ⟨8926765863316287394688977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11902354484421716526251969 8926765863316287394688977)
  ·
    refine ⟨6695074397487215546016733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8926765863316287394688977 6695074397487215546016733)
    ·
      refine ⟨2510652899057705829756275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6695074397487215546016733 2510652899057705829756275)
      ·
        refine ⟨3765979348586558744634413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2510652899057705829756275 3765979348586558744634413)
        ·
          refine ⟨1412242255719959529237905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3765979348586558744634413 1412242255719959529237905)
          ·
            refine ⟨1059181691789969646928429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1412242255719959529237905 1059181691789969646928429)
            ·
              refine ⟨397193134421238617598161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1059181691789969646928429 397193134421238617598161)
              ·
                refine ⟨297894850815928963198621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397193134421238617598161 297894850815928963198621)
                ·
                  refine ⟨111710569055973361199483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297894850815928963198621 111710569055973361199483)
                  ·
                    rfl

theorem cell21_489500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_489500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489500 prefixEnd_489500 := by exact prefixLift 489500
  have htrace : WordTrace (prefixWord ++ tailWord_489500) baseStart_489500 baseEnd_489500 := by
    simpa [prefixWord, tailWord_489500, baseEnd_489500] using wordTrace_append hprefix tailTrace_489500
  have hstable : (prefixWord ++ tailWord_489500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489500).length < 2 ^ (prefixWord ++ tailWord_489500).sum := by decide
  have hdescent : baseEnd_489500 < baseStart_489500 := by decide
  rcases family_descends (prefixWord ++ tailWord_489500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489514 : List Nat := [3, 1, 4, 1, 2, 1, 4, 1, 4]
def baseStart_489514 : Nat := 118140960795 + 489514 * 2 ^ 59
def prefixEnd_489514 : Nat := 4983230072969 + 3 ^ 40 * 489514 * 2
def baseEnd_489514 : Nat := 111713764046712447966121

theorem tailTrace_489514 : CollatzResearch.WordTrace tailWord_489514 prefixEnd_489514 111713764046712447966121 := by
  unfold tailWord_489514
  simp only [CollatzResearch.WordTrace]
  refine ⟨4463510587145463795096899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11902694899054570120258397 4463510587145463795096899)
  ·
    refine ⟨6695265880718195692645349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4463510587145463795096899 6695265880718195692645349)
    ·
      refine ⟨1255362352634661692371003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6695265880718195692645349 1255362352634661692371003)
      ·
        refine ⟨1883043528951992538556505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1255362352634661692371003 1883043528951992538556505)
        ·
          refine ⟨1412282646713994403917379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1883043528951992538556505 1412282646713994403917379)
          ·
            refine ⟨2118423970070991605876069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412282646713994403917379 2118423970070991605876069)
            ·
              refine ⟨397204494388310926101763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2118423970070991605876069 397204494388310926101763)
              ·
                refine ⟨595806741582466389152645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397204494388310926101763 595806741582466389152645)
                ·
                  refine ⟨111713764046712447966121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 595806741582466389152645 111713764046712447966121)
                  ·
                    rfl

theorem cell21_489514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_489514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489514 prefixEnd_489514 := by exact prefixLift 489514
  have htrace : WordTrace (prefixWord ++ tailWord_489514) baseStart_489514 baseEnd_489514 := by
    simpa [prefixWord, tailWord_489514, baseEnd_489514] using wordTrace_append hprefix tailTrace_489514
  have hstable : (prefixWord ++ tailWord_489514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489514).length < 2 ^ (prefixWord ++ tailWord_489514).sum := by decide
  have hdescent : baseEnd_489514 < baseStart_489514 := by decide
  rcases family_descends (prefixWord ++ tailWord_489514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489525 : List Nat := [1, 3, 3, 1, 1, 1, 2, 4, 5]
def baseStart_489525 : Nat := 118140960795 + 489525 * 2 ^ 59
def prefixEnd_489525 : Nat := 4983230072969 + 3 ^ 40 * 489525 * 2
def baseEnd_489525 : Nat := 111716274396578873282765

theorem tailTrace_489525 : CollatzResearch.WordTrace tailWord_489525 prefixEnd_489525 111716274396578873282765 := by
  unfold tailWord_489525
  simp only [CollatzResearch.WordTrace]
  refine ⟨17854443551542004059038029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11902962367694669372692019 17854443551542004059038029)
  ·
    refine ⟨6695416331828251522139261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17854443551542004059038029 6695416331828251522139261)
    ·
      refine ⟨2510781124435594320802223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6695416331828251522139261 2510781124435594320802223)
      ·
        refine ⟨3766171686653391481203335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2510781124435594320802223 3766171686653391481203335)
        ·
          refine ⟨5649257529980087221805003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3766171686653391481203335 5649257529980087221805003)
          ·
            refine ⟨8473886294970130832707505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5649257529980087221805003 8473886294970130832707505)
            ·
              refine ⟨6355414721227598124530629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8473886294970130832707505 6355414721227598124530629)
              ·
                refine ⟨1191640260230174648349493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6355414721227598124530629 1191640260230174648349493)
                ·
                  refine ⟨111716274396578873282765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1191640260230174648349493 111716274396578873282765)
                  ·
                    rfl

theorem cell21_489525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_489525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489525 prefixEnd_489525 := by exact prefixLift 489525
  have htrace : WordTrace (prefixWord ++ tailWord_489525) baseStart_489525 baseEnd_489525 := by
    simpa [prefixWord, tailWord_489525, baseEnd_489525] using wordTrace_append hprefix tailTrace_489525
  have hstable : (prefixWord ++ tailWord_489525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489525).length < 2 ^ (prefixWord ++ tailWord_489525).sum := by decide
  have hdescent : baseEnd_489525 < baseStart_489525 := by decide
  rcases family_descends (prefixWord ++ tailWord_489525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489539 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 6]
def baseStart_489539 : Nat := 118140960795 + 489539 * 2 ^ 59
def prefixEnd_489539 : Nat := 4983230072969 + 3 ^ 40 * 489539 * 2
def baseEnd_489539 : Nat := 111719469387317960049403

theorem tailTrace_489539 : CollatzResearch.WordTrace tailWord_489539 prefixEnd_489539 111719469387317960049403 := by
  unfold tailWord_489539
  simp only [CollatzResearch.WordTrace]
  refine ⟨17854954173491284450047671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11903302782327522966698447 17854954173491284450047671)
  ·
    refine ⟨26782431260236926675071507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17854954173491284450047671 26782431260236926675071507)
    ·
      refine ⟨40173646890355390012607261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26782431260236926675071507 40173646890355390012607261)
      ·
        refine ⟨15065117583883271254727723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40173646890355390012607261 15065117583883271254727723)
        ·
          refine ⟨22597676375824906882091585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15065117583883271254727723 22597676375824906882091585)
          ·
            refine ⟨16948257281868680161568689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22597676375824906882091585 16948257281868680161568689)
            ·
              refine ⟨12711192961401510121176517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16948257281868680161568689 12711192961401510121176517)
              ·
                refine ⟨2383348680262783147720597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12711192961401510121176517 2383348680262783147720597)
                ·
                  refine ⟨111719469387317960049403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2383348680262783147720597 111719469387317960049403)
                  ·
                    rfl

theorem cell21_489539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 6].length) (baseStart_489539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489539 prefixEnd_489539 := by exact prefixLift 489539
  have htrace : WordTrace (prefixWord ++ tailWord_489539) baseStart_489539 baseEnd_489539 := by
    simpa [prefixWord, tailWord_489539, baseEnd_489539] using wordTrace_append hprefix tailTrace_489539
  have hstable : (prefixWord ++ tailWord_489539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489539).length < 2 ^ (prefixWord ++ tailWord_489539).sum := by decide
  have hdescent : baseEnd_489539 < baseStart_489539 := by decide
  rcases family_descends (prefixWord ++ tailWord_489539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489559 : List Nat := [1, 1, 3, 2, 2, 1, 6, 2, 3]
def baseStart_489559 : Nat := 118140960795 + 489559 * 2 ^ 59
def prefixEnd_489559 : Nat := 4983230072969 + 3 ^ 40 * 489559 * 2
def baseEnd_489559 : Nat := 111724033659802369716029

theorem tailTrace_489559 : CollatzResearch.WordTrace tailWord_489559 prefixEnd_489559 111724033659802369716029 := by
  unfold tailWord_489559
  simp only [CollatzResearch.WordTrace]
  refine ⟨17855683633418827865775731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11903789088945885243850487 17855683633418827865775731)
  ·
    refine ⟨26783525450128241798663597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17855683633418827865775731 26783525450128241798663597)
    ·
      refine ⟨10043822043798090674498849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26783525450128241798663597 10043822043798090674498849)
      ·
        refine ⟨7532866532848568005874137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10043822043798090674498849 7532866532848568005874137)
        ·
          refine ⟨5649649899636426004405603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7532866532848568005874137 5649649899636426004405603)
          ·
            refine ⟨8474474849454639006608405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5649649899636426004405603 8474474849454639006608405)
            ·
              refine ⟨397241008568186203434769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8474474849454639006608405 397241008568186203434769)
              ·
                refine ⟨297930756426139652576077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397241008568186203434769 297930756426139652576077)
                ·
                  refine ⟨111724033659802369716029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297930756426139652576077 111724033659802369716029)
                  ·
                    rfl

theorem cell21_489559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 3].length) (baseStart_489559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489559 prefixEnd_489559 := by exact prefixLift 489559
  have htrace : WordTrace (prefixWord ++ tailWord_489559) baseStart_489559 baseEnd_489559 := by
    simpa [prefixWord, tailWord_489559, baseEnd_489559] using wordTrace_append hprefix tailTrace_489559
  have hstable : (prefixWord ++ tailWord_489559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489559).length < 2 ^ (prefixWord ++ tailWord_489559).sum := by decide
  have hdescent : baseEnd_489559 < baseStart_489559 := by decide
  rcases family_descends (prefixWord ++ tailWord_489559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489618 : List Nat := [3, 2, 3, 1, 1, 1, 4, 1, 5]
def baseStart_489618 : Nat := 118140960795 + 489618 * 2 ^ 59
def prefixEnd_489618 : Nat := 4983230072969 + 3 ^ 40 * 489618 * 2
def baseEnd_489618 : Nat := 111737498263631378232575

theorem tailTrace_489618 : CollatzResearch.WordTrace tailWord_489618 prefixEnd_489618 111737498263631378232575 := by
  unfold tailWord_489618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4464458885051270235543377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11905223693470053961449005 4464458885051270235543377)
  ·
    refine ⟨3348344163788452676657533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4464458885051270235543377 3348344163788452676657533)
    ·
      refine ⟨1255629061420669753746575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3348344163788452676657533 1255629061420669753746575)
      ·
        refine ⟨1883443592131004630619863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1255629061420669753746575 1883443592131004630619863)
        ·
          refine ⟨2825165388196506945929795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1883443592131004630619863 2825165388196506945929795)
          ·
            refine ⟨4237748082294760418894693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825165388196506945929795 4237748082294760418894693)
            ·
              refine ⟨794577765430267578542755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4237748082294760418894693 794577765430267578542755)
              ·
                refine ⟨1191866648145401367814133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794577765430267578542755 1191866648145401367814133)
                ·
                  refine ⟨111737498263631378232575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1191866648145401367814133 111737498263631378232575)
                  ·
                    rfl

theorem cell21_489618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_489618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489618 prefixEnd_489618 := by exact prefixLift 489618
  have htrace : WordTrace (prefixWord ++ tailWord_489618) baseStart_489618 baseEnd_489618 := by
    simpa [prefixWord, tailWord_489618, baseEnd_489618] using wordTrace_append hprefix tailTrace_489618
  have hstable : (prefixWord ++ tailWord_489618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489618).length < 2 ^ (prefixWord ++ tailWord_489618).sum := by decide
  have hdescent : baseEnd_489618 < baseStart_489618 := by decide
  rcases family_descends (prefixWord ++ tailWord_489618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489666 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 6]
def baseStart_489666 : Nat := 118140960795 + 489666 * 2 ^ 59
def prefixEnd_489666 : Nat := 4983230072969 + 3 ^ 40 * 489666 * 2
def baseEnd_489666 : Nat := 111748452517593961432477

theorem tailTrace_489666 : CollatzResearch.WordTrace tailWord_489666 prefixEnd_489666 111748452517593961432477 := by
  unfold tailWord_489666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4464896561007796284980213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11906390829354123426613901 4464896561007796284980213)
  ·
    refine ⟨418584052594480901716895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4464896561007796284980213 418584052594480901716895)
    ·
      refine ⟨627876078891721352575343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418584052594480901716895 627876078891721352575343)
      ·
        refine ⟨941814118337582028863015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627876078891721352575343 941814118337582028863015)
        ·
          refine ⟨1412721177506373043294523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941814118337582028863015 1412721177506373043294523)
          ·
            refine ⟨2119081766259559564941785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412721177506373043294523 2119081766259559564941785)
            ·
              refine ⟨1589311324694669673706339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2119081766259559564941785 1589311324694669673706339)
              ·
                refine ⟨2383966987042004510559509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589311324694669673706339 2383966987042004510559509)
                ·
                  refine ⟨111748452517593961432477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2383966987042004510559509 111748452517593961432477)
                  ·
                    rfl

theorem cell21_489666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_489666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489666 prefixEnd_489666 := by exact prefixLift 489666
  have htrace : WordTrace (prefixWord ++ tailWord_489666) baseStart_489666 baseEnd_489666 := by
    simpa [prefixWord, tailWord_489666, baseEnd_489666] using wordTrace_append hprefix tailTrace_489666
  have hstable : (prefixWord ++ tailWord_489666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489666).length < 2 ^ (prefixWord ++ tailWord_489666).sum := by decide
  have hdescent : baseEnd_489666 < baseStart_489666 := by decide
  rcases family_descends (prefixWord ++ tailWord_489666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489784 : List Nat := [2, 1, 2, 1, 3, 1, 5, 2, 4]
def baseStart_489784 : Nat := 118140960795 + 489784 * 2 ^ 59
def prefixEnd_489784 : Nat := 4983230072969 + 3 ^ 40 * 489784 * 2
def baseEnd_489784 : Nat := 111775381725251978465569

theorem tailTrace_489784 : CollatzResearch.WordTrace tailWord_489784 prefixEnd_489784 111775381725251978465569 := by
  unfold tailWord_489784
  simp only [CollatzResearch.WordTrace]
  refine ⟨8931945028801845646358203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11909260038402460861810937 8931945028801845646358203)
  ·
    refine ⟨13397917543202768469537305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8931945028801845646358203 13397917543202768469537305)
    ·
      refine ⟨10048438157402076352152979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13397917543202768469537305 10048438157402076352152979)
      ·
        refine ⟨15072657236103114528229469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10048438157402076352152979 15072657236103114528229469)
        ·
          refine ⟨5652246463538667948086051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15072657236103114528229469 5652246463538667948086051)
          ·
            refine ⟨8478369695308001922129077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5652246463538667948086051 8478369695308001922129077)
            ·
              refine ⟨794847158935125180199601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8478369695308001922129077 794847158935125180199601)
              ·
                refine ⟨596135369201343885149701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 794847158935125180199601 596135369201343885149701)
                ·
                  refine ⟨111775381725251978465569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 596135369201343885149701 111775381725251978465569)
                  ·
                    rfl

theorem cell21_489784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_489784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489784 prefixEnd_489784 := by exact prefixLift 489784
  have htrace : WordTrace (prefixWord ++ tailWord_489784) baseStart_489784 baseEnd_489784 := by
    simpa [prefixWord, tailWord_489784, baseEnd_489784] using wordTrace_append hprefix tailTrace_489784
  have hstable : (prefixWord ++ tailWord_489784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489784).length < 2 ^ (prefixWord ++ tailWord_489784).sum := by decide
  have hdescent : baseEnd_489784 < baseStart_489784 := by decide
  rcases family_descends (prefixWord ++ tailWord_489784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489860 : List Nat := [2, 3, 2, 1, 1, 2, 3, 3, 4]
def baseStart_489860 : Nat := 118140960795 + 489860 * 2 ^ 59
def prefixEnd_489860 : Nat := 4983230072969 + 3 ^ 40 * 489860 * 2
def baseEnd_489860 : Nat := 111792725960692735198747

theorem tailTrace_489860 : CollatzResearch.WordTrace tailWord_489860 prefixEnd_489860 111792725960692735198747 := by
  unfold tailWord_489860
  simp only [CollatzResearch.WordTrace]
  refine ⟨8933331002664178136241517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11911108003552237514988689 8933331002664178136241517)
  ·
    refine ⟨3349999125999066801090569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8933331002664178136241517 3349999125999066801090569)
    ·
      refine ⟨2512499344499300100817927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3349999125999066801090569 2512499344499300100817927)
      ·
        refine ⟨3768749016748950151226891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2512499344499300100817927 3768749016748950151226891)
        ·
          refine ⟨5653123525123425226840337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3768749016748950151226891 5653123525123425226840337)
          ·
            refine ⟨4239842643842568920130253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5653123525123425226840337 4239842643842568920130253)
            ·
              refine ⟨1589940991440963345048845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4239842643842568920130253 1589940991440963345048845)
              ·
                refine ⟨596227871790361254393317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1589940991440963345048845 596227871790361254393317)
                ·
                  refine ⟨111792725960692735198747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 596227871790361254393317 111792725960692735198747)
                  ·
                    rfl

theorem cell21_489860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_489860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489860 prefixEnd_489860 := by exact prefixLift 489860
  have htrace : WordTrace (prefixWord ++ tailWord_489860) baseStart_489860 baseEnd_489860 := by
    simpa [prefixWord, tailWord_489860, baseEnd_489860] using wordTrace_append hprefix tailTrace_489860
  have hstable : (prefixWord ++ tailWord_489860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489860).length < 2 ^ (prefixWord ++ tailWord_489860).sum := by decide
  have hdescent : baseEnd_489860 < baseStart_489860 := by decide
  rcases family_descends (prefixWord ++ tailWord_489860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489970 : List Nat := [3, 2, 1, 4, 2, 1, 3, 1, 4]
def baseStart_489970 : Nat := 118140960795 + 489970 * 2 ^ 59
def prefixEnd_489970 : Nat := 4983230072969 + 3 ^ 40 * 489970 * 2
def baseEnd_489970 : Nat := 111817829459356988365189

theorem tailTrace_489970 : CollatzResearch.WordTrace tailWord_489970 prefixEnd_489970 111817829459356988365189 := by
  unfold tailWord_489970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4467668508732461264746841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11913782689953230039324909 4467668508732461264746841)
  ·
    refine ⟨3350751381549345948560131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4467668508732461264746841 3350751381549345948560131)
    ·
      refine ⟨5026127072324018922840197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3350751381549345948560131 5026127072324018922840197)
      ·
        refine ⟨942398826060753548032537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5026127072324018922840197 942398826060753548032537)
        ·
          refine ⟨706799119545565161024403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 942398826060753548032537 706799119545565161024403)
          ·
            refine ⟨1060198679318347741536605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706799119545565161024403 1060198679318347741536605)
            ·
              refine ⟨397574504744380403076227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1060198679318347741536605 397574504744380403076227)
              ·
                refine ⟨596361757116570604614341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397574504744380403076227 596361757116570604614341)
                ·
                  refine ⟨111817829459356988365189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 596361757116570604614341 111817829459356988365189)
                  ·
                    rfl

theorem cell21_489970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_489970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489970 prefixEnd_489970 := by exact prefixLift 489970
  have htrace : WordTrace (prefixWord ++ tailWord_489970) baseStart_489970 baseEnd_489970 := by
    simpa [prefixWord, tailWord_489970, baseEnd_489970] using wordTrace_append hprefix tailTrace_489970
  have hstable : (prefixWord ++ tailWord_489970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489970).length < 2 ^ (prefixWord ++ tailWord_489970).sum := by decide
  have hdescent : baseEnd_489970 < baseStart_489970 := by decide
  rcases family_descends (prefixWord ++ tailWord_489970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489990 : List Nat := [6, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_489990 : Nat := 118140960795 + 489990 * 2 ^ 59
def prefixEnd_489990 : Nat := 4983230072969 + 3 ^ 40 * 489990 * 2
def baseEnd_489990 : Nat := 111822393731841398031815

theorem tailTrace_489990 : CollatzResearch.WordTrace tailWord_489990 prefixEnd_489990 111822393731841398031815 := by
  unfold tailWord_489990
  simp only [CollatzResearch.WordTrace]
  refine ⟨558481359214293389834857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11914268996571592316476949 558481359214293389834857)
  ·
    refine ⟨418861019410720042376143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 558481359214293389834857 418861019410720042376143)
    ·
      refine ⟨628291529116080063564215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418861019410720042376143 628291529116080063564215)
      ·
        refine ⟨942437293674120095346323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628291529116080063564215 942437293674120095346323)
        ·
          refine ⟨1413655940511180143019485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942437293674120095346323 1413655940511180143019485)
          ·
            refine ⟨530120977691692553632307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1413655940511180143019485 530120977691692553632307)
            ·
              refine ⟨795181466537538830448461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530120977691692553632307 795181466537538830448461)
              ·
                refine ⟨298193049951577061418173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 795181466537538830448461 298193049951577061418173)
                ·
                  refine ⟨111822393731841398031815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 298193049951577061418173 111822393731841398031815)
                  ·
                    rfl

theorem cell21_489990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_489990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489990 prefixEnd_489990 := by exact prefixLift 489990
  have htrace : WordTrace (prefixWord ++ tailWord_489990) baseStart_489990 baseEnd_489990 := by
    simpa [prefixWord, tailWord_489990, baseEnd_489990] using wordTrace_append hprefix tailTrace_489990
  have hstable : (prefixWord ++ tailWord_489990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489990).length < 2 ^ (prefixWord ++ tailWord_489990).sum := by decide
  have hdescent : baseEnd_489990 < baseStart_489990 := by decide
  rcases family_descends (prefixWord ++ tailWord_489990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_489995 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 6]
def baseStart_489995 : Nat := 118140960795 + 489995 * 2 ^ 59
def prefixEnd_489995 : Nat := 4983230072969 + 3 ^ 40 * 489995 * 2
def baseEnd_489995 : Nat := 111823534799962500448471

theorem tailTrace_489995 : CollatzResearch.WordTrace tailWord_489995 prefixEnd_489995 111823534799962500448471 := by
  unfold tailWord_489995
  simp only [CollatzResearch.WordTrace]
  refine ⟨17871585859839274328647439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11914390573226182885764959 17871585859839274328647439)
  ·
    refine ⟨26807378789758911492971159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17871585859839274328647439 26807378789758911492971159)
    ·
      refine ⟨40211068184638367239456739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26807378789758911492971159 40211068184638367239456739)
      ·
        refine ⟨60316602276957550859185109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40211068184638367239456739 60316602276957550859185109)
        ·
          refine ⟨1413670365866192598262151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 60316602276957550859185109 1413670365866192598262151)
          ·
            refine ⟨2120505548799288897393227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413670365866192598262151 2120505548799288897393227)
            ·
              refine ⟨3180758323198933346089841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120505548799288897393227 3180758323198933346089841)
              ·
                refine ⟨2385568742399200009567381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3180758323198933346089841 2385568742399200009567381)
                ·
                  refine ⟨111823534799962500448471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2385568742399200009567381 111823534799962500448471)
                  ·
                    rfl

theorem cell21_489995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 6].length) (baseStart_489995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_489995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_489995 prefixEnd_489995 := by exact prefixLift 489995
  have htrace : WordTrace (prefixWord ++ tailWord_489995) baseStart_489995 baseEnd_489995 := by
    simpa [prefixWord, tailWord_489995, baseEnd_489995] using wordTrace_append hprefix tailTrace_489995
  have hstable : (prefixWord ++ tailWord_489995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_489995).length < 2 ^ (prefixWord ++ tailWord_489995).sum := by decide
  have hdescent : baseEnd_489995 < baseStart_489995 := by decide
  rcases family_descends (prefixWord ++ tailWord_489995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490026 : List Nat := [3, 1, 4, 1, 1, 2, 1, 8]
def baseStart_490026 : Nat := 118140960795 + 490026 * 2 ^ 59
def prefixEnd_490026 : Nat := 4983230072969 + 3 ^ 40 * 490026 * 2
def baseEnd_490026 : Nat := 37276869807437778477247

theorem tailTrace_490026 : CollatzResearch.WordTrace tailWord_490026 prefixEnd_490026 37276869807437778477247 := by
  unfold tailWord_490026
  simp only [CollatzResearch.WordTrace]
  refine ⟨4468179130681741655756483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11915144348484644415350621 4468179130681741655756483)
  ·
    refine ⟨6702268696022612483634725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4468179130681741655756483 6702268696022612483634725)
    ·
      refine ⟨1256675380504239840681511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6702268696022612483634725 1256675380504239840681511)
      ·
        refine ⟨1885013070756359761022267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256675380504239840681511 1885013070756359761022267)
        ·
          refine ⟨2827519606134539641533401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885013070756359761022267 2827519606134539641533401)
          ·
            refine ⟨2120639704600904731150051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2827519606134539641533401 2120639704600904731150051)
            ·
              refine ⟨3180959556901357096725077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120639704600904731150051 3180959556901357096725077)
              ·
                refine ⟨37276869807437778477247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3180959556901357096725077 37276869807437778477247)
                ·
                  rfl

theorem cell21_490026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_490026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_490026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_490026 prefixEnd_490026 := by exact prefixLift 490026
  have htrace : WordTrace (prefixWord ++ tailWord_490026) baseStart_490026 baseEnd_490026 := by
    simpa [prefixWord, tailWord_490026, baseEnd_490026] using wordTrace_append hprefix tailTrace_490026
  have hstable : (prefixWord ++ tailWord_490026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490026).length < 2 ^ (prefixWord ++ tailWord_490026).sum := by decide
  have hdescent : baseEnd_490026 < baseStart_490026 := by decide
  rcases family_descends (prefixWord ++ tailWord_490026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490040 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 7]
def baseStart_490040 : Nat := 118140960795 + 490040 * 2 ^ 59
def prefixEnd_490040 : Nat := 4983230072969 + 3 ^ 40 * 490040 * 2
def baseEnd_490040 : Nat := 111833804413052422198379

theorem tailTrace_490040 : CollatzResearch.WordTrace tailWord_490040 prefixEnd_490040 111833804413052422198379 := by
  unfold tailWord_490040
  simp only [CollatzResearch.WordTrace]
  refine ⟨8936613572338123507017787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11915484763117498009357049 8936613572338123507017787)
  ·
    refine ⟨13404920358507185260526681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8936613572338123507017787 13404920358507185260526681)
    ·
      refine ⟨10053690268880388945395011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13404920358507185260526681 10053690268880388945395011)
      ·
        refine ⟨15080535403320583418092517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10053690268880388945395011 15080535403320583418092517)
        ·
          refine ⟨2827600388122609390892347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15080535403320583418092517 2827600388122609390892347)
          ·
            refine ⟨4241400582183914086338521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827600388122609390892347 4241400582183914086338521)
            ·
              refine ⟨3181050436637935564753891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4241400582183914086338521 3181050436637935564753891)
              ·
                refine ⟨4771575654956903347130837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3181050436637935564753891 4771575654956903347130837)
                ·
                  refine ⟨111833804413052422198379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4771575654956903347130837 111833804413052422198379)
                  ·
                    rfl

theorem cell21_490040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_490040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_490040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_490040 prefixEnd_490040 := by exact prefixLift 490040
  have htrace : WordTrace (prefixWord ++ tailWord_490040) baseStart_490040 baseEnd_490040 := by
    simpa [prefixWord, tailWord_490040, baseEnd_490040] using wordTrace_append hprefix tailTrace_490040
  have hstable : (prefixWord ++ tailWord_490040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490040).length < 2 ^ (prefixWord ++ tailWord_490040).sum := by decide
  have hdescent : baseEnd_490040 < baseStart_490040 := by decide
  rcases family_descends (prefixWord ++ tailWord_490040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490122 : List Nat := [3, 1, 2, 3, 4, 1, 1, 2, 4]
def baseStart_490122 : Nat := 118140960795 + 490122 * 2 ^ 59
def prefixEnd_490122 : Nat := 4983230072969 + 3 ^ 40 * 490122 * 2
def baseEnd_490122 : Nat := 111852517930238501831545

theorem tailTrace_490122 : CollatzResearch.WordTrace tailWord_490122 prefixEnd_490122 111852517930238501831545 := by
  unfold tailWord_490122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4469054482594793754630155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11917478620252783345680413 4469054482594793754630155)
  ·
    refine ⟨6703581723892190631945233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4469054482594793754630155 6703581723892190631945233)
    ·
      refine ⟨5027686292919142973958925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6703581723892190631945233 5027686292919142973958925)
      ·
        refine ⟨1885382359844678615234597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5027686292919142973958925 1885382359844678615234597)
        ·
          refine ⟨353509192470877240356487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1885382359844678615234597 353509192470877240356487)
          ·
            refine ⟨530263788706315860534731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353509192470877240356487 530263788706315860534731)
            ·
              refine ⟨795395683059473790802097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530263788706315860534731 795395683059473790802097)
              ·
                refine ⟨596546762294605343101573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795395683059473790802097 596546762294605343101573)
                ·
                  refine ⟨111852517930238501831545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 596546762294605343101573 111852517930238501831545)
                  ·
                    rfl

theorem cell21_490122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_490122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_490122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_490122 prefixEnd_490122 := by exact prefixLift 490122
  have htrace : WordTrace (prefixWord ++ tailWord_490122) baseStart_490122 baseEnd_490122 := by
    simpa [prefixWord, tailWord_490122, baseEnd_490122] using wordTrace_append hprefix tailTrace_490122
  have hstable : (prefixWord ++ tailWord_490122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490122).length < 2 ^ (prefixWord ++ tailWord_490122).sum := by decide
  have hdescent : baseEnd_490122 < baseStart_490122 := by decide
  rcases family_descends (prefixWord ++ tailWord_490122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490167 : List Nat := [1, 1, 3, 1, 6, 2, 1, 3, 3]
def baseStart_490167 : Nat := 118140960795 + 490167 * 2 ^ 59
def prefixEnd_490167 : Nat := 4983230072969 + 3 ^ 40 * 490167 * 2
def baseEnd_490167 : Nat := 111862787543328423581453

theorem tailTrace_490167 : CollatzResearch.WordTrace tailWord_490167 prefixEnd_490167 111862787543328423581453 := by
  unfold tailWord_490167
  simp only [CollatzResearch.WordTrace]
  refine ⟨17877859215216147703908755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11918572810144098469272503 17877859215216147703908755)
  ·
    refine ⟨26816788822824221555863133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17877859215216147703908755 26816788822824221555863133)
    ·
      refine ⟨10056295808559083083448675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26816788822824221555863133 10056295808559083083448675)
      ·
        refine ⟨15084443712838624625173013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10056295808559083083448675 15084443712838624625173013)
        ·
          refine ⟨707083299039310529304985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15084443712838624625173013 707083299039310529304985)
          ·
            refine ⟨530312474279482896978739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707083299039310529304985 530312474279482896978739)
            ·
              refine ⟨795468711419224345468109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530312474279482896978739 795468711419224345468109)
              ·
                refine ⟨298300766782209129550541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 795468711419224345468109 298300766782209129550541)
                ·
                  refine ⟨111862787543328423581453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 298300766782209129550541 111862787543328423581453)
                  ·
                    rfl

theorem cell21_490167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 3].length) (baseStart_490167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_490167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_490167 prefixEnd_490167 := by exact prefixLift 490167
  have htrace : WordTrace (prefixWord ++ tailWord_490167) baseStart_490167 baseEnd_490167 := by
    simpa [prefixWord, tailWord_490167, baseEnd_490167] using wordTrace_append hprefix tailTrace_490167
  have hstable : (prefixWord ++ tailWord_490167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490167).length < 2 ^ (prefixWord ++ tailWord_490167).sum := by decide
  have hdescent : baseEnd_490167 < baseStart_490167 := by decide
  rcases family_descends (prefixWord ++ tailWord_490167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490268 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 7]
def baseStart_490268 : Nat := 118140960795 + 490268 * 2 ^ 59
def prefixEnd_490268 : Nat := 4983230072969 + 3 ^ 40 * 490268 * 2
def baseEnd_490268 : Nat := 111885837119374692397913

theorem tailTrace_490268 : CollatzResearch.WordTrace tailWord_490268 prefixEnd_490268 111885837119374692397913 := by
  unfold tailWord_490268
  simp only [CollatzResearch.WordTrace]
  refine ⟨8940771493925120976667729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11921028658566827968890305 8940771493925120976667729)
  ·
    refine ⟨6705578620443840732500797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8940771493925120976667729 6705578620443840732500797)
    ·
      refine ⟨2514591982666440274687799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6705578620443840732500797 2514591982666440274687799)
      ·
        refine ⟨3771887973999660412031699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2514591982666440274687799 3771887973999660412031699)
        ·
          refine ⟨5657831960999490618047549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3771887973999660412031699 5657831960999490618047549)
          ·
            refine ⟨2121686985374808981767831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5657831960999490618047549 2121686985374808981767831)
            ·
              refine ⟨3182530478062213472651747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2121686985374808981767831 3182530478062213472651747)
              ·
                refine ⟨4773795717093320208977621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3182530478062213472651747 4773795717093320208977621)
                ·
                  refine ⟨111885837119374692397913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4773795717093320208977621 111885837119374692397913)
                  ·
                    rfl

theorem cell21_490268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_490268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_490268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_490268 prefixEnd_490268 := by exact prefixLift 490268
  have htrace : WordTrace (prefixWord ++ tailWord_490268) baseStart_490268 baseEnd_490268 := by
    simpa [prefixWord, tailWord_490268, baseEnd_490268] using wordTrace_append hprefix tailTrace_490268
  have hstable : (prefixWord ++ tailWord_490268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490268).length < 2 ^ (prefixWord ++ tailWord_490268).sum := by decide
  have hdescent : baseEnd_490268 < baseStart_490268 := by decide
  rcases family_descends (prefixWord ++ tailWord_490268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490302 : List Nat := [4, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_490302 : Nat := 118140960795 + 490302 * 2 ^ 59
def prefixEnd_490302 : Nat := 4983230072969 + 3 ^ 40 * 490302 * 2
def baseEnd_490302 : Nat := 111893596382598188831177

theorem tailTrace_490302 : CollatzResearch.WordTrace tailWord_490302 prefixEnd_490302 111893596382598188831177 := by
  unfold tailWord_490302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2235347883715883220009145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11921855379818043840048773 2235347883715883220009145)
  ·
    refine ⟨1676510912786912415006859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2235347883715883220009145 1676510912786912415006859)
    ·
      refine ⟨2514766369180368622510289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1676510912786912415006859 2514766369180368622510289)
      ·
        refine ⟨1886074776885276466882717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2514766369180368622510289 1886074776885276466882717)
        ·
          refine ⟨707278041331978675081019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1886074776885276466882717 707278041331978675081019)
          ·
            refine ⟨1060917061997968012621529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707278041331978675081019 1060917061997968012621529)
            ·
              refine ⟨795687796498476009466147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1060917061997968012621529 795687796498476009466147)
              ·
                refine ⟨1193531694747714014199221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795687796498476009466147 1193531694747714014199221)
                ·
                  refine ⟨111893596382598188831177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1193531694747714014199221 111893596382598188831177)
                  ·
                    rfl

theorem cell21_490302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_490302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_490302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_490302 prefixEnd_490302 := by exact prefixLift 490302
  have htrace : WordTrace (prefixWord ++ tailWord_490302) baseStart_490302 baseEnd_490302 := by
    simpa [prefixWord, tailWord_490302, baseEnd_490302] using wordTrace_append hprefix tailTrace_490302
  have hstable : (prefixWord ++ tailWord_490302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490302).length < 2 ^ (prefixWord ++ tailWord_490302).sum := by decide
  have hdescent : baseEnd_490302 < baseStart_490302 := by decide
  rcases family_descends (prefixWord ++ tailWord_490302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490330 : List Nat := [3, 1, 1, 2, 1, 4, 4, 5]
def baseStart_490330 : Nat := 118140960795 + 490330 * 2 ^ 59
def prefixEnd_490330 : Nat := 4983230072969 + 3 ^ 40 * 490330 * 2
def baseEnd_490330 : Nat := 37299995454692120788151

theorem tailTrace_490330 : CollatzResearch.WordTrace tailWord_490330 prefixEnd_490330 37299995454692120788151 := by
  unfold tailWord_490330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4470951078406406635523111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11922536209083751028061629 4470951078406406635523111)
  ·
    refine ⟨6706426617609609953284667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4470951078406406635523111 6706426617609609953284667)
    ·
      refine ⟨10059639926414414929927001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6706426617609609953284667 10059639926414414929927001)
      ·
        refine ⟨7544729944810811197445251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10059639926414414929927001 7544729944810811197445251)
        ·
          refine ⟨11317094917216216796167877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7544729944810811197445251 11317094917216216796167877)
          ·
            refine ⟨2121955296978040649281477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11317094917216216796167877 2121955296978040649281477)
            ·
              refine ⟨397866618183382621740277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2121955296978040649281477 397866618183382621740277)
              ·
                refine ⟨37299995454692120788151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 397866618183382621740277 37299995454692120788151)
                ·
                  rfl

theorem cell21_490330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_490330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_490330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_490330 prefixEnd_490330 := by exact prefixLift 490330
  have htrace : WordTrace (prefixWord ++ tailWord_490330) baseStart_490330 baseEnd_490330 := by
    simpa [prefixWord, tailWord_490330, baseEnd_490330] using wordTrace_append hprefix tailTrace_490330
  have hstable : (prefixWord ++ tailWord_490330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490330).length < 2 ^ (prefixWord ++ tailWord_490330).sum := by decide
  have hdescent : baseEnd_490330 < baseStart_490330 := by decide
  rcases family_descends (prefixWord ++ tailWord_490330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490361 : List Nat := [1, 2, 1, 3, 2, 5, 1, 1, 5]
def baseStart_490361 : Nat := 118140960795 + 490361 * 2 ^ 59
def prefixEnd_490361 : Nat := 4983230072969 + 3 ^ 40 * 490361 * 2
def baseEnd_490361 : Nat := 111907060986427197347723

theorem tailTrace_490361 : CollatzResearch.WordTrace tailWord_490361 prefixEnd_490361 111907060986427197347723 := by
  unfold tailWord_490361
  simp only [CollatzResearch.WordTrace]
  refine ⟨17884934976513318836470937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11923289984342212557647291 17884934976513318836470937)
  ·
    refine ⟨13413701232384989127353203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17884934976513318836470937 13413701232384989127353203)
    ·
      refine ⟨20120551848577483691029805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13413701232384989127353203 20120551848577483691029805)
      ·
        refine ⟨7545206943216556384136177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20120551848577483691029805 7545206943216556384136177)
        ·
          refine ⟨5658905207412417288102133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7545206943216556384136177 5658905207412417288102133)
          ·
            refine ⟨530522363194914120759575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5658905207412417288102133 530522363194914120759575)
            ·
              refine ⟨795783544792371181139363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530522363194914120759575 795783544792371181139363)
              ·
                refine ⟨1193675317188556771709045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795783544792371181139363 1193675317188556771709045)
                ·
                  refine ⟨111907060986427197347723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1193675317188556771709045 111907060986427197347723)
                  ·
                    rfl

theorem cell21_490361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 5].length) (baseStart_490361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_490361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_490361 prefixEnd_490361 := by exact prefixLift 490361
  have htrace : WordTrace (prefixWord ++ tailWord_490361) baseStart_490361 baseEnd_490361 := by
    simpa [prefixWord, tailWord_490361, baseEnd_490361] using wordTrace_append hprefix tailTrace_490361
  have hstable : (prefixWord ++ tailWord_490361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490361).length < 2 ^ (prefixWord ++ tailWord_490361).sum := by decide
  have hdescent : baseEnd_490361 < baseStart_490361 := by decide
  rcases family_descends (prefixWord ++ tailWord_490361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490389 : List Nat := [1, 3, 2, 1, 1, 4, 2, 7]
def baseStart_490389 : Nat := 118140960795 + 490389 * 2 ^ 59
def prefixEnd_490389 : Nat := 4983230072969 + 3 ^ 40 * 490389 * 2
def baseEnd_490389 : Nat := 37304483655968456960333

theorem tailTrace_490389 : CollatzResearch.WordTrace tailWord_490389 prefixEnd_490389 37304483655968456960333 := by
  unfold tailWord_490389
  simp only [CollatzResearch.WordTrace]
  refine ⟨17885956220411879618490221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11923970813607919745660147 17885956220411879618490221)
  ·
    refine ⟨6707233582654454856933833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17885956220411879618490221 6707233582654454856933833)
    ·
      refine ⟨5030425186990841142700375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6707233582654454856933833 5030425186990841142700375)
      ·
        refine ⟨7545637780486261714050563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5030425186990841142700375 7545637780486261714050563)
        ·
          refine ⟨11318456670729392571075845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7545637780486261714050563 11318456670729392571075845)
          ·
            refine ⟨2122210625761761107076721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11318456670729392571075845 2122210625761761107076721)
            ·
              refine ⟨1591657969321320830307541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2122210625761761107076721 1591657969321320830307541)
              ·
                refine ⟨37304483655968456960333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1591657969321320830307541 37304483655968456960333)
                ·
                  rfl

theorem cell21_490389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 7].length) (baseStart_490389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_490389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_490389 prefixEnd_490389 := by exact prefixLift 490389
  have htrace : WordTrace (prefixWord ++ tailWord_490389) baseStart_490389 baseEnd_490389 := by
    simpa [prefixWord, tailWord_490389, baseEnd_490389] using wordTrace_append hprefix tailTrace_490389
  have hstable : (prefixWord ++ tailWord_490389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490389).length < 2 ^ (prefixWord ++ tailWord_490389).sum := by decide
  have hdescent : baseEnd_490389 < baseStart_490389 := by decide
  rcases family_descends (prefixWord ++ tailWord_490389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490558 : List Nat := [4, 2, 1, 3, 1, 1, 2, 7]
def baseStart_490558 : Nat := 118140960795 + 490558 * 2 ^ 59
def prefixEnd_490558 : Nat := 4983230072969 + 3 ^ 40 * 490558 * 2
def baseEnd_490558 : Nat := 37317339690132877521329

theorem tailTrace_490558 : CollatzResearch.WordTrace tailWord_490558 prefixEnd_490558 37317339690132877521329 := by
  unfold tailWord_490558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2236515019599952685174041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11928080104533080987594885 2236515019599952685174041)
  ·
    refine ⟨1677386264699964513880531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2236515019599952685174041 1677386264699964513880531)
    ·
      refine ⟨2516079397049946770820797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1677386264699964513880531 2516079397049946770820797)
      ·
        refine ⟨943529773893730039057799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2516079397049946770820797 943529773893730039057799)
        ·
          refine ⟨1415294660840595058586699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943529773893730039057799 1415294660840595058586699)
          ·
            refine ⟨2122941991260892587880049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415294660840595058586699 2122941991260892587880049)
            ·
              refine ⟨1592206493445669440910037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2122941991260892587880049 1592206493445669440910037)
              ·
                refine ⟨37317339690132877521329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1592206493445669440910037 37317339690132877521329)
                ·
                  rfl

theorem cell21_490558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_490558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_490558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_490558 prefixEnd_490558 := by exact prefixLift 490558
  have htrace : WordTrace (prefixWord ++ tailWord_490558) baseStart_490558 baseEnd_490558 := by
    simpa [prefixWord, tailWord_490558, baseEnd_490558] using wordTrace_append hprefix tailTrace_490558
  have hstable : (prefixWord ++ tailWord_490558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490558).length < 2 ^ (prefixWord ++ tailWord_490558).sum := by decide
  have hdescent : baseEnd_490558 < baseStart_490558 := by decide
  rcases family_descends (prefixWord ++ tailWord_490558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490631 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 9]
def baseStart_490631 : Nat := 118140960795 + 490631 * 2 ^ 59
def prefixEnd_490631 : Nat := 4983230072969 + 3 ^ 40 * 490631 * 2
def baseEnd_490631 : Nat := 111968678664966727847171

theorem tailTrace_490631 : CollatzResearch.WordTrace tailWord_490631 prefixEnd_490631 111968678664966727847171 := by
  unfold tailWord_490631
  simp only [CollatzResearch.WordTrace]
  refine ⟨17894782685535154948799747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11929855123690103299199831 17894782685535154948799747)
  ·
    refine ⟨26842174028302732423199621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17894782685535154948799747 26842174028302732423199621)
    ·
      refine ⟨5032907630306762329349929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26842174028302732423199621 5032907630306762329349929)
      ·
        refine ⟨3774680722730071747012447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5032907630306762329349929 3774680722730071747012447)
        ·
          refine ⟨5662021084095107620518671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3774680722730071747012447 5662021084095107620518671)
          ·
            refine ⟨8493031626142661430778007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5662021084095107620518671 8493031626142661430778007)
            ·
              refine ⟨12739547439213992146167011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8493031626142661430778007 12739547439213992146167011)
              ·
                refine ⟨19109321158820988219250517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12739547439213992146167011 19109321158820988219250517)
                ·
                  refine ⟨111968678664966727847171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19109321158820988219250517 111968678664966727847171)
                  ·
                    rfl

theorem cell21_490631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 9].length) (baseStart_490631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_490631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_490631 prefixEnd_490631 := by exact prefixLift 490631
  have htrace : WordTrace (prefixWord ++ tailWord_490631) baseStart_490631 baseEnd_490631 := by
    simpa [prefixWord, tailWord_490631, baseEnd_490631] using wordTrace_append hprefix tailTrace_490631
  have hstable : (prefixWord ++ tailWord_490631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490631).length < 2 ^ (prefixWord ++ tailWord_490631).sum := by decide
  have hdescent : baseEnd_490631 < baseStart_490631 := by decide
  rcases family_descends (prefixWord ++ tailWord_490631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490648 : List Nat := [2, 1, 2, 4, 2, 1, 1, 3, 5]
def baseStart_490648 : Nat := 118140960795 + 490648 * 2 ^ 59
def prefixEnd_490648 : Nat := 4983230072969 + 3 ^ 40 * 490648 * 2
def baseEnd_490648 : Nat := 111972558296578476063803

theorem tailTrace_490648 : CollatzResearch.WordTrace tailWord_490648 prefixEnd_490648 111972558296578476063803 := by
  unfold tailWord_490648
  simp only [CollatzResearch.WordTrace]
  refine ⟨8947701363236783426084299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11930268484315711234779065 8947701363236783426084299)
  ·
    refine ⟨13421552044855175139126449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8947701363236783426084299 13421552044855175139126449)
    ·
      refine ⟨10066164033641381354344837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13421552044855175139126449 10066164033641381354344837)
      ·
        refine ⟨1887405756307759003939657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10066164033641381354344837 1887405756307759003939657)
        ·
          refine ⟨1415554317230819252954743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1887405756307759003939657 1415554317230819252954743)
          ·
            refine ⟨2123331475846228879432115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415554317230819252954743 2123331475846228879432115)
            ·
              refine ⟨3184997213769343319148173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2123331475846228879432115 3184997213769343319148173)
              ·
                refine ⟨1194373955163503744680565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3184997213769343319148173 1194373955163503744680565)
                ·
                  refine ⟨111972558296578476063803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1194373955163503744680565 111972558296578476063803)
                  ·
                    rfl

theorem cell21_490648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_490648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_490648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_490648 prefixEnd_490648 := by exact prefixLift 490648
  have htrace : WordTrace (prefixWord ++ tailWord_490648) baseStart_490648 baseEnd_490648 := by
    simpa [prefixWord, tailWord_490648, baseEnd_490648] using wordTrace_append hprefix tailTrace_490648
  have hstable : (prefixWord ++ tailWord_490648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490648).length < 2 ^ (prefixWord ++ tailWord_490648).sum := by decide
  have hdescent : baseEnd_490648 < baseStart_490648 := by decide
  rcases family_descends (prefixWord ++ tailWord_490648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490755 : List Nat := [1, 1, 1, 3, 2, 5, 2, 2, 4]
def baseStart_490755 : Nat := 118140960795 + 490755 * 2 ^ 59
def prefixEnd_490755 : Nat := 4983230072969 + 3 ^ 40 * 490755 * 2
def baseEnd_490755 : Nat := 111996977154370067780251

theorem tailTrace_490755 : CollatzResearch.WordTrace tailWord_490755 prefixEnd_490755 111996977154370067780251 := by
  unfold tailWord_490755
  simp only [CollatzResearch.WordTrace]
  refine ⟨17899305337085924126313719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11932870224723949417542479 17899305337085924126313719)
  ·
    refine ⟨26848958005628886189470579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17899305337085924126313719 26848958005628886189470579)
    ·
      refine ⟨40273437008443329284205869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26848958005628886189470579 40273437008443329284205869)
      ·
        refine ⟨15102538878166248481577201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40273437008443329284205869 15102538878166248481577201)
        ·
          refine ⟨11326904158624686361182901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15102538878166248481577201 11326904158624686361182901)
          ·
            refine ⟨1061897264871064346360897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11326904158624686361182901 1061897264871064346360897)
            ·
              refine ⟨796422948653298259770673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1061897264871064346360897 796422948653298259770673)
              ·
                refine ⟨597317211489973694828005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796422948653298259770673 597317211489973694828005)
                ·
                  refine ⟨111996977154370067780251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 597317211489973694828005 111996977154370067780251)
                  ·
                    rfl

theorem cell21_490755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 4].length) (baseStart_490755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_490755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_490755 prefixEnd_490755 := by exact prefixLift 490755
  have htrace : WordTrace (prefixWord ++ tailWord_490755) baseStart_490755 baseEnd_490755 := by
    simpa [prefixWord, tailWord_490755, baseEnd_490755] using wordTrace_append hprefix tailTrace_490755
  have hstable : (prefixWord ++ tailWord_490755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490755).length < 2 ^ (prefixWord ++ tailWord_490755).sum := by decide
  have hdescent : baseEnd_490755 < baseStart_490755 := by decide
  rcases family_descends (prefixWord ++ tailWord_490755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490806 : List Nat := [5, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_490806 : Nat := 118140960795 + 490806 * 2 ^ 59
def prefixEnd_490806 : Nat := 4983230072969 + 3 ^ 40 * 490806 * 2
def baseEnd_490806 : Nat := 112008616049205312430147

theorem tailTrace_490806 : CollatzResearch.WordTrace tailWord_490806 prefixEnd_490806 112008616049205312430147 := by
  unfold tailWord_490806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1118822841243822489776267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11934110306600773224280181 1118822841243822489776267)
  ·
    refine ⟨1678234261865733734664401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1118822841243822489776267 1678234261865733734664401)
    ·
      refine ⟨1258675696399300300998301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1678234261865733734664401 1258675696399300300998301)
      ·
        refine ⟨472003386149737612874363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1258675696399300300998301 472003386149737612874363)
        ·
          refine ⟨708005079224606419311545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472003386149737612874363 708005079224606419311545)
          ·
            refine ⟨531003809418454814483659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708005079224606419311545 531003809418454814483659)
            ·
              refine ⟨796505714127682221725489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531003809418454814483659 796505714127682221725489)
              ·
                refine ⟨597379285595761666294117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796505714127682221725489 597379285595761666294117)
                ·
                  refine ⟨112008616049205312430147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 597379285595761666294117 112008616049205312430147)
                  ·
                    rfl

theorem cell21_490806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_490806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_490806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_490806 prefixEnd_490806 := by exact prefixLift 490806
  have htrace : WordTrace (prefixWord ++ tailWord_490806) baseStart_490806 baseEnd_490806 := by
    simpa [prefixWord, tailWord_490806, baseEnd_490806] using wordTrace_append hprefix tailTrace_490806
  have hstable : (prefixWord ++ tailWord_490806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490806).length < 2 ^ (prefixWord ++ tailWord_490806).sum := by decide
  have hdescent : baseEnd_490806 < baseStart_490806 := by decide
  rcases family_descends (prefixWord ++ tailWord_490806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490817 : List Nat := [1, 2, 5, 2, 1, 2, 2, 1, 5]
def baseStart_490817 : Nat := 118140960795 + 490817 * 2 ^ 59
def prefixEnd_490817 : Nat := 4983230072969 + 3 ^ 40 * 490817 * 2
def baseEnd_490817 : Nat := 112011126399071737746791

theorem tailTrace_490817 : CollatzResearch.WordTrace tailWord_490817 prefixEnd_490817 112011126399071737746791 := by
  unfold tailWord_490817
  simp only [CollatzResearch.WordTrace]
  refine ⟨17901566662861308715070705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11934377775240872476713803 17901566662861308715070705)
  ·
    refine ⟨13426174997145981536303029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17901566662861308715070705 13426174997145981536303029)
    ·
      refine ⟨1258703905982435769028409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13426174997145981536303029 1258703905982435769028409)
      ·
        refine ⟨944027929486826826771307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1258703905982435769028409 944027929486826826771307)
        ·
          refine ⟨1416041894230240240156961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944027929486826826771307 1416041894230240240156961)
          ·
            refine ⟨1062031420672680180117721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1416041894230240240156961 1062031420672680180117721)
            ·
              refine ⟨796523565504510135088291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062031420672680180117721 796523565504510135088291)
              ·
                refine ⟨1194785348256765202632437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796523565504510135088291 1194785348256765202632437)
                ·
                  refine ⟨112011126399071737746791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1194785348256765202632437 112011126399071737746791)
                  ·
                    rfl

theorem cell21_490817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_490817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_490817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_490817 prefixEnd_490817 := by exact prefixLift 490817
  have htrace : WordTrace (prefixWord ++ tailWord_490817) baseStart_490817 baseEnd_490817 := by
    simpa [prefixWord, tailWord_490817, baseEnd_490817] using wordTrace_append hprefix tailTrace_490817
  have hstable : (prefixWord ++ tailWord_490817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490817).length < 2 ^ (prefixWord ++ tailWord_490817).sum := by decide
  have hdescent : baseEnd_490817 < baseStart_490817 := by decide
  rcases family_descends (prefixWord ++ tailWord_490817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490882 : List Nat := [3, 4, 2, 1, 1, 3, 2, 1, 4]
def baseStart_490882 : Nat := 118140960795 + 490882 * 2 ^ 59
def prefixEnd_490882 : Nat := 4983230072969 + 3 ^ 40 * 490882 * 2
def baseEnd_490882 : Nat := 112025960284646069163325

theorem tailTrace_490882 : CollatzResearch.WordTrace tailWord_490882 prefixEnd_490882 112025960284646069163325 := by
  unfold tailWord_490882
  simp only [CollatzResearch.WordTrace]
  refine ⟨4475984351906456204046725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11935958271750549877457933 4475984351906456204046725)
  ·
    refine ⟨839247065982460538258761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4475984351906456204046725 839247065982460538258761)
    ·
      refine ⟨629435299486845403694071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 839247065982460538258761 629435299486845403694071)
      ·
        refine ⟨944152949230268105541107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629435299486845403694071 944152949230268105541107)
        ·
          refine ⟨1416229423845402158311661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944152949230268105541107 1416229423845402158311661)
          ·
            refine ⟨531086033942025809366873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1416229423845402158311661 531086033942025809366873)
            ·
              refine ⟨398314525456519357025155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531086033942025809366873 398314525456519357025155)
              ·
                refine ⟨597471788184779035537733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398314525456519357025155 597471788184779035537733)
                ·
                  refine ⟨112025960284646069163325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 597471788184779035537733 112025960284646069163325)
                  ·
                    rfl

theorem cell21_490882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_490882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_490882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_490882 prefixEnd_490882 := by exact prefixLift 490882
  have htrace : WordTrace (prefixWord ++ tailWord_490882) baseStart_490882 baseEnd_490882 := by
    simpa [prefixWord, tailWord_490882, baseEnd_490882] using wordTrace_append hprefix tailTrace_490882
  have hstable : (prefixWord ++ tailWord_490882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490882).length < 2 ^ (prefixWord ++ tailWord_490882).sum := by decide
  have hdescent : baseEnd_490882 < baseStart_490882 := by decide
  rcases family_descends (prefixWord ++ tailWord_490882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490935 : List Nat := [1, 1, 3, 1, 3, 2, 2, 3, 5]
def baseStart_490935 : Nat := 118140960795 + 490935 * 2 ^ 59
def prefixEnd_490935 : Nat := 4983230072969 + 3 ^ 40 * 490935 * 2
def baseEnd_490935 : Nat := 112038055606729754779883

theorem tailTrace_490935 : CollatzResearch.WordTrace tailWord_490935 prefixEnd_490935 112038055606729754779883 := by
  unfold tailWord_490935
  simp only [CollatzResearch.WordTrace]
  refine ⟨17905870476433814867866259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11937246984289209911910839 17905870476433814867866259)
  ·
    refine ⟨26858805714650722301799389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17905870476433814867866259 26858805714650722301799389)
    ·
      refine ⟨10072052142994020863174771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26858805714650722301799389 10072052142994020863174771)
      ·
        refine ⟨15108078214491031294762157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10072052142994020863174771 15108078214491031294762157)
        ·
          refine ⟨5665529330434136735535809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15108078214491031294762157 5665529330434136735535809)
          ·
            refine ⟨4249146997825602551651857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5665529330434136735535809 4249146997825602551651857)
            ·
              refine ⟨3186860248369201913738893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4249146997825602551651857 3186860248369201913738893)
              ·
                refine ⟨1195072593138450717652085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3186860248369201913738893 1195072593138450717652085)
                ·
                  refine ⟨112038055606729754779883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1195072593138450717652085 112038055606729754779883)
                  ·
                    rfl

theorem cell21_490935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 5].length) (baseStart_490935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_490935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_490935 prefixEnd_490935 := by exact prefixLift 490935
  have htrace : WordTrace (prefixWord ++ tailWord_490935) baseStart_490935 baseEnd_490935 := by
    simpa [prefixWord, tailWord_490935, baseEnd_490935] using wordTrace_append hprefix tailTrace_490935
  have hstable : (prefixWord ++ tailWord_490935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490935).length < 2 ^ (prefixWord ++ tailWord_490935).sum := by decide
  have hdescent : baseEnd_490935 < baseStart_490935 := by decide
  rcases family_descends (prefixWord ++ tailWord_490935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490969 : List Nat := [1, 2, 1, 2, 4, 3, 2, 3, 3]
def baseStart_490969 : Nat := 118140960795 + 490969 * 2 ^ 59
def prefixEnd_490969 : Nat := 4983230072969 + 3 ^ 40 * 490969 * 2
def baseEnd_490969 : Nat := 112045814869953251213147

theorem tailTrace_490969 : CollatzResearch.WordTrace tailWord_490969 prefixEnd_490969 112045814869953251213147 := by
  unfold tailWord_490969
  simp only [CollatzResearch.WordTrace]
  refine ⟨17907110558310638674603961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11938073705540425783069307 17907110558310638674603961)
  ·
    refine ⟨13430332918732979005952971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17907110558310638674603961 13430332918732979005952971)
    ·
      refine ⟨20145499378099468508929457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13430332918732979005952971 20145499378099468508929457)
      ·
        refine ⟨15109124533574601381697093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20145499378099468508929457 15109124533574601381697093)
        ·
          refine ⟨2832960850045237759068205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15109124533574601381697093 2832960850045237759068205)
          ·
            refine ⟨1062360318766964159650577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2832960850045237759068205 1062360318766964159650577)
            ·
              refine ⟨796770239075223119737933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062360318766964159650577 796770239075223119737933)
              ·
                refine ⟨298788839653208669901725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 796770239075223119737933 298788839653208669901725)
                ·
                  refine ⟨112045814869953251213147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 298788839653208669901725 112045814869953251213147)
                  ·
                    rfl

theorem cell21_490969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 3].length) (baseStart_490969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_490969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_490969 prefixEnd_490969 := by exact prefixLift 490969
  have htrace : WordTrace (prefixWord ++ tailWord_490969) baseStart_490969 baseEnd_490969 := by
    simpa [prefixWord, tailWord_490969, baseEnd_490969] using wordTrace_append hprefix tailTrace_490969
  have hstable : (prefixWord ++ tailWord_490969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490969).length < 2 ^ (prefixWord ++ tailWord_490969).sum := by decide
  have hdescent : baseEnd_490969 < baseStart_490969 := by decide
  rcases family_descends (prefixWord ++ tailWord_490969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_490983 : List Nat := [1, 1, 5, 2, 1, 2, 3, 2, 4]
def baseStart_490983 : Nat := 118140960795 + 490983 * 2 ^ 59
def prefixEnd_490983 : Nat := 4983230072969 + 3 ^ 40 * 490983 * 2
def baseEnd_490983 : Nat := 112049009860692337979785

theorem tailTrace_490983 : CollatzResearch.WordTrace tailWord_490983 prefixEnd_490983 112049009860692337979785 := by
  unfold tailWord_490983
  simp only [CollatzResearch.WordTrace]
  refine ⟨17907621180259919065613603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11938414120173279377075735 17907621180259919065613603)
  ·
    refine ⟨26861431770389878598420405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17907621180259919065613603 26861431770389878598420405)
    ·
      refine ⟨2518259228474051118601913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26861431770389878598420405 2518259228474051118601913)
      ·
        refine ⟨1888694421355538338951435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2518259228474051118601913 1888694421355538338951435)
        ·
          refine ⟨2833041632033307508427153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1888694421355538338951435 2833041632033307508427153)
          ·
            refine ⟨2124781224024980631320365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2833041632033307508427153 2124781224024980631320365)
            ·
              refine ⟨796792959009367736745137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2124781224024980631320365 796792959009367736745137)
              ·
                refine ⟨597594719257025802558853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796792959009367736745137 597594719257025802558853)
                ·
                  refine ⟨112049009860692337979785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 597594719257025802558853 112049009860692337979785)
                  ·
                    rfl

theorem cell21_490983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 4].length) (baseStart_490983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_490983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_490983 prefixEnd_490983 := by exact prefixLift 490983
  have htrace : WordTrace (prefixWord ++ tailWord_490983) baseStart_490983 baseEnd_490983 := by
    simpa [prefixWord, tailWord_490983, baseEnd_490983] using wordTrace_append hprefix tailTrace_490983
  have hstable : (prefixWord ++ tailWord_490983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_490983).length < 2 ^ (prefixWord ++ tailWord_490983).sum := by decide
  have hdescent : baseEnd_490983 < baseStart_490983 := by decide
  rcases family_descends (prefixWord ++ tailWord_490983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491025 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 8]
def baseStart_491025 : Nat := 118140960795 + 491025 * 2 ^ 59
def prefixEnd_491025 : Nat := 4983230072969 + 3 ^ 40 * 491025 * 2
def baseEnd_491025 : Nat := 112058594832909598279699

theorem tailTrace_491025 : CollatzResearch.WordTrace tailWord_491025 prefixEnd_491025 112058594832909598279699 := by
  unfold tailWord_491025
  simp only [CollatzResearch.WordTrace]
  refine ⟨17909153046107760238642529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11939435364071840159095019 17909153046107760238642529)
  ·
    refine ⟨13431864784580820178981897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17909153046107760238642529 13431864784580820178981897)
    ·
      refine ⟨10073898588435615134236423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13431864784580820178981897 10073898588435615134236423)
      ·
        refine ⟨15110847882653422701354635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10073898588435615134236423 15110847882653422701354635)
        ·
          refine ⟨22666271823980134052031953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15110847882653422701354635 22666271823980134052031953)
          ·
            refine ⟨16999703867985100539023965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22666271823980134052031953 16999703867985100539023965)
            ·
              refine ⟨6374888950494412702133987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16999703867985100539023965 6374888950494412702133987)
              ·
                refine ⟨9562333425741619053200981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6374888950494412702133987 9562333425741619053200981)
                ·
                  refine ⟨112058594832909598279699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9562333425741619053200981 112058594832909598279699)
                  ·
                    rfl

theorem cell21_491025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_491025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491025 prefixEnd_491025 := by exact prefixLift 491025
  have htrace : WordTrace (prefixWord ++ tailWord_491025) baseStart_491025 baseEnd_491025 := by
    simpa [prefixWord, tailWord_491025, baseEnd_491025] using wordTrace_append hprefix tailTrace_491025
  have hstable : (prefixWord ++ tailWord_491025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491025).length < 2 ^ (prefixWord ++ tailWord_491025).sum := by decide
  have hdescent : baseEnd_491025 < baseStart_491025 := by decide
  rcases family_descends (prefixWord ++ tailWord_491025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491042 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 6]
def baseStart_491042 : Nat := 118140960795 + 491042 * 2 ^ 59
def prefixEnd_491042 : Nat := 4983230072969 + 3 ^ 40 * 491042 * 2
def baseEnd_491042 : Nat := 112062474464521346496331

theorem tailTrace_491042 : CollatzResearch.WordTrace tailWord_491042 prefixEnd_491042 112062474464521346496331 := by
  unfold tailWord_491042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4477443271761543035502845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11939848724697448094674253 4477443271761543035502845)
  ·
    refine ⟨1679041226910578638313567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4477443271761543035502845 1679041226910578638313567)
    ·
      refine ⟨2518561840365867957470351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1679041226910578638313567 2518561840365867957470351)
      ·
        refine ⟨3777842760548801936205527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2518561840365867957470351 3777842760548801936205527)
        ·
          refine ⟨5666764140823202904308291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3777842760548801936205527 5666764140823202904308291)
          ·
            refine ⟨8500146211234804356462437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5666764140823202904308291 8500146211234804356462437)
            ·
              refine ⟨1593777414606525816836707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8500146211234804356462437 1593777414606525816836707)
              ·
                refine ⟨2390666121909788725255061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1593777414606525816836707 2390666121909788725255061)
                ·
                  refine ⟨112062474464521346496331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2390666121909788725255061 112062474464521346496331)
                  ·
                    rfl

theorem cell21_491042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_491042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491042 prefixEnd_491042 := by exact prefixLift 491042
  have htrace : WordTrace (prefixWord ++ tailWord_491042) baseStart_491042 baseEnd_491042 := by
    simpa [prefixWord, tailWord_491042, baseEnd_491042] using wordTrace_append hprefix tailTrace_491042
  have hstable : (prefixWord ++ tailWord_491042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491042).length < 2 ^ (prefixWord ++ tailWord_491042).sum := by decide
  have hdescent : baseEnd_491042 < baseStart_491042 := by decide
  rcases family_descends (prefixWord ++ tailWord_491042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491059 : List Nat := [1, 1, 1, 2, 4, 3, 4, 1, 4]
def baseStart_491059 : Nat := 118140960795 + 491059 * 2 ^ 59
def prefixEnd_491059 : Nat := 4983230072969 + 3 ^ 40 * 491059 * 2
def baseEnd_491059 : Nat := 112066354096133094712963

theorem tailTrace_491059 : CollatzResearch.WordTrace tailWord_491059 prefixEnd_491059 112066354096133094712963 := by
  unfold tailWord_491059
  simp only [CollatzResearch.WordTrace]
  refine ⟨17910393127984584045380231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11940262085323056030253487 17910393127984584045380231)
  ·
    refine ⟨26865589691976876068070347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17910393127984584045380231 26865589691976876068070347)
    ·
      refine ⟨40298384537965314102105521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26865589691976876068070347 40298384537965314102105521)
      ·
        refine ⟨30223788403473985576579141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40298384537965314102105521 30223788403473985576579141)
        ·
          refine ⟨5666960325651372295608589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30223788403473985576579141 5666960325651372295608589)
          ·
            refine ⟨2125110122119264610853221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5666960325651372295608589 2125110122119264610853221)
            ·
              refine ⟨398458147897362114534979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2125110122119264610853221 398458147897362114534979)
              ·
                refine ⟨597687221846043171802469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398458147897362114534979 597687221846043171802469)
                ·
                  refine ⟨112066354096133094712963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 597687221846043171802469 112066354096133094712963)
                  ·
                    rfl

theorem cell21_491059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 4].length) (baseStart_491059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491059 prefixEnd_491059 := by exact prefixLift 491059
  have htrace : WordTrace (prefixWord ++ tailWord_491059) baseStart_491059 baseEnd_491059 := by
    simpa [prefixWord, tailWord_491059, baseEnd_491059] using wordTrace_append hprefix tailTrace_491059
  have hstable : (prefixWord ++ tailWord_491059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491059).length < 2 ^ (prefixWord ++ tailWord_491059).sum := by decide
  have hdescent : baseEnd_491059 < baseStart_491059 := by decide
  rcases family_descends (prefixWord ++ tailWord_491059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491228 : List Nat := [2, 2, 5, 1, 2, 1, 1, 3, 4]
def baseStart_491228 : Nat := 118140960795 + 491228 * 2 ^ 59
def prefixEnd_491228 : Nat := 4983230072969 + 3 ^ 40 * 491228 * 2
def baseEnd_491228 : Nat := 112104922198626356395951

theorem tailTrace_491228 : CollatzResearch.WordTrace tailWord_491228 prefixEnd_491228 112104922198626356395951 := by
  unfold tailWord_491228
  simp only [CollatzResearch.WordTrace]
  refine ⟨8958278532186162954141169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11944371376248217272188225 8958278532186162954141169)
  ·
    refine ⟨6718708899139622215605877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8958278532186162954141169 6718708899139622215605877)
    ·
      refine ⟨629878959294339582713051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6718708899139622215605877 629878959294339582713051)
      ·
        refine ⟨944818438941509374069577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629878959294339582713051 944818438941509374069577)
        ·
          refine ⟨708613829206132030552183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944818438941509374069577 708613829206132030552183)
          ·
            refine ⟨1062920743809198045828275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708613829206132030552183 1062920743809198045828275)
            ·
              refine ⟨1594381115713797068742413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062920743809198045828275 1594381115713797068742413)
              ·
                refine ⟨597892918392673900778405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1594381115713797068742413 597892918392673900778405)
                ·
                  refine ⟨112104922198626356395951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 597892918392673900778405 112104922198626356395951)
                  ·
                    rfl

theorem cell21_491228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_491228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491228 prefixEnd_491228 := by exact prefixLift 491228
  have htrace : WordTrace (prefixWord ++ tailWord_491228) baseStart_491228 baseEnd_491228 := by
    simpa [prefixWord, tailWord_491228, baseEnd_491228] using wordTrace_append hprefix tailTrace_491228
  have hstable : (prefixWord ++ tailWord_491228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491228).length < 2 ^ (prefixWord ++ tailWord_491228).sum := by decide
  have hdescent : baseEnd_491228 < baseStart_491228 := by decide
  rcases family_descends (prefixWord ++ tailWord_491228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491301 : List Nat := [1, 3, 1, 2, 3, 3, 3, 5]
def baseStart_491301 : Nat := 118140960795 + 491301 * 2 ^ 59
def prefixEnd_491301 : Nat := 4983230072969 + 3 ^ 40 * 491301 * 2
def baseEnd_491301 : Nat := 37373860597731483893045

theorem tailTrace_491301 : CollatzResearch.WordTrace tailWord_491301 prefixEnd_491301 37373860597731483893045 := by
  unfold tailWord_491301
  simp only [CollatzResearch.WordTrace]
  refine ⟨17919219593107859375689757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11946146395405239583793171 17919219593107859375689757)
  ·
    refine ⟨6719707347415447265883659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17919219593107859375689757 6719707347415447265883659)
    ·
      refine ⟨10079561021123170898825489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6719707347415447265883659 10079561021123170898825489)
      ·
        refine ⟨7559670765842378174119117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10079561021123170898825489 7559670765842378174119117)
        ·
          refine ⟨2834876537190891815294669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7559670765842378174119117 2834876537190891815294669)
          ·
            refine ⟨1063078701446584430735501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2834876537190891815294669 1063078701446584430735501)
            ·
              refine ⟨398654513042469161525813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1063078701446584430735501 398654513042469161525813)
              ·
                refine ⟨37373860597731483893045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 398654513042469161525813 37373860597731483893045)
                ·
                  rfl

theorem cell21_491301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 5].length) (baseStart_491301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491301 prefixEnd_491301 := by exact prefixLift 491301
  have htrace : WordTrace (prefixWord ++ tailWord_491301) baseStart_491301 baseEnd_491301 := by
    simpa [prefixWord, tailWord_491301, baseEnd_491301] using wordTrace_append hprefix tailTrace_491301
  have hstable : (prefixWord ++ tailWord_491301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491301).length < 2 ^ (prefixWord ++ tailWord_491301).sum := by decide
  have hdescent : baseEnd_491301 < baseStart_491301 := by decide
  rcases family_descends (prefixWord ++ tailWord_491301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491321 : List Nat := [1, 2, 1, 7, 2, 1, 1, 2, 4]
def baseStart_491321 : Nat := 118140960795 + 491321 * 2 ^ 59
def prefixEnd_491321 : Nat := 4983230072969 + 3 ^ 40 * 491321 * 2
def baseEnd_491321 : Nat := 112126146065678861345761

theorem tailTrace_491321 : CollatzResearch.WordTrace tailWord_491321 prefixEnd_491321 112126146065678861345761 := by
  unfold tailWord_491321
  simp only [CollatzResearch.WordTrace]
  refine ⟨17919949053035402791417817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11946632702023601860945211 17919949053035402791417817)
  ·
    refine ⟨13439961789776552093563363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17919949053035402791417817 13439961789776552093563363)
    ·
      refine ⟨20159942684664828140345045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13439961789776552093563363 20159942684664828140345045)
      ·
        refine ⟨472498656671831909539337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 20159942684664828140345045 472498656671831909539337)
        ·
          refine ⟨354373992503873932154503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472498656671831909539337 354373992503873932154503)
          ·
            refine ⟨531560988755810898231755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354373992503873932154503 531560988755810898231755)
            ·
              refine ⟨797341483133716347347633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531560988755810898231755 797341483133716347347633)
              ·
                refine ⟨598006112350287260510725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 797341483133716347347633 598006112350287260510725)
                ·
                  refine ⟨112126146065678861345761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 598006112350287260510725 112126146065678861345761)
                  ·
                    rfl

theorem cell21_491321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 4].length) (baseStart_491321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491321 prefixEnd_491321 := by exact prefixLift 491321
  have htrace : WordTrace (prefixWord ++ tailWord_491321) baseStart_491321 baseEnd_491321 := by
    simpa [prefixWord, tailWord_491321, baseEnd_491321] using wordTrace_append hprefix tailTrace_491321
  have hstable : (prefixWord ++ tailWord_491321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491321).length < 2 ^ (prefixWord ++ tailWord_491321).sum := by decide
  have hdescent : baseEnd_491321 < baseStart_491321 := by decide
  rcases family_descends (prefixWord ++ tailWord_491321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491360 : List Nat := [2, 1, 1, 3, 3, 3, 1, 7]
def baseStart_491360 : Nat := 118140960795 + 491360 * 2 ^ 59
def prefixEnd_491360 : Nat := 4983230072969 + 3 ^ 40 * 491360 * 2
def baseEnd_491360 : Nat := 37378348799007820065227

theorem tailTrace_491360 : CollatzResearch.WordTrace tailWord_491360 prefixEnd_491360 37378348799007820065227 := by
  unfold tailWord_491360
  simp only [CollatzResearch.WordTrace]
  refine ⟨8960685749947056226043767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11947580999929408301391689 8960685749947056226043767)
  ·
    refine ⟨13441028624920584339065651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8960685749947056226043767 13441028624920584339065651)
    ·
      refine ⟨20161542937380876508598477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13441028624920584339065651 20161542937380876508598477)
      ·
        refine ⟨7560578601517828690724429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20161542937380876508598477 7560578601517828690724429)
        ·
          refine ⟨2835216975569185759021661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7560578601517828690724429 2835216975569185759021661)
          ·
            refine ⟨1063206365838444659633123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2835216975569185759021661 1063206365838444659633123)
            ·
              refine ⟨1594809548757666989449685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063206365838444659633123 1594809548757666989449685)
              ·
                refine ⟨37378348799007820065227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1594809548757666989449685 37378348799007820065227)
                ·
                  rfl

theorem cell21_491360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 7].length) (baseStart_491360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491360 prefixEnd_491360 := by exact prefixLift 491360
  have htrace : WordTrace (prefixWord ++ tailWord_491360) baseStart_491360 baseEnd_491360 := by
    simpa [prefixWord, tailWord_491360, baseEnd_491360] using wordTrace_append hprefix tailTrace_491360
  have hstable : (prefixWord ++ tailWord_491360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491360).length < 2 ^ (prefixWord ++ tailWord_491360).sum := by decide
  have hdescent : baseEnd_491360 < baseStart_491360 := by decide
  rcases family_descends (prefixWord ++ tailWord_491360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491453 : List Nat := [1, 4, 1, 2, 3, 3, 1, 6]
def baseStart_491453 : Nat := 118140960795 + 491453 * 2 ^ 59
def prefixEnd_491453 : Nat := 4983230072969 + 3 ^ 40 * 491453 * 2
def baseEnd_491453 : Nat := 37385423421358655048497

theorem tailTrace_491453 : CollatzResearch.WordTrace tailWord_491453 prefixEnd_491453 37385423421358655048497 := by
  unfold tailWord_491453
  simp only [CollatzResearch.WordTrace]
  refine ⟨17924763488557189335223013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11949842325704792890148675 17924763488557189335223013)
  ·
    refine ⟨3360893154104473000354315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17924763488557189335223013 3360893154104473000354315)
    ·
      refine ⟨5041339731156709500531473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3360893154104473000354315 5041339731156709500531473)
      ·
        refine ⟨3781004798367532125398605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5041339731156709500531473 3781004798367532125398605)
        ·
          refine ⟨1417876799387824547024477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3781004798367532125398605 1417876799387824547024477)
          ·
            refine ⟨531703799770434205134179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1417876799387824547024477 531703799770434205134179)
            ·
              refine ⟨797555699655651307701269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531703799770434205134179 797555699655651307701269)
              ·
                refine ⟨37385423421358655048497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 797555699655651307701269 37385423421358655048497)
                ·
                  rfl

theorem cell21_491453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 6].length) (baseStart_491453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491453 prefixEnd_491453 := by exact prefixLift 491453
  have htrace : WordTrace (prefixWord ++ tailWord_491453) baseStart_491453 baseEnd_491453 := by
    simpa [prefixWord, tailWord_491453, baseEnd_491453] using wordTrace_append hprefix tailTrace_491453
  have hstable : (prefixWord ++ tailWord_491453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491453).length < 2 ^ (prefixWord ++ tailWord_491453).sum := by decide
  have hdescent : baseEnd_491453 < baseStart_491453 := by decide
  rcases family_descends (prefixWord ++ tailWord_491453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491501 : List Nat := [1, 5, 1, 4, 1, 1, 2, 1, 5]
def baseStart_491501 : Nat := 118140960795 + 491501 * 2 ^ 59
def prefixEnd_491501 : Nat := 4983230072969 + 3 ^ 40 * 491501 * 2
def baseEnd_491501 : Nat := 112167224518038548345393

theorem tailTrace_491501 : CollatzResearch.WordTrace tailWord_491501 prefixEnd_491501 112167224518038548345393 := by
  unfold tailWord_491501
  simp only [CollatzResearch.WordTrace]
  refine ⟨17926514192383293532970357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11951009461588862355313571 17926514192383293532970357)
  ·
    refine ⟨1680610705535933768715971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17926514192383293532970357 1680610705535933768715971)
    ·
      refine ⟨2520916058303900653073957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1680610705535933768715971 2520916058303900653073957)
      ·
        refine ⟨472671760931981372451367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2520916058303900653073957 472671760931981372451367)
        ·
          refine ⟨709007641397972058677051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472671760931981372451367 709007641397972058677051)
          ·
            refine ⟨1063511462096958088015577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709007641397972058677051 1063511462096958088015577)
            ·
              refine ⟨797633596572718566011683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063511462096958088015577 797633596572718566011683)
              ·
                refine ⟨1196450394859077849017525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797633596572718566011683 1196450394859077849017525)
                ·
                  refine ⟨112167224518038548345393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1196450394859077849017525 112167224518038548345393)
                  ·
                    rfl

theorem cell21_491501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_491501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491501 prefixEnd_491501 := by exact prefixLift 491501
  have htrace : WordTrace (prefixWord ++ tailWord_491501) baseStart_491501 baseEnd_491501 := by
    simpa [prefixWord, tailWord_491501, baseEnd_491501] using wordTrace_append hprefix tailTrace_491501
  have hstable : (prefixWord ++ tailWord_491501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491501).length < 2 ^ (prefixWord ++ tailWord_491501).sum := by decide
  have hdescent : baseEnd_491501 < baseStart_491501 := by decide
  rcases family_descends (prefixWord ++ tailWord_491501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491557 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 6]
def baseStart_491557 : Nat := 118140960795 + 491557 * 2 ^ 59
def prefixEnd_491557 : Nat := 4983230072969 + 3 ^ 40 * 491557 * 2
def baseEnd_491557 : Nat := 112180004480994895411945

theorem tailTrace_491557 : CollatzResearch.WordTrace tailWord_491557 prefixEnd_491557 112180004480994895411945 := by
  unfold tailWord_491557
  simp only [CollatzResearch.WordTrace]
  refine ⟨17928556680180415097008925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11952371120120276731339283 17928556680180415097008925)
  ·
    refine ⟨6723208755067655661378347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17928556680180415097008925 6723208755067655661378347)
    ·
      refine ⟨10084813132601483492067521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6723208755067655661378347 10084813132601483492067521)
      ·
        refine ⟨7563609849451112619050641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10084813132601483492067521 7563609849451112619050641)
        ·
          refine ⟨5672707387088334464287981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7563609849451112619050641 5672707387088334464287981)
          ·
            refine ⟨2127265270158125424107993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5672707387088334464287981 2127265270158125424107993)
            ·
              refine ⟨1595448952618594068080995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2127265270158125424107993 1595448952618594068080995)
              ·
                refine ⟨2393173428927891102121493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595448952618594068080995 2393173428927891102121493)
                ·
                  refine ⟨112180004480994895411945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2393173428927891102121493 112180004480994895411945)
                  ·
                    rfl

theorem cell21_491557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_491557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491557 prefixEnd_491557 := by exact prefixLift 491557
  have htrace : WordTrace (prefixWord ++ tailWord_491557) baseStart_491557 baseEnd_491557 := by
    simpa [prefixWord, tailWord_491557, baseEnd_491557] using wordTrace_append hprefix tailTrace_491557
  have hstable : (prefixWord ++ tailWord_491557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491557).length < 2 ^ (prefixWord ++ tailWord_491557).sum := by decide
  have hdescent : baseEnd_491557 < baseStart_491557 := by decide
  rcases family_descends (prefixWord ++ tailWord_491557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491571 : List Nat := [1, 1, 1, 2, 4, 1, 3, 8]
def baseStart_491571 : Nat := 118140960795 + 491571 * 2 ^ 59
def prefixEnd_491571 : Nat := 4983230072969 + 3 ^ 40 * 491571 * 2
def baseEnd_491571 : Nat := 37394399823911327392861

theorem tailTrace_491571 : CollatzResearch.WordTrace tailWord_491571 prefixEnd_491571 37394399823911327392861 := by
  unfold tailWord_491571
  simp only [CollatzResearch.WordTrace]
  refine ⟨17929067302129695488018567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11952711534753130325345711 17929067302129695488018567)
  ·
    refine ⟨26893600953194543232027851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17929067302129695488018567 26893600953194543232027851)
    ·
      refine ⟨40340401429791814848041777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26893600953194543232027851 40340401429791814848041777)
      ·
        refine ⟨30255301072343861136031333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40340401429791814848041777 30255301072343861136031333)
        ·
          refine ⟨5672868951064473963005875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30255301072343861136031333 5672868951064473963005875)
          ·
            refine ⟨8509303426596710944508813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5672868951064473963005875 8509303426596710944508813)
            ·
              refine ⟨3190988784973766604190805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8509303426596710944508813 3190988784973766604190805)
              ·
                refine ⟨37394399823911327392861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3190988784973766604190805 37394399823911327392861)
                ·
                  rfl

theorem cell21_491571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 8].length) (baseStart_491571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491571 prefixEnd_491571 := by exact prefixLift 491571
  have htrace : WordTrace (prefixWord ++ tailWord_491571) baseStart_491571 baseEnd_491571 := by
    simpa [prefixWord, tailWord_491571, baseEnd_491571] using wordTrace_append hprefix tailTrace_491571
  have hstable : (prefixWord ++ tailWord_491571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491571).length < 2 ^ (prefixWord ++ tailWord_491571).sum := by decide
  have hdescent : baseEnd_491571 < baseStart_491571 := by decide
  rcases family_descends (prefixWord ++ tailWord_491571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491633 : List Nat := [1, 2, 2, 2, 1, 1, 3, 5, 4]
def baseStart_491633 : Nat := 118140960795 + 491633 * 2 ^ 59
def prefixEnd_491633 : Nat := 4983230072969 + 3 ^ 40 * 491633 * 2
def baseEnd_491633 : Nat := 112197348716435652145123

theorem tailTrace_491633 : CollatzResearch.WordTrace tailWord_491633 prefixEnd_491633 112197348716435652145123 := by
  unfold tailWord_491633
  simp only [CollatzResearch.WordTrace]
  refine ⟨17931328627905080076775553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11954219085270053384517035 17931328627905080076775553)
  ·
    refine ⟨13448496470928810057581665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17931328627905080076775553 13448496470928810057581665)
    ·
      refine ⟨10086372353196607543186249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13448496470928810057581665 10086372353196607543186249)
      ·
        refine ⟨7564779264897455657389687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10086372353196607543186249 7564779264897455657389687)
        ·
          refine ⟨11347168897346183486084531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7564779264897455657389687 11347168897346183486084531)
          ·
            refine ⟨17020753346019275229126797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11347168897346183486084531 17020753346019275229126797)
            ·
              refine ⟨6382782504757228210922549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17020753346019275229126797 6382782504757228210922549)
              ·
                refine ⟨598385859820990144773989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6382782504757228210922549 598385859820990144773989)
                ·
                  refine ⟨112197348716435652145123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 598385859820990144773989 112197348716435652145123)
                  ·
                    rfl

theorem cell21_491633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_491633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491633 prefixEnd_491633 := by exact prefixLift 491633
  have htrace : WordTrace (prefixWord ++ tailWord_491633) baseStart_491633 baseEnd_491633 := by
    simpa [prefixWord, tailWord_491633, baseEnd_491633] using wordTrace_append hprefix tailTrace_491633
  have hstable : (prefixWord ++ tailWord_491633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491633).length < 2 ^ (prefixWord ++ tailWord_491633).sum := by decide
  have hdescent : baseEnd_491633 < baseStart_491633 := by decide
  rcases family_descends (prefixWord ++ tailWord_491633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491712 : List Nat := [2, 1, 1, 2, 5, 1, 3, 3, 3]
def baseStart_491712 : Nat := 118140960795 + 491712 * 2 ^ 59
def prefixEnd_491712 : Nat := 4983230072969 + 3 ^ 40 * 491712 * 2
def baseEnd_491712 : Nat := 112215377592749070328295

theorem tailTrace_491712 : CollatzResearch.WordTrace tailWord_491712 prefixEnd_491712 112215377592749070328295 := by
  unfold tailWord_491712
  simp only [CollatzResearch.WordTrace]
  refine ⟨8967104997309438284450695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11956139996412584379267593 8967104997309438284450695)
  ·
    refine ⟨13450657495964157426676043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8967104997309438284450695 13450657495964157426676043)
    ·
      refine ⟨20175986243946236140014065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13450657495964157426676043 20175986243946236140014065)
      ·
        refine ⟨15131989682959677105010549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20175986243946236140014065 15131989682959677105010549)
        ·
          refine ⟨1418624032777469728594739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15131989682959677105010549 1418624032777469728594739)
          ·
            refine ⟨2127936049166204592892109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418624032777469728594739 2127936049166204592892109)
            ·
              refine ⟨797976018437326722334541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2127936049166204592892109 797976018437326722334541)
              ·
                refine ⟨299241006913997520875453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 797976018437326722334541 299241006913997520875453)
                ·
                  refine ⟨112215377592749070328295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299241006913997520875453 112215377592749070328295)
                  ·
                    rfl

theorem cell21_491712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 3].length) (baseStart_491712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491712 prefixEnd_491712 := by exact prefixLift 491712
  have htrace : WordTrace (prefixWord ++ tailWord_491712) baseStart_491712 baseEnd_491712 := by
    simpa [prefixWord, tailWord_491712, baseEnd_491712] using wordTrace_append hprefix tailTrace_491712
  have hstable : (prefixWord ++ tailWord_491712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491712).length < 2 ^ (prefixWord ++ tailWord_491712).sum := by decide
  have hdescent : baseEnd_491712 < baseStart_491712 := by decide
  rcases family_descends (prefixWord ++ tailWord_491712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491754 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 7]
def baseStart_491754 : Nat := 118140960795 + 491754 * 2 ^ 59
def prefixEnd_491754 : Nat := 4983230072969 + 3 ^ 40 * 491754 * 2
def baseEnd_491754 : Nat := 112224962564966330628209

theorem tailTrace_491754 : CollatzResearch.WordTrace tailWord_491754 prefixEnd_491754 112224962564966330628209 := by
  unfold tailWord_491754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4483935465116679435482579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11957161240311145161286877 4483935465116679435482579)
  ·
    refine ⟨6725903197675019153223869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4483935465116679435482579 6725903197675019153223869)
    ·
      refine ⟨2522213699128132182458951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6725903197675019153223869 2522213699128132182458951)
      ·
        refine ⟨3783320548692198273688427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522213699128132182458951 3783320548692198273688427)
        ·
          refine ⟨5674980823038297410532641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3783320548692198273688427 5674980823038297410532641)
          ·
            refine ⟨4256235617278723057899481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5674980823038297410532641 4256235617278723057899481)
            ·
              refine ⟨3192176712959042293424611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4256235617278723057899481 3192176712959042293424611)
              ·
                refine ⟨4788265069438563440136917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3192176712959042293424611 4788265069438563440136917)
                ·
                  refine ⟨112224962564966330628209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4788265069438563440136917 112224962564966330628209)
                  ·
                    rfl

theorem cell21_491754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_491754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491754 prefixEnd_491754 := by exact prefixLift 491754
  have htrace : WordTrace (prefixWord ++ tailWord_491754) baseStart_491754 baseEnd_491754 := by
    simpa [prefixWord, tailWord_491754, baseEnd_491754] using wordTrace_append hprefix tailTrace_491754
  have hstable : (prefixWord ++ tailWord_491754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491754).length < 2 ^ (prefixWord ++ tailWord_491754).sum := by decide
  have hdescent : baseEnd_491754 < baseStart_491754 := by decide
  rcases family_descends (prefixWord ++ tailWord_491754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491768 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 8]
def baseStart_491768 : Nat := 118140960795 + 491768 * 2 ^ 59
def prefixEnd_491768 : Nat := 4983230072969 + 3 ^ 40 * 491768 * 2
def baseEnd_491768 : Nat := 112228157555705417394847

theorem tailTrace_491768 : CollatzResearch.WordTrace tailWord_491768 prefixEnd_491768 112228157555705417394847 := by
  unfold tailWord_491768
  simp only [CollatzResearch.WordTrace]
  refine ⟨8968126241207999066469979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11957501654943998755293305 8968126241207999066469979)
  ·
    refine ⟨13452189361811998599704969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8968126241207999066469979 13452189361811998599704969)
    ·
      refine ⟨10089142021358998949778727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13452189361811998599704969 10089142021358998949778727)
      ·
        refine ⟨15133713032038498424668091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10089142021358998949778727 15133713032038498424668091)
        ·
          refine ⟨22700569548057747637002137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15133713032038498424668091 22700569548057747637002137)
          ·
            refine ⟨17025427161043310727751603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22700569548057747637002137 17025427161043310727751603)
            ·
              refine ⟨25538140741564966091627405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17025427161043310727751603 25538140741564966091627405)
              ·
                refine ⟨9576802778086862284360277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25538140741564966091627405 9576802778086862284360277)
                ·
                  refine ⟨112228157555705417394847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9576802778086862284360277 112228157555705417394847)
                  ·
                    rfl

theorem cell21_491768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_491768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491768 prefixEnd_491768 := by exact prefixLift 491768
  have htrace : WordTrace (prefixWord ++ tailWord_491768) baseStart_491768 baseEnd_491768 := by
    simpa [prefixWord, tailWord_491768, baseEnd_491768] using wordTrace_append hprefix tailTrace_491768
  have hstable : (prefixWord ++ tailWord_491768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491768).length < 2 ^ (prefixWord ++ tailWord_491768).sum := by decide
  have hdescent : baseEnd_491768 < baseStart_491768 := by decide
  rcases family_descends (prefixWord ++ tailWord_491768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491785 : List Nat := [1, 2, 1, 1, 3, 4, 1, 4, 4]
def baseStart_491785 : Nat := 118140960795 + 491785 * 2 ^ 59
def prefixEnd_491785 : Nat := 4983230072969 + 3 ^ 40 * 491785 * 2
def baseEnd_491785 : Nat := 112232037187317165611479

theorem tailTrace_491785 : CollatzResearch.WordTrace tailWord_491785 prefixEnd_491785 112232037187317165611479 := by
  unfold tailWord_491785
  simp only [CollatzResearch.WordTrace]
  refine ⟨17936872523354410036308809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11957915015569606690872539 17936872523354410036308809)
  ·
    refine ⟨13452654392515807527231607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17936872523354410036308809 13452654392515807527231607)
    ·
      refine ⟨20178981588773711290847411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13452654392515807527231607 20178981588773711290847411)
      ·
        refine ⟨30268472383160566936271117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20178981588773711290847411 30268472383160566936271117)
        ·
          refine ⟨11350677143685212601101669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30268472383160566936271117 11350677143685212601101669)
          ·
            refine ⟨2128251964440977362706563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11350677143685212601101669 2128251964440977362706563)
            ·
              refine ⟨3192377946661466044059845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128251964440977362706563 3192377946661466044059845)
              ·
                refine ⟨598570864999024883261221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3192377946661466044059845 598570864999024883261221)
                ·
                  refine ⟨112232037187317165611479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 598570864999024883261221 112232037187317165611479)
                  ·
                    rfl

theorem cell21_491785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_491785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491785 prefixEnd_491785 := by exact prefixLift 491785
  have htrace : WordTrace (prefixWord ++ tailWord_491785) baseStart_491785 baseEnd_491785 := by
    simpa [prefixWord, tailWord_491785, baseEnd_491785] using wordTrace_append hprefix tailTrace_491785
  have hstable : (prefixWord ++ tailWord_491785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491785).length < 2 ^ (prefixWord ++ tailWord_491785).sum := by decide
  have hdescent : baseEnd_491785 < baseStart_491785 := by decide
  rcases family_descends (prefixWord ++ tailWord_491785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491822 : List Nat := [4, 1, 3, 3, 1, 1, 2, 3, 3]
def baseStart_491822 : Nat := 118140960795 + 491822 * 2 ^ 59
def prefixEnd_491822 : Nat := 4983230072969 + 3 ^ 40 * 491822 * 2
def baseEnd_491822 : Nat := 112240481091413323494737

theorem tailTrace_491822 : CollatzResearch.WordTrace tailWord_491822 prefixEnd_491822 112240481091413323494737 := by
  unfold tailWord_491822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2242277753027545669425715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11958814682813576903603813 2242277753027545669425715)
  ·
    refine ⟨3363416629541318504138573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2242277753027545669425715 3363416629541318504138573)
    ·
      refine ⟨1261281236077994439051965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3363416629541318504138573 1261281236077994439051965)
      ·
        refine ⟨472980463529247914644487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1261281236077994439051965 472980463529247914644487)
        ·
          refine ⟨709470695293871871966731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472980463529247914644487 709470695293871871966731)
          ·
            refine ⟨1064206042940807807950097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709470695293871871966731 1064206042940807807950097)
            ·
              refine ⟨798154532205605855962573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064206042940807807950097 798154532205605855962573)
              ·
                refine ⟨299307949577102195985965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 798154532205605855962573 299307949577102195985965)
                ·
                  refine ⟨112240481091413323494737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299307949577102195985965 112240481091413323494737)
                  ·
                    rfl

theorem cell21_491822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_491822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491822 prefixEnd_491822 := by exact prefixLift 491822
  have htrace : WordTrace (prefixWord ++ tailWord_491822) baseStart_491822 baseEnd_491822 := by
    simpa [prefixWord, tailWord_491822, baseEnd_491822] using wordTrace_append hprefix tailTrace_491822
  have hstable : (prefixWord ++ tailWord_491822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491822).length < 2 ^ (prefixWord ++ tailWord_491822).sum := by decide
  have hdescent : baseEnd_491822 < baseStart_491822 := by decide
  rcases family_descends (prefixWord ++ tailWord_491822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491847 : List Nat := [1, 1, 4, 1, 2, 2, 1, 6, 3]
def baseStart_491847 : Nat := 118140960795 + 491847 * 2 ^ 59
def prefixEnd_491847 : Nat := 4983230072969 + 3 ^ 40 * 491847 * 2
def baseEnd_491847 : Nat := 112246186432018835578019

theorem tailTrace_491847 : CollatzResearch.WordTrace tailWord_491847 prefixEnd_491847 112246186432018835578019 := by
  unfold tailWord_491847
  simp only [CollatzResearch.WordTrace]
  refine ⟨17939133849129794625065795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11959422566086529750043863 17939133849129794625065795)
  ·
    refine ⟨26908700773694691937598693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17939133849129794625065795 26908700773694691937598693)
    ·
      refine ⟨5045381395067754738299755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26908700773694691937598693 5045381395067754738299755)
      ·
        refine ⟨7568072092601632107449633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5045381395067754738299755 7568072092601632107449633)
        ·
          refine ⟨5676054069451224080587225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7568072092601632107449633 5676054069451224080587225)
          ·
            refine ⟨4257040552088418060440419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5676054069451224080587225 4257040552088418060440419)
            ·
              refine ⟨6385560828132627090660629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4257040552088418060440419 6385560828132627090660629)
              ·
                refine ⟨299323163818716894874717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6385560828132627090660629 299323163818716894874717)
                ·
                  refine ⟨112246186432018835578019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299323163818716894874717 112246186432018835578019)
                  ·
                    rfl

theorem cell21_491847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 3].length) (baseStart_491847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491847 prefixEnd_491847 := by exact prefixLift 491847
  have htrace : WordTrace (prefixWord ++ tailWord_491847) baseStart_491847 baseEnd_491847 := by
    simpa [prefixWord, tailWord_491847, baseEnd_491847] using wordTrace_append hprefix tailTrace_491847
  have hstable : (prefixWord ++ tailWord_491847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491847).length < 2 ^ (prefixWord ++ tailWord_491847).sum := by decide
  have hdescent : baseEnd_491847 < baseStart_491847 := by decide
  rcases family_descends (prefixWord ++ tailWord_491847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491875 : List Nat := [1, 1, 1, 5, 2, 1, 3, 7]
def baseStart_491875 : Nat := 118140960795 + 491875 * 2 ^ 59
def prefixEnd_491875 : Nat := 4983230072969 + 3 ^ 40 * 491875 * 2
def baseEnd_491875 : Nat := 37417525471165669703765

theorem tailTrace_491875 : CollatzResearch.WordTrace tailWord_491875 prefixEnd_491875 37417525471165669703765 := by
  unfold tailWord_491875
  simp only [CollatzResearch.WordTrace]
  refine ⟨17940155093028355407085079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11960103395352236938056719 17940155093028355407085079)
  ·
    refine ⟨26910232639542533110627619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17940155093028355407085079 26910232639542533110627619)
    ·
      refine ⟨40365348959313799665941429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26910232639542533110627619 40365348959313799665941429)
      ·
        refine ⟨3784251464935668718682009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40365348959313799665941429 3784251464935668718682009)
        ·
          refine ⟨2838188598701751539011507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3784251464935668718682009 2838188598701751539011507)
          ·
            refine ⟨4257282898052627308517261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838188598701751539011507 4257282898052627308517261)
            ·
              refine ⟨1596481086769735240693973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4257282898052627308517261 1596481086769735240693973)
              ·
                refine ⟨37417525471165669703765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1596481086769735240693973 37417525471165669703765)
                ·
                  rfl

theorem cell21_491875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 7].length) (baseStart_491875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491875 prefixEnd_491875 := by exact prefixLift 491875
  have htrace : WordTrace (prefixWord ++ tailWord_491875) baseStart_491875 baseEnd_491875 := by
    simpa [prefixWord, tailWord_491875, baseEnd_491875] using wordTrace_append hprefix tailTrace_491875
  have hstable : (prefixWord ++ tailWord_491875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491875).length < 2 ^ (prefixWord ++ tailWord_491875).sum := by decide
  have hdescent : baseEnd_491875 < baseStart_491875 := by decide
  rcases family_descends (prefixWord ++ tailWord_491875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_491999 : List Nat := [1, 1, 2, 3, 3, 2, 1, 5, 3]
def baseStart_491999 : Nat := 118140960795 + 491999 * 2 ^ 59
def prefixEnd_491999 : Nat := 4983230072969 + 3 ^ 40 * 491999 * 2
def baseEnd_491999 : Nat := 112280874902900349044375

theorem tailTrace_491999 : CollatzResearch.WordTrace tailWord_491999 prefixEnd_491999 112280874902900349044375 := by
  unfold tailWord_491999
  simp only [CollatzResearch.WordTrace]
  refine ⟨17944677744579124584599051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11963118496386083056399367 17944677744579124584599051)
  ·
    refine ⟨26917016616868686876898577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17944677744579124584599051 26917016616868686876898577)
    ·
      refine ⟨20187762462651515157673933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26917016616868686876898577 20187762462651515157673933)
      ·
        refine ⟨7570410923494318184127725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20187762462651515157673933 7570410923494318184127725)
        ·
          refine ⟨2838904096310369319047897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7570410923494318184127725 2838904096310369319047897)
          ·
            refine ⟨2129178072232776989285923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2838904096310369319047897 2129178072232776989285923)
            ·
              refine ⟨3193767108349165483928885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2129178072232776989285923 3193767108349165483928885)
              ·
                refine ⟨299415666407734264118333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3193767108349165483928885 299415666407734264118333)
                ·
                  refine ⟨112280874902900349044375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299415666407734264118333 112280874902900349044375)
                  ·
                    rfl

theorem cell21_491999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 3].length) (baseStart_491999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_491999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_491999 prefixEnd_491999 := by exact prefixLift 491999
  have htrace : WordTrace (prefixWord ++ tailWord_491999) baseStart_491999 baseEnd_491999 := by
    simpa [prefixWord, tailWord_491999, baseEnd_491999] using wordTrace_append hprefix tailTrace_491999
  have hstable : (prefixWord ++ tailWord_491999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_491999).length < 2 ^ (prefixWord ++ tailWord_491999).sum := by decide
  have hdescent : baseEnd_491999 < baseStart_491999 := by decide
  rcases family_descends (prefixWord ++ tailWord_491999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492041 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 7]
def baseStart_492041 : Nat := 118140960795 + 492041 * 2 ^ 59
def prefixEnd_492041 : Nat := 4983230072969 + 3 ^ 40 * 492041 * 2
def baseEnd_492041 : Nat := 112290459875117609344289

theorem tailTrace_492041 : CollatzResearch.WordTrace tailWord_492041 prefixEnd_492041 112290459875117609344289 := by
  unfold tailWord_492041
  simp only [CollatzResearch.WordTrace]
  refine ⟨17946209610426965757627977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11964139740284643838418651 17946209610426965757627977)
  ·
    refine ⟨13459657207820224318220983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17946209610426965757627977 13459657207820224318220983)
    ·
      refine ⟨20189485811730336477331475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13459657207820224318220983 20189485811730336477331475)
      ·
        refine ⟨30284228717595504715997213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20189485811730336477331475 30284228717595504715997213)
        ·
          refine ⟨11356585769098314268498955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30284228717595504715997213 11356585769098314268498955)
          ·
            refine ⟨17034878653647471402748433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11356585769098314268498955 17034878653647471402748433)
            ·
              refine ⟨12776158990235603552061325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17034878653647471402748433 12776158990235603552061325)
              ·
                refine ⟨4791059621338351332022997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12776158990235603552061325 4791059621338351332022997)
                ·
                  refine ⟨112290459875117609344289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4791059621338351332022997 112290459875117609344289)
                  ·
                    rfl

theorem cell21_492041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_492041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492041 prefixEnd_492041 := by exact prefixLift 492041
  have htrace : WordTrace (prefixWord ++ tailWord_492041) baseStart_492041 baseEnd_492041 := by
    simpa [prefixWord, tailWord_492041, baseEnd_492041] using wordTrace_append hprefix tailTrace_492041
  have hstable : (prefixWord ++ tailWord_492041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492041).length < 2 ^ (prefixWord ++ tailWord_492041).sum := by decide
  have hdescent : baseEnd_492041 < baseStart_492041 := by decide
  rcases family_descends (prefixWord ++ tailWord_492041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492044 : List Nat := [2, 2, 1, 2, 4, 1, 4, 5]
def baseStart_492044 : Nat := 118140960795 + 492044 * 2 ^ 59
def prefixEnd_492044 : Nat := 4983230072969 + 3 ^ 40 * 492044 * 2
def baseEnd_492044 : Nat := 37430381505330090264761

theorem tailTrace_492044 : CollatzResearch.WordTrace tailWord_492044 prefixEnd_492044 37430381505330090264761 := by
  unfold tailWord_492044
  simp only [CollatzResearch.WordTrace]
  refine ⟨8973159514708048634993593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11964212686277398179991457 8973159514708048634993593)
  ·
    refine ⟨6729869636031036476245195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8973159514708048634993593 6729869636031036476245195)
    ·
      refine ⟨10094804454046554714367793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6729869636031036476245195 10094804454046554714367793)
      ·
        refine ⟨7571103340534916035775845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10094804454046554714367793 7571103340534916035775845)
        ·
          refine ⟨1419581876350296756707971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7571103340534916035775845 1419581876350296756707971)
          ·
            refine ⟨2129372814525445135061957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419581876350296756707971 2129372814525445135061957)
            ·
              refine ⟨399257402723520962824117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2129372814525445135061957 399257402723520962824117)
              ·
                refine ⟨37430381505330090264761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 399257402723520962824117 37430381505330090264761)
                ·
                  rfl

theorem cell21_492044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 5].length) (baseStart_492044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492044 prefixEnd_492044 := by exact prefixLift 492044
  have htrace : WordTrace (prefixWord ++ tailWord_492044) baseStart_492044 baseEnd_492044 := by
    simpa [prefixWord, tailWord_492044, baseEnd_492044] using wordTrace_append hprefix tailTrace_492044
  have hstable : (prefixWord ++ tailWord_492044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492044).length < 2 ^ (prefixWord ++ tailWord_492044).sum := by decide
  have hdescent : baseEnd_492044 < baseStart_492044 := by decide
  rcases family_descends (prefixWord ++ tailWord_492044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492089 : List Nat := [1, 2, 1, 5, 1, 1, 3, 3, 4]
def baseStart_492089 : Nat := 118140960795 + 492089 * 2 ^ 59
def prefixEnd_492089 : Nat := 4983230072969 + 3 ^ 40 * 492089 * 2
def baseEnd_492089 : Nat := 112301414129080192544191

theorem tailTrace_492089 : CollatzResearch.WordTrace tailWord_492089 prefixEnd_492089 112301414129080192544191 := by
  unfold tailWord_492089
  simp only [CollatzResearch.WordTrace]
  refine ⟨17947960314253069955375321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11965306876168713303583547 17947960314253069955375321)
  ·
    refine ⟨13460970235689802466531491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17947960314253069955375321 13460970235689802466531491)
    ·
      refine ⟨20191455353534703699797237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13460970235689802466531491 20191455353534703699797237)
      ·
        refine ⟨1892948939393878471855991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20191455353534703699797237 1892948939393878471855991)
        ·
          refine ⟨2839423409090817707783987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1892948939393878471855991 2839423409090817707783987)
          ·
            refine ⟨4259135113636226561675981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2839423409090817707783987 4259135113636226561675981)
            ·
              refine ⟨1597175667613584960628493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4259135113636226561675981 1597175667613584960628493)
              ·
                refine ⟨598940875355094360235685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1597175667613584960628493 598940875355094360235685)
                ·
                  refine ⟨112301414129080192544191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 598940875355094360235685 112301414129080192544191)
                  ·
                    rfl

theorem cell21_492089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_492089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492089 prefixEnd_492089 := by exact prefixLift 492089
  have htrace : WordTrace (prefixWord ++ tailWord_492089) baseStart_492089 baseEnd_492089 := by
    simpa [prefixWord, tailWord_492089, baseEnd_492089] using wordTrace_append hprefix tailTrace_492089
  have hstable : (prefixWord ++ tailWord_492089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492089).length < 2 ^ (prefixWord ++ tailWord_492089).sum := by decide
  have hdescent : baseEnd_492089 < baseStart_492089 := by decide
  rcases family_descends (prefixWord ++ tailWord_492089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492103 : List Nat := [1, 1, 4, 1, 4, 1, 2, 7]
def baseStart_492103 : Nat := 118140960795 + 492103 * 2 ^ 59
def prefixEnd_492103 : Nat := 4983230072969 + 3 ^ 40 * 492103 * 2
def baseEnd_492103 : Nat := 37434869706606426436943

theorem tailTrace_492103 : CollatzResearch.WordTrace tailWord_492103 prefixEnd_492103 37434869706606426436943 := by
  unfold tailWord_492103
  simp only [CollatzResearch.WordTrace]
  refine ⟨17948470936202350346384963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11965647290801566897589975 17948470936202350346384963)
  ·
    refine ⟨26922706404303525519577445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17948470936202350346384963 26922706404303525519577445)
    ·
      refine ⟨5048007450806911034920771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26922706404303525519577445 5048007450806911034920771)
      ·
        refine ⟨7572011176210366552381157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5048007450806911034920771 7572011176210366552381157)
        ·
          refine ⟨1419752095539443728571467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7572011176210366552381157 1419752095539443728571467)
          ·
            refine ⟨2129628143309165592857201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419752095539443728571467 2129628143309165592857201)
            ·
              refine ⟨1597221107481874194642901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2129628143309165592857201 1597221107481874194642901)
              ·
                refine ⟨37434869706606426436943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1597221107481874194642901 37434869706606426436943)
                ·
                  rfl

theorem cell21_492103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 7].length) (baseStart_492103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492103 prefixEnd_492103 := by exact prefixLift 492103
  have htrace : WordTrace (prefixWord ++ tailWord_492103) baseStart_492103 baseEnd_492103 := by
    simpa [prefixWord, tailWord_492103, baseEnd_492103] using wordTrace_append hprefix tailTrace_492103
  have hstable : (prefixWord ++ tailWord_492103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492103).length < 2 ^ (prefixWord ++ tailWord_492103).sum := by decide
  have hdescent : baseEnd_492103 < baseStart_492103 := by decide
  rcases family_descends (prefixWord ++ tailWord_492103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492213 : List Nat := [1, 3, 3, 3, 1, 3, 2, 5]
def baseStart_492213 : Nat := 118140960795 + 492213 * 2 ^ 59
def prefixEnd_492213 : Nat := 4983230072969 + 3 ^ 40 * 492213 * 2
def baseEnd_492213 : Nat := 37443237539494510825757

theorem tailTrace_492213 : CollatzResearch.WordTrace tailWord_492213 prefixEnd_492213 37443237539494510825757 := by
  unfold tailWord_492213
  simp only [CollatzResearch.WordTrace]
  refine ⟨17952482965803839132889293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11968321977202559421926195 17952482965803839132889293)
  ·
    refine ⟨6732181112176439674833485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17952482965803839132889293 6732181112176439674833485)
    ·
      refine ⟨2524567917066164878062557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6732181112176439674833485 2524567917066164878062557)
      ·
        refine ⟨946712968899811829273459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2524567917066164878062557 946712968899811829273459)
        ·
          refine ⟨1420069453349717743910189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946712968899811829273459 1420069453349717743910189)
          ·
            refine ⟨532526045006144153966321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1420069453349717743910189 532526045006144153966321)
            ·
              refine ⟨399394533754608115474741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532526045006144153966321 399394533754608115474741)
              ·
                refine ⟨37443237539494510825757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 399394533754608115474741 37443237539494510825757)
                ·
                  rfl

theorem cell21_492213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 5].length) (baseStart_492213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492213 prefixEnd_492213 := by exact prefixLift 492213
  have htrace : WordTrace (prefixWord ++ tailWord_492213) baseStart_492213 baseEnd_492213 := by
    simpa [prefixWord, tailWord_492213, baseEnd_492213] using wordTrace_append hprefix tailTrace_492213
  have hstable : (prefixWord ++ tailWord_492213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492213).length < 2 ^ (prefixWord ++ tailWord_492213).sum := by decide
  have hdescent : baseEnd_492213 < baseStart_492213 := by decide
  rcases family_descends (prefixWord ++ tailWord_492213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492224 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 6]
def baseStart_492224 : Nat := 118140960795 + 492224 * 2 ^ 59
def prefixEnd_492224 : Nat := 4983230072969 + 3 ^ 40 * 492224 * 2
def baseEnd_492224 : Nat := 112332222968349957793915

theorem tailTrace_492224 : CollatzResearch.WordTrace tailWord_492224 prefixEnd_492224 112332222968349957793915 := by
  unfold tailWord_492224
  simp only [CollatzResearch.WordTrace]
  refine ⟨8976442084381994005769863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11968589445842658674359817 8976442084381994005769863)
  ·
    refine ⟨13464663126572991008654795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8976442084381994005769863 13464663126572991008654795)
    ·
      refine ⟨20196994689859486512982193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13464663126572991008654795 20196994689859486512982193)
      ·
        refine ⟨15147746017394614884736645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20196994689859486512982193 15147746017394614884736645)
        ·
          refine ⟨2840202378261490290888121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15147746017394614884736645 2840202378261490290888121)
          ·
            refine ⟨2130151783696117718166091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2840202378261490290888121 2130151783696117718166091)
            ·
              refine ⟨3195227675544176577249137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2130151783696117718166091 3195227675544176577249137)
              ·
                refine ⟨2396420756658132432936853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3195227675544176577249137 2396420756658132432936853)
                ·
                  refine ⟨112332222968349957793915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2396420756658132432936853 112332222968349957793915)
                  ·
                    rfl

theorem cell21_492224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_492224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492224 prefixEnd_492224 := by exact prefixLift 492224
  have htrace : WordTrace (prefixWord ++ tailWord_492224) baseStart_492224 baseEnd_492224 := by
    simpa [prefixWord, tailWord_492224, baseEnd_492224] using wordTrace_append hprefix tailTrace_492224
  have hstable : (prefixWord ++ tailWord_492224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492224).length < 2 ^ (prefixWord ++ tailWord_492224).sum := by decide
  have hdescent : baseEnd_492224 < baseStart_492224 := by decide
  rcases family_descends (prefixWord ++ tailWord_492224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492230 : List Nat := [6, 1, 2, 1, 2, 2, 7]
def baseStart_492230 : Nat := 118140960795 + 492230 * 2 ^ 59
def prefixEnd_492230 : Nat := 4983230072969 + 3 ^ 40 * 492230 * 2
def baseEnd_492230 : Nat := 12481510250010586743767

theorem tailTrace_492230 : CollatzResearch.WordTrace tailWord_492230 prefixEnd_492230 12481510250010586743767 := by
  unfold tailWord_492230
  simp only [CollatzResearch.WordTrace]
  refine ⟨561034468960695344883067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11968735337828167357505429 561034468960695344883067)
  ·
    refine ⟨841551703441043017324601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 561034468960695344883067 841551703441043017324601)
    ·
      refine ⟨631163777580782262993451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 841551703441043017324601 631163777580782262993451)
      ·
        refine ⟨946745666371173394490177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631163777580782262993451 946745666371173394490177)
        ·
          refine ⟨710059249778380045867633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 946745666371173394490177 710059249778380045867633)
          ·
            refine ⟨532544437333785034400725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 710059249778380045867633 532544437333785034400725)
            ·
              refine ⟨12481510250010586743767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 532544437333785034400725 12481510250010586743767)
              ·
                rfl

theorem cell21_492230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 7].length) (baseStart_492230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492230 prefixEnd_492230 := by exact prefixLift 492230
  have htrace : WordTrace (prefixWord ++ tailWord_492230) baseStart_492230 baseEnd_492230 := by
    simpa [prefixWord, tailWord_492230, baseEnd_492230] using wordTrace_append hprefix tailTrace_492230
  have hstable : (prefixWord ++ tailWord_492230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492230).length < 2 ^ (prefixWord ++ tailWord_492230).sum := by decide
  have hdescent : baseEnd_492230 < baseStart_492230 := by decide
  rcases family_descends (prefixWord ++ tailWord_492230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492244 : List Nat := [2, 4, 1, 3, 2, 2, 1, 1, 5]
def baseStart_492244 : Nat := 118140960795 + 492244 * 2 ^ 59
def prefixEnd_492244 : Nat := 4983230072969 + 3 ^ 40 * 492244 * 2
def baseEnd_492244 : Nat := 112336787240834367460541

theorem tailTrace_492244 : CollatzResearch.WordTrace tailWord_492244 prefixEnd_492244 112336787240834367460541 := by
  unfold tailWord_492244
  simp only [CollatzResearch.WordTrace]
  refine ⟨8976806814345765713633893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11969075752461020951511857 8976806814345765713633893)
  ·
    refine ⟨1683151277689831071306355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8976806814345765713633893 1683151277689831071306355)
    ·
      refine ⟨2524726916534746606959533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1683151277689831071306355 2524726916534746606959533)
      ·
        refine ⟨946772593700529977609825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2524726916534746606959533 946772593700529977609825)
        ·
          refine ⟨710079445275397483207369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 946772593700529977609825 710079445275397483207369)
          ·
            refine ⟨532559583956548112405527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 710079445275397483207369 532559583956548112405527)
            ·
              refine ⟨798839375934822168608291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532559583956548112405527 798839375934822168608291)
              ·
                refine ⟨1198259063902233252912437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798839375934822168608291 1198259063902233252912437)
                ·
                  refine ⟨112336787240834367460541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1198259063902233252912437 112336787240834367460541)
                  ·
                    rfl

theorem cell21_492244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_492244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492244 prefixEnd_492244 := by exact prefixLift 492244
  have htrace : WordTrace (prefixWord ++ tailWord_492244) baseStart_492244 baseEnd_492244 := by
    simpa [prefixWord, tailWord_492244, baseEnd_492244] using wordTrace_append hprefix tailTrace_492244
  have hstable : (prefixWord ++ tailWord_492244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492244).length < 2 ^ (prefixWord ++ tailWord_492244).sum := by decide
  have hdescent : baseEnd_492244 < baseStart_492244 := by decide
  rcases family_descends (prefixWord ++ tailWord_492244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492255 : List Nat := [1, 1, 2, 3, 2, 4, 2, 6]
def baseStart_492255 : Nat := 118140960795 + 492255 * 2 ^ 59
def prefixEnd_492255 : Nat := 4983230072969 + 3 ^ 40 * 492255 * 2
def baseEnd_492255 : Nat := 37446432530233597592395

theorem tailTrace_492255 : CollatzResearch.WordTrace tailWord_492255 prefixEnd_492255 37446432530233597592395 := by
  unfold tailWord_492255
  simp only [CollatzResearch.WordTrace]
  refine ⟨17954014831651680305918219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11969343221101120203945479 17954014831651680305918219)
  ·
    refine ⟨26931022247477520458877329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17954014831651680305918219 26931022247477520458877329)
    ·
      refine ⟨20198266685608140344157997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26931022247477520458877329 20198266685608140344157997)
      ·
        refine ⟨7574350007103052629059249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20198266685608140344157997 7574350007103052629059249)
        ·
          refine ⟨5680762505327289471794437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7574350007103052629059249 5680762505327289471794437)
          ·
            refine ⟨1065142969748866775961457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5680762505327289471794437 1065142969748866775961457)
            ·
              refine ⟨798857227311650081971093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1065142969748866775961457 798857227311650081971093)
              ·
                refine ⟨37446432530233597592395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 798857227311650081971093 37446432530233597592395)
                ·
                  rfl

theorem cell21_492255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 6].length) (baseStart_492255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492255 prefixEnd_492255 := by exact prefixLift 492255
  have htrace : WordTrace (prefixWord ++ tailWord_492255) baseStart_492255 baseEnd_492255 := by
    simpa [prefixWord, tailWord_492255, baseEnd_492255] using wordTrace_append hprefix tailTrace_492255
  have hstable : (prefixWord ++ tailWord_492255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492255).length < 2 ^ (prefixWord ++ tailWord_492255).sum := by decide
  have hdescent : baseEnd_492255 < baseStart_492255 := by decide
  rcases family_descends (prefixWord ++ tailWord_492255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492306 : List Nat := [3, 2, 4, 1, 3, 1, 1, 6]
def baseStart_492306 : Nat := 118140960795 + 492306 * 2 ^ 59
def prefixEnd_492306 : Nat := 4983230072969 + 3 ^ 40 * 492306 * 2
def baseEnd_492306 : Nat := 37450312161845345809027

theorem tailTrace_492306 : CollatzResearch.WordTrace tailWord_492306 prefixEnd_492306 37450312161845345809027 := by
  unfold tailWord_492306
  simp only [CollatzResearch.WordTrace]
  refine ⟨4488968738616729004006193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11970583302977944010683181 4488968738616729004006193)
  ·
    refine ⟨3366726553962546753004645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4488968738616729004006193 3366726553962546753004645)
    ·
      refine ⟨631261228867977516188371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3366726553962546753004645 631261228867977516188371)
      ·
        refine ⟨946891843301966274282557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631261228867977516188371 946891843301966274282557)
        ·
          refine ⟨355084441238237352855959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 946891843301966274282557 355084441238237352855959)
          ·
            refine ⟨532626661857356029283939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355084441238237352855959 532626661857356029283939)
            ·
              refine ⟨798939992786034043925909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532626661857356029283939 798939992786034043925909)
              ·
                refine ⟨37450312161845345809027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 798939992786034043925909 37450312161845345809027)
                ·
                  rfl

theorem cell21_492306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_492306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492306 prefixEnd_492306 := by exact prefixLift 492306
  have htrace : WordTrace (prefixWord ++ tailWord_492306) baseStart_492306 baseEnd_492306 := by
    simpa [prefixWord, tailWord_492306, baseEnd_492306] using wordTrace_append hprefix tailTrace_492306
  have hstable : (prefixWord ++ tailWord_492306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492306).length < 2 ^ (prefixWord ++ tailWord_492306).sum := by decide
  have hdescent : baseEnd_492306 < baseStart_492306 := by decide
  rcases family_descends (prefixWord ++ tailWord_492306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492376 : List Nat := [2, 1, 2, 2, 1, 1, 1, 7, 4]
def baseStart_492376 : Nat := 118140960795 + 492376 * 2 ^ 59
def prefixEnd_492376 : Nat := 4983230072969 + 3 ^ 40 * 492376 * 2
def baseEnd_492376 : Nat := 112366911439231471260271

theorem tailTrace_492376 : CollatzResearch.WordTrace tailWord_492376 prefixEnd_492376 112366911439231471260271 := by
  unfold tailWord_492376
  simp only [CollatzResearch.WordTrace]
  refine ⟨8979214032106658985536491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11972285376142211980715321 8979214032106658985536491)
  ·
    refine ⟨13468821048159988478304737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8979214032106658985536491 13468821048159988478304737)
    ·
      refine ⟨10101615786119991358728553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13468821048159988478304737 10101615786119991358728553)
      ·
        refine ⟨7576211839589993519046415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10101615786119991358728553 7576211839589993519046415)
        ·
          refine ⟨11364317759384990278569623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7576211839589993519046415 11364317759384990278569623)
          ·
            refine ⟨17046476639077485417854435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11364317759384990278569623 17046476639077485417854435)
            ·
              refine ⟨25569714958616228126781653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17046476639077485417854435 25569714958616228126781653)
              ·
                refine ⟨599290194342567846721445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25569714958616228126781653 599290194342567846721445)
                ·
                  refine ⟨112366911439231471260271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 599290194342567846721445 112366911439231471260271)
                  ·
                    rfl

theorem cell21_492376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_492376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492376 prefixEnd_492376 := by exact prefixLift 492376
  have htrace : WordTrace (prefixWord ++ tailWord_492376) baseStart_492376 baseEnd_492376 := by
    simpa [prefixWord, tailWord_492376, baseEnd_492376] using wordTrace_append hprefix tailTrace_492376
  have hstable : (prefixWord ++ tailWord_492376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492376).length < 2 ^ (prefixWord ++ tailWord_492376).sum := by decide
  have hdescent : baseEnd_492376 < baseStart_492376 := by decide
  rcases family_descends (prefixWord ++ tailWord_492376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492435 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 8]
def baseStart_492435 : Nat := 118140960795 + 492435 * 2 ^ 59
def prefixEnd_492435 : Nat := 4983230072969 + 3 ^ 40 * 492435 * 2
def baseEnd_492435 : Nat := 112380376043060479776817

theorem tailTrace_492435 : CollatzResearch.WordTrace tailWord_492435 prefixEnd_492435 112380376043060479776817 := by
  unfold tailWord_492435
  simp only [CollatzResearch.WordTrace]
  refine ⟨17960579970999571047470759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11973719980666380698313839 17960579970999571047470759)
  ·
    refine ⟨26940869956499356571206139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17960579970999571047470759 26940869956499356571206139)
    ·
      refine ⟨40411304934749034856809209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26940869956499356571206139 40411304934749034856809209)
      ·
        refine ⟨30308478701061776142606907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40411304934749034856809209 30308478701061776142606907)
        ·
          refine ⟨45462718051592664213910361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30308478701061776142606907 45462718051592664213910361)
          ·
            refine ⟨34097038538694498160432771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45462718051592664213910361 34097038538694498160432771)
            ·
              refine ⟨51145557808041747240649157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34097038538694498160432771 51145557808041747240649157)
              ·
                refine ⟨9589792089007827607621717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51145557808041747240649157 9589792089007827607621717)
                ·
                  refine ⟨112380376043060479776817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9589792089007827607621717 112380376043060479776817)
                  ·
                    rfl

theorem cell21_492435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 8].length) (baseStart_492435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492435 prefixEnd_492435 := by exact prefixLift 492435
  have htrace : WordTrace (prefixWord ++ tailWord_492435) baseStart_492435 baseEnd_492435 := by
    simpa [prefixWord, tailWord_492435, baseEnd_492435] using wordTrace_append hprefix tailTrace_492435
  have hstable : (prefixWord ++ tailWord_492435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492435).length < 2 ^ (prefixWord ++ tailWord_492435).sum := by decide
  have hdescent : baseEnd_492435 < baseStart_492435 := by decide
  rcases family_descends (prefixWord ++ tailWord_492435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492469 : List Nat := [1, 3, 3, 2, 1, 1, 4, 2, 4]
def baseStart_492469 : Nat := 118140960795 + 492469 * 2 ^ 59
def prefixEnd_492469 : Nat := 4983230072969 + 3 ^ 40 * 492469 * 2
def baseEnd_492469 : Nat := 112388135306283976210081

theorem tailTrace_492469 : CollatzResearch.WordTrace tailWord_492469 prefixEnd_492469 112388135306283976210081 := by
  unfold tailWord_492469
  simp only [CollatzResearch.WordTrace]
  refine ⟨17961820052876394854208461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11974546701917596569472307 17961820052876394854208461)
  ·
    refine ⟨6735682519828648070328173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17961820052876394854208461 6735682519828648070328173)
    ·
      refine ⟨2525880944935743026373065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6735682519828648070328173 2525880944935743026373065)
      ·
        refine ⟨1894410708701807269779799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2525880944935743026373065 1894410708701807269779799)
        ·
          refine ⟨2841616063052710904669699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1894410708701807269779799 2841616063052710904669699)
          ·
            refine ⟨4262424094579066357004549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2841616063052710904669699 4262424094579066357004549)
            ·
              refine ⟨799204517733574941938353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4262424094579066357004549 799204517733574941938353)
              ·
                refine ⟨599403388300181206453765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 799204517733574941938353 599403388300181206453765)
                ·
                  refine ⟨112388135306283976210081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 599403388300181206453765 112388135306283976210081)
                  ·
                    rfl

theorem cell21_492469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_492469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492469 prefixEnd_492469 := by exact prefixLift 492469
  have htrace : WordTrace (prefixWord ++ tailWord_492469) baseStart_492469 baseEnd_492469 := by
    simpa [prefixWord, tailWord_492469, baseEnd_492469] using wordTrace_append hprefix tailTrace_492469
  have hstable : (prefixWord ++ tailWord_492469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492469).length < 2 ^ (prefixWord ++ tailWord_492469).sum := by decide
  have hdescent : baseEnd_492469 < baseStart_492469 := by decide
  rcases family_descends (prefixWord ++ tailWord_492469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492472 : List Nat := [2, 1, 2, 1, 2, 6, 2, 2, 3]
def baseStart_492472 : Nat := 118140960795 + 492472 * 2 ^ 59
def prefixEnd_492472 : Nat := 4983230072969 + 3 ^ 40 * 492472 * 2
def baseEnd_492472 : Nat := 112388819947156637660075

theorem tailTrace_492472 : CollatzResearch.WordTrace tailWord_492472 prefixEnd_492472 112388819947156637660075 := by
  unfold tailWord_492472
  simp only [CollatzResearch.WordTrace]
  refine ⟨8980964735932763183283835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11974619647910350911045113 8980964735932763183283835)
  ·
    refine ⟨13471447103899144774925753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8980964735932763183283835 13471447103899144774925753)
    ·
      refine ⟨10103585327924358581194315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13471447103899144774925753 10103585327924358581194315)
      ·
        refine ⟨15155377991886537871791473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10103585327924358581194315 15155377991886537871791473)
        ·
          refine ⟨11366533493914903403843605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15155377991886537871791473 11366533493914903403843605)
          ·
            refine ⟨532806257527261097055169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11366533493914903403843605 532806257527261097055169)
            ·
              refine ⟨399604693145445822791377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532806257527261097055169 399604693145445822791377)
              ·
                refine ⟨299703519859084367093533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 399604693145445822791377 299703519859084367093533)
                ·
                  refine ⟨112388819947156637660075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299703519859084367093533 112388819947156637660075)
                  ·
                    rfl

theorem cell21_492472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 3].length) (baseStart_492472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492472 prefixEnd_492472 := by exact prefixLift 492472
  have htrace : WordTrace (prefixWord ++ tailWord_492472) baseStart_492472 baseEnd_492472 := by
    simpa [prefixWord, tailWord_492472, baseEnd_492472] using wordTrace_append hprefix tailTrace_492472
  have hstable : (prefixWord ++ tailWord_492472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492472).length < 2 ^ (prefixWord ++ tailWord_492472).sum := by decide
  have hdescent : baseEnd_492472 < baseStart_492472 := by decide
  rcases family_descends (prefixWord ++ tailWord_492472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492497 : List Nat := [1, 2, 2, 1, 2, 1, 5, 2, 5]
def baseStart_492497 : Nat := 118140960795 + 492497 * 2 ^ 59
def prefixEnd_492497 : Nat := 4983230072969 + 3 ^ 40 * 492497 * 2
def baseEnd_492497 : Nat := 112394525287762149743357

theorem tailTrace_492497 : CollatzResearch.WordTrace tailWord_492497 prefixEnd_492497 112394525287762149743357 := by
  unfold tailWord_492497
  simp only [CollatzResearch.WordTrace]
  refine ⟨17962841296774955636227745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11975227531183303757485163 17962841296774955636227745)
  ·
    refine ⟨13472130972581216727170809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17962841296774955636227745 13472130972581216727170809)
    ·
      refine ⟨10104098229435912545378107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13472130972581216727170809 10104098229435912545378107)
      ·
        refine ⟨15156147344153868818067161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10104098229435912545378107 15156147344153868818067161)
        ·
          refine ⟨11367110508115401613550371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15156147344153868818067161 11367110508115401613550371)
          ·
            refine ⟨17050665762173102420325557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11367110508115401613550371 17050665762173102420325557)
            ·
              refine ⟨1598499915203728351905521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17050665762173102420325557 1598499915203728351905521)
              ·
                refine ⟨1198874936402796263929141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1598499915203728351905521 1198874936402796263929141)
                ·
                  refine ⟨112394525287762149743357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1198874936402796263929141 112394525287762149743357)
                  ·
                    rfl

theorem cell21_492497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_492497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492497 prefixEnd_492497 := by exact prefixLift 492497
  have htrace : WordTrace (prefixWord ++ tailWord_492497) baseStart_492497 baseEnd_492497 := by
    simpa [prefixWord, tailWord_492497, baseEnd_492497] using wordTrace_append hprefix tailTrace_492497
  have hstable : (prefixWord ++ tailWord_492497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492497).length < 2 ^ (prefixWord ++ tailWord_492497).sum := by decide
  have hdescent : baseEnd_492497 < baseStart_492497 := by decide
  rcases family_descends (prefixWord ++ tailWord_492497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492500 : List Nat := [2, 4, 1, 2, 1, 3, 3, 5]
def baseStart_492500 : Nat := 118140960795 + 492500 * 2 ^ 59
def prefixEnd_492500 : Nat := 4983230072969 + 3 ^ 40 * 492500 * 2
def baseEnd_492500 : Nat := 37465069976211603731117

theorem tailTrace_492500 : CollatzResearch.WordTrace tailWord_492500 prefixEnd_492500 37465069976211603731117 := by
  unfold tailWord_492500
  simp only [CollatzResearch.WordTrace]
  refine ⟨8981475357882043574293477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11975300477176058099057969 8981475357882043574293477)
  ·
    refine ⟨1684026629602883170180027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8981475357882043574293477 1684026629602883170180027)
    ·
      refine ⟨2526039944404324755270041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1684026629602883170180027 2526039944404324755270041)
      ·
        refine ⟨1894529958303243566452531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2526039944404324755270041 1894529958303243566452531)
        ·
          refine ⟨2841794937454865349678797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1894529958303243566452531 2841794937454865349678797)
          ·
            refine ⟨1065673101545574506129549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2841794937454865349678797 1065673101545574506129549)
            ·
              refine ⟨399627413079590439798581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1065673101545574506129549 399627413079590439798581)
              ·
                refine ⟨37465069976211603731117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 399627413079590439798581 37465069976211603731117)
                ·
                  rfl

theorem cell21_492500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 5].length) (baseStart_492500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492500 prefixEnd_492500 := by exact prefixLift 492500
  have htrace : WordTrace (prefixWord ++ tailWord_492500) baseStart_492500 baseEnd_492500 := by
    simpa [prefixWord, tailWord_492500, baseEnd_492500] using wordTrace_append hprefix tailTrace_492500
  have hstable : (prefixWord ++ tailWord_492500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492500).length < 2 ^ (prefixWord ++ tailWord_492500).sum := by decide
  have hdescent : baseEnd_492500 < baseStart_492500 := by decide
  rcases family_descends (prefixWord ++ tailWord_492500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492576 : List Nat := [2, 1, 1, 7, 1, 2, 7]
def baseStart_492576 : Nat := 118140960795 + 492576 * 2 ^ 59
def prefixEnd_492576 : Nat := 4983230072969 + 3 ^ 40 * 492576 * 2
def baseEnd_492576 : Nat := 12490283796008396436281

theorem tailTrace_492576 : CollatzResearch.WordTrace tailWord_492576 prefixEnd_492576 12490283796008396436281 := by
  unfold tailWord_492576
  simp only [CollatzResearch.WordTrace]
  refine ⟨8982861331744376064176791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11977148442325834752235721 8982861331744376064176791)
  ·
    refine ⟨13474291997616564096265187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8982861331744376064176791 13474291997616564096265187)
    ·
      refine ⟨20211437996424846144397781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13474291997616564096265187 20211437996424846144397781)
      ·
        refine ⟨473705578041207331509323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 20211437996424846144397781 473705578041207331509323)
        ·
          refine ⟨710558367061810997263985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473705578041207331509323 710558367061810997263985)
          ·
            refine ⟨532918775296358247947989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 710558367061810997263985 532918775296358247947989)
            ·
              refine ⟨12490283796008396436281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 532918775296358247947989 12490283796008396436281)
              ·
                rfl

theorem cell21_492576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 7].length) (baseStart_492576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492576 prefixEnd_492576 := by exact prefixLift 492576
  have htrace : WordTrace (prefixWord ++ tailWord_492576) baseStart_492576 baseEnd_492576 := by
    simpa [prefixWord, tailWord_492576, baseEnd_492576] using wordTrace_append hprefix tailTrace_492576
  have hstable : (prefixWord ++ tailWord_492576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492576).length < 2 ^ (prefixWord ++ tailWord_492576).sum := by decide
  have hdescent : baseEnd_492576 < baseStart_492576 := by decide
  rcases family_descends (prefixWord ++ tailWord_492576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492587 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 6]
def baseStart_492587 : Nat := 118140960795 + 492587 * 2 ^ 59
def prefixEnd_492587 : Nat := 4983230072969 + 3 ^ 40 * 492587 * 2
def baseEnd_492587 : Nat := 112415064513941993243173

theorem tailTrace_492587 : CollatzResearch.WordTrace tailWord_492587 prefixEnd_492587 112415064513941993243173 := by
  unfold tailWord_492587
  simp only [CollatzResearch.WordTrace]
  refine ⟨17966123866448901007004015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11977415910965934004669343 17966123866448901007004015)
  ·
    refine ⟨26949185799673351510506023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17966123866448901007004015 26949185799673351510506023)
    ·
      refine ⟨40423778699510027265759035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26949185799673351510506023 40423778699510027265759035)
      ·
        refine ⟨60635668049265040898638553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40423778699510027265759035 60635668049265040898638553)
        ·
          refine ⟨45476751036948780673978915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60635668049265040898638553 45476751036948780673978915)
          ·
            refine ⟨68215126555423171010968373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45476751036948780673978915 68215126555423171010968373)
            ·
              refine ⟨6395168114570922282278285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68215126555423171010968373 6395168114570922282278285)
              ·
                refine ⟨2398188042964095855854357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6395168114570922282278285 2398188042964095855854357)
                ·
                  refine ⟨112415064513941993243173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2398188042964095855854357 112415064513941993243173)
                  ·
                    rfl

theorem cell21_492587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 6].length) (baseStart_492587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492587 prefixEnd_492587 := by exact prefixLift 492587
  have htrace : WordTrace (prefixWord ++ tailWord_492587) baseStart_492587 baseEnd_492587 := by
    simpa [prefixWord, tailWord_492587, baseEnd_492587] using wordTrace_append hprefix tailTrace_492587
  have hstable : (prefixWord ++ tailWord_492587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492587).length < 2 ^ (prefixWord ++ tailWord_492587).sum := by decide
  have hdescent : baseEnd_492587 < baseStart_492587 := by decide
  rcases family_descends (prefixWord ++ tailWord_492587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492618 : List Nat := [3, 1, 2, 1, 1, 2, 4, 7]
def baseStart_492618 : Nat := 118140960795 + 492618 * 2 ^ 59
def prefixEnd_492618 : Nat := 4983230072969 + 3 ^ 40 * 492618 * 2
def baseEnd_492618 : Nat := 37474046378764276075481

theorem tailTrace_492618 : CollatzResearch.WordTrace tailWord_492618 prefixEnd_492618 37474046378764276075481 := by
  unfold tailWord_492618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4491813632334148325345627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11978169686224395534255005 4491813632334148325345627)
  ·
    refine ⟨6737720448501222488018441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4491813632334148325345627 6737720448501222488018441)
    ·
      refine ⟨5053290336375916866013831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6737720448501222488018441 5053290336375916866013831)
      ·
        refine ⟨7579935504563875299020747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5053290336375916866013831 7579935504563875299020747)
        ·
          refine ⟨11369903256845812948531121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7579935504563875299020747 11369903256845812948531121)
          ·
            refine ⟨8527427442634359711398341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11369903256845812948531121 8527427442634359711398341)
            ·
              refine ⟨1598892645493942445887189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8527427442634359711398341 1598892645493942445887189)
              ·
                refine ⟨37474046378764276075481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1598892645493942445887189 37474046378764276075481)
                ·
                  rfl

theorem cell21_492618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_492618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492618 prefixEnd_492618 := by exact prefixLift 492618
  have htrace : WordTrace (prefixWord ++ tailWord_492618) baseStart_492618 baseEnd_492618 := by
    simpa [prefixWord, tailWord_492618, baseEnd_492618] using wordTrace_append hprefix tailTrace_492618
  have hstable : (prefixWord ++ tailWord_492618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492618).length < 2 ^ (prefixWord ++ tailWord_492618).sum := by decide
  have hdescent : baseEnd_492618 < baseStart_492618 := by decide
  rcases family_descends (prefixWord ++ tailWord_492618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492773 : List Nat := [1, 3, 1, 4, 3, 1, 1, 3, 4]
def baseStart_492773 : Nat := 118140960795 + 492773 * 2 ^ 59
def prefixEnd_492773 : Nat := 4983230072969 + 3 ^ 40 * 492773 * 2
def baseEnd_492773 : Nat := 112457512248047003142793

theorem tailTrace_492773 : CollatzResearch.WordTrace tailWord_492773 prefixEnd_492773 112457512248047003142793 := by
  unfold tailWord_492773
  simp only [CollatzResearch.WordTrace]
  refine ⟨17972907843775054773274973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11981938562516703182183315 17972907843775054773274973)
  ·
    refine ⟨6739840441415645539978115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17972907843775054773274973 6739840441415645539978115)
    ·
      refine ⟨10109760662123468309967173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6739840441415645539978115 10109760662123468309967173)
      ·
        refine ⟨1895580124148150308118845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10109760662123468309967173 1895580124148150308118845)
        ·
          refine ⟨710842546555556365544567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1895580124148150308118845 710842546555556365544567)
          ·
            refine ⟨1066263819833334548316851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710842546555556365544567 1066263819833334548316851)
            ·
              refine ⟨1599395729750001822475277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066263819833334548316851 1599395729750001822475277)
              ·
                refine ⟨599773398656250683428229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1599395729750001822475277 599773398656250683428229)
                ·
                  refine ⟨112457512248047003142793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 599773398656250683428229 112457512248047003142793)
                  ·
                    rfl

theorem cell21_492773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_492773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_492773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_492773 prefixEnd_492773 := by exact prefixLift 492773
  have htrace : WordTrace (prefixWord ++ tailWord_492773) baseStart_492773 baseEnd_492773 := by
    simpa [prefixWord, tailWord_492773, baseEnd_492773] using wordTrace_append hprefix tailTrace_492773
  have hstable : (prefixWord ++ tailWord_492773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492773).length < 2 ^ (prefixWord ++ tailWord_492773).sum := by decide
  have hdescent : baseEnd_492773 < baseStart_492773 := by decide
  rcases family_descends (prefixWord ++ tailWord_492773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493043 : List Nat := [1, 1, 1, 2, 2, 2, 2, 6, 4]
def baseStart_493043 : Nat := 118140960795 + 493043 * 2 ^ 59
def prefixEnd_493043 : Nat := 4983230072969 + 3 ^ 40 * 493043 * 2
def baseEnd_493043 : Nat := 112519129926586533642241

theorem tailTrace_493043 : CollatzResearch.WordTrace tailWord_493043 prefixEnd_493043 112519129926586533642241 := by
  unfold tailWord_493043
  simp only [CollatzResearch.WordTrace]
  refine ⟨17982755552796890885603783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11988503701864593923735855 17982755552796890885603783)
  ·
    refine ⟨26974133329195336328405675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17982755552796890885603783 26974133329195336328405675)
    ·
      refine ⟨40461199993793004492608513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26974133329195336328405675 40461199993793004492608513)
      ·
        refine ⟨30345899995344753369456385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40461199993793004492608513 30345899995344753369456385)
        ·
          refine ⟨22759424996508565027092289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30345899995344753369456385 22759424996508565027092289)
          ·
            refine ⟨17069568747381423770319217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22759424996508565027092289 17069568747381423770319217)
            ·
              refine ⟨12802176560536067827739413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17069568747381423770319217 12802176560536067827739413)
              ·
                refine ⟨600102026275128179425285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12802176560536067827739413 600102026275128179425285)
                ·
                  refine ⟨112519129926586533642241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 600102026275128179425285 112519129926586533642241)
                  ·
                    rfl

theorem cell21_493043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 4].length) (baseStart_493043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493043 prefixEnd_493043 := by exact prefixLift 493043
  have htrace : WordTrace (prefixWord ++ tailWord_493043) baseStart_493043 baseEnd_493043 := by
    simpa [prefixWord, tailWord_493043, baseEnd_493043] using wordTrace_append hprefix tailTrace_493043
  have hstable : (prefixWord ++ tailWord_493043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493043).length < 2 ^ (prefixWord ++ tailWord_493043).sum := by decide
  have hdescent : baseEnd_493043 < baseStart_493043 := by decide
  rcases family_descends (prefixWord ++ tailWord_493043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493046 : List Nat := [5, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_493046 : Nat := 118140960795 + 493046 * 2 ^ 59
def prefixEnd_493046 : Nat := 4983230072969 + 3 ^ 40 * 493046 * 2
def baseEnd_493046 : Nat := 112519814567459195092235

theorem tailTrace_493046 : CollatzResearch.WordTrace tailWord_493046 prefixEnd_493046 112519814567459195092235 := by
  unfold tailWord_493046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1123929060736626399872687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11988576647857348265308661 1123929060736626399872687)
  ·
    refine ⟨1685893591104939599809031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1123929060736626399872687 1685893591104939599809031)
    ·
      refine ⟨2528840386657409399713547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1685893591104939599809031 2528840386657409399713547)
      ·
        refine ⟨3793260579986114099570321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2528840386657409399713547 3793260579986114099570321)
        ·
          refine ⟨2844945434989585574677741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3793260579986114099570321 2844945434989585574677741)
          ·
            refine ⟨1066854538121094590504153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2844945434989585574677741 1066854538121094590504153)
            ·
              refine ⟨800140903590820942878115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1066854538121094590504153 800140903590820942878115)
              ·
                refine ⟨1200211355386231414317173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 800140903590820942878115 1200211355386231414317173)
                ·
                  refine ⟨112519814567459195092235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1200211355386231414317173 112519814567459195092235)
                  ·
                    rfl

theorem cell21_493046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_493046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493046 prefixEnd_493046 := by exact prefixLift 493046
  have htrace : WordTrace (prefixWord ++ tailWord_493046) baseStart_493046 baseEnd_493046 := by
    simpa [prefixWord, tailWord_493046, baseEnd_493046] using wordTrace_append hprefix tailTrace_493046
  have hstable : (prefixWord ++ tailWord_493046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493046).length < 2 ^ (prefixWord ++ tailWord_493046).sum := by decide
  have hdescent : baseEnd_493046 < baseStart_493046 := by decide
  rcases family_descends (prefixWord ++ tailWord_493046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493080 : List Nat := [2, 1, 2, 3, 5, 1, 1, 3, 3]
def baseStart_493080 : Nat := 118140960795 + 493080 * 2 ^ 59
def prefixEnd_493080 : Nat := 4983230072969 + 3 ^ 40 * 493080 * 2
def baseEnd_493080 : Nat := 112527573830682691525499

theorem tailTrace_493080 : CollatzResearch.WordTrace tailWord_493080 prefixEnd_493080 112527573830682691525499 := by
  unfold tailWord_493080
  simp only [CollatzResearch.WordTrace]
  refine ⟨8992052526831423102350347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11989403369108564136467129 8992052526831423102350347)
  ·
    refine ⟨13488078790247134653525521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8992052526831423102350347 13488078790247134653525521)
    ·
      refine ⟨10116059092685350990144141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13488078790247134653525521 10116059092685350990144141)
      ·
        refine ⟨3793522159757006621304053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10116059092685350990144141 3793522159757006621304053)
        ·
          refine ⟨355642702477219370747255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3793522159757006621304053 355642702477219370747255)
          ·
            refine ⟨533464053715829056120883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355642702477219370747255 533464053715829056120883)
            ·
              refine ⟨800196080573743584181325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533464053715829056120883 800196080573743584181325)
              ·
                refine ⟨300073530215153844067997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 800196080573743584181325 300073530215153844067997)
                ·
                  refine ⟨112527573830682691525499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300073530215153844067997 112527573830682691525499)
                  ·
                    rfl

theorem cell21_493080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 3].length) (baseStart_493080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493080 prefixEnd_493080 := by exact prefixLift 493080
  have htrace : WordTrace (prefixWord ++ tailWord_493080) baseStart_493080 baseEnd_493080 := by
    simpa [prefixWord, tailWord_493080, baseEnd_493080] using wordTrace_append hprefix tailTrace_493080
  have hstable : (prefixWord ++ tailWord_493080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493080).length < 2 ^ (prefixWord ++ tailWord_493080).sum := by decide
  have hdescent : baseEnd_493080 < baseStart_493080 := by decide
  rcases family_descends (prefixWord ++ tailWord_493080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493091 : List Nat := [1, 1, 1, 4, 6, 1, 7]
def baseStart_493091 : Nat := 118140960795 + 493091 * 2 ^ 59
def prefixEnd_493091 : Nat := 4983230072969 + 3 ^ 40 * 493091 * 2
def baseEnd_493091 : Nat := 12503342686727679649127

theorem tailTrace_493091 : CollatzResearch.WordTrace tailWord_493091 prefixEnd_493091 12503342686727679649127 := by
  unfold tailWord_493091
  simp only [CollatzResearch.WordTrace]
  refine ⟨17984506256622995083351127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11989670837748663388900751 17984506256622995083351127)
  ·
    refine ⟨26976759384934492625026691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17984506256622995083351127 26976759384934492625026691)
    ·
      refine ⟨40465139077401738937540037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26976759384934492625026691 40465139077401738937540037)
      ·
        refine ⟨7587213577012826050788757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40465139077401738937540037 7587213577012826050788757)
        ·
          refine ⟨355650636422476221130723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7587213577012826050788757 355650636422476221130723)
          ·
            refine ⟨533475954633714331696085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355650636422476221130723 533475954633714331696085)
            ·
              refine ⟨12503342686727679649127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 533475954633714331696085 12503342686727679649127)
              ·
                rfl

theorem cell21_493091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 7].length) (baseStart_493091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493091 prefixEnd_493091 := by exact prefixLift 493091
  have htrace : WordTrace (prefixWord ++ tailWord_493091) baseStart_493091 baseEnd_493091 := by
    simpa [prefixWord, tailWord_493091, baseEnd_493091] using wordTrace_append hprefix tailTrace_493091
  have hstable : (prefixWord ++ tailWord_493091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493091).length < 2 ^ (prefixWord ++ tailWord_493091).sum := by decide
  have hdescent : baseEnd_493091 < baseStart_493091 := by decide
  rcases family_descends (prefixWord ++ tailWord_493091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493164 : List Nat := [2, 2, 1, 1, 3, 1, 1, 5, 5]
def baseStart_493164 : Nat := 118140960795 + 493164 * 2 ^ 59
def prefixEnd_493164 : Nat := 4983230072969 + 3 ^ 40 * 493164 * 2
def baseEnd_493164 : Nat := 112546743775117212125327

theorem tailTrace_493164 : CollatzResearch.WordTrace tailWord_493164 prefixEnd_493164 112546743775117212125327 := by
  unfold tailWord_493164
  simp only [CollatzResearch.WordTrace]
  refine ⟨8993584392679264275379273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11991445856905685700505697 8993584392679264275379273)
  ·
    refine ⟨6745188294509448206534455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8993584392679264275379273 6745188294509448206534455)
    ·
      refine ⟨10117782441764172309801683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6745188294509448206534455 10117782441764172309801683)
      ·
        refine ⟨15176673662646258464702525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10117782441764172309801683 15176673662646258464702525)
        ·
          refine ⟨5691252623492346924263447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15176673662646258464702525 5691252623492346924263447)
          ·
            refine ⟨8536878935238520386395171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5691252623492346924263447 8536878935238520386395171)
            ·
              refine ⟨12805318402857780579592757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8536878935238520386395171 12805318402857780579592757)
              ·
                refine ⟨1200498600267916929336821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12805318402857780579592757 1200498600267916929336821)
                ·
                  refine ⟨112546743775117212125327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1200498600267916929336821 112546743775117212125327)
                  ·
                    rfl

theorem cell21_493164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_493164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493164 prefixEnd_493164 := by exact prefixLift 493164
  have htrace : WordTrace (prefixWord ++ tailWord_493164) baseStart_493164 baseEnd_493164 := by
    simpa [prefixWord, tailWord_493164, baseEnd_493164] using wordTrace_append hprefix tailTrace_493164
  have hstable : (prefixWord ++ tailWord_493164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493164).length < 2 ^ (prefixWord ++ tailWord_493164).sum := by decide
  have hdescent : baseEnd_493164 < baseStart_493164 := by decide
  rcases family_descends (prefixWord ++ tailWord_493164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493181 : List Nat := [1, 4, 1, 1, 4, 2, 1, 2, 5]
def baseStart_493181 : Nat := 118140960795 + 493181 * 2 ^ 59
def prefixEnd_493181 : Nat := 4983230072969 + 3 ^ 40 * 493181 * 2
def baseEnd_493181 : Nat := 112550623406728960341959

theorem tailTrace_493181 : CollatzResearch.WordTrace tailWord_493181 prefixEnd_493181 112550623406728960341959 := by
  unfold tailWord_493181
  simp only [CollatzResearch.WordTrace]
  refine ⟨17987788826296940454127397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11991859217531293636084931 17987788826296940454127397)
  ·
    refine ⟨3372710404930676335148887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17987788826296940454127397 3372710404930676335148887)
    ·
      refine ⟨5059065607396014502723331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3372710404930676335148887 5059065607396014502723331)
      ·
        refine ⟨7588598411094021754084997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5059065607396014502723331 7588598411094021754084997)
        ·
          refine ⟨1422862202080129078890937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7588598411094021754084997 1422862202080129078890937)
          ·
            refine ⟨1067146651560096809168203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1422862202080129078890937 1067146651560096809168203)
            ·
              refine ⟨1600719977340145213752305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067146651560096809168203 1600719977340145213752305)
              ·
                refine ⟨1200539983005108910314229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1600719977340145213752305 1200539983005108910314229)
                ·
                  refine ⟨112550623406728960341959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1200539983005108910314229 112550623406728960341959)
                  ·
                    rfl

theorem cell21_493181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_493181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493181 prefixEnd_493181 := by exact prefixLift 493181
  have htrace : WordTrace (prefixWord ++ tailWord_493181) baseStart_493181 baseEnd_493181 := by
    simpa [prefixWord, tailWord_493181, baseEnd_493181] using wordTrace_append hprefix tailTrace_493181
  have hstable : (prefixWord ++ tailWord_493181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493181).length < 2 ^ (prefixWord ++ tailWord_493181).sum := by decide
  have hdescent : baseEnd_493181 < baseStart_493181 := by decide
  rcases family_descends (prefixWord ++ tailWord_493181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493198 : List Nat := [4, 1, 1, 3, 1, 2, 1, 5, 3]
def baseStart_493198 : Nat := 118140960795 + 493198 * 2 ^ 59
def prefixEnd_493198 : Nat := 4983230072969 + 3 ^ 40 * 493198 * 2
def baseEnd_493198 : Nat := 112554503038340708558591

theorem tailTrace_493198 : CollatzResearch.WordTrace tailWord_493198 prefixEnd_493198 112554503038340708558591 := by
  unfold tailWord_493198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2248551108404419044687031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11992272578156901571664165 2248551108404419044687031)
  ·
    refine ⟨3372826662606628567030547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2248551108404419044687031 3372826662606628567030547)
    ·
      refine ⟨5059239993909942850545821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3372826662606628567030547 5059239993909942850545821)
      ·
        refine ⟨1897214997716228568954683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5059239993909942850545821 1897214997716228568954683)
        ·
          refine ⟨2845822496574342853432025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897214997716228568954683 2845822496574342853432025)
          ·
            refine ⟨2134366872430757140074019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2845822496574342853432025 2134366872430757140074019)
            ·
              refine ⟨3201550308646135710111029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134366872430757140074019 3201550308646135710111029)
              ·
                refine ⟨300145341435575222822909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3201550308646135710111029 300145341435575222822909)
                ·
                  refine ⟨112554503038340708558591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300145341435575222822909 112554503038340708558591)
                  ·
                    rfl

theorem cell21_493198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_493198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493198 prefixEnd_493198 := by exact prefixLift 493198
  have htrace : WordTrace (prefixWord ++ tailWord_493198) baseStart_493198 baseEnd_493198 := by
    simpa [prefixWord, tailWord_493198, baseEnd_493198] using wordTrace_append hprefix tailTrace_493198
  have hstable : (prefixWord ++ tailWord_493198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493198).length < 2 ^ (prefixWord ++ tailWord_493198).sum := by decide
  have hdescent : baseEnd_493198 < baseStart_493198 := by decide
  rcases family_descends (prefixWord ++ tailWord_493198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493212 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 6]
def baseStart_493212 : Nat := 118140960795 + 493212 * 2 ^ 59
def prefixEnd_493212 : Nat := 4983230072969 + 3 ^ 40 * 493212 * 2
def baseEnd_493212 : Nat := 112557698029079795325229

theorem tailTrace_493212 : CollatzResearch.WordTrace tailWord_493212 prefixEnd_493212 112557698029079795325229 := by
  unfold tailWord_493212
  simp only [CollatzResearch.WordTrace]
  refine ⟨8994459744592316374252945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11992612992789755165670593 8994459744592316374252945)
  ·
    refine ⟨6745844808444237280689709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8994459744592316374252945 6745844808444237280689709)
    ·
      refine ⟨2529691803166588980258641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6745844808444237280689709 2529691803166588980258641)
      ·
        refine ⟨1897268852374941735193981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2529691803166588980258641 1897268852374941735193981)
        ·
          refine ⟨711475819640603150697743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1897268852374941735193981 711475819640603150697743)
          ·
            refine ⟨1067213729460904726046615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711475819640603150697743 1067213729460904726046615)
            ·
              refine ⟨1600820594191357089069923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067213729460904726046615 1600820594191357089069923)
              ·
                refine ⟨2401230891287035633604885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1600820594191357089069923 2401230891287035633604885)
                ·
                  refine ⟨112557698029079795325229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2401230891287035633604885 112557698029079795325229)
                  ·
                    rfl

theorem cell21_493212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_493212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493212 prefixEnd_493212 := by exact prefixLift 493212
  have htrace : WordTrace (prefixWord ++ tailWord_493212) baseStart_493212 baseEnd_493212 := by
    simpa [prefixWord, tailWord_493212, baseEnd_493212] using wordTrace_append hprefix tailTrace_493212
  have hstable : (prefixWord ++ tailWord_493212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493212).length < 2 ^ (prefixWord ++ tailWord_493212).sum := by decide
  have hdescent : baseEnd_493212 < baseStart_493212 := by decide
  rcases family_descends (prefixWord ++ tailWord_493212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493229 : List Nat := [1, 5, 2, 1, 1, 1, 5, 1, 4]
def baseStart_493229 : Nat := 118140960795 + 493229 * 2 ^ 59
def prefixEnd_493229 : Nat := 4983230072969 + 3 ^ 40 * 493229 * 2
def baseEnd_493229 : Nat := 112561577660691543541861

theorem tailTrace_493229 : CollatzResearch.WordTrace tailWord_493229 prefixEnd_493229 112561577660691543541861 := by
  unfold tailWord_493229
  simp only [CollatzResearch.WordTrace]
  refine ⟨17989539530123044651874741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11993026353415363101249827 17989539530123044651874741)
  ·
    refine ⟨1686519330949035436113257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17989539530123044651874741 1686519330949035436113257)
    ·
      refine ⟨1264889498211776577084943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1686519330949035436113257 1264889498211776577084943)
      ·
        refine ⟨1897334247317664865627415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1264889498211776577084943 1897334247317664865627415)
        ·
          refine ⟨2846001370976497298441123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897334247317664865627415 2846001370976497298441123)
          ·
            refine ⟨4269002056464745947661685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846001370976497298441123 4269002056464745947661685)
            ·
              refine ⟨400218942793569932593283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4269002056464745947661685 400218942793569932593283)
              ·
                refine ⟨600328414190354898889925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400218942793569932593283 600328414190354898889925)
                ·
                  refine ⟨112561577660691543541861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 600328414190354898889925 112561577660691543541861)
                  ·
                    rfl

theorem cell21_493229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_493229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493229 prefixEnd_493229 := by exact prefixLift 493229
  have htrace : WordTrace (prefixWord ++ tailWord_493229) baseStart_493229 baseEnd_493229 := by
    simpa [prefixWord, tailWord_493229, baseEnd_493229] using wordTrace_append hprefix tailTrace_493229
  have hstable : (prefixWord ++ tailWord_493229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493229).length < 2 ^ (prefixWord ++ tailWord_493229).sum := by decide
  have hdescent : baseEnd_493229 < baseStart_493229 := by decide
  rcases family_descends (prefixWord ++ tailWord_493229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493271 : List Nat := [1, 1, 3, 2, 1, 3, 2, 4, 4]
def baseStart_493271 : Nat := 118140960795 + 493271 * 2 ^ 59
def prefixEnd_493271 : Nat := 4983230072969 + 3 ^ 40 * 493271 * 2
def baseEnd_493271 : Nat := 112571162632908803841775

theorem tailTrace_493271 : CollatzResearch.WordTrace tailWord_493271 prefixEnd_493271 112571162632908803841775 := by
  unfold tailWord_493271
  simp only [CollatzResearch.WordTrace]
  refine ⟨17991071395970885824903667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11994047597313923883269111 17991071395970885824903667)
  ·
    refine ⟨26986607093956328737355501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17991071395970885824903667 26986607093956328737355501)
    ·
      refine ⟨10119977660233623276508313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26986607093956328737355501 10119977660233623276508313)
      ·
        refine ⟨7589983245175217457381235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10119977660233623276508313 7589983245175217457381235)
        ·
          refine ⟨11384974867762826186071853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7589983245175217457381235 11384974867762826186071853)
          ·
            refine ⟨4269365575411059819776945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11384974867762826186071853 4269365575411059819776945)
            ·
              refine ⟨3202024181558294864832709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4269365575411059819776945 3202024181558294864832709)
              ·
                refine ⟨600379534042180287156133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3202024181558294864832709 600379534042180287156133)
                ·
                  refine ⟨112571162632908803841775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 600379534042180287156133 112571162632908803841775)
                  ·
                    rfl

theorem cell21_493271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 4].length) (baseStart_493271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493271 prefixEnd_493271 := by exact prefixLift 493271
  have htrace : WordTrace (prefixWord ++ tailWord_493271) baseStart_493271 baseEnd_493271 := by
    simpa [prefixWord, tailWord_493271, baseEnd_493271] using wordTrace_append hprefix tailTrace_493271
  have hstable : (prefixWord ++ tailWord_493271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493271).length < 2 ^ (prefixWord ++ tailWord_493271).sum := by decide
  have hdescent : baseEnd_493271 < baseStart_493271 := by decide
  rcases family_descends (prefixWord ++ tailWord_493271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493288 : List Nat := [2, 1, 4, 1, 3, 2, 1, 3, 4]
def baseStart_493288 : Nat := 118140960795 + 493288 * 2 ^ 59
def prefixEnd_493288 : Nat := 4983230072969 + 3 ^ 40 * 493288 * 2
def baseEnd_493288 : Nat := 112575042264520552058407

theorem tailTrace_493288 : CollatzResearch.WordTrace tailWord_493288 prefixEnd_493288 112575042264520552058407 := by
  unfold tailWord_493288
  simp only [CollatzResearch.WordTrace]
  refine ⟨8995845718454648864136259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11994460957939531818848345 8995845718454648864136259)
  ·
    refine ⟨13493768577681973296204389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8995845718454648864136259 13493768577681973296204389)
    ·
      refine ⟨2530081608315369993038323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13493768577681973296204389 2530081608315369993038323)
      ·
        refine ⟨3795122412473054989557485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2530081608315369993038323 3795122412473054989557485)
        ·
          refine ⟨1423170904677395621084057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3795122412473054989557485 1423170904677395621084057)
          ·
            refine ⟨1067378178508046715813043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1423170904677395621084057 1067378178508046715813043)
            ·
              refine ⟨1601067267762070073719565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067378178508046715813043 1601067267762070073719565)
              ·
                refine ⟨600400225410776277644837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1601067267762070073719565 600400225410776277644837)
                ·
                  refine ⟨112575042264520552058407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 600400225410776277644837 112575042264520552058407)
                  ·
                    rfl

theorem cell21_493288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_493288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493288 prefixEnd_493288 := by exact prefixLift 493288
  have htrace : WordTrace (prefixWord ++ tailWord_493288) baseStart_493288 baseEnd_493288 := by
    simpa [prefixWord, tailWord_493288, baseEnd_493288] using wordTrace_append hprefix tailTrace_493288
  have hstable : (prefixWord ++ tailWord_493288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493288).length < 2 ^ (prefixWord ++ tailWord_493288).sum := by decide
  have hdescent : baseEnd_493288 < baseStart_493288 := by decide
  rcases family_descends (prefixWord ++ tailWord_493288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493302 : List Nat := [5, 1, 1, 1, 1, 3, 2, 7]
def baseStart_493302 : Nat := 118140960795 + 493302 * 2 ^ 59
def prefixEnd_493302 : Nat := 4983230072969 + 3 ^ 40 * 493302 * 2
def baseEnd_493302 : Nat := 37526079085086546275015

theorem tailTrace_493302 : CollatzResearch.WordTrace tailWord_493302 prefixEnd_493302 37526079085086546275015 := by
  unfold tailWord_493302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1124512628678661132455135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11994801372572385412854773 1124512628678661132455135)
  ·
    refine ⟨1686768943017991698682703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1124512628678661132455135 1686768943017991698682703)
    ·
      refine ⟨2530153414526987548024055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1686768943017991698682703 2530153414526987548024055)
      ·
        refine ⟨3795230121790481322036083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2530153414526987548024055 3795230121790481322036083)
        ·
          refine ⟨5692845182685721983054125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3795230121790481322036083 5692845182685721983054125)
          ·
            refine ⟨2134816943507145743645297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5692845182685721983054125 2134816943507145743645297)
            ·
              refine ⟨1601112707630359307733973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2134816943507145743645297 1601112707630359307733973)
              ·
                refine ⟨37526079085086546275015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1601112707630359307733973 37526079085086546275015)
                ·
                  rfl

theorem cell21_493302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_493302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493302 prefixEnd_493302 := by exact prefixLift 493302
  have htrace : WordTrace (prefixWord ++ tailWord_493302) baseStart_493302 baseEnd_493302 := by
    simpa [prefixWord, tailWord_493302, baseEnd_493302] using wordTrace_append hprefix tailTrace_493302
  have hstable : (prefixWord ++ tailWord_493302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493302).length < 2 ^ (prefixWord ++ tailWord_493302).sum := by decide
  have hdescent : baseEnd_493302 < baseStart_493302 := by decide
  rcases family_descends (prefixWord ++ tailWord_493302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493347 : List Nat := [1, 1, 1, 4, 2, 1, 4, 3, 4]
def baseStart_493347 : Nat := 118140960795 + 493347 * 2 ^ 59
def prefixEnd_493347 : Nat := 4983230072969 + 3 ^ 40 * 493347 * 2
def baseEnd_493347 : Nat := 112588506868349560574953

theorem tailTrace_493347 : CollatzResearch.WordTrace tailWord_493347 prefixEnd_493347 112588506868349560574953 := by
  unfold tailWord_493347
  simp only [CollatzResearch.WordTrace]
  refine ⟨17993843343695550804670295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11995895562463700536446863 17993843343695550804670295)
  ·
    refine ⟨26990765015543326207005443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17993843343695550804670295 26990765015543326207005443)
    ·
      refine ⟨40486147523314989310508165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26990765015543326207005443 40486147523314989310508165)
      ·
        refine ⟨7591152660621560495720281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40486147523314989310508165 7591152660621560495720281)
        ·
          refine ⟨5693364495466170371790211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7591152660621560495720281 5693364495466170371790211)
          ·
            refine ⟨8540046743199255557685317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5693364495466170371790211 8540046743199255557685317)
            ·
              refine ⟨1601258764349860417065997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8540046743199255557685317 1601258764349860417065997)
              ·
                refine ⟨600472036631197656399749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1601258764349860417065997 600472036631197656399749)
                ·
                  refine ⟨112588506868349560574953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 600472036631197656399749 112588506868349560574953)
                  ·
                    rfl

theorem cell21_493347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 4].length) (baseStart_493347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493347 prefixEnd_493347 := by exact prefixLift 493347
  have htrace : WordTrace (prefixWord ++ tailWord_493347) baseStart_493347 baseEnd_493347 := by
    simpa [prefixWord, tailWord_493347, baseEnd_493347] using wordTrace_append hprefix tailTrace_493347
  have hstable : (prefixWord ++ tailWord_493347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493347).length < 2 ^ (prefixWord ++ tailWord_493347).sum := by decide
  have hdescent : baseEnd_493347 < baseStart_493347 := by decide
  rcases family_descends (prefixWord ++ tailWord_493347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493412 : List Nat := [2, 3, 1, 1, 6, 1, 2, 5]
def baseStart_493412 : Nat := 118140960795 + 493412 * 2 ^ 59
def prefixEnd_493412 : Nat := 4983230072969 + 3 ^ 40 * 493412 * 2
def baseEnd_493412 : Nat := 37534446917974630663829

theorem tailTrace_493412 : CollatzResearch.WordTrace tailWord_493412 prefixEnd_493412 37534446917974630663829 := by
  unfold tailWord_493412
  simp only [CollatzResearch.WordTrace]
  refine ⟨8998107044230033452893245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11997476058973377937190993 8998107044230033452893245)
  ·
    refine ⟨3374290141586262544834967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8998107044230033452893245 3374290141586262544834967)
    ·
      refine ⟨5061435212379393817252451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3374290141586262544834967 5061435212379393817252451)
      ·
        refine ⟨7592152818569090725878677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5061435212379393817252451 7592152818569090725878677)
        ·
          refine ⟨355882163370426127775563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7592152818569090725878677 355882163370426127775563)
          ·
            refine ⟨533823245055639191663345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355882163370426127775563 533823245055639191663345)
            ·
              refine ⟨400367433791729393747509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533823245055639191663345 400367433791729393747509)
              ·
                refine ⟨37534446917974630663829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 400367433791729393747509 37534446917974630663829)
                ·
                  rfl

theorem cell21_493412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 5].length) (baseStart_493412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493412 prefixEnd_493412 := by exact prefixLift 493412
  have htrace : WordTrace (prefixWord ++ tailWord_493412) baseStart_493412 baseEnd_493412 := by
    simpa [prefixWord, tailWord_493412, baseEnd_493412] using wordTrace_append hprefix tailTrace_493412
  have hstable : (prefixWord ++ tailWord_493412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493412).length < 2 ^ (prefixWord ++ tailWord_493412).sum := by decide
  have hdescent : baseEnd_493412 < baseStart_493412 := by decide
  rcases family_descends (prefixWord ++ tailWord_493412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493502 : List Nat := [4, 2, 1, 1, 1, 4, 1, 4, 3]
def baseStart_493502 : Nat := 118140960795 + 493502 * 2 ^ 59
def prefixEnd_493502 : Nat := 4983230072969 + 3 ^ 40 * 493502 * 2
def baseEnd_493502 : Nat := 112623879980103735491303

theorem tailTrace_493502 : CollatzResearch.WordTrace tailWord_493502 prefixEnd_493502 112623879980103735491303 := by
  unfold tailWord_493502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2249937082266751534570345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11999664438756008184375173 2249937082266751534570345)
  ·
    refine ⟨1687452811700063650927759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2249937082266751534570345 1687452811700063650927759)
    ·
      refine ⟨2531179217550095476391639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1687452811700063650927759 2531179217550095476391639)
      ·
        refine ⟨3796768826325143214587459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2531179217550095476391639 3796768826325143214587459)
        ·
          refine ⟨5695153239487714821881189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3796768826325143214587459 5695153239487714821881189)
          ·
            refine ⟨1067841232403946529102723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5695153239487714821881189 1067841232403946529102723)
            ·
              refine ⟨1601761848605919793654085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067841232403946529102723 1601761848605919793654085)
              ·
                refine ⟨300330346613609961310141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1601761848605919793654085 300330346613609961310141)
                ·
                  refine ⟨112623879980103735491303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300330346613609961310141 112623879980103735491303)
                  ·
                    rfl

theorem cell21_493502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_493502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493502 prefixEnd_493502 := by exact prefixLift 493502
  have htrace : WordTrace (prefixWord ++ tailWord_493502) baseStart_493502 baseEnd_493502 := by
    simpa [prefixWord, tailWord_493502, baseEnd_493502] using wordTrace_append hprefix tailTrace_493502
  have hstable : (prefixWord ++ tailWord_493502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493502).length < 2 ^ (prefixWord ++ tailWord_493502).sum := by decide
  have hdescent : baseEnd_493502 < baseStart_493502 := by decide
  rcases family_descends (prefixWord ++ tailWord_493502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493561 : List Nat := [1, 2, 1, 3, 1, 4, 2, 4, 3]
def baseStart_493561 : Nat := 118140960795 + 493561 * 2 ^ 59
def prefixEnd_493561 : Nat := 4983230072969 + 3 ^ 40 * 493561 * 2
def baseEnd_493561 : Nat := 112637344583932744007849

theorem tailTrace_493561 : CollatzResearch.WordTrace tailWord_493561 prefixEnd_493561 112637344583932744007849 := by
  unfold tailWord_493561
  simp only [CollatzResearch.WordTrace]
  refine ⟨18001648564920265352960537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12001099043280176901973691 18001648564920265352960537)
  ·
    refine ⟨13501236423690199014720403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18001648564920265352960537 13501236423690199014720403)
    ·
      refine ⟨20251854635535298522080605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13501236423690199014720403 20251854635535298522080605)
      ·
        refine ⟨7594445488325736945780227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20251854635535298522080605 7594445488325736945780227)
        ·
          refine ⟨11391668232488605418670341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7594445488325736945780227 11391668232488605418670341)
          ·
            refine ⟨2135937793591613516000689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11391668232488605418670341 2135937793591613516000689)
            ·
              refine ⟨1601953345193710137000517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2135937793591613516000689 1601953345193710137000517)
              ·
                refine ⟨300366252223820650687597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1601953345193710137000517 300366252223820650687597)
                ·
                  refine ⟨112637344583932744007849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300366252223820650687597 112637344583932744007849)
                  ·
                    rfl

theorem cell21_493561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 3].length) (baseStart_493561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493561 prefixEnd_493561 := by exact prefixLift 493561
  have htrace : WordTrace (prefixWord ++ tailWord_493561) baseStart_493561 baseEnd_493561 := by
    simpa [prefixWord, tailWord_493561, baseEnd_493561] using wordTrace_append hprefix tailTrace_493561
  have hstable : (prefixWord ++ tailWord_493561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493561).length < 2 ^ (prefixWord ++ tailWord_493561).sum := by decide
  have hdescent : baseEnd_493561 < baseStart_493561 := by decide
  rcases family_descends (prefixWord ++ tailWord_493561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493682 : List Nat := [3, 2, 1, 2, 2, 4, 1, 6]
def baseStart_493682 : Nat := 118140960795 + 493682 * 2 ^ 59
def prefixEnd_493682 : Nat := 4983230072969 + 3 ^ 40 * 493682 * 2
def baseEnd_493682 : Nat := 37554986144154474163645

theorem tailTrace_493682 : CollatzResearch.WordTrace tailWord_493682 prefixEnd_493682 37554986144154474163645 := by
  unfold tailWord_493682
  simp only [CollatzResearch.WordTrace]
  refine ⟨4501515449370475754528825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12004041198321268678743533 4501515449370475754528825)
  ·
    refine ⟨3376136587027856815896619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4501515449370475754528825 3376136587027856815896619)
    ·
      refine ⟨5064204880541785223844929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3376136587027856815896619 5064204880541785223844929)
      ·
        refine ⟨3798153660406338917883697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5064204880541785223844929 3798153660406338917883697)
        ·
          refine ⟨2848615245304754188412773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3798153660406338917883697 2848615245304754188412773)
          ·
            refine ⟨534115358494641410327395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2848615245304754188412773 534115358494641410327395)
            ·
              refine ⟨801173037741962115491093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534115358494641410327395 801173037741962115491093)
              ·
                refine ⟨37554986144154474163645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 801173037741962115491093 37554986144154474163645)
                ·
                  rfl

theorem cell21_493682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_493682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493682 prefixEnd_493682 := by exact prefixLift 493682
  have htrace : WordTrace (prefixWord ++ tailWord_493682) baseStart_493682 baseEnd_493682 := by
    simpa [prefixWord, tailWord_493682, baseEnd_493682] using wordTrace_append hprefix tailTrace_493682
  have hstable : (prefixWord ++ tailWord_493682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493682).length < 2 ^ (prefixWord ++ tailWord_493682).sum := by decide
  have hdescent : baseEnd_493682 < baseStart_493682 := by decide
  rcases family_descends (prefixWord ++ tailWord_493682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493727 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 6]
def baseStart_493727 : Nat := 118140960795 + 493727 * 2 ^ 59
def prefixEnd_493727 : Nat := 4983230072969 + 3 ^ 40 * 493727 * 2
def baseEnd_493727 : Nat := 112675228045553344240843

theorem tailTrace_493727 : CollatzResearch.WordTrace tailWord_493727 prefixEnd_493727 112675228045553344240843 := by
  unfold tailWord_493727
  simp only [CollatzResearch.WordTrace]
  refine ⟨18007703082318875703503435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12005135388212583802335623 18007703082318875703503435)
  ·
    refine ⟨27011554623478313555255153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18007703082318875703503435 27011554623478313555255153)
    ·
      refine ⟨20258665967608735166441365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27011554623478313555255153 20258665967608735166441365)
      ·
        refine ⟨949624967231659460926939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20258665967608735166441365 949624967231659460926939)
        ·
          refine ⟨1424437450847489191390409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949624967231659460926939 1424437450847489191390409)
          ·
            refine ⟨1068328088135616893542807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1424437450847489191390409 1068328088135616893542807)
            ·
              refine ⟨1602492132203425340314211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068328088135616893542807 1602492132203425340314211)
              ·
                refine ⟨2403738198305138010471317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1602492132203425340314211 2403738198305138010471317)
                ·
                  refine ⟨112675228045553344240843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2403738198305138010471317 112675228045553344240843)
                  ·
                    rfl

theorem cell21_493727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 6].length) (baseStart_493727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493727 prefixEnd_493727 := by exact prefixLift 493727
  have htrace : WordTrace (prefixWord ++ tailWord_493727) baseStart_493727 baseEnd_493727 := by
    simpa [prefixWord, tailWord_493727, baseEnd_493727] using wordTrace_append hprefix tailTrace_493727
  have hstable : (prefixWord ++ tailWord_493727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493727).length < 2 ^ (prefixWord ++ tailWord_493727).sum := by decide
  have hdescent : baseEnd_493727 < baseStart_493727 := by decide
  rcases family_descends (prefixWord ++ tailWord_493727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493730 : List Nat := [3, 3, 1, 3, 1, 1, 2, 4, 3]
def baseStart_493730 : Nat := 118140960795 + 493730 * 2 ^ 59
def prefixEnd_493730 : Nat := 4983230072969 + 3 ^ 40 * 493730 * 2
def baseEnd_493730 : Nat := 112675912686426005690837

theorem tailTrace_493730 : CollatzResearch.WordTrace tailWord_493730 prefixEnd_493730 112675912686426005690837 := by
  unfold tailWord_493730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4501953125327001803965661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12005208334205338143908429 4501953125327001803965661)
  ·
    refine ⟨1688232421997625676487123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4501953125327001803965661 1688232421997625676487123)
    ·
      refine ⟨2532348632996438514730685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1688232421997625676487123 2532348632996438514730685)
      ·
        refine ⟨949630737373664443024007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2532348632996438514730685 949630737373664443024007)
        ·
          refine ⟨1424446106060496664536011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949630737373664443024007 1424446106060496664536011)
          ·
            refine ⟨2136669159090744996804017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424446106060496664536011 2136669159090744996804017)
            ·
              refine ⟨1602501869318058747603013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2136669159090744996804017 1602501869318058747603013)
              ·
                refine ⟨300469100497136015175565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1602501869318058747603013 300469100497136015175565)
                ·
                  refine ⟨112675912686426005690837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300469100497136015175565 112675912686426005690837)
                  ·
                    rfl

theorem cell21_493730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_493730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493730 prefixEnd_493730 := by exact prefixLift 493730
  have htrace : WordTrace (prefixWord ++ tailWord_493730) baseStart_493730 baseEnd_493730 := by
    simpa [prefixWord, tailWord_493730, baseEnd_493730] using wordTrace_append hprefix tailTrace_493730
  have hstable : (prefixWord ++ tailWord_493730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493730).length < 2 ^ (prefixWord ++ tailWord_493730).sum := by decide
  have hdescent : baseEnd_493730 < baseStart_493730 := by decide
  rcases family_descends (prefixWord ++ tailWord_493730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493755 : List Nat := [1, 1, 1, 1, 1, 2, 5, 4, 5]
def baseStart_493755 : Nat := 118140960795 + 493755 * 2 ^ 59
def prefixEnd_493755 : Nat := 4983230072969 + 3 ^ 40 * 493755 * 2
def baseEnd_493755 : Nat := 112681618027031517774119

theorem tailTrace_493755 : CollatzResearch.WordTrace tailWord_493755 prefixEnd_493755 112681618027031517774119 := by
  unfold tailWord_493755
  simp only [CollatzResearch.WordTrace]
  refine ⟨18008724326217436485522719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12005816217478290990348479 18008724326217436485522719)
  ·
    refine ⟨27013086489326154728284079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18008724326217436485522719 27013086489326154728284079)
    ·
      refine ⟨40519629733989232092426119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27013086489326154728284079 40519629733989232092426119)
      ·
        refine ⟨60779444600983848138639179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40519629733989232092426119 60779444600983848138639179)
        ·
          refine ⟨91169166901475772207958769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60779444600983848138639179 91169166901475772207958769)
          ·
            refine ⟨68376875176106829155969077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91169166901475772207958769 68376875176106829155969077)
            ·
              refine ⟨6410332047760015233372101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68376875176106829155969077 6410332047760015233372101)
              ·
                refine ⟨1201937258955002856257269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6410332047760015233372101 1201937258955002856257269)
                ·
                  refine ⟨112681618027031517774119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1201937258955002856257269 112681618027031517774119)
                  ·
                    rfl

theorem cell21_493755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 5].length) (baseStart_493755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493755 prefixEnd_493755 := by exact prefixLift 493755
  have htrace : WordTrace (prefixWord ++ tailWord_493755) baseStart_493755 baseEnd_493755 := by
    simpa [prefixWord, tailWord_493755, baseEnd_493755] using wordTrace_append hprefix tailTrace_493755
  have hstable : (prefixWord ++ tailWord_493755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493755).length < 2 ^ (prefixWord ++ tailWord_493755).sum := by decide
  have hdescent : baseEnd_493755 < baseStart_493755 := by decide
  rcases family_descends (prefixWord ++ tailWord_493755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493758 : List Nat := [4, 2, 1, 1, 4, 1, 1, 7]
def baseStart_493758 : Nat := 118140960795 + 493758 * 2 ^ 59
def prefixEnd_493758 : Nat := 4983230072969 + 3 ^ 40 * 493758 * 2
def baseEnd_493758 : Nat := 37560767555968059741371

theorem tailTrace_493758 : CollatzResearch.WordTrace tailWord_493758 prefixEnd_493758 37560767555968059741371 := by
  unfold tailWord_493758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2251104218150820999735241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12005889163471045331921285 2251104218150820999735241)
  ·
    refine ⟨1688328163613115749801431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2251104218150820999735241 1688328163613115749801431)
    ·
      refine ⟨2532492245419673624702147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1688328163613115749801431 2532492245419673624702147)
      ·
        refine ⟨3798738368129510437053221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2532492245419673624702147 3798738368129510437053221)
        ·
          refine ⟨712263444024283206947479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3798738368129510437053221 712263444024283206947479)
          ·
            refine ⟨1068395166036424810421219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712263444024283206947479 1068395166036424810421219)
            ·
              refine ⟨1602592749054637215631829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068395166036424810421219 1602592749054637215631829)
              ·
                refine ⟨37560767555968059741371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1602592749054637215631829 37560767555968059741371)
                ·
                  rfl

theorem cell21_493758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_493758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493758 prefixEnd_493758 := by exact prefixLift 493758
  have htrace : WordTrace (prefixWord ++ tailWord_493758) baseStart_493758 baseEnd_493758 := by
    simpa [prefixWord, tailWord_493758, baseEnd_493758] using wordTrace_append hprefix tailTrace_493758
  have hstable : (prefixWord ++ tailWord_493758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493758).length < 2 ^ (prefixWord ++ tailWord_493758).sum := by decide
  have hdescent : baseEnd_493758 < baseStart_493758 := by decide
  rcases family_descends (prefixWord ++ tailWord_493758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493786 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 6]
def baseStart_493786 : Nat := 118140960795 + 493786 * 2 ^ 59
def prefixEnd_493786 : Nat := 4983230072969 + 3 ^ 40 * 493786 * 2
def baseEnd_493786 : Nat := 112688692649382352757389

theorem tailTrace_493786 : CollatzResearch.WordTrace tailWord_493786 prefixEnd_493786 112688692649382352757389 := by
  unfold tailWord_493786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4502463747276282194975303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12006569992736752519934141 4502463747276282194975303)
  ·
    refine ⟨6753695620914423292462955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4502463747276282194975303 6753695620914423292462955)
    ·
      refine ⟨10130543431371634938694433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6753695620914423292462955 10130543431371634938694433)
      ·
        refine ⟨7597907573528726204020825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10130543431371634938694433 7597907573528726204020825)
        ·
          refine ⟨5698430680146544653015619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7597907573528726204020825 5698430680146544653015619)
          ·
            refine ⟨8547646020219816979523429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5698430680146544653015619 8547646020219816979523429)
            ·
              refine ⟨1602683628791215683660643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8547646020219816979523429 1602683628791215683660643)
              ·
                refine ⟨2404025443186823525490965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1602683628791215683660643 2404025443186823525490965)
                ·
                  refine ⟨112688692649382352757389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2404025443186823525490965 112688692649382352757389)
                  ·
                    rfl

theorem cell21_493786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_493786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493786 prefixEnd_493786 := by exact prefixLift 493786
  have htrace : WordTrace (prefixWord ++ tailWord_493786) baseStart_493786 baseEnd_493786 := by
    simpa [prefixWord, tailWord_493786, baseEnd_493786] using wordTrace_append hprefix tailTrace_493786
  have hstable : (prefixWord ++ tailWord_493786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493786).length < 2 ^ (prefixWord ++ tailWord_493786).sum := by decide
  have hdescent : baseEnd_493786 < baseStart_493786 := by decide
  rcases family_descends (prefixWord ++ tailWord_493786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493789 : List Nat := [1, 4, 3, 2, 1, 1, 3, 1, 5]
def baseStart_493789 : Nat := 118140960795 + 493789 * 2 ^ 59
def prefixEnd_493789 : Nat := 4983230072969 + 3 ^ 40 * 493789 * 2
def baseEnd_493789 : Nat := 112689377290255014207383

theorem tailTrace_493789 : CollatzResearch.WordTrace tailWord_493789 prefixEnd_493789 112689377290255014207383 := by
  unfold tailWord_493789
  simp only [CollatzResearch.WordTrace]
  refine ⟨18009964408094260292260421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12006642938729506861506947 18009964408094260292260421)
  ·
    refine ⟨3376868326517673804798829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18009964408094260292260421 3376868326517673804798829)
    ·
      refine ⟨1266325622444127676799561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3376868326517673804798829 1266325622444127676799561)
      ·
        refine ⟨949744216833095757599671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1266325622444127676799561 949744216833095757599671)
        ·
          refine ⟨1424616325249643636399507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949744216833095757599671 1424616325249643636399507)
          ·
            refine ⟨2136924487874465454599261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424616325249643636399507 2136924487874465454599261)
            ·
              refine ⟨801346682952924545474723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2136924487874465454599261 801346682952924545474723)
              ·
                refine ⟨1202020024429386818212085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801346682952924545474723 1202020024429386818212085)
                ·
                  refine ⟨112689377290255014207383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1202020024429386818212085 112689377290255014207383)
                  ·
                    rfl

theorem cell21_493789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_493789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493789 prefixEnd_493789 := by exact prefixLift 493789
  have htrace : WordTrace (prefixWord ++ tailWord_493789) baseStart_493789 baseEnd_493789 := by
    simpa [prefixWord, tailWord_493789, baseEnd_493789] using wordTrace_append hprefix tailTrace_493789
  have hstable : (prefixWord ++ tailWord_493789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493789).length < 2 ^ (prefixWord ++ tailWord_493789).sum := by decide
  have hdescent : baseEnd_493789 < baseStart_493789 := by decide
  rcases family_descends (prefixWord ++ tailWord_493789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493938 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 6]
def baseStart_493938 : Nat := 118140960795 + 493938 * 2 ^ 59
def prefixEnd_493938 : Nat := 4983230072969 + 3 ^ 40 * 493938 * 2
def baseEnd_493938 : Nat := 112723381120263866223745

theorem tailTrace_493938 : CollatzResearch.WordTrace tailWord_493938 prefixEnd_493938 112723381120263866223745 := by
  unfold tailWord_493938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4503849721138614684858617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12010265923036305826289645 4503849721138614684858617)
  ·
    refine ⟨3377887290853961013643963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4503849721138614684858617 3377887290853961013643963)
    ·
      refine ⟨5066830936280941520465945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3377887290853961013643963 5066830936280941520465945)
      ·
        refine ⟨3800123202210706140349459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5066830936280941520465945 3800123202210706140349459)
        ·
          refine ⟨5700184803316059210524189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3800123202210706140349459 5700184803316059210524189)
          ·
            refine ⟨2137569301243522203946571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5700184803316059210524189 2137569301243522203946571)
            ·
              refine ⟨3206353951865283305919857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137569301243522203946571 3206353951865283305919857)
              ·
                refine ⟨2404765463898962479439893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3206353951865283305919857 2404765463898962479439893)
                ·
                  refine ⟨112723381120263866223745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2404765463898962479439893 112723381120263866223745)
                  ·
                    rfl

theorem cell21_493938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_493938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493938 prefixEnd_493938 := by exact prefixLift 493938
  have htrace : WordTrace (prefixWord ++ tailWord_493938) baseStart_493938 baseEnd_493938 := by
    simpa [prefixWord, tailWord_493938, baseEnd_493938] using wordTrace_append hprefix tailTrace_493938
  have hstable : (prefixWord ++ tailWord_493938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493938).length < 2 ^ (prefixWord ++ tailWord_493938).sum := by decide
  have hdescent : baseEnd_493938 < baseStart_493938 := by decide
  rcases family_descends (prefixWord ++ tailWord_493938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493972 : List Nat := [2, 4, 2, 1, 3, 1, 1, 3, 4]
def baseStart_493972 : Nat := 118140960795 + 493972 * 2 ^ 59
def prefixEnd_493972 : Nat := 4983230072969 + 3 ^ 40 * 493972 * 2
def baseEnd_493972 : Nat := 112731140383487362657009

theorem tailTrace_493972 : CollatzResearch.WordTrace tailWord_493972 prefixEnd_493972 112731140383487362657009 := by
  unfold tailWord_493972
  simp only [CollatzResearch.WordTrace]
  refine ⟨9008319483215641273086085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12011092644287521697448113 9008319483215641273086085)
  ·
    refine ⟨1689059903102932738703641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9008319483215641273086085 1689059903102932738703641)
    ·
      refine ⟨1266794927327199554027731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1689059903102932738703641 1266794927327199554027731)
      ·
        refine ⟨1900192390990799331041597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1266794927327199554027731 1900192390990799331041597)
        ·
          refine ⟨712572146621549749140599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1900192390990799331041597 712572146621549749140599)
          ·
            refine ⟨1068858219932324623710899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712572146621549749140599 1068858219932324623710899)
            ·
              refine ⟨1603287329898486935566349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068858219932324623710899 1603287329898486935566349)
              ·
                refine ⟨601232748711932600837381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1603287329898486935566349 601232748711932600837381)
                ·
                  refine ⟨112731140383487362657009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 601232748711932600837381 112731140383487362657009)
                  ·
                    rfl

theorem cell21_493972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_493972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493972 prefixEnd_493972 := by exact prefixLift 493972
  have htrace : WordTrace (prefixWord ++ tailWord_493972) baseStart_493972 baseEnd_493972 := by
    simpa [prefixWord, tailWord_493972, baseEnd_493972] using wordTrace_append hprefix tailTrace_493972
  have hstable : (prefixWord ++ tailWord_493972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493972).length < 2 ^ (prefixWord ++ tailWord_493972).sum := by decide
  have hdescent : baseEnd_493972 < baseStart_493972 := by decide
  rcases family_descends (prefixWord ++ tailWord_493972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493983 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 7]
def baseStart_493983 : Nat := 118140960795 + 493983 * 2 ^ 59
def prefixEnd_493983 : Nat := 4983230072969 + 3 ^ 40 * 493983 * 2
def baseEnd_493983 : Nat := 112733650733353787973653

theorem tailTrace_493983 : CollatzResearch.WordTrace tailWord_493983 prefixEnd_493983 112733650733353787973653 := by
  unfold tailWord_493983
  simp only [CollatzResearch.WordTrace]
  refine ⟨18017040169391431424822603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12011360112927620949881735 18017040169391431424822603)
  ·
    refine ⟨27025560254087147137233905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18017040169391431424822603 27025560254087147137233905)
    ·
      refine ⟨20269170190565360352925429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27025560254087147137233905 20269170190565360352925429)
      ·
        refine ⟨1900234705365502533086759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20269170190565360352925429 1900234705365502533086759)
        ·
          refine ⟨2850352058048253799630139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900234705365502533086759 2850352058048253799630139)
          ·
            refine ⟨4275528087072380699445209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2850352058048253799630139 4275528087072380699445209)
            ·
              refine ⟨3206646065304285524583907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4275528087072380699445209 3206646065304285524583907)
              ·
                refine ⟨4809969097956428286875861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3206646065304285524583907 4809969097956428286875861)
                ·
                  refine ⟨112733650733353787973653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4809969097956428286875861 112733650733353787973653)
                  ·
                    rfl

theorem cell21_493983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 7].length) (baseStart_493983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_493983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_493983 prefixEnd_493983 := by exact prefixLift 493983
  have htrace : WordTrace (prefixWord ++ tailWord_493983) baseStart_493983 baseEnd_493983 := by
    simpa [prefixWord, tailWord_493983, baseEnd_493983] using wordTrace_append hprefix tailTrace_493983
  have hstable : (prefixWord ++ tailWord_493983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493983).length < 2 ^ (prefixWord ++ tailWord_493983).sum := by decide
  have hdescent : baseEnd_493983 < baseStart_493983 := by decide
  rcases family_descends (prefixWord ++ tailWord_493983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494014 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_494014 : Nat := 118140960795 + 494014 * 2 ^ 59
def prefixEnd_494014 : Nat := 4983230072969 + 3 ^ 40 * 494014 * 2
def baseEnd_494014 : Nat := 112740725355704622956923

theorem tailTrace_494014 : CollatzResearch.WordTrace tailWord_494014 prefixEnd_494014 112740725355704622956923 := by
  unfold tailWord_494014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2252271354034890464900137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12012113888186082479467397 2252271354034890464900137)
  ·
    refine ⟨1689203515526167848675103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2252271354034890464900137 1689203515526167848675103)
    ·
      refine ⟨2533805273289251773012655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1689203515526167848675103 2533805273289251773012655)
      ·
        refine ⟨3800707909933877659518983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2533805273289251773012655 3800707909933877659518983)
        ·
          refine ⟨5701061864900816489278475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3800707909933877659518983 5701061864900816489278475)
          ·
            refine ⟨8551592797351224733917713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5701061864900816489278475 8551592797351224733917713)
            ·
              refine ⟨6413694598013418550438285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8551592797351224733917713 6413694598013418550438285)
              ·
                refine ⟨2405135474255031956414357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6413694598013418550438285 2405135474255031956414357)
                ·
                  refine ⟨112740725355704622956923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2405135474255031956414357 112740725355704622956923)
                  ·
                    rfl

theorem cell21_494014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_494014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494014 prefixEnd_494014 := by exact prefixLift 494014
  have htrace : WordTrace (prefixWord ++ tailWord_494014) baseStart_494014 baseEnd_494014 := by
    simpa [prefixWord, tailWord_494014, baseEnd_494014] using wordTrace_append hprefix tailTrace_494014
  have hstable : (prefixWord ++ tailWord_494014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494014).length < 2 ^ (prefixWord ++ tailWord_494014).sum := by decide
  have hdescent : baseEnd_494014 < baseStart_494014 := by decide
  rcases family_descends (prefixWord ++ tailWord_494014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494259 : List Nat := [1, 1, 1, 2, 3, 5, 3, 1, 4]
def baseStart_494259 : Nat := 118140960795 + 494259 * 2 ^ 59
def prefixEnd_494259 : Nat := 4983230072969 + 3 ^ 40 * 494259 * 2
def baseEnd_494259 : Nat := 112796637693638641373089

theorem tailTrace_494259 : CollatzResearch.WordTrace tailWord_494259 prefixEnd_494259 112796637693638641373089 := by
  unfold tailWord_494259
  simp only [CollatzResearch.WordTrace]
  refine ⟨18027106716391530561869831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12018071144261020374579887 18027106716391530561869831)
  ·
    refine ⟨27040660074587295842804747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18027106716391530561869831 27040660074587295842804747)
    ·
      refine ⟨40560990111880943764207121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27040660074587295842804747 40560990111880943764207121)
      ·
        refine ⟨30420742583910707823155341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40560990111880943764207121 30420742583910707823155341)
        ·
          refine ⟨11407778468966515433683253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30420742583910707823155341 11407778468966515433683253)
          ·
            refine ⟨1069479231465610821907805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11407778468966515433683253 1069479231465610821907805)
            ·
              refine ⟨401054711799604058215427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1069479231465610821907805 401054711799604058215427)
              ·
                refine ⟨601582067699406087323141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401054711799604058215427 601582067699406087323141)
                ·
                  refine ⟨112796637693638641373089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 601582067699406087323141 112796637693638641373089)
                  ·
                    rfl

theorem cell21_494259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 4].length) (baseStart_494259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494259 prefixEnd_494259 := by exact prefixLift 494259
  have htrace : WordTrace (prefixWord ++ tailWord_494259) baseStart_494259 baseEnd_494259 := by
    simpa [prefixWord, tailWord_494259, baseEnd_494259] using wordTrace_append hprefix tailTrace_494259
  have hstable : (prefixWord ++ tailWord_494259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494259).length < 2 ^ (prefixWord ++ tailWord_494259).sum := by decide
  have hdescent : baseEnd_494259 < baseStart_494259 := by decide
  rcases family_descends (prefixWord ++ tailWord_494259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494290 : List Nat := [3, 2, 2, 2, 4, 1, 7]
def baseStart_494290 : Nat := 118140960795 + 494290 * 2 ^ 59
def prefixEnd_494290 : Nat := 4983230072969 + 3 ^ 40 * 494290 * 2
def baseEnd_494290 : Nat := 12533745812887719595151

theorem tailTrace_494290 : CollatzResearch.WordTrace tailWord_494290 prefixEnd_494290 12533745812887719595151 := by
  unfold tailWord_494290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4507059344819805714062081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12018824919519481904165549 4507059344819805714062081)
  ·
    refine ⟨3380294508614854285546561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4507059344819805714062081 3380294508614854285546561)
    ·
      refine ⟨2535220881461140714159921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3380294508614854285546561 2535220881461140714159921)
      ·
        refine ⟨1901415661095855535619941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2535220881461140714159921 1901415661095855535619941)
        ·
          refine ⟨356515436455472912928739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1901415661095855535619941 356515436455472912928739)
          ·
            refine ⟨534773154683209369393109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356515436455472912928739 534773154683209369393109)
            ·
              refine ⟨12533745812887719595151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 534773154683209369393109 12533745812887719595151)
              ·
                rfl

theorem cell21_494290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 7].length) (baseStart_494290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494290 prefixEnd_494290 := by exact prefixLift 494290
  have htrace : WordTrace (prefixWord ++ tailWord_494290) baseStart_494290 baseEnd_494290 := by
    simpa [prefixWord, tailWord_494290, baseEnd_494290] using wordTrace_append hprefix tailTrace_494290
  have hstable : (prefixWord ++ tailWord_494290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494290).length < 2 ^ (prefixWord ++ tailWord_494290).sum := by decide
  have hdescent : baseEnd_494290 < baseStart_494290 := by decide
  rcases family_descends (prefixWord ++ tailWord_494290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494332 : List Nat := [2, 2, 2, 1, 3, 2, 2, 7]
def baseStart_494332 : Nat := 118140960795 + 494332 * 2 ^ 59
def prefixEnd_494332 : Nat := 4983230072969 + 3 ^ 40 * 494332 * 2
def baseEnd_494332 : Nat := 37604432429402245552091

theorem tailTrace_494332 : CollatzResearch.WordTrace tailWord_494332 prefixEnd_494332 37604432429402245552091 := by
  unfold tailWord_494332
  simp only [CollatzResearch.WordTrace]
  refine ⟨9014884622563532014638625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12019846163418042686184833 9014884622563532014638625)
  ·
    refine ⟨6761163466922649010978969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9014884622563532014638625 6761163466922649010978969)
    ·
      refine ⟨5070872600191986758234227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6761163466922649010978969 5070872600191986758234227)
      ·
        refine ⟨7606308900287980137351341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5070872600191986758234227 7606308900287980137351341)
        ·
          refine ⟨2852365837607992551506753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7606308900287980137351341 2852365837607992551506753)
          ·
            refine ⟨2139274378205994413630065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2852365837607992551506753 2139274378205994413630065)
            ·
              refine ⟨1604455783654495810222549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2139274378205994413630065 1604455783654495810222549)
              ·
                refine ⟨37604432429402245552091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1604455783654495810222549 37604432429402245552091)
                ·
                  rfl

theorem cell21_494332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 7].length) (baseStart_494332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494332 prefixEnd_494332 := by exact prefixLift 494332
  have htrace : WordTrace (prefixWord ++ tailWord_494332) baseStart_494332 baseEnd_494332 := by
    simpa [prefixWord, tailWord_494332, baseEnd_494332] using wordTrace_append hprefix tailTrace_494332
  have hstable : (prefixWord ++ tailWord_494332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494332).length < 2 ^ (prefixWord ++ tailWord_494332).sum := by decide
  have hdescent : baseEnd_494332 < baseStart_494332 := by decide
  rcases family_descends (prefixWord ++ tailWord_494332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494428 : List Nat := [2, 2, 4, 2, 1, 2, 3, 1, 4]
def baseStart_494428 : Nat := 118140960795 + 494428 * 2 ^ 59
def prefixEnd_494428 : Nat := 4983230072969 + 3 ^ 40 * 494428 * 2
def baseEnd_494428 : Nat := 112835205796131903056077

theorem tailTrace_494428 : CollatzResearch.WordTrace tailWord_494428 prefixEnd_494428 112835205796131903056077 := by
  unfold tailWord_494428
  simp only [CollatzResearch.WordTrace]
  refine ⟨9016635326389636212385969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12022180435186181616514625 9016635326389636212385969)
  ·
    refine ⟨6762476494792227159289477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9016635326389636212385969 6762476494792227159289477)
    ·
      refine ⟨1267964342773542592366777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6762476494792227159289477 1267964342773542592366777)
      ·
        refine ⟨950973257080156944275083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1267964342773542592366777 950973257080156944275083)
        ·
          refine ⟨1426459885620235416412625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 950973257080156944275083 1426459885620235416412625)
          ·
            refine ⟨1069844914215176562309469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1426459885620235416412625 1069844914215176562309469)
            ·
              refine ⟨401191842830691210866051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1069844914215176562309469 401191842830691210866051)
              ·
                refine ⟨601787764246036816299077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401191842830691210866051 601787764246036816299077)
                ·
                  refine ⟨112835205796131903056077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 601787764246036816299077 112835205796131903056077)
                  ·
                    rfl

theorem cell21_494428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_494428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494428 prefixEnd_494428 := by exact prefixLift 494428
  have htrace : WordTrace (prefixWord ++ tailWord_494428) baseStart_494428 baseEnd_494428 := by
    simpa [prefixWord, tailWord_494428, baseEnd_494428] using wordTrace_append hprefix tailTrace_494428
  have hstable : (prefixWord ++ tailWord_494428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494428).length < 2 ^ (prefixWord ++ tailWord_494428).sum := by decide
  have hdescent : baseEnd_494428 < baseStart_494428 := by decide
  rcases family_descends (prefixWord ++ tailWord_494428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494439 : List Nat := [1, 1, 5, 1, 2, 2, 2, 2, 5]
def baseStart_494439 : Nat := 118140960795 + 494439 * 2 ^ 59
def prefixEnd_494439 : Nat := 4983230072969 + 3 ^ 40 * 494439 * 2
def baseEnd_494439 : Nat := 112837716145998328372721

theorem tailTrace_494439 : CollatzResearch.WordTrace tailWord_494439 prefixEnd_494439 112837716145998328372721 := by
  unfold tailWord_494439
  simp only [CollatzResearch.WordTrace]
  refine ⟨18033671855739421303422371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12022447903826280868948247 18033671855739421303422371)
  ·
    refine ⟨27050507783609131955133557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18033671855739421303422371 27050507783609131955133557)
    ·
      refine ⟨2535985104713356120793771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27050507783609131955133557 2535985104713356120793771)
      ·
        refine ⟨3803977657070034181190657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2535985104713356120793771 3803977657070034181190657)
        ·
          refine ⟨2852983242802525635892993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3803977657070034181190657 2852983242802525635892993)
          ·
            refine ⟨2139737432101894226919745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2852983242802525635892993 2139737432101894226919745)
            ·
              refine ⟨1604803074076420670189809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2139737432101894226919745 1604803074076420670189809)
              ·
                refine ⟨1203602305557315502642357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1604803074076420670189809 1203602305557315502642357)
                ·
                  refine ⟨112837716145998328372721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1203602305557315502642357 112837716145998328372721)
                  ·
                    rfl

theorem cell21_494439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 5].length) (baseStart_494439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494439 prefixEnd_494439 := by exact prefixLift 494439
  have htrace : WordTrace (prefixWord ++ tailWord_494439) baseStart_494439 baseEnd_494439 := by
    simpa [prefixWord, tailWord_494439, baseEnd_494439] using wordTrace_append hprefix tailTrace_494439
  have hstable : (prefixWord ++ tailWord_494439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494439).length < 2 ^ (prefixWord ++ tailWord_494439).sum := by decide
  have hdescent : baseEnd_494439 < baseStart_494439 := by decide
  rcases family_descends (prefixWord ++ tailWord_494439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494473 : List Nat := [1, 2, 1, 1, 5, 3, 3, 2, 3]
def baseStart_494473 : Nat := 118140960795 + 494473 * 2 ^ 59
def prefixEnd_494473 : Nat := 4983230072969 + 3 ^ 40 * 494473 * 2
def baseEnd_494473 : Nat := 112845475409221824805985

theorem tailTrace_494473 : CollatzResearch.WordTrace tailWord_494473 prefixEnd_494473 112845475409221824805985 := by
  unfold tailWord_494473
  simp only [CollatzResearch.WordTrace]
  refine ⟨18034911937616245110160073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12023274625077496740106715 18034911937616245110160073)
  ·
    refine ⟨13526183953212183832620055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18034911937616245110160073 13526183953212183832620055)
    ·
      refine ⟨20289275929818275748930083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13526183953212183832620055 20289275929818275748930083)
      ·
        refine ⟨30433913894727413623395125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20289275929818275748930083 30433913894727413623395125)
        ·
          refine ⟨2853179427630695027193293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30433913894727413623395125 2853179427630695027193293)
          ·
            refine ⟨1069942285361510635197485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2853179427630695027193293 1069942285361510635197485)
            ·
              refine ⟨401228357010566488199057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1069942285361510635197485 401228357010566488199057)
              ·
                refine ⟨300921267757924866149293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401228357010566488199057 300921267757924866149293)
                ·
                  refine ⟨112845475409221824805985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300921267757924866149293 112845475409221824805985)
                  ·
                    rfl

theorem cell21_494473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 3].length) (baseStart_494473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494473 prefixEnd_494473 := by exact prefixLift 494473
  have htrace : WordTrace (prefixWord ++ tailWord_494473) baseStart_494473 baseEnd_494473 := by
    simpa [prefixWord, tailWord_494473, baseEnd_494473] using wordTrace_append hprefix tailTrace_494473
  have hstable : (prefixWord ++ tailWord_494473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494473).length < 2 ^ (prefixWord ++ tailWord_494473).sum := by decide
  have hdescent : baseEnd_494473 < baseStart_494473 := by decide
  rcases family_descends (prefixWord ++ tailWord_494473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494518 : List Nat := [5, 1, 4, 1, 10]
def baseStart_494518 : Nat := 118140960795 + 494518 * 2 ^ 59
def prefixEnd_494518 : Nat := 4983230072969 + 3 ^ 40 * 494518 * 2
def baseEnd_494518 : Nat := 1393280802744589463653

theorem tailTrace_494518 : CollatzResearch.WordTrace tailWord_494518 prefixEnd_494518 1393280802744589463653 := by
  unfold tailWord_494518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1127284576403326112221763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12024368814968811863698805 1127284576403326112221763)
  ·
    refine ⟨1690926864604989168332645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1127284576403326112221763 1690926864604989168332645)
    ·
      refine ⟨317048787113435469062371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1690926864604989168332645 317048787113435469062371)
      ·
        refine ⟨475573180670153203593557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317048787113435469062371 475573180670153203593557)
        ·
          refine ⟨1393280802744589463653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 475573180670153203593557 1393280802744589463653)
          ·
            rfl

theorem cell21_494518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 10].length) (baseStart_494518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494518 prefixEnd_494518 := by exact prefixLift 494518
  have htrace : WordTrace (prefixWord ++ tailWord_494518) baseStart_494518 baseEnd_494518 := by
    simpa [prefixWord, tailWord_494518, baseEnd_494518] using wordTrace_append hprefix tailTrace_494518
  have hstable : (prefixWord ++ tailWord_494518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494518).length < 2 ^ (prefixWord ++ tailWord_494518).sum := by decide
  have hdescent : baseEnd_494518 < baseStart_494518 := by decide
  rcases family_descends (prefixWord ++ tailWord_494518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494625 : List Nat := [1, 2, 3, 2, 3, 3, 1, 3, 3]
def baseStart_494625 : Nat := 118140960795 + 494625 * 2 ^ 59
def prefixEnd_494625 : Nat := 4983230072969 + 3 ^ 40 * 494625 * 2
def baseEnd_494625 : Nat := 112880163880103338272341

theorem tailTrace_494625 : CollatzResearch.WordTrace tailWord_494625 prefixEnd_494625 112880163880103338272341 := by
  unfold tailWord_494625
  simp only [CollatzResearch.WordTrace]
  refine ⟨18040455833065575069693329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12026970555377050046462219 18040455833065575069693329)
  ·
    refine ⟨13530341874799181302269997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18040455833065575069693329 13530341874799181302269997)
    ·
      refine ⟨5073878203049692988351249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13530341874799181302269997 5073878203049692988351249)
      ·
        refine ⟨3805408652287269741263437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5073878203049692988351249 3805408652287269741263437)
        ·
          refine ⟨1427028244607726152973789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3805408652287269741263437 1427028244607726152973789)
          ·
            refine ⟨535135591727897307365171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1427028244607726152973789 535135591727897307365171)
            ·
              refine ⟨802703387591845961047757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535135591727897307365171 802703387591845961047757)
              ·
                refine ⟨301013770346942235392909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 802703387591845961047757 301013770346942235392909)
                ·
                  refine ⟨112880163880103338272341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301013770346942235392909 112880163880103338272341)
                  ·
                    rfl

theorem cell21_494625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 3].length) (baseStart_494625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494625 prefixEnd_494625 := by exact prefixLift 494625
  have htrace : WordTrace (prefixWord ++ tailWord_494625) baseStart_494625 baseEnd_494625 := by
    simpa [prefixWord, tailWord_494625, baseEnd_494625] using wordTrace_append hprefix tailTrace_494625
  have hstable : (prefixWord ++ tailWord_494625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494625).length < 2 ^ (prefixWord ++ tailWord_494625).sum := by decide
  have hdescent : baseEnd_494625 < baseStart_494625 := by decide
  rcases family_descends (prefixWord ++ tailWord_494625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494684 : List Nat := [2, 2, 4, 1, 1, 1, 2, 5, 3]
def baseStart_494684 : Nat := 118140960795 + 494684 * 2 ^ 59
def prefixEnd_494684 : Nat := 4983230072969 + 3 ^ 40 * 494684 * 2
def baseEnd_494684 : Nat := 112893628483932346788887

theorem tailTrace_494684 : CollatzResearch.WordTrace tailWord_494684 prefixEnd_494684 112893628483932346788887 := by
  unfold tailWord_494684
  simp only [CollatzResearch.WordTrace]
  refine ⟨9021303869925914073045553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12028405159901218764060737 9021303869925914073045553)
  ·
    refine ⟨6765977902444435554784165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9021303869925914073045553 6765977902444435554784165)
    ·
      refine ⟨1268620856708331666522031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6765977902444435554784165 1268620856708331666522031)
      ·
        refine ⟨1902931285062497499783047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1268620856708331666522031 1902931285062497499783047)
        ·
          refine ⟨2854396927593746249674571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1902931285062497499783047 2854396927593746249674571)
          ·
            refine ⟨4281595391390619374511857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854396927593746249674571 4281595391390619374511857)
            ·
              refine ⟨3211196543542964530883893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4281595391390619374511857 3211196543542964530883893)
              ·
                refine ⟨301049675957152924770365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3211196543542964530883893 301049675957152924770365)
                ·
                  refine ⟨112893628483932346788887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301049675957152924770365 112893628483932346788887)
                  ·
                    rfl

theorem cell21_494684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_494684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494684 prefixEnd_494684 := by exact prefixLift 494684
  have htrace : WordTrace (prefixWord ++ tailWord_494684) baseStart_494684 baseEnd_494684 := by
    simpa [prefixWord, tailWord_494684, baseEnd_494684] using wordTrace_append hprefix tailTrace_494684
  have hstable : (prefixWord ++ tailWord_494684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494684).length < 2 ^ (prefixWord ++ tailWord_494684).sum := by decide
  have hdescent : baseEnd_494684 < baseStart_494684 := by decide
  rcases family_descends (prefixWord ++ tailWord_494684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494695 : List Nat := [1, 1, 5, 1, 1, 12]
def baseStart_494695 : Nat := 118140960795 + 494695 * 2 ^ 59
def prefixEnd_494695 : Nat := 4983230072969 + 3 ^ 40 * 494695 * 2
def baseEnd_494695 : Nat := 4181338475325880448353

theorem tailTrace_494695 : CollatzResearch.WordTrace tailWord_494695 prefixEnd_494695 4181338475325880448353 := by
  unfold tailWord_494695
  simp only [CollatzResearch.WordTrace]
  refine ⟨18043008942811977024741539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12028672628541318016494359 18043008942811977024741539)
  ·
    refine ⟨27064513414217965537112309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18043008942811977024741539 27064513414217965537112309)
    ·
      refine ⟨2537298132582934269104279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27064513414217965537112309 2537298132582934269104279)
      ·
        refine ⟨3805947198874401403656419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2537298132582934269104279 3805947198874401403656419)
        ·
          refine ⟨5708920798311602105484629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3805947198874401403656419 5708920798311602105484629)
          ·
            refine ⟨4181338475325880448353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5708920798311602105484629 4181338475325880448353)
            ·
              rfl

theorem cell21_494695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 12].length) (baseStart_494695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494695 prefixEnd_494695 := by exact prefixLift 494695
  have htrace : WordTrace (prefixWord ++ tailWord_494695) baseStart_494695 baseEnd_494695 := by
    simpa [prefixWord, tailWord_494695, baseEnd_494695] using wordTrace_append hprefix tailTrace_494695
  have hstable : (prefixWord ++ tailWord_494695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494695).length < 2 ^ (prefixWord ++ tailWord_494695).sum := by decide
  have hdescent : baseEnd_494695 < baseStart_494695 := by decide
  rcases family_descends (prefixWord ++ tailWord_494695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494698 : List Nat := [3, 1, 3, 2, 2, 1, 1, 4, 4]
def baseStart_494698 : Nat := 118140960795 + 494698 * 2 ^ 59
def prefixEnd_494698 : Nat := 4983230072969 + 3 ^ 40 * 494698 * 2
def baseEnd_494698 : Nat := 112896823474671433555525

theorem tailTrace_494698 : CollatzResearch.WordTrace tailWord_494698 prefixEnd_494698 112896823474671433555525 := by
  unfold tailWord_494698
  simp only [CollatzResearch.WordTrace]
  refine ⟨4510779590450277134275187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12028745574534072358067165 4510779590450277134275187)
  ·
    refine ⟨6766169385675415701412781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4510779590450277134275187 6766169385675415701412781)
    ·
      refine ⟨2537313519628280888029793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6766169385675415701412781 2537313519628280888029793)
      ·
        refine ⟨1902985139721210666022345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2537313519628280888029793 1902985139721210666022345)
        ·
          refine ⟨1427238854790907999516759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1902985139721210666022345 1427238854790907999516759)
          ·
            refine ⟨2140858282186361999275139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427238854790907999516759 2140858282186361999275139)
            ·
              refine ⟨3211287423279542998912709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2140858282186361999275139 3211287423279542998912709)
              ·
                refine ⟨602116391864914312296133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3211287423279542998912709 602116391864914312296133)
                ·
                  refine ⟨112896823474671433555525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 602116391864914312296133 112896823474671433555525)
                  ·
                    rfl

theorem cell21_494698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_494698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494698 prefixEnd_494698 := by exact prefixLift 494698
  have htrace : WordTrace (prefixWord ++ tailWord_494698) baseStart_494698 baseEnd_494698 := by
    simpa [prefixWord, tailWord_494698, baseEnd_494698] using wordTrace_append hprefix tailTrace_494698
  have hstable : (prefixWord ++ tailWord_494698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494698).length < 2 ^ (prefixWord ++ tailWord_494698).sum := by decide
  have hdescent : baseEnd_494698 < baseStart_494698 := by decide
  rcases family_descends (prefixWord ++ tailWord_494698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494701 : List Nat := [1, 5, 1, 1, 2, 2, 4, 2, 3]
def baseStart_494701 : Nat := 118140960795 + 494701 * 2 ^ 59
def prefixEnd_494701 : Nat := 4983230072969 + 3 ^ 40 * 494701 * 2
def baseEnd_494701 : Nat := 112897508115544095005519

theorem tailTrace_494701 : CollatzResearch.WordTrace tailWord_494701 prefixEnd_494701 112897508115544095005519 := by
  unfold tailWord_494701
  simp only [CollatzResearch.WordTrace]
  refine ⟨18043227780790240049459957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12028818520526826699639971 18043227780790240049459957)
  ·
    refine ⟨1691552604449085004636871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18043227780790240049459957 1691552604449085004636871)
    ·
      refine ⟨2537328906673627506955307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1691552604449085004636871 2537328906673627506955307)
      ·
        refine ⟨3805993360010441260432961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2537328906673627506955307 3805993360010441260432961)
        ·
          refine ⟨2854495020007830945324721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3805993360010441260432961 2854495020007830945324721)
          ·
            refine ⟨2140871265005873208993541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2854495020007830945324721 2140871265005873208993541)
            ·
              refine ⟨401413362188601226686289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2140871265005873208993541 401413362188601226686289)
              ·
                refine ⟨301060021641450920014717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401413362188601226686289 301060021641450920014717)
                ·
                  refine ⟨112897508115544095005519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301060021641450920014717 112897508115544095005519)
                  ·
                    rfl

theorem cell21_494701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_494701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494701 prefixEnd_494701 := by exact prefixLift 494701
  have htrace : WordTrace (prefixWord ++ tailWord_494701) baseStart_494701 baseEnd_494701 := by
    simpa [prefixWord, tailWord_494701, baseEnd_494701] using wordTrace_append hprefix tailTrace_494701
  have hstable : (prefixWord ++ tailWord_494701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494701).length < 2 ^ (prefixWord ++ tailWord_494701).sum := by decide
  have hdescent : baseEnd_494701 < baseStart_494701 := by decide
  rcases family_descends (prefixWord ++ tailWord_494701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494718 : List Nat := [4, 2, 4, 1, 1, 1, 1, 2, 5]
def baseStart_494718 : Nat := 118140960795 + 494718 * 2 ^ 59
def prefixEnd_494718 : Nat := 4983230072969 + 3 ^ 40 * 494718 * 2
def baseEnd_494718 : Nat := 112901387747155843222151

theorem tailTrace_494718 : CollatzResearch.WordTrace tailWord_494718 prefixEnd_494718 112901387747155843222151 := by
  unfold tailWord_494718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2255480977716081494103601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12029231881152434635219205 2255480977716081494103601)
  ·
    refine ⟨1691610733287061120577701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2255480977716081494103601 1691610733287061120577701)
    ·
      refine ⟨317177012491323960108319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1691610733287061120577701 317177012491323960108319)
      ·
        refine ⟨475765518736985940162479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317177012491323960108319 475765518736985940162479)
        ·
          refine ⟨713648278105478910243719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475765518736985940162479 713648278105478910243719)
          ·
            refine ⟨1070472417158218365365579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713648278105478910243719 1070472417158218365365579)
            ·
              refine ⟨1605708625737327548048369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070472417158218365365579 1605708625737327548048369)
              ·
                refine ⟨1204281469302995661036277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605708625737327548048369 1204281469302995661036277)
                ·
                  refine ⟨112901387747155843222151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1204281469302995661036277 112901387747155843222151)
                  ·
                    rfl

theorem cell21_494718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_494718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494718 prefixEnd_494718 := by exact prefixLift 494718
  have htrace : WordTrace (prefixWord ++ tailWord_494718) baseStart_494718 baseEnd_494718 := by
    simpa [prefixWord, tailWord_494718, baseEnd_494718] using wordTrace_append hprefix tailTrace_494718
  have hstable : (prefixWord ++ tailWord_494718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494718).length < 2 ^ (prefixWord ++ tailWord_494718).sum := by decide
  have hdescent : baseEnd_494718 < baseStart_494718 := by decide
  rcases family_descends (prefixWord ++ tailWord_494718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494757 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 6]
def baseStart_494757 : Nat := 118140960795 + 494757 * 2 ^ 59
def prefixEnd_494757 : Nat := 4983230072969 + 3 ^ 40 * 494757 * 2
def baseEnd_494757 : Nat := 112910288078500442072071

theorem tailTrace_494757 : CollatzResearch.WordTrace tailWord_494757 prefixEnd_494757 112910288078500442072071 := by
  unfold tailWord_494757
  simp only [CollatzResearch.WordTrace]
  refine ⟨18045270268587361613498525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12030180179058241075665683 18045270268587361613498525)
  ·
    refine ⟨6766976350720260605061947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18045270268587361613498525 6766976350720260605061947)
    ·
      refine ⟨10150464526080390907592921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6766976350720260605061947 10150464526080390907592921)
      ·
        refine ⟨7612848394560293180694691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10150464526080390907592921 7612848394560293180694691)
        ·
          refine ⟨11419272591840439771042037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7612848394560293180694691 11419272591840439771042037)
          ·
            refine ⟨1070556805485041228535191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11419272591840439771042037 1070556805485041228535191)
            ·
              refine ⟨1605835208227561842802787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070556805485041228535191 1605835208227561842802787)
              ·
                refine ⟨2408752812341342764204181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1605835208227561842802787 2408752812341342764204181)
                ·
                  refine ⟨112910288078500442072071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2408752812341342764204181 112910288078500442072071)
                  ·
                    rfl

theorem cell21_494757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_494757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494757 prefixEnd_494757 := by exact prefixLift 494757
  have htrace : WordTrace (prefixWord ++ tailWord_494757) baseStart_494757 baseEnd_494757 := by
    simpa [prefixWord, tailWord_494757, baseEnd_494757] using wordTrace_append hprefix tailTrace_494757
  have hstable : (prefixWord ++ tailWord_494757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494757).length < 2 ^ (prefixWord ++ tailWord_494757).sum := by decide
  have hdescent : baseEnd_494757 < baseStart_494757 := by decide
  rcases family_descends (prefixWord ++ tailWord_494757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494847 : List Nat := [1, 1, 2, 2, 1, 5, 2, 7]
def baseStart_494847 : Nat := 118140960795 + 494847 * 2 ^ 59
def prefixEnd_494847 : Nat := 4983230072969 + 3 ^ 40 * 494847 * 2
def baseEnd_494847 : Nat := 37643609101560095190629

theorem tailTrace_494847 : CollatzResearch.WordTrace tailWord_494847 prefixEnd_494847 37643609101560095190629 := by
  unfold tailWord_494847
  simp only [CollatzResearch.WordTrace]
  refine ⟨18048552838261306984274795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12032368558840871322849863 18048552838261306984274795)
  ·
    refine ⟨27072829257391960476412193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18048552838261306984274795 27072829257391960476412193)
    ·
      refine ⟨20304621943043970357309145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27072829257391960476412193 20304621943043970357309145)
      ·
        refine ⟨15228466457282977767981859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20304621943043970357309145 15228466457282977767981859)
        ·
          refine ⟨22842699685924466651972789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15228466457282977767981859 22842699685924466651972789)
          ·
            refine ⟨2141503095555418748622449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22842699685924466651972789 2141503095555418748622449)
            ·
              refine ⟨1606127321666564061466837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2141503095555418748622449 1606127321666564061466837)
              ·
                refine ⟨37643609101560095190629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1606127321666564061466837 37643609101560095190629)
                ·
                  rfl

theorem cell21_494847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 7].length) (baseStart_494847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494847 prefixEnd_494847 := by exact prefixLift 494847
  have htrace : WordTrace (prefixWord ++ tailWord_494847) baseStart_494847 baseEnd_494847 := by
    simpa [prefixWord, tailWord_494847, baseEnd_494847] using wordTrace_append hprefix tailTrace_494847
  have hstable : (prefixWord ++ tailWord_494847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494847).length < 2 ^ (prefixWord ++ tailWord_494847).sum := by decide
  have hdescent : baseEnd_494847 < baseStart_494847 := by decide
  rcases family_descends (prefixWord ++ tailWord_494847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494892 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 8]
def baseStart_494892 : Nat := 118140960795 + 494892 * 2 ^ 59
def prefixEnd_494892 : Nat := 4983230072969 + 3 ^ 40 * 494892 * 2
def baseEnd_494892 : Nat := 112941096917770207321795

theorem tailTrace_494892 : CollatzResearch.WordTrace tailWord_494892 prefixEnd_494892 112941096917770207321795 := by
  unfold tailWord_494892
  simp only [CollatzResearch.WordTrace]
  refine ⟨9025097061549139834831465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12033462748732186446441953 9025097061549139834831465)
  ·
    refine ⟨6768822796161854876123599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9025097061549139834831465 6768822796161854876123599)
    ·
      refine ⟨10153234194242782314185399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6768822796161854876123599 10153234194242782314185399)
      ·
        refine ⟨15229851291364173471278099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10153234194242782314185399 15229851291364173471278099)
        ·
          refine ⟨22844776937046260206917149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15229851291364173471278099 22844776937046260206917149)
          ·
            refine ⟨8566791351392347577593931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22844776937046260206917149 8566791351392347577593931)
            ·
              refine ⟨12850187027088521366390897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8566791351392347577593931 12850187027088521366390897)
              ·
                refine ⟨9637640270316391024793173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12850187027088521366390897 9637640270316391024793173)
                ·
                  refine ⟨112941096917770207321795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9637640270316391024793173 112941096917770207321795)
                  ·
                    rfl

theorem cell21_494892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_494892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494892 prefixEnd_494892 := by exact prefixLift 494892
  have htrace : WordTrace (prefixWord ++ tailWord_494892) baseStart_494892 baseEnd_494892 := by
    simpa [prefixWord, tailWord_494892, baseEnd_494892] using wordTrace_append hprefix tailTrace_494892
  have hstable : (prefixWord ++ tailWord_494892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494892).length < 2 ^ (prefixWord ++ tailWord_494892).sum := by decide
  have hdescent : baseEnd_494892 < baseStart_494892 := by decide
  rcases family_descends (prefixWord ++ tailWord_494892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494918 : List Nat := [6, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_494918 : Nat := 118140960795 + 494918 * 2 ^ 59
def prefixEnd_494918 : Nat := 4983230072969 + 3 ^ 40 * 494918 * 2
def baseEnd_494918 : Nat := 112947030471999939888409

theorem tailTrace_494918 : CollatzResearch.WordTrace tailWord_494918 prefixEnd_494918 112947030471999939888409 := by
  unfold tailWord_494918
  simp only [CollatzResearch.WordTrace]
  refine ⟨564098200656377690940919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12034094947336057406739605 564098200656377690940919)
  ·
    refine ⟨846147300984566536411379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 564098200656377690940919 846147300984566536411379)
    ·
      refine ⟨1269220951476849804617069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 846147300984566536411379 1269220951476849804617069)
      ·
        refine ⟨475957856803818676731401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1269220951476849804617069 475957856803818676731401)
        ·
          refine ⟨356968392602864007548551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475957856803818676731401 356968392602864007548551)
          ·
            refine ⟨535452588904296011322827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356968392602864007548551 535452588904296011322827)
            ·
              refine ⟨803178883356444016984241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535452588904296011322827 803178883356444016984241)
              ·
                refine ⟨602384162517333012738181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 803178883356444016984241 602384162517333012738181)
                ·
                  refine ⟨112947030471999939888409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 602384162517333012738181 112947030471999939888409)
                  ·
                    rfl

theorem cell21_494918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_494918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494918 prefixEnd_494918 := by exact prefixLift 494918
  have htrace : WordTrace (prefixWord ++ tailWord_494918) baseStart_494918 baseEnd_494918 := by
    simpa [prefixWord, tailWord_494918, baseEnd_494918] using wordTrace_append hprefix tailTrace_494918
  have hstable : (prefixWord ++ tailWord_494918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494918).length < 2 ^ (prefixWord ++ tailWord_494918).sum := by decide
  have hdescent : baseEnd_494918 < baseStart_494918 := by decide
  rcases family_descends (prefixWord ++ tailWord_494918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494957 : List Nat := [1, 5, 1, 1, 1, 5, 2, 5]
def baseStart_494957 : Nat := 118140960795 + 494957 * 2 ^ 59
def prefixEnd_494957 : Nat := 4983230072969 + 3 ^ 40 * 494957 * 2
def baseEnd_494957 : Nat := 37651976934448179579443

theorem tailTrace_494957 : CollatzResearch.WordTrace tailWord_494957 prefixEnd_494957 37651976934448179579443 := by
  unfold tailWord_494957
  simp only [CollatzResearch.WordTrace]
  refine ⟨18052564867862795770779125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12035043245241863847186083 18052564867862795770779125)
  ·
    refine ⟨1692427956362137103510543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18052564867862795770779125 1692427956362137103510543)
    ·
      refine ⟨2538641934543205655265815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1692427956362137103510543 2538641934543205655265815)
      ·
        refine ⟨3807962901814808482898723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2538641934543205655265815 3807962901814808482898723)
        ·
          refine ⟨5711944352722212724348085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3807962901814808482898723 5711944352722212724348085)
          ·
            refine ⟨535494783067707442907633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5711944352722212724348085 535494783067707442907633)
            ·
              refine ⟨401621087300780582180725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535494783067707442907633 401621087300780582180725)
              ·
                refine ⟨37651976934448179579443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 401621087300780582180725 37651976934448179579443)
                ·
                  rfl

theorem cell21_494957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 5].length) (baseStart_494957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494957 prefixEnd_494957 := by exact prefixLift 494957
  have htrace : WordTrace (prefixWord ++ tailWord_494957) baseStart_494957 baseEnd_494957 := by
    simpa [prefixWord, tailWord_494957, baseEnd_494957] using wordTrace_append hprefix tailTrace_494957
  have hstable : (prefixWord ++ tailWord_494957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494957).length < 2 ^ (prefixWord ++ tailWord_494957).sum := by decide
  have hdescent : baseEnd_494957 < baseStart_494957 := by decide
  rcases family_descends (prefixWord ++ tailWord_494957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494974 : List Nat := [4, 2, 3, 2, 1, 2, 7]
def baseStart_494974 : Nat := 118140960795 + 494974 * 2 ^ 59
def prefixEnd_494974 : Nat := 4983230072969 + 3 ^ 40 * 494974 * 2
def baseEnd_494974 : Nat := 12551090048328476328329

theorem tailTrace_494974 : CollatzResearch.WordTrace tailWord_494974 prefixEnd_494974 12551090048328476328329 := by
  unfold tailWord_494974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2256648113600150959268497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12035456605867471782765317 2256648113600150959268497)
  ·
    refine ⟨1692486085200113219451373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2256648113600150959268497 1692486085200113219451373)
    ·
      refine ⟨634682281950042457294265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1692486085200113219451373 634682281950042457294265)
      ·
        refine ⟨476011711462531842970699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634682281950042457294265 476011711462531842970699)
        ·
          refine ⟨714017567193797764456049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476011711462531842970699 714017567193797764456049)
          ·
            refine ⟨535513175395348323342037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 714017567193797764456049 535513175395348323342037)
            ·
              refine ⟨12551090048328476328329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 535513175395348323342037 12551090048328476328329)
              ·
                rfl

theorem cell21_494974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 7].length) (baseStart_494974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494974 prefixEnd_494974 := by exact prefixLift 494974
  have htrace : WordTrace (prefixWord ++ tailWord_494974) baseStart_494974 baseEnd_494974 := by
    simpa [prefixWord, tailWord_494974, baseEnd_494974] using wordTrace_append hprefix tailTrace_494974
  have hstable : (prefixWord ++ tailWord_494974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494974).length < 2 ^ (prefixWord ++ tailWord_494974).sum := by decide
  have hdescent : baseEnd_494974 < baseStart_494974 := by decide
  rcases family_descends (prefixWord ++ tailWord_494974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494988 : List Nat := [2, 2, 1, 2, 1, 3, 5, 2, 3]
def baseStart_494988 : Nat := 118140960795 + 494988 * 2 ^ 59
def prefixEnd_494988 : Nat := 4983230072969 + 3 ^ 40 * 494988 * 2
def baseEnd_494988 : Nat := 112963005425695373721599

theorem tailTrace_494988 : CollatzResearch.WordTrace tailWord_494988 prefixEnd_494988 112963005425695373721599 := by
  unfold tailWord_494988
  simp only [CollatzResearch.WordTrace]
  refine ⟨9026847765375244032578809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12035797020500325376771745 9026847765375244032578809)
  ·
    refine ⟨6770135824031433024434107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9026847765375244032578809 6770135824031433024434107)
    ·
      refine ⟨10155203736047149536651161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6770135824031433024434107 10155203736047149536651161)
      ·
        refine ⟨7616402802035362152488371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10155203736047149536651161 7616402802035362152488371)
        ·
          refine ⟨11424604203053043228732557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7616402802035362152488371 11424604203053043228732557)
          ·
            refine ⟨4284226576144891210774709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11424604203053043228732557 4284226576144891210774709)
            ·
              refine ⟨401646241513583551010129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4284226576144891210774709 401646241513583551010129)
              ·
                refine ⟨301234681135187663257597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401646241513583551010129 301234681135187663257597)
                ·
                  refine ⟨112963005425695373721599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301234681135187663257597 112963005425695373721599)
                  ·
                    rfl

theorem cell21_494988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_494988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_494988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_494988 prefixEnd_494988 := by exact prefixLift 494988
  have htrace : WordTrace (prefixWord ++ tailWord_494988) baseStart_494988 baseEnd_494988 := by
    simpa [prefixWord, tailWord_494988, baseEnd_494988] using wordTrace_append hprefix tailTrace_494988
  have hstable : (prefixWord ++ tailWord_494988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494988).length < 2 ^ (prefixWord ++ tailWord_494988).sum := by decide
  have hdescent : baseEnd_494988 < baseStart_494988 := by decide
  rcases family_descends (prefixWord ++ tailWord_494988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495047 : List Nat := [1, 1, 4, 1, 1, 3, 3, 4, 3]
def baseStart_495047 : Nat := 118140960795 + 495047 * 2 ^ 59
def prefixEnd_495047 : Nat := 4983230072969 + 3 ^ 40 * 495047 * 2
def baseEnd_495047 : Nat := 112976470029524382238145

theorem tailTrace_495047 : CollatzResearch.WordTrace tailWord_495047 prefixEnd_495047 112976470029524382238145 := by
  unfold tailWord_495047
  simp only [CollatzResearch.WordTrace]
  refine ⟨18055847437536741141555395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12037231625024494094370263 18055847437536741141555395)
  ·
    refine ⟨27083771156305111712333093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18055847437536741141555395 27083771156305111712333093)
    ·
      refine ⟨5078207091807208446062455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27083771156305111712333093 5078207091807208446062455)
      ·
        refine ⟨7617310637710812669093683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5078207091807208446062455 7617310637710812669093683)
        ·
          refine ⟨11425965956566219003640525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7617310637710812669093683 11425965956566219003640525)
          ·
            refine ⟨4284737233712332126365197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11425965956566219003640525 4284737233712332126365197)
            ·
              refine ⟨1606776462642124547386949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4284737233712332126365197 1606776462642124547386949)
              ·
                refine ⟨301270586745398352635053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1606776462642124547386949 301270586745398352635053)
                ·
                  refine ⟨112976470029524382238145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301270586745398352635053 112976470029524382238145)
                  ·
                    rfl

theorem cell21_495047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 3].length) (baseStart_495047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495047 prefixEnd_495047 := by exact prefixLift 495047
  have htrace : WordTrace (prefixWord ++ tailWord_495047) baseStart_495047 baseEnd_495047 := by
    simpa [prefixWord, tailWord_495047, baseEnd_495047] using wordTrace_append hprefix tailTrace_495047
  have hstable : (prefixWord ++ tailWord_495047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495047).length < 2 ^ (prefixWord ++ tailWord_495047).sum := by decide
  have hdescent : baseEnd_495047 < baseStart_495047 := by decide
  rcases family_descends (prefixWord ++ tailWord_495047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495061 : List Nat := [1, 3, 2, 3, 1, 1, 1, 5, 4]
def baseStart_495061 : Nat := 118140960795 + 495061 * 2 ^ 59
def prefixEnd_495061 : Nat := 4983230072969 + 3 ^ 40 * 495061 * 2
def baseEnd_495061 : Nat := 112979665020263469004783

theorem tailTrace_495061 : CollatzResearch.WordTrace tailWord_495061 prefixEnd_495061 112979665020263469004783 := by
  unfold tailWord_495061
  simp only [CollatzResearch.WordTrace]
  refine ⟨18056358059486021532565037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12037572039657347688376691 18056358059486021532565037)
  ·
    refine ⟨6771134272307258074711889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18056358059486021532565037 6771134272307258074711889)
    ·
      refine ⟨5078350704230443556033917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6771134272307258074711889 5078350704230443556033917)
      ·
        refine ⟨1904381514086416333512719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5078350704230443556033917 1904381514086416333512719)
        ·
          refine ⟨2856572271129624500269079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1904381514086416333512719 2856572271129624500269079)
          ·
            refine ⟨4284858406694436750403619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2856572271129624500269079 4284858406694436750403619)
            ·
              refine ⟨6427287610041655125605429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4284858406694436750403619 6427287610041655125605429)
              ·
                refine ⟨602558213441405168025509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6427287610041655125605429 602558213441405168025509)
                ·
                  refine ⟨112979665020263469004783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 602558213441405168025509 112979665020263469004783)
                  ·
                    rfl

theorem cell21_495061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_495061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495061 prefixEnd_495061 := by exact prefixLift 495061
  have htrace : WordTrace (prefixWord ++ tailWord_495061) baseStart_495061 baseEnd_495061 := by
    simpa [prefixWord, tailWord_495061, baseEnd_495061] using wordTrace_append hprefix tailTrace_495061
  have hstable : (prefixWord ++ tailWord_495061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495061).length < 2 ^ (prefixWord ++ tailWord_495061).sum := by decide
  have hdescent : baseEnd_495061 < baseStart_495061 := by decide
  rcases family_descends (prefixWord ++ tailWord_495061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495216 : List Nat := [2, 1, 1, 1, 6, 1, 4, 2, 3]
def baseStart_495216 : Nat := 118140960795 + 495216 * 2 ^ 59
def prefixEnd_495216 : Nat := 4983230072969 + 3 ^ 40 * 495216 * 2
def baseEnd_495216 : Nat := 113015038132017643921133

theorem tailTrace_495216 : CollatzResearch.WordTrace tailWord_495216 prefixEnd_495216 113015038132017643921133 := by
  unfold tailWord_495216
  simp only [CollatzResearch.WordTrace]
  refine ⟨9031005686962241502228751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12041340915949655336305001 9031005686962241502228751)
  ·
    refine ⟨13546508530443362253343127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9031005686962241502228751 13546508530443362253343127)
    ·
      refine ⟨20319762795665043380014691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13546508530443362253343127 20319762795665043380014691)
      ·
        refine ⟨30479644193497565070022037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20319762795665043380014691 30479644193497565070022037)
        ·
          refine ⟨1428733321570198362657283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30479644193497565070022037 1428733321570198362657283)
          ·
            refine ⟨2143099982355297543985925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428733321570198362657283 2143099982355297543985925)
            ·
              refine ⟨401831246691618289497361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2143099982355297543985925 401831246691618289497361)
              ·
                refine ⟨301373435018713717123021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401831246691618289497361 301373435018713717123021)
                ·
                  refine ⟨113015038132017643921133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301373435018713717123021 113015038132017643921133)
                  ·
                    rfl

theorem cell21_495216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 3].length) (baseStart_495216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495216 prefixEnd_495216 := by exact prefixLift 495216
  have htrace : WordTrace (prefixWord ++ tailWord_495216) baseStart_495216 baseEnd_495216 := by
    simpa [prefixWord, tailWord_495216, baseEnd_495216] using wordTrace_append hprefix tailTrace_495216
  have hstable : (prefixWord ++ tailWord_495216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495216).length < 2 ^ (prefixWord ++ tailWord_495216).sum := by decide
  have hdescent : baseEnd_495216 < baseStart_495216 := by decide
  rcases family_descends (prefixWord ++ tailWord_495216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495241 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 7]
def baseStart_495241 : Nat := 118140960795 + 495241 * 2 ^ 59
def prefixEnd_495241 : Nat := 4983230072969 + 3 ^ 40 * 495241 * 2
def baseEnd_495241 : Nat := 113020743472623156004415

theorem tailTrace_495241 : CollatzResearch.WordTrace tailWord_495241 prefixEnd_495241 113020743472623156004415 := by
  unfold tailWord_495241
  simp only [CollatzResearch.WordTrace]
  refine ⟨18062923198833912274117577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12041948799222608182745051 18062923198833912274117577)
  ·
    refine ⟨13547192399125434205588183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18062923198833912274117577 13547192399125434205588183)
    ·
      refine ⟨20320788598688151308382275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13547192399125434205588183 20320788598688151308382275)
      ·
        refine ⟨30481182898032226962573413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20320788598688151308382275 30481182898032226962573413)
        ·
          refine ⟨5715221793381042555482515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30481182898032226962573413 5715221793381042555482515)
          ·
            refine ⟨8572832690071563833223773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5715221793381042555482515 8572832690071563833223773)
            ·
              refine ⟨3214812258776836437458915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8572832690071563833223773 3214812258776836437458915)
              ·
                refine ⟨4822218388165254656188373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3214812258776836437458915 4822218388165254656188373)
                ·
                  refine ⟨113020743472623156004415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4822218388165254656188373 113020743472623156004415)
                  ·
                    rfl

theorem cell21_495241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_495241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495241 prefixEnd_495241 := by exact prefixLift 495241
  have htrace : WordTrace (prefixWord ++ tailWord_495241) baseStart_495241 baseEnd_495241 := by
    simpa [prefixWord, tailWord_495241, baseEnd_495241] using wordTrace_append hprefix tailTrace_495241
  have hstable : (prefixWord ++ tailWord_495241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495241).length < 2 ^ (prefixWord ++ tailWord_495241).sum := by decide
  have hdescent : baseEnd_495241 < baseStart_495241 := by decide
  rcases family_descends (prefixWord ++ tailWord_495241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495309 : List Nat := [1, 6, 2, 1, 1, 1, 3, 3, 3]
def baseStart_495309 : Nat := 118140960795 + 495309 * 2 ^ 59
def prefixEnd_495309 : Nat := 4983230072969 + 3 ^ 40 * 495309 * 2
def baseEnd_495309 : Nat := 113036261999070148870943

theorem tailTrace_495309 : CollatzResearch.WordTrace tailWord_495309 prefixEnd_495309 113036261999070148870943 := by
  unfold tailWord_495309
  simp only [CollatzResearch.WordTrace]
  refine ⟨18065403362587559887592981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12043602241725039925061987 18065403362587559887592981)
  ·
    refine ⟨846815782621291869730921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18065403362587559887592981 846815782621291869730921)
    ·
      refine ⟨635111836965968902298191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 846815782621291869730921 635111836965968902298191)
      ·
        refine ⟨952667755448953353447287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635111836965968902298191 952667755448953353447287)
        ·
          refine ⟨1429001633173430030170931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952667755448953353447287 1429001633173430030170931)
          ·
            refine ⟨2143502449760145045256397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429001633173430030170931 2143502449760145045256397)
            ·
              refine ⟨803813418660054391971149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2143502449760145045256397 803813418660054391971149)
              ·
                refine ⟨301430031997520396989181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 803813418660054391971149 301430031997520396989181)
                ·
                  refine ⟨113036261999070148870943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301430031997520396989181 113036261999070148870943)
                  ·
                    rfl

theorem cell21_495309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_495309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495309 prefixEnd_495309 := by exact prefixLift 495309
  have htrace : WordTrace (prefixWord ++ tailWord_495309) baseStart_495309 baseEnd_495309 := by
    simpa [prefixWord, tailWord_495309, baseEnd_495309] using wordTrace_append hprefix tailTrace_495309
  have hstable : (prefixWord ++ tailWord_495309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495309).length < 2 ^ (prefixWord ++ tailWord_495309).sum := by decide
  have hdescent : baseEnd_495309 < baseStart_495309 := by decide
  rcases family_descends (prefixWord ++ tailWord_495309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495396 : List Nat := [2, 3, 1, 3, 2, 3, 1, 6]
def baseStart_495396 : Nat := 118140960795 + 495396 * 2 ^ 59
def prefixEnd_495396 : Nat := 4983230072969 + 3 ^ 40 * 495396 * 2
def baseEnd_495396 : Nat := 37685372194792443640255

theorem tailTrace_495396 : CollatzResearch.WordTrace tailWord_495396 prefixEnd_495396 37685372194792443640255 := by
  unfold tailWord_495396
  simp only [CollatzResearch.WordTrace]
  refine ⟨9034288256636186873005021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12045717675514915830673361 9034288256636186873005021)
  ·
    refine ⟨3387858096238570077376883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9034288256636186873005021 3387858096238570077376883)
    ·
      refine ⟨5081787144357855116065325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3387858096238570077376883 5081787144357855116065325)
      ·
        refine ⟨1905670179134195668524497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5081787144357855116065325 1905670179134195668524497)
        ·
          refine ⟨1429252634350646751393373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1905670179134195668524497 1429252634350646751393373)
          ·
            refine ⟨535969737881492531772515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1429252634350646751393373 535969737881492531772515)
            ·
              refine ⟨803954606822238797658773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535969737881492531772515 803954606822238797658773)
              ·
                refine ⟨37685372194792443640255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 803954606822238797658773 37685372194792443640255)
                ·
                  rfl

theorem cell21_495396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 6].length) (baseStart_495396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495396 prefixEnd_495396 := by exact prefixLift 495396
  have htrace : WordTrace (prefixWord ++ tailWord_495396) baseStart_495396 baseEnd_495396 := by
    simpa [prefixWord, tailWord_495396, baseEnd_495396] using wordTrace_append hprefix tailTrace_495396
  have hstable : (prefixWord ++ tailWord_495396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495396).length < 2 ^ (prefixWord ++ tailWord_495396).sum := by decide
  have hdescent : baseEnd_495396 < baseStart_495396 := by decide
  rcases family_descends (prefixWord ++ tailWord_495396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495410 : List Nat := [3, 2, 1, 1, 3, 3, 1, 2, 5]
def baseStart_495410 : Nat := 118140960795 + 495410 * 2 ^ 59
def prefixEnd_495410 : Nat := 4983230072969 + 3 ^ 40 * 495410 * 2
def baseEnd_495410 : Nat := 113059311575116417687403

theorem tailTrace_495410 : CollatzResearch.WordTrace tailWord_495410 prefixEnd_495410 113059311575116417687403 := by
  unfold tailWord_495410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4517271783805413534254921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12046058090147769424679789 4517271783805413534254921)
  ·
    refine ⟨3387953837854060150691191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4517271783805413534254921 3387953837854060150691191)
    ·
      refine ⟨5081930756781090226036787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3387953837854060150691191 5081930756781090226036787)
      ·
        refine ⟨7622896135171635339055181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5081930756781090226036787 7622896135171635339055181)
        ·
          refine ⟨2858586050689363252145693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7622896135171635339055181 2858586050689363252145693)
          ·
            refine ⟨1071969769008511219554635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2858586050689363252145693 1071969769008511219554635)
            ·
              refine ⟨1607954653512766829331953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071969769008511219554635 1607954653512766829331953)
              ·
                refine ⟨1205965990134575121998965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1607954653512766829331953 1205965990134575121998965)
                ·
                  refine ⟨113059311575116417687403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1205965990134575121998965 113059311575116417687403)
                  ·
                    rfl

theorem cell21_495410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_495410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495410 prefixEnd_495410 := by exact prefixLift 495410
  have htrace : WordTrace (prefixWord ++ tailWord_495410) baseStart_495410 baseEnd_495410 := by
    simpa [prefixWord, tailWord_495410, baseEnd_495410] using wordTrace_append hprefix tailTrace_495410
  have hstable : (prefixWord ++ tailWord_495410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495410).length < 2 ^ (prefixWord ++ tailWord_495410).sum := by decide
  have hdescent : baseEnd_495410 < baseStart_495410 := by decide
  rcases family_descends (prefixWord ++ tailWord_495410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495427 : List Nat := [1, 1, 1, 3, 1, 6, 2, 3, 3]
def baseStart_495427 : Nat := 118140960795 + 495427 * 2 ^ 59
def prefixEnd_495427 : Nat := 4983230072969 + 3 ^ 40 * 495427 * 2
def baseEnd_495427 : Nat := 113063191206728165904035

theorem tailTrace_495427 : CollatzResearch.WordTrace tailWord_495427 prefixEnd_495427 113063191206728165904035 := by
  unfold tailWord_495427
  simp only [CollatzResearch.WordTrace]
  refine ⟨18069707176160066040388535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12046471450773377360259023 18069707176160066040388535)
  ·
    refine ⟨27104560764240099060582803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18069707176160066040388535 27104560764240099060582803)
    ·
      refine ⟨40656841146360148590874205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27104560764240099060582803 40656841146360148590874205)
      ·
        refine ⟨15246315429885055721577827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40656841146360148590874205 15246315429885055721577827)
        ·
          refine ⟨22869473144827583582366741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15246315429885055721577827 22869473144827583582366741)
          ·
            refine ⟨1072006553663792980423441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22869473144827583582366741 1072006553663792980423441)
            ·
              refine ⟨804004915247844735317581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072006553663792980423441 804004915247844735317581)
              ·
                refine ⟨301501843217941775744093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 804004915247844735317581 301501843217941775744093)
                ·
                  refine ⟨113063191206728165904035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301501843217941775744093 113063191206728165904035)
                  ·
                    rfl

theorem cell21_495427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 3].length) (baseStart_495427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495427 prefixEnd_495427 := by exact prefixLift 495427
  have htrace : WordTrace (prefixWord ++ tailWord_495427) baseStart_495427 baseEnd_495427 := by
    simpa [prefixWord, tailWord_495427, baseEnd_495427] using wordTrace_append hprefix tailTrace_495427
  have hstable : (prefixWord ++ tailWord_495427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495427).length < 2 ^ (prefixWord ++ tailWord_495427).sum := by decide
  have hdescent : baseEnd_495427 < baseStart_495427 := by decide
  rcases family_descends (prefixWord ++ tailWord_495427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495441 : List Nat := [1, 2, 2, 1, 5, 1, 3, 2, 4]
def baseStart_495441 : Nat := 118140960795 + 495441 * 2 ^ 59
def prefixEnd_495441 : Nat := 4983230072969 + 3 ^ 40 * 495441 * 2
def baseEnd_495441 : Nat := 113066386197467252670673

theorem tailTrace_495441 : CollatzResearch.WordTrace tailWord_495441 prefixEnd_495441 113066386197467252670673 := by
  unfold tailWord_495441
  simp only [CollatzResearch.WordTrace]
  refine ⟨18070217798109346431398177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12046811865406230954265451 18070217798109346431398177)
  ·
    refine ⟨13552663348582009823548633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18070217798109346431398177 13552663348582009823548633)
    ·
      refine ⟨10164497511436507367661475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13552663348582009823548633 10164497511436507367661475)
      ·
        refine ⟨15246746267154761051492213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10164497511436507367661475 15246746267154761051492213)
        ·
          refine ⟨1429382462545758848577395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15246746267154761051492213 1429382462545758848577395)
          ·
            refine ⟨2144073693818638272866093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429382462545758848577395 2144073693818638272866093)
            ·
              refine ⟨804027635181989352324785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2144073693818638272866093 804027635181989352324785)
              ·
                refine ⟨603020726386492014243589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 804027635181989352324785 603020726386492014243589)
                ·
                  refine ⟨113066386197467252670673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 603020726386492014243589 113066386197467252670673)
                  ·
                    rfl

theorem cell21_495441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_495441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495441 prefixEnd_495441 := by exact prefixLift 495441
  have htrace : WordTrace (prefixWord ++ tailWord_495441) baseStart_495441 baseEnd_495441 := by
    simpa [prefixWord, tailWord_495441, baseEnd_495441] using wordTrace_append hprefix tailTrace_495441
  have hstable : (prefixWord ++ tailWord_495441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495441).length < 2 ^ (prefixWord ++ tailWord_495441).sum := by decide
  have hdescent : baseEnd_495441 < baseStart_495441 := by decide
  rcases family_descends (prefixWord ++ tailWord_495441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495478 : List Nat := [5, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_495478 : Nat := 118140960795 + 495478 * 2 ^ 59
def prefixEnd_495478 : Nat := 4983230072969 + 3 ^ 40 * 495478 * 2
def baseEnd_495478 : Nat := 113074830101563410553931

theorem tailTrace_495478 : CollatzResearch.WordTrace tailWord_495478 prefixEnd_495478 113074830101563410553931 := by
  unfold tailWord_495478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1129472956185956359405943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12047711532650201166996725 1129472956185956359405943)
  ·
    refine ⟨1694209434278934539108915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1129472956185956359405943 1694209434278934539108915)
    ·
      refine ⟨2541314151418401808663373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1694209434278934539108915 2541314151418401808663373)
      ·
        refine ⟨952992806781900678248765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2541314151418401808663373 952992806781900678248765)
        ·
          refine ⟨357372302543212754343287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 952992806781900678248765 357372302543212754343287)
          ·
            refine ⟨536058453814819131514931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357372302543212754343287 536058453814819131514931)
            ·
              refine ⟨804087680722228697272397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536058453814819131514931 804087680722228697272397)
              ·
                refine ⟨301532880270835761477149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 804087680722228697272397 301532880270835761477149)
                ·
                  refine ⟨113074830101563410553931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301532880270835761477149 113074830101563410553931)
                  ·
                    rfl

theorem cell21_495478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_495478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495478 prefixEnd_495478 := by exact prefixLift 495478
  have htrace : WordTrace (prefixWord ++ tailWord_495478) baseStart_495478 baseEnd_495478 := by
    simpa [prefixWord, tailWord_495478, baseEnd_495478] using wordTrace_append hprefix tailTrace_495478
  have hstable : (prefixWord ++ tailWord_495478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495478).length < 2 ^ (prefixWord ++ tailWord_495478).sum := by decide
  have hdescent : baseEnd_495478 < baseStart_495478 := by decide
  rcases family_descends (prefixWord ++ tailWord_495478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495489 : List Nat := [1, 2, 4, 4, 2, 1, 7]
def baseStart_495489 : Nat := 118140960795 + 495489 * 2 ^ 59
def prefixEnd_495489 : Nat := 4983230072969 + 3 ^ 40 * 495489 * 2
def baseEnd_495489 : Nat := 12564148939047759541175

theorem tailTrace_495489 : CollatzResearch.WordTrace tailWord_495489 prefixEnd_495489 12564148939047759541175 := by
  unfold tailWord_495489
  simp only [CollatzResearch.WordTrace]
  refine ⟨18071968501935450629145521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12047979001290300419430347 18071968501935450629145521)
  ·
    refine ⟨13553976376451587971859141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18071968501935450629145521 13553976376451587971859141)
    ·
      refine ⟨2541370570584672744723589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13553976376451587971859141 2541370570584672744723589)
      ·
        refine ⟨476506981984626139635673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2541370570584672744723589 476506981984626139635673)
        ·
          refine ⟨357380236488469604726755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476506981984626139635673 357380236488469604726755)
          ·
            refine ⟨536070354732704407090133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357380236488469604726755 536070354732704407090133)
            ·
              refine ⟨12564148939047759541175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 536070354732704407090133 12564148939047759541175)
              ·
                rfl

theorem cell21_495489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 7].length) (baseStart_495489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495489 prefixEnd_495489 := by exact prefixLift 495489
  have htrace : WordTrace (prefixWord ++ tailWord_495489) baseStart_495489 baseEnd_495489 := by
    simpa [prefixWord, tailWord_495489, baseEnd_495489] using wordTrace_append hprefix tailTrace_495489
  have hstable : (prefixWord ++ tailWord_495489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495489).length < 2 ^ (prefixWord ++ tailWord_495489).sum := by decide
  have hdescent : baseEnd_495489 < baseStart_495489 := by decide
  rcases family_descends (prefixWord ++ tailWord_495489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495500 : List Nat := [2, 2, 1, 2, 1, 2, 1, 6, 4]
def baseStart_495500 : Nat := 118140960795 + 495500 * 2 ^ 59
def prefixEnd_495500 : Nat := 4983230072969 + 3 ^ 40 * 495500 * 2
def baseEnd_495500 : Nat := 113079850801296261187219

theorem tailTrace_495500 : CollatzResearch.WordTrace tailWord_495500 prefixEnd_495500 113079850801296261187219 := by
  unfold tailWord_495500
  simp only [CollatzResearch.WordTrace]
  refine ⟨9036184852447799753897977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12048246469930399671863969 9036184852447799753897977)
  ·
    refine ⟨6777138639335849815423483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9036184852447799753897977 6777138639335849815423483)
    ·
      refine ⟨10165707959003774723135225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6777138639335849815423483 10165707959003774723135225)
      ·
        refine ⟨7624280969252831042351419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10165707959003774723135225 7624280969252831042351419)
        ·
          refine ⟨11436421453879246563527129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7624280969252831042351419 11436421453879246563527129)
          ·
            refine ⟨8577316090409434922645347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11436421453879246563527129 8577316090409434922645347)
            ·
              refine ⟨12865974135614152383968021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8577316090409434922645347 12865974135614152383968021)
              ·
                refine ⟨603092537606913392998501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12865974135614152383968021 603092537606913392998501)
                ·
                  refine ⟨113079850801296261187219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 603092537606913392998501 113079850801296261187219)
                  ·
                    rfl

theorem cell21_495500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_495500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495500 prefixEnd_495500 := by exact prefixLift 495500
  have htrace : WordTrace (prefixWord ++ tailWord_495500) baseStart_495500 baseEnd_495500 := by
    simpa [prefixWord, tailWord_495500, baseEnd_495500] using wordTrace_append hprefix tailTrace_495500
  have hstable : (prefixWord ++ tailWord_495500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495500).length < 2 ^ (prefixWord ++ tailWord_495500).sum := by decide
  have hdescent : baseEnd_495500 < baseStart_495500 := by decide
  rcases family_descends (prefixWord ++ tailWord_495500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495517 : List Nat := [1, 4, 2, 1, 2, 3, 1, 3, 4]
def baseStart_495517 : Nat := 118140960795 + 495517 * 2 ^ 59
def prefixEnd_495517 : Nat := 4983230072969 + 3 ^ 40 * 495517 * 2
def baseEnd_495517 : Nat := 113083730432908009403851

theorem tailTrace_495517 : CollatzResearch.WordTrace tailWord_495517 prefixEnd_495517 113083730432908009403851 := by
  unfold tailWord_495517
  simp only [CollatzResearch.WordTrace]
  refine ⟨18072989745834011411164805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12048659830556007607443203 18072989745834011411164805)
  ·
    refine ⟨3388685577343877139593401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18072989745834011411164805 3388685577343877139593401)
    ·
      refine ⟨2541514183007907854695051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3388685577343877139593401 2541514183007907854695051)
      ·
        refine ⟨3812271274511861782042577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2541514183007907854695051 3812271274511861782042577)
        ·
          refine ⟨2859203455883896336531933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3812271274511861782042577 2859203455883896336531933)
          ·
            refine ⟨1072201295956461126199475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2859203455883896336531933 1072201295956461126199475)
            ·
              refine ⟨1608301943934691689299213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072201295956461126199475 1608301943934691689299213)
              ·
                refine ⟨603113228975509383487205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1608301943934691689299213 603113228975509383487205)
                ·
                  refine ⟨113083730432908009403851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 603113228975509383487205 113083730432908009403851)
                  ·
                    rfl

theorem cell21_495517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_495517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495517 prefixEnd_495517 := by exact prefixLift 495517
  have htrace : WordTrace (prefixWord ++ tailWord_495517) baseStart_495517 baseEnd_495517 := by
    simpa [prefixWord, tailWord_495517, baseEnd_495517] using wordTrace_append hprefix tailTrace_495517
  have hstable : (prefixWord ++ tailWord_495517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495517).length < 2 ^ (prefixWord ++ tailWord_495517).sum := by decide
  have hdescent : baseEnd_495517 < baseStart_495517 := by decide
  rcases family_descends (prefixWord ++ tailWord_495517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495548 : List Nat := [2, 2, 2, 5, 2, 8]
def baseStart_495548 : Nat := 118140960795 + 495548 * 2 ^ 59
def prefixEnd_495548 : Nat := 4983230072969 + 3 ^ 40 * 495548 * 2
def baseEnd_495548 : Nat := 4188548335379957199523

theorem tailTrace_495548 : CollatzResearch.WordTrace tailWord_495548 prefixEnd_495548 4188548335379957199523 := by
  unfold tailWord_495548
  simp only [CollatzResearch.WordTrace]
  refine ⟨9037060204360851852771649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12049413605814469137028865 9037060204360851852771649)
  ·
    refine ⟨6777795153270638889578737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9037060204360851852771649 6777795153270638889578737)
    ·
      refine ⟨5083346364952979167184053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6777795153270638889578737 5083346364952979167184053)
      ·
        refine ⟨476563721714341796923505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5083346364952979167184053 476563721714341796923505)
        ·
          refine ⟨357422791285756347692629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476563721714341796923505 357422791285756347692629)
          ·
            refine ⟨4188548335379957199523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 357422791285756347692629 4188548335379957199523)
            ·
              rfl

theorem cell21_495548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 8].length) (baseStart_495548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495548 prefixEnd_495548 := by exact prefixLift 495548
  have htrace : WordTrace (prefixWord ++ tailWord_495548) baseStart_495548 baseEnd_495548 := by
    simpa [prefixWord, tailWord_495548, baseEnd_495548] using wordTrace_append hprefix tailTrace_495548
  have hstable : (prefixWord ++ tailWord_495548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495548).length < 2 ^ (prefixWord ++ tailWord_495548).sum := by decide
  have hdescent : baseEnd_495548 < baseStart_495548 := by decide
  rcases family_descends (prefixWord ++ tailWord_495548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495576 : List Nat := [2, 1, 2, 2, 2, 2, 1, 5, 4]
def baseStart_495576 : Nat := 118140960795 + 495576 * 2 ^ 59
def prefixEnd_495576 : Nat := 4983230072969 + 3 ^ 40 * 495576 * 2
def baseEnd_495576 : Nat := 113097195036737017920397

theorem tailTrace_495576 : CollatzResearch.WordTrace tailWord_495576 prefixEnd_495576 113097195036737017920397 := by
  unfold tailWord_495576
  simp only [CollatzResearch.WordTrace]
  refine ⟨9037570826310132243781291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12050094435080176325041721 9037570826310132243781291)
  ·
    refine ⟨13556356239465198365671937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9037570826310132243781291 13556356239465198365671937)
    ·
      refine ⟨10167267179598898774253953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13556356239465198365671937 10167267179598898774253953)
      ·
        refine ⟨7625450384699174080690465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10167267179598898774253953 7625450384699174080690465)
        ·
          refine ⟨5719087788524380560517849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7625450384699174080690465 5719087788524380560517849)
          ·
            refine ⟨4289315841393285420388387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5719087788524380560517849 4289315841393285420388387)
            ·
              refine ⟨6433973762089928130582581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4289315841393285420388387 6433973762089928130582581)
              ·
                refine ⟨603185040195930762242117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6433973762089928130582581 603185040195930762242117)
                ·
                  refine ⟨113097195036737017920397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 603185040195930762242117 113097195036737017920397)
                  ·
                    rfl

theorem cell21_495576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_495576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495576 prefixEnd_495576 := by exact prefixLift 495576
  have htrace : WordTrace (prefixWord ++ tailWord_495576) baseStart_495576 baseEnd_495576 := by
    simpa [prefixWord, tailWord_495576, baseEnd_495576] using wordTrace_append hprefix tailTrace_495576
  have hstable : (prefixWord ++ tailWord_495576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495576).length < 2 ^ (prefixWord ++ tailWord_495576).sum := by decide
  have hdescent : baseEnd_495576 < baseStart_495576 := by decide
  rcases family_descends (prefixWord ++ tailWord_495576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495621 : List Nat := [1, 3, 1, 1, 2, 4, 1, 3, 5]
def baseStart_495621 : Nat := 118140960795 + 495621 * 2 ^ 59
def prefixEnd_495621 : Nat := 4983230072969 + 3 ^ 40 * 495621 * 2
def baseEnd_495621 : Nat := 113107464649826939670305

theorem tailTrace_495621 : CollatzResearch.WordTrace tailWord_495621 prefixEnd_495621 113107464649826939670305 := by
  unfold tailWord_495621
  simp only [CollatzResearch.WordTrace]
  refine ⟨18076782937457237172950717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12051188624971491448633811 18076782937457237172950717)
  ·
    refine ⟨6778793601546463939856519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18076782937457237172950717 6778793601546463939856519)
    ·
      refine ⟨10168190402319695909784779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6778793601546463939856519 10168190402319695909784779)
      ·
        refine ⟨15252285603479543864677169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10168190402319695909784779 15252285603479543864677169)
        ·
          refine ⟨11439214202609657898507877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15252285603479543864677169 11439214202609657898507877)
          ·
            refine ⟨2144852662989310855970227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11439214202609657898507877 2144852662989310855970227)
            ·
              refine ⟨3217278994483966283955341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2144852662989310855970227 3217278994483966283955341)
              ·
                refine ⟨1206479622931487356483253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3217278994483966283955341 1206479622931487356483253)
                ·
                  refine ⟨113107464649826939670305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1206479622931487356483253 113107464649826939670305)
                  ·
                    rfl

theorem cell21_495621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_495621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495621 prefixEnd_495621 := by exact prefixLift 495621
  have htrace : WordTrace (prefixWord ++ tailWord_495621) baseStart_495621 baseEnd_495621 := by
    simpa [prefixWord, tailWord_495621, baseEnd_495621] using wordTrace_append hprefix tailTrace_495621
  have hstable : (prefixWord ++ tailWord_495621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495621).length < 2 ^ (prefixWord ++ tailWord_495621).sum := by decide
  have hdescent : baseEnd_495621 < baseStart_495621 := by decide
  rcases family_descends (prefixWord ++ tailWord_495621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495666 : List Nat := [3, 2, 1, 1, 2, 3, 9]
def baseStart_495666 : Nat := 118140960795 + 495666 * 2 ^ 59
def prefixEnd_495666 : Nat := 4983230072969 + 3 ^ 40 * 495666 * 2
def baseEnd_495666 : Nat := 12568637140324095713357

theorem tailTrace_495666 : CollatzResearch.WordTrace tailWord_495666 prefixEnd_495666 12568637140324095713357 := by
  unfold tailWord_495666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4519606055573552464584713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12052282814862806572225901 4519606055573552464584713)
  ·
    refine ⟨3389704541680164348438535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4519606055573552464584713 3389704541680164348438535)
    ·
      refine ⟨5084556812520246522657803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3389704541680164348438535 5084556812520246522657803)
      ·
        refine ⟨7626835218780369783986705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5084556812520246522657803 7626835218780369783986705)
        ·
          refine ⟨5720126414085277337990029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7626835218780369783986705 5720126414085277337990029)
          ·
            refine ⟨2145047405281979001746261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5720126414085277337990029 2145047405281979001746261)
            ·
              refine ⟨12568637140324095713357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2145047405281979001746261 12568637140324095713357)
              ·
                rfl

theorem cell21_495666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 9].length) (baseStart_495666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495666 prefixEnd_495666 := by exact prefixLift 495666
  have htrace : WordTrace (prefixWord ++ tailWord_495666) baseStart_495666 baseEnd_495666 := by
    simpa [prefixWord, tailWord_495666, baseEnd_495666] using wordTrace_append hprefix tailTrace_495666
  have hstable : (prefixWord ++ tailWord_495666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495666).length < 2 ^ (prefixWord ++ tailWord_495666).sum := by decide
  have hdescent : baseEnd_495666 < baseStart_495666 := by decide
  rcases family_descends (prefixWord ++ tailWord_495666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495672 : List Nat := [2, 1, 2, 1, 6, 1, 3, 2, 3]
def baseStart_495672 : Nat := 118140960795 + 495672 * 2 ^ 59
def prefixEnd_495672 : Nat := 4983230072969 + 3 ^ 40 * 495672 * 2
def baseEnd_495672 : Nat := 113119103544662184320201

theorem tailTrace_495672 : CollatzResearch.WordTrace tailWord_495672 prefixEnd_495672 113119103544662184320201 := by
  unfold tailWord_495672
  simp only [CollatzResearch.WordTrace]
  refine ⟨9039321530136236441528635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12052428706848315255371513 9039321530136236441528635)
  ·
    refine ⟨13558982295204354662292953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9039321530136236441528635 13558982295204354662292953)
    ·
      refine ⟨10169236721403265996719715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13558982295204354662292953 10169236721403265996719715)
      ·
        refine ⟨15253855082104898995079573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10169236721403265996719715 15253855082104898995079573)
        ·
          refine ⟨715024456973667140394355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15253855082104898995079573 715024456973667140394355)
          ·
            refine ⟨1072536685460500710591533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715024456973667140394355 1072536685460500710591533)
            ·
              refine ⟨402201257047687766471825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1072536685460500710591533 402201257047687766471825)
              ·
                refine ⟨301650942785765824853869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402201257047687766471825 301650942785765824853869)
                ·
                  refine ⟨113119103544662184320201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301650942785765824853869 113119103544662184320201)
                  ·
                    rfl

theorem cell21_495672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 3].length) (baseStart_495672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495672 prefixEnd_495672 := by exact prefixLift 495672
  have htrace : WordTrace (prefixWord ++ tailWord_495672) baseStart_495672 baseEnd_495672 := by
    simpa [prefixWord, tailWord_495672, baseEnd_495672] using wordTrace_append hprefix tailTrace_495672
  have hstable : (prefixWord ++ tailWord_495672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495672).length < 2 ^ (prefixWord ++ tailWord_495672).sum := by decide
  have hdescent : baseEnd_495672 < baseStart_495672 := by decide
  rcases family_descends (prefixWord ++ tailWord_495672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495686 : List Nat := [6, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_495686 : Nat := 118140960795 + 495686 * 2 ^ 59
def prefixEnd_495686 : Nat := 4983230072969 + 3 ^ 40 * 495686 * 2
def baseEnd_495686 : Nat := 113122298535401271086839

theorem tailTrace_495686 : CollatzResearch.WordTrace tailWord_495686 prefixEnd_495686 113122298535401271086839 := by
  unfold tailWord_495686
  simp only [CollatzResearch.WordTrace]
  refine ⟨564973552569429789814591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12052769121481168849377941 564973552569429789814591)
  ·
    refine ⟨847460328854144684721887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 564973552569429789814591 847460328854144684721887)
    ·
      refine ⟨1271190493281217027082831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 847460328854144684721887 1271190493281217027082831)
      ·
        refine ⟨1906785739921825540624247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1271190493281217027082831 1906785739921825540624247)
        ·
          refine ⟨2860178609882738310936371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1906785739921825540624247 2860178609882738310936371)
          ·
            refine ⟨4290267914824107466404557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2860178609882738310936371 4290267914824107466404557)
            ·
              refine ⟨1608850468059040299901709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4290267914824107466404557 1608850468059040299901709)
              ·
                refine ⟨603318925522140112463141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1608850468059040299901709 603318925522140112463141)
                ·
                  refine ⟨113122298535401271086839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 603318925522140112463141 113122298535401271086839)
                  ·
                    rfl

theorem cell21_495686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_495686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495686 prefixEnd_495686 := by exact prefixLift 495686
  have htrace : WordTrace (prefixWord ++ tailWord_495686) baseStart_495686 baseEnd_495686 := by
    simpa [prefixWord, tailWord_495686, baseEnd_495686] using wordTrace_append hprefix tailTrace_495686
  have hstable : (prefixWord ++ tailWord_495686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495686).length < 2 ^ (prefixWord ++ tailWord_495686).sum := by decide
  have hdescent : baseEnd_495686 < baseStart_495686 := by decide
  rcases family_descends (prefixWord ++ tailWord_495686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495711 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 6]
def baseStart_495711 : Nat := 118140960795 + 495711 * 2 ^ 59
def prefixEnd_495711 : Nat := 4983230072969 + 3 ^ 40 * 495711 * 2
def baseEnd_495711 : Nat := 113128003876006783170121

theorem tailTrace_495711 : CollatzResearch.WordTrace tailWord_495711 prefixEnd_495711 113128003876006783170121 := by
  unfold tailWord_495711
  simp only [CollatzResearch.WordTrace]
  refine ⟨18080065507131182543726987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12053377004754121695817991 18080065507131182543726987)
  ·
    refine ⟨27120098260696773815590481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18080065507131182543726987 27120098260696773815590481)
    ·
      refine ⟨20340073695522580361692861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27120098260696773815590481 20340073695522580361692861)
      ·
        refine ⟨7627527635820967635634823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20340073695522580361692861 7627527635820967635634823)
        ·
          refine ⟨11441291453731451453452235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7627527635820967635634823 11441291453731451453452235)
          ·
            refine ⟨17161937180597177180178353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11441291453731451453452235 17161937180597177180178353)
            ·
              refine ⟨12871452885447882885133765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17161937180597177180178353 12871452885447882885133765)
              ·
                refine ⟨2413397416021478040962581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12871452885447882885133765 2413397416021478040962581)
                ·
                  refine ⟨113128003876006783170121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2413397416021478040962581 113128003876006783170121)
                  ·
                    rfl

theorem cell21_495711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 6].length) (baseStart_495711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495711 prefixEnd_495711 := by exact prefixLift 495711
  have htrace : WordTrace (prefixWord ++ tailWord_495711) baseStart_495711 baseEnd_495711 := by
    simpa [prefixWord, tailWord_495711, baseEnd_495711] using wordTrace_append hprefix tailTrace_495711
  have hstable : (prefixWord ++ tailWord_495711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495711).length < 2 ^ (prefixWord ++ tailWord_495711).sum := by decide
  have hdescent : baseEnd_495711 < baseStart_495711 := by decide
  rcases family_descends (prefixWord ++ tailWord_495711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495728 : List Nat := [2, 1, 1, 1, 5, 2, 1, 4, 4]
def baseStart_495728 : Nat := 118140960795 + 495728 * 2 ^ 59
def prefixEnd_495728 : Nat := 4983230072969 + 3 ^ 40 * 495728 * 2
def baseEnd_495728 : Nat := 113131883507618531386753

theorem tailTrace_495728 : CollatzResearch.WordTrace tailWord_495728 prefixEnd_495728 113131883507618531386753 := by
  unfold tailWord_495728
  simp only [CollatzResearch.WordTrace]
  refine ⟨9040342774034797223547919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12053790365379729631397225 9040342774034797223547919)
  ·
    refine ⟨13560514161052195835321879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9040342774034797223547919 13560514161052195835321879)
    ·
      refine ⟨20340771241578293752982819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13560514161052195835321879 20340771241578293752982819)
      ·
        refine ⟨30511156862367440629474229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20340771241578293752982819 30511156862367440629474229)
        ·
          refine ⟨2860420955846947559013209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30511156862367440629474229 2860420955846947559013209)
          ·
            refine ⟨2145315716885210669259907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2860420955846947559013209 2145315716885210669259907)
            ·
              refine ⟨3217973575327816003889861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2145315716885210669259907 3217973575327816003889861)
              ·
                refine ⟨603370045373965500729349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3217973575327816003889861 603370045373965500729349)
                ·
                  refine ⟨113131883507618531386753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 603370045373965500729349 113131883507618531386753)
                  ·
                    rfl

theorem cell21_495728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_495728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495728 prefixEnd_495728 := by exact prefixLift 495728
  have htrace : WordTrace (prefixWord ++ tailWord_495728) baseStart_495728 baseEnd_495728 := by
    simpa [prefixWord, tailWord_495728, baseEnd_495728] using wordTrace_append hprefix tailTrace_495728
  have hstable : (prefixWord ++ tailWord_495728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495728).length < 2 ^ (prefixWord ++ tailWord_495728).sum := by decide
  have hdescent : baseEnd_495728 < baseStart_495728 := by decide
  rcases family_descends (prefixWord ++ tailWord_495728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495810 : List Nat := [3, 5, 1, 1, 1, 3, 2, 5]
def baseStart_495810 : Nat := 118140960795 + 495810 * 2 ^ 59
def prefixEnd_495810 : Nat := 4983230072969 + 3 ^ 40 * 495810 * 2
def baseEnd_495810 : Nat := 37716865674934870339973

theorem tailTrace_495810 : CollatzResearch.WordTrace tailWord_495810 prefixEnd_495810 37716865674934870339973 := by
  unfold tailWord_495810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4520919083443130612895221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12055784222515014967720589 4520919083443130612895221)
  ·
    refine ⟨423836164072793494958927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4520919083443130612895221 423836164072793494958927)
    ·
      refine ⟨635754246109190242438391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423836164072793494958927 635754246109190242438391)
      ·
        refine ⟨953631369163785363657587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635754246109190242438391 953631369163785363657587)
        ·
          refine ⟨1430447053745678045486381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953631369163785363657587 1430447053745678045486381)
          ·
            refine ⟨536417645154629267057393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1430447053745678045486381 536417645154629267057393)
            ·
              refine ⟨402313233865971950293045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536417645154629267057393 402313233865971950293045)
              ·
                refine ⟨37716865674934870339973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 402313233865971950293045 37716865674934870339973)
                ·
                  rfl

theorem cell21_495810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_495810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495810 prefixEnd_495810 := by exact prefixLift 495810
  have htrace : WordTrace (prefixWord ++ tailWord_495810) baseStart_495810 baseEnd_495810 := by
    simpa [prefixWord, tailWord_495810, baseEnd_495810] using wordTrace_append hprefix tailTrace_495810
  have hstable : (prefixWord ++ tailWord_495810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495810).length < 2 ^ (prefixWord ++ tailWord_495810).sum := by decide
  have hdescent : baseEnd_495810 < baseStart_495810 := by decide
  rcases family_descends (prefixWord ++ tailWord_495810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495818 : List Nat := [3, 1, 2, 1, 3, 1, 3, 7]
def baseStart_495818 : Nat := 118140960795 + 495818 * 2 ^ 59
def prefixEnd_495818 : Nat := 4983230072969 + 3 ^ 40 * 495818 * 2
def baseEnd_495818 : Nat := 37717474244599458295523

theorem tailTrace_495818 : CollatzResearch.WordTrace tailWord_495818 prefixEnd_495818 37717474244599458295523 := by
  unfold tailWord_495818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4520992029435884954468027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12055978745162359878581405 4520992029435884954468027)
  ·
    refine ⟨6781488044153827431702041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4520992029435884954468027 6781488044153827431702041)
    ·
      refine ⟨5086116033115370573776531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6781488044153827431702041 5086116033115370573776531)
      ·
        refine ⟨7629174049673055860664797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5086116033115370573776531 7629174049673055860664797)
        ·
          refine ⟨2860940268627395947749299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7629174049673055860664797 2860940268627395947749299)
          ·
            refine ⟨4291410402941093921623949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2860940268627395947749299 4291410402941093921623949)
            ·
              refine ⟨1609278901102910220608981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4291410402941093921623949 1609278901102910220608981)
              ·
                refine ⟨37717474244599458295523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1609278901102910220608981 37717474244599458295523)
                ·
                  rfl

theorem cell21_495818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_495818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495818 prefixEnd_495818 := by exact prefixLift 495818
  have htrace : WordTrace (prefixWord ++ tailWord_495818) baseStart_495818 baseEnd_495818 := by
    simpa [prefixWord, tailWord_495818, baseEnd_495818] using wordTrace_append hprefix tailTrace_495818
  have hstable : (prefixWord ++ tailWord_495818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495818).length < 2 ^ (prefixWord ++ tailWord_495818).sum := by decide
  have hdescent : baseEnd_495818 < baseStart_495818 := by decide
  rcases family_descends (prefixWord ++ tailWord_495818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495925 : List Nat := [1, 3, 3, 1, 2, 1, 3, 2, 5]
def baseStart_495925 : Nat := 118140960795 + 495925 * 2 ^ 59
def prefixEnd_495925 : Nat := 4983230072969 + 3 ^ 40 * 495925 * 2
def baseEnd_495925 : Nat := 113176841591589966603017

theorem tailTrace_495925 : CollatzResearch.WordTrace tailWord_495925 prefixEnd_495925 113176841591589966603017 := by
  unfold tailWord_495925
  simp only [CollatzResearch.WordTrace]
  refine ⟨18087870728355897092017229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12058580485570598061344819 18087870728355897092017229)
  ·
    refine ⟨6782951523133461409506461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18087870728355897092017229 6782951523133461409506461)
    ·
      refine ⟨2543606821175048028564923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6782951523133461409506461 2543606821175048028564923)
      ·
        refine ⟨3815410231762572042847385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2543606821175048028564923 3815410231762572042847385)
        ·
          refine ⟨2861557673821929032135539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3815410231762572042847385 2861557673821929032135539)
          ·
            refine ⟨4292336510732893548203309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861557673821929032135539 4292336510732893548203309)
            ·
              refine ⟨1609626191524835080576241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4292336510732893548203309 1609626191524835080576241)
              ·
                refine ⟨1207219643643626310432181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1609626191524835080576241 1207219643643626310432181)
                ·
                  refine ⟨113176841591589966603017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1207219643643626310432181 113176841591589966603017)
                  ·
                    rfl

theorem cell21_495925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_495925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495925 prefixEnd_495925 := by exact prefixLift 495925
  have htrace : WordTrace (prefixWord ++ tailWord_495925) baseStart_495925 baseEnd_495925 := by
    simpa [prefixWord, tailWord_495925, baseEnd_495925] using wordTrace_append hprefix tailTrace_495925
  have hstable : (prefixWord ++ tailWord_495925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495925).length < 2 ^ (prefixWord ++ tailWord_495925).sum := by decide
  have hdescent : baseEnd_495925 < baseStart_495925 := by decide
  rcases family_descends (prefixWord ++ tailWord_495925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495956 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 6]
def baseStart_495956 : Nat := 118140960795 + 495956 * 2 ^ 59
def prefixEnd_495956 : Nat := 4983230072969 + 3 ^ 40 * 495956 * 2
def baseEnd_495956 : Nat := 113183916213940801586287

theorem tailTrace_495956 : CollatzResearch.WordTrace tailWord_495956 prefixEnd_495956 113183916213940801586287 := by
  unfold tailWord_495956
  simp only [CollatzResearch.WordTrace]
  refine ⟨9044500695621794693197861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12059334260829059590930481 9044500695621794693197861)
  ·
    refine ⟨1695843880429086504974599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9044500695621794693197861 1695843880429086504974599)
    ·
      refine ⟨2543765820643629757461899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1695843880429086504974599 2543765820643629757461899)
      ·
        refine ⟨3815648730965444636192849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2543765820643629757461899 3815648730965444636192849)
        ·
          refine ⟨2861736548224083477144637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3815648730965444636192849 2861736548224083477144637)
          ·
            refine ⟨1073151205584031303929239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2861736548224083477144637 1073151205584031303929239)
            ·
              refine ⟨1609726808376046955893859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073151205584031303929239 1609726808376046955893859)
              ·
                refine ⟨2414590212564070433840789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1609726808376046955893859 2414590212564070433840789)
                ·
                  refine ⟨113183916213940801586287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2414590212564070433840789 113183916213940801586287)
                  ·
                    rfl

theorem cell21_495956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_495956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495956 prefixEnd_495956 := by exact prefixLift 495956
  have htrace : WordTrace (prefixWord ++ tailWord_495956) baseStart_495956 baseEnd_495956 := by
    simpa [prefixWord, tailWord_495956, baseEnd_495956] using wordTrace_append hprefix tailTrace_495956
  have hstable : (prefixWord ++ tailWord_495956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495956).length < 2 ^ (prefixWord ++ tailWord_495956).sum := by decide
  have hdescent : baseEnd_495956 < baseStart_495956 := by decide
  rcases family_descends (prefixWord ++ tailWord_495956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495973 : List Nat := [1, 3, 1, 3, 1, 4, 3, 1, 4]
def baseStart_495973 : Nat := 118140960795 + 495973 * 2 ^ 59
def prefixEnd_495973 : Nat := 4983230072969 + 3 ^ 40 * 495973 * 2
def baseEnd_495973 : Nat := 113187795845552549802919

theorem tailTrace_495973 : CollatzResearch.WordTrace tailWord_495973 prefixEnd_495973 113187795845552549802919 := by
  unfold tailWord_495973
  simp only [CollatzResearch.WordTrace]
  refine ⟨18089621432182001289764573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12059747621454667526509715 18089621432182001289764573)
  ·
    refine ⟨6783608037068250483661715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18089621432182001289764573 6783608037068250483661715)
    ·
      refine ⟨10175412055602375725492573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6783608037068250483661715 10175412055602375725492573)
      ·
        refine ⟨3815779520850890897059715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10175412055602375725492573 3815779520850890897059715)
        ·
          refine ⟨5723669281276336345589573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815779520850890897059715 5723669281276336345589573)
          ·
            refine ⟨1073187990239313064798045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5723669281276336345589573 1073187990239313064798045)
            ·
              refine ⟨402445496339742399299267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1073187990239313064798045 402445496339742399299267)
              ·
                refine ⟨603668244509613598948901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402445496339742399299267 603668244509613598948901)
                ·
                  refine ⟨113187795845552549802919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 603668244509613598948901 113187795845552549802919)
                  ·
                    rfl

theorem cell21_495973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_495973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_495973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_495973 prefixEnd_495973 := by exact prefixLift 495973
  have htrace : WordTrace (prefixWord ++ tailWord_495973) baseStart_495973 baseEnd_495973 := by
    simpa [prefixWord, tailWord_495973, baseEnd_495973] using wordTrace_append hprefix tailTrace_495973
  have hstable : (prefixWord ++ tailWord_495973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495973).length < 2 ^ (prefixWord ++ tailWord_495973).sum := by decide
  have hdescent : baseEnd_495973 < baseStart_495973 := by decide
  rcases family_descends (prefixWord ++ tailWord_495973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496032 : List Nat := [2, 1, 1, 4, 1, 4, 1, 3, 4]
def baseStart_496032 : Nat := 118140960795 + 496032 * 2 ^ 59
def prefixEnd_496032 : Nat := 4983230072969 + 3 ^ 40 * 496032 * 2
def baseEnd_496032 : Nat := 113201260449381558319465

theorem tailTrace_496032 : CollatzResearch.WordTrace tailWord_496032 prefixEnd_496032 113201260449381558319465 := by
  unfold tailWord_496032
  simp only [CollatzResearch.WordTrace]
  refine ⟨9045886669484127183081175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12061182225978836244108233 9045886669484127183081175)
  ·
    refine ⟨13568830004226190774621763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9045886669484127183081175 13568830004226190774621763)
    ·
      refine ⟨20353245006339286161932645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13568830004226190774621763 20353245006339286161932645)
      ·
        refine ⟨3816233438688616155362371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20353245006339286161932645 3816233438688616155362371)
        ·
          refine ⟨5724350158032924233043557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3816233438688616155362371 5724350158032924233043557)
          ·
            refine ⟨1073315654631173293695667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5724350158032924233043557 1073315654631173293695667)
            ·
              refine ⟨1609973481946759940543501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073315654631173293695667 1609973481946759940543501)
              ·
                refine ⟨603740055730034977703813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1609973481946759940543501 603740055730034977703813)
                ·
                  refine ⟨113201260449381558319465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 603740055730034977703813 113201260449381558319465)
                  ·
                    rfl

theorem cell21_496032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_496032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_496032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_496032 prefixEnd_496032 := by exact prefixLift 496032
  have htrace : WordTrace (prefixWord ++ tailWord_496032) baseStart_496032 baseEnd_496032 := by
    simpa [prefixWord, tailWord_496032, baseEnd_496032] using wordTrace_append hprefix tailTrace_496032
  have hstable : (prefixWord ++ tailWord_496032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496032).length < 2 ^ (prefixWord ++ tailWord_496032).sum := by decide
  have hdescent : baseEnd_496032 < baseStart_496032 := by decide
  rcases family_descends (prefixWord ++ tailWord_496032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496173 : List Nat := [1, 5, 4, 1, 1, 2, 7]
def baseStart_496173 : Nat := 118140960795 + 496173 * 2 ^ 59
def prefixEnd_496173 : Nat := 4983230072969 + 3 ^ 40 * 496173 * 2
def baseEnd_496173 : Nat := 12581493174488516274353

theorem tailTrace_496173 : CollatzResearch.WordTrace tailWord_496173 prefixEnd_496173 12581493174488516274353 := by
  unfold tailWord_496173
  simp only [CollatzResearch.WordTrace]
  refine ⟨18096916031457435447045173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12064610687638290298030115 18096916031457435447045173)
  ·
    refine ⟨1696585877949134573160485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18096916031457435447045173 1696585877949134573160485)
    ·
      refine ⟨318109852115462732467591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1696585877949134573160485 318109852115462732467591)
      ·
        refine ⟨477164778173194098701387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318109852115462732467591 477164778173194098701387)
        ·
          refine ⟨715747167259791148052081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477164778173194098701387 715747167259791148052081)
          ·
            refine ⟨536810375444843361039061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 715747167259791148052081 536810375444843361039061)
            ·
              refine ⟨12581493174488516274353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 536810375444843361039061 12581493174488516274353)
              ·
                rfl

theorem cell21_496173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 7].length) (baseStart_496173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_496173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_496173 prefixEnd_496173 := by exact prefixLift 496173
  have htrace : WordTrace (prefixWord ++ tailWord_496173) baseStart_496173 baseEnd_496173 := by
    simpa [prefixWord, tailWord_496173, baseEnd_496173] using wordTrace_append hprefix tailTrace_496173
  have hstable : (prefixWord ++ tailWord_496173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496173).length < 2 ^ (prefixWord ++ tailWord_496173).sum := by decide
  have hdescent : baseEnd_496173 < baseStart_496173 := by decide
  rcases family_descends (prefixWord ++ tailWord_496173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496260 : List Nat := [2, 3, 2, 1, 3, 1, 2, 3, 4]
def baseStart_496260 : Nat := 118140960795 + 496260 * 2 ^ 59
def prefixEnd_496260 : Nat := 4983230072969 + 3 ^ 40 * 496260 * 2
def baseEnd_496260 : Nat := 113253293155703828518999

theorem tailTrace_496260 : CollatzResearch.WordTrace tailWord_496260 prefixEnd_496260 113253293155703828518999 := by
  unfold tailWord_496260
  simp only [CollatzResearch.WordTrace]
  refine ⟨9050044591071124652731117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12066726121428166203641489 9050044591071124652731117)
  ·
    refine ⟨3393766721651671744774169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9050044591071124652731117 3393766721651671744774169)
    ·
      refine ⟨2545325041238753808580627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3393766721651671744774169 2545325041238753808580627)
      ·
        refine ⟨3817987561858130712870941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2545325041238753808580627 3817987561858130712870941)
        ·
          refine ⟨1431745335696799017326603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3817987561858130712870941 1431745335696799017326603)
          ·
            refine ⟨2147618003545198525989905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431745335696799017326603 2147618003545198525989905)
            ·
              refine ⟨1610713502658898894492429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2147618003545198525989905 1610713502658898894492429)
              ·
                refine ⟨604017563497087085434661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1610713502658898894492429 604017563497087085434661)
                ·
                  refine ⟨113253293155703828518999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 604017563497087085434661 113253293155703828518999)
                  ·
                    rfl

theorem cell21_496260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_496260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_496260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_496260 prefixEnd_496260 := by exact prefixLift 496260
  have htrace : WordTrace (prefixWord ++ tailWord_496260) baseStart_496260 baseEnd_496260 := by
    simpa [prefixWord, tailWord_496260, baseEnd_496260] using wordTrace_append hprefix tailTrace_496260
  have hstable : (prefixWord ++ tailWord_496260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496260).length < 2 ^ (prefixWord ++ tailWord_496260).sum := by decide
  have hdescent : baseEnd_496260 < baseStart_496260 := by decide
  rcases family_descends (prefixWord ++ tailWord_496260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496412 : List Nat := [2, 2, 3, 1, 1, 4, 2, 2, 4]
def baseStart_496412 : Nat := 118140960795 + 496412 * 2 ^ 59
def prefixEnd_496412 : Nat := 4983230072969 + 3 ^ 40 * 496412 * 2
def baseEnd_496412 : Nat := 113287981626585341985355

theorem tailTrace_496412 : CollatzResearch.WordTrace tailWord_496412 prefixEnd_496412 113287981626585341985355 := by
  unfold tailWord_496412
  simp only [CollatzResearch.WordTrace]
  refine ⟨9052816538795789632497745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12070422051727719509996993 9052816538795789632497745)
  ·
    refine ⟨6789612404096842224373309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9052816538795789632497745 6789612404096842224373309)
    ·
      refine ⟨2546104651536315834139991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6789612404096842224373309 2546104651536315834139991)
      ·
        refine ⟨3819156977304473751209987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2546104651536315834139991 3819156977304473751209987)
        ·
          refine ⟨5728735465956710626814981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3819156977304473751209987 5728735465956710626814981)
          ·
            refine ⟨1074137899866883242527809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5728735465956710626814981 1074137899866883242527809)
            ·
              refine ⟨805603424900162431895857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1074137899866883242527809 805603424900162431895857)
              ·
                refine ⟨604202568675121823921893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 805603424900162431895857 604202568675121823921893)
                ·
                  refine ⟨113287981626585341985355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 604202568675121823921893 113287981626585341985355)
                  ·
                    rfl

theorem cell21_496412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_496412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_496412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_496412 prefixEnd_496412 := by exact prefixLift 496412
  have htrace : WordTrace (prefixWord ++ tailWord_496412) baseStart_496412 baseEnd_496412 := by
    simpa [prefixWord, tailWord_496412, baseEnd_496412] using wordTrace_append hprefix tailTrace_496412
  have hstable : (prefixWord ++ tailWord_496412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496412).length < 2 ^ (prefixWord ++ tailWord_496412).sum := by decide
  have hdescent : baseEnd_496412 < baseStart_496412 := by decide
  rcases family_descends (prefixWord ++ tailWord_496412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
