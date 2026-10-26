import V185TrunkScan23Chunk0957

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5672244 : List Nat := [2, 5, 1, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_5672244 : Nat := 118140960795 + 5672244 * 2 ^ 59
def prefixEnd_5672244 : Nat := 4983230072969 + 3 ^ 40 * 5672244 * 2
def baseEnd_5672244 : Nat := 2912587561581610552963831

theorem tailTrace_5672244 : CollatzResearch.WordTrace tailWord_5672244 prefixEnd_5672244 2912587561581610552963831 := by
  unfold tailWord_5672244
  simp only [CollatzResearch.WordTrace]
  refine ⟨103441867431218102497403893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137922489908290803329871857 103441867431218102497403893)
  ·
    refine ⟨9697675071676697109131615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103441867431218102497403893 9697675071676697109131615)
    ·
      refine ⟨14546512607515045663697423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9697675071676697109131615 14546512607515045663697423)
      ·
        refine ⟨21819768911272568495546135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14546512607515045663697423 21819768911272568495546135)
        ·
          refine ⟨32729653366908852743319203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21819768911272568495546135 32729653366908852743319203)
          ·
            refine ⟨49094480050363279114978805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32729653366908852743319203 49094480050363279114978805)
            ·
              refine ⟨4602607504721557417029263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49094480050363279114978805 4602607504721557417029263)
              ·
                refine ⟨6903911257082336125543895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4602607504721557417029263 6903911257082336125543895)
                ·
                  refine ⟨10355866885623504188315843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6903911257082336125543895 10355866885623504188315843)
                  ·
                    refine ⟨15533800328435256282473765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10355866885623504188315843 15533800328435256282473765)
                    ·
                      refine ⟨2912587561581610552963831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15533800328435256282473765 2912587561581610552963831)
                      ·
                        rfl

theorem cell23_5672244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_5672244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672244 prefixEnd_5672244 := by exact prefixLift 5672244
  have htrace : WordTrace (prefixWord ++ tailWord_5672244) baseStart_5672244 baseEnd_5672244 := by
    simpa [prefixWord, tailWord_5672244, baseEnd_5672244] using wordTrace_append hprefix tailTrace_5672244
  have hstable : (prefixWord ++ tailWord_5672244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672244).length < 2 ^ (prefixWord ++ tailWord_5672244).sum := by decide
  have hdescent : baseEnd_5672244 < baseStart_5672244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672263 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 2, 7]
def baseStart_5672263 : Nat := 118140960795 + 5672263 * 2 ^ 59
def prefixEnd_5672263 : Nat := 4983230072969 + 3 ^ 40 * 5672263 * 2
def baseEnd_5672263 : Nat := 970865772571348659542081

theorem tailTrace_5672263 : CollatzResearch.WordTrace tailWord_5672263 prefixEnd_5672263 970865772571348659542081 := by
  unfold tailWord_5672263
  simp only [CollatzResearch.WordTrace]
  refine ⟨206884427849367371239749443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137922951899578247493166295 206884427849367371239749443)
  ·
    refine ⟨310326641774051056859624165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206884427849367371239749443 310326641774051056859624165)
    ·
      refine ⟨58186245332634573161179531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310326641774051056859624165 58186245332634573161179531)
      ·
        refine ⟨87279367998951859741769297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58186245332634573161179531 87279367998951859741769297)
        ·
          refine ⟨65459525999213894806326973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87279367998951859741769297 65459525999213894806326973)
          ·
            refine ⟨24547322249705210552372615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65459525999213894806326973 24547322249705210552372615)
            ·
              refine ⟨36820983374557815828558923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24547322249705210552372615 36820983374557815828558923)
              ·
                refine ⟨55231475061836723742838385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36820983374557815828558923 55231475061836723742838385)
                ·
                  refine ⟨41423606296377542807128789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55231475061836723742838385 41423606296377542807128789)
                  ·
                    refine ⟨970865772571348659542081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41423606296377542807128789 970865772571348659542081)
                    ·
                      rfl

theorem cell23_5672263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_5672263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672263 prefixEnd_5672263 := by exact prefixLift 5672263
  have htrace : WordTrace (prefixWord ++ tailWord_5672263) baseStart_5672263 baseEnd_5672263 := by
    simpa [prefixWord, tailWord_5672263, baseEnd_5672263] using wordTrace_append hprefix tailTrace_5672263
  have hstable : (prefixWord ++ tailWord_5672263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672263).length < 2 ^ (prefixWord ++ tailWord_5672263).sum := by decide
  have hdescent : baseEnd_5672263 < baseStart_5672263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672277 : List Nat := [1, 3, 2, 2, 3, 2, 2, 1, 1, 3, 3]
def baseStart_5672277 : Nat := 118140960795 + 5672277 * 2 ^ 59
def prefixEnd_5672277 : Nat := 4983230072969 + 3 ^ 40 * 5672277 * 2
def baseEnd_5672277 : Nat := 2912604506443208923851179

theorem tailTrace_5672277 : CollatzResearch.WordTrace tailWord_5672277 prefixEnd_5672277 2912604506443208923851179 := by
  unfold tailWord_5672277
  simp only [CollatzResearch.WordTrace]
  refine ⟨206884938471316651630759085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137923292314211101087172723 206884938471316651630759085)
  ·
    refine ⟨77581851926743744361534657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206884938471316651630759085 77581851926743744361534657)
    ·
      refine ⟨58186388945057808271150993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77581851926743744361534657 58186388945057808271150993)
      ·
        refine ⟨43639791708793356203363245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58186388945057808271150993 43639791708793356203363245)
        ·
          refine ⟨16364921890797508576261217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43639791708793356203363245 16364921890797508576261217)
          ·
            refine ⟨12273691418098131432195913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16364921890797508576261217 12273691418098131432195913)
            ·
              refine ⟨9205268563573598574146935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12273691418098131432195913 9205268563573598574146935)
              ·
                refine ⟨13807902845360397861220403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9205268563573598574146935 13807902845360397861220403)
                ·
                  refine ⟨20711854268040596791830605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13807902845360397861220403 20711854268040596791830605)
                  ·
                    refine ⟨7766945350515223796936477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20711854268040596791830605 7766945350515223796936477)
                    ·
                      refine ⟨2912604506443208923851179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7766945350515223796936477 2912604506443208923851179)
                      ·
                        rfl

theorem cell23_5672277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_5672277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672277 prefixEnd_5672277 := by exact prefixLift 5672277
  have htrace : WordTrace (prefixWord ++ tailWord_5672277) baseStart_5672277 baseEnd_5672277 := by
    simpa [prefixWord, tailWord_5672277, baseEnd_5672277] using wordTrace_append hprefix tailTrace_5672277
  have hstable : (prefixWord ++ tailWord_5672277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672277).length < 2 ^ (prefixWord ++ tailWord_5672277).sum := by decide
  have hdescent : baseEnd_5672277 < baseStart_5672277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672287 : List Nat := [1, 1, 2, 3, 1, 2, 1, 6, 1, 3, 2]
def baseStart_5672287 : Nat := 118140960795 + 5672287 * 2 ^ 59
def prefixEnd_5672287 : Nat := 4983230072969 + 3 ^ 40 * 5672287 * 2
def baseEnd_5672287 : Nat := 2912609641249753884726133

theorem tailTrace_5672287 : CollatzResearch.WordTrace tailWord_5672287 prefixEnd_5672287 2912609641249753884726133 := by
  unfold tailWord_5672287
  simp only [CollatzResearch.WordTrace]
  refine ⟨206885303201280423338623115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137923535467520282225748743 206885303201280423338623115)
  ·
    refine ⟨310327954801920635007934673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206885303201280423338623115 310327954801920635007934673)
    ·
      refine ⟨232745966101440476255951005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310327954801920635007934673 232745966101440476255951005)
      ·
        refine ⟨87279737288040178595981627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232745966101440476255951005 87279737288040178595981627)
        ·
          refine ⟨130919605932060267893972441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87279737288040178595981627 130919605932060267893972441)
          ·
            refine ⟨98189704449045200920479331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130919605932060267893972441 98189704449045200920479331)
            ·
              refine ⟨147284556673567801380718997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98189704449045200920479331 147284556673567801380718997)
              ·
                refine ⟨6903963594073490689721203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 147284556673567801380718997 6903963594073490689721203)
                ·
                  refine ⟨10355945391110236034581805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6903963594073490689721203 10355945391110236034581805)
                  ·
                    refine ⟨3883479521666338512968177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10355945391110236034581805 3883479521666338512968177)
                    ·
                      refine ⟨2912609641249753884726133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3883479521666338512968177 2912609641249753884726133)
                      ·
                        rfl

theorem cell23_5672287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_5672287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672287 prefixEnd_5672287 := by exact prefixLift 5672287
  have htrace : WordTrace (prefixWord ++ tailWord_5672287) baseStart_5672287 baseEnd_5672287 := by
    simpa [prefixWord, tailWord_5672287, baseEnd_5672287] using wordTrace_append hprefix tailTrace_5672287
  have hstable : (prefixWord ++ tailWord_5672287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672287).length < 2 ^ (prefixWord ++ tailWord_5672287).sum := by decide
  have hdescent : baseEnd_5672287 < baseStart_5672287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672290 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_5672290 : Nat := 118140960795 + 5672290 * 2 ^ 59
def prefixEnd_5672290 : Nat := 4983230072969 + 3 ^ 40 * 5672290 * 2
def baseEnd_5672290 : Nat := 2912611181691717372988619

theorem tailTrace_5672290 : CollatzResearch.WordTrace tailWord_5672290 prefixEnd_5672290 2912611181691717372988619 := by
  unfold tailWord_5672290
  simp only [CollatzResearch.WordTrace]
  refine ⟨51721353155067388712745581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137923608413513036567321549 51721353155067388712745581)
  ·
    refine ⟨19395507433150270767279593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51721353155067388712745581 19395507433150270767279593)
    ·
      refine ⟨14546630574862703075459695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19395507433150270767279593 14546630574862703075459695)
      ·
        refine ⟨21819945862294054613189543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14546630574862703075459695 21819945862294054613189543)
        ·
          refine ⟨32729918793441081919784315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21819945862294054613189543 32729918793441081919784315)
          ·
            refine ⟨49094878190161622879676473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32729918793441081919784315 49094878190161622879676473)
            ·
              refine ⟨36821158642621217159757355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49094878190161622879676473 36821158642621217159757355)
              ·
                refine ⟨55231737963931825739636033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36821158642621217159757355 55231737963931825739636033)
                ·
                  refine ⟨41423803472948869304727025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55231737963931825739636033 41423803472948869304727025)
                  ·
                    refine ⟨31067852604711651978545269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41423803472948869304727025 31067852604711651978545269)
                    ·
                      refine ⟨2912611181691717372988619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31067852604711651978545269 2912611181691717372988619)
                      ·
                        rfl

theorem cell23_5672290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_5672290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672290 prefixEnd_5672290 := by exact prefixLift 5672290
  have htrace : WordTrace (prefixWord ++ tailWord_5672290) baseStart_5672290 baseEnd_5672290 := by
    simpa [prefixWord, tailWord_5672290, baseEnd_5672290] using wordTrace_append hprefix tailTrace_5672290
  have hstable : (prefixWord ++ tailWord_5672290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672290).length < 2 ^ (prefixWord ++ tailWord_5672290).sum := by decide
  have hdescent : baseEnd_5672290 < baseStart_5672290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672293 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 1, 8]
def baseStart_5672293 : Nat := 118140960795 + 5672293 * 2 ^ 59
def prefixEnd_5672293 : Nat := 4983230072969 + 3 ^ 40 * 5672293 * 2
def baseEnd_5672293 : Nat := 970870907377893620417035

theorem tailTrace_5672293 : CollatzResearch.WordTrace tailWord_5672293 prefixEnd_5672293 970870907377893620417035 := by
  unfold tailWord_5672293
  simp only [CollatzResearch.WordTrace]
  refine ⟨206885522039258686363341533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137923681359505790908894355 206885522039258686363341533)
  ·
    refine ⟨77582070764722007386253075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206885522039258686363341533 77582070764722007386253075)
    ·
      refine ⟨116373106147083011079379613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77582070764722007386253075 116373106147083011079379613)
      ·
        refine ⟨43639914805156129154767355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116373106147083011079379613 43639914805156129154767355)
        ·
          refine ⟨65459872207734193732151033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43639914805156129154767355 65459872207734193732151033)
          ·
            refine ⟨49094904155800645299113275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65459872207734193732151033 49094904155800645299113275)
            ·
              refine ⟨73642356233700967948669913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49094904155800645299113275 73642356233700967948669913)
              ·
                refine ⟨55231767175275725961502435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73642356233700967948669913 55231767175275725961502435)
                ·
                  refine ⟨82847650762913588942253653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55231767175275725961502435 82847650762913588942253653)
                  ·
                    refine ⟨970870907377893620417035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82847650762913588942253653 970870907377893620417035)
                    ·
                      rfl

theorem cell23_5672293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_5672293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672293 prefixEnd_5672293 := by exact prefixLift 5672293
  have htrace : WordTrace (prefixWord ++ tailWord_5672293) baseStart_5672293 baseEnd_5672293 := by
    simpa [prefixWord, tailWord_5672293, baseEnd_5672293] using wordTrace_append hprefix tailTrace_5672293
  have hstable : (prefixWord ++ tailWord_5672293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672293).length < 2 ^ (prefixWord ++ tailWord_5672293).sum := by decide
  have hdescent : baseEnd_5672293 < baseStart_5672293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672298 : List Nat := [3, 1, 3, 3, 3, 1, 2, 1, 1, 2, 3]
def baseStart_5672298 : Nat := 118140960795 + 5672298 * 2 ^ 59
def prefixEnd_5672298 : Nat := 4983230072969 + 3 ^ 40 * 5672298 * 2
def baseEnd_5672298 : Nat := 2912615289536953341688583

theorem tailTrace_5672298 : CollatzResearch.WordTrace tailWord_5672298 prefixEnd_5672298 2912615289536953341688583 := by
  unfold tailWord_5672298
  simp only [CollatzResearch.WordTrace]
  refine ⟨51721426101060143054318387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137923802936160381478182365 51721426101060143054318387)
  ·
    refine ⟨77582139151590214581477581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51721426101060143054318387 77582139151590214581477581)
    ·
      refine ⟨29093302181846330468054093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77582139151590214581477581 29093302181846330468054093)
      ·
        refine ⟨10909988318192373925520285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29093302181846330468054093 10909988318192373925520285)
        ·
          refine ⟨4091245619322140222070107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10909988318192373925520285 4091245619322140222070107)
          ·
            refine ⟨6136868428983210333105161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4091245619322140222070107 6136868428983210333105161)
            ·
              refine ⟨4602651321737407749828871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6136868428983210333105161 4602651321737407749828871)
              ·
                refine ⟨6903976982606111624743307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4602651321737407749828871 6903976982606111624743307)
                ·
                  refine ⟨10355965473909167437114961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6903976982606111624743307 10355965473909167437114961)
                  ·
                    refine ⟨7766974105431875577836221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10355965473909167437114961 7766974105431875577836221)
                    ·
                      refine ⟨2912615289536953341688583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7766974105431875577836221 2912615289536953341688583)
                      ·
                        rfl

theorem cell23_5672298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_5672298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672298 prefixEnd_5672298 := by exact prefixLift 5672298
  have htrace : WordTrace (prefixWord ++ tailWord_5672298) baseStart_5672298 baseEnd_5672298 := by
    simpa [prefixWord, tailWord_5672298, baseEnd_5672298] using wordTrace_append hprefix tailTrace_5672298
  have hstable : (prefixWord ++ tailWord_5672298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672298).length < 2 ^ (prefixWord ++ tailWord_5672298).sum := by decide
  have hdescent : baseEnd_5672298 < baseStart_5672298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672303 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 5]
def baseStart_5672303 : Nat := 118140960795 + 5672303 * 2 ^ 59
def prefixEnd_5672303 : Nat := 4983230072969 + 3 ^ 40 * 5672303 * 2
def baseEnd_5672303 : Nat := 2912617856940225822126059

theorem tailTrace_5672303 : CollatzResearch.WordTrace tailWord_5672303 prefixEnd_5672303 2912617856940225822126059 := by
  unfold tailWord_5672303
  simp only [CollatzResearch.WordTrace]
  refine ⟨206885886769222458071205563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137923924512814972047470375 206885886769222458071205563)
  ·
    refine ⟨310328830153833687106808345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206885886769222458071205563 310328830153833687106808345)
    ·
      refine ⟨232746622615375265330106259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310328830153833687106808345 232746622615375265330106259)
      ·
        refine ⟨349119933923062897995159389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232746622615375265330106259 349119933923062897995159389)
        ·
          refine ⟨130919975221148586748184771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 349119933923062897995159389 130919975221148586748184771)
          ·
            refine ⟨196379962831722880122277157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130919975221148586748184771 196379962831722880122277157)
            ·
              refine ⟨36821243030948040022926967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196379962831722880122277157 36821243030948040022926967)
              ·
                refine ⟨55231864546422060034390451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36821243030948040022926967 55231864546422060034390451)
                ·
                  refine ⟨82847796819633090051585677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55231864546422060034390451 82847796819633090051585677)
                  ·
                    refine ⟨31067923807362408769344629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82847796819633090051585677 31067923807362408769344629)
                    ·
                      refine ⟨2912617856940225822126059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31067923807362408769344629 2912617856940225822126059)
                      ·
                        rfl

theorem cell23_5672303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_5672303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672303 prefixEnd_5672303 := by exact prefixLift 5672303
  have htrace : WordTrace (prefixWord ++ tailWord_5672303) baseStart_5672303 baseEnd_5672303 := by
    simpa [prefixWord, tailWord_5672303, baseEnd_5672303] using wordTrace_append hprefix tailTrace_5672303
  have hstable : (prefixWord ++ tailWord_5672303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672303).length < 2 ^ (prefixWord ++ tailWord_5672303).sum := by decide
  have hdescent : baseEnd_5672303 < baseStart_5672303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672338 : List Nat := [3, 2, 3, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_5672338 : Nat := 118140960795 + 5672338 * 2 ^ 59
def prefixEnd_5672338 : Nat := 4983230072969 + 3 ^ 40 * 5672338 * 2
def baseEnd_5672338 : Nat := 2912635828763133185188399

theorem tailTrace_5672338 : CollatzResearch.WordTrace tailWord_5672338 prefixEnd_5672338 2912635828763133185188399 := by
  unfold tailWord_5672338
  simp only [CollatzResearch.WordTrace]
  refine ⟨51721790831023914762182417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137924775549397106032486445 51721790831023914762182417)
  ·
    refine ⟨38791343123267936071636813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51721790831023914762182417 38791343123267936071636813)
    ·
      refine ⟨14546753671225476026863805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38791343123267936071636813 14546753671225476026863805)
      ·
        refine ⟨5455032626709553510073927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14546753671225476026863805 5455032626709553510073927)
        ·
          refine ⟨8182548940064330265110891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5455032626709553510073927 8182548940064330265110891)
          ·
            refine ⟨12273823410096495397666337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8182548940064330265110891 12273823410096495397666337)
            ·
              refine ⟨9205367557572371548249753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12273823410096495397666337 9205367557572371548249753)
              ·
                refine ⟨6904025668179278661187315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9205367557572371548249753 6904025668179278661187315)
                ·
                  refine ⟨10356038502268917991780973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6904025668179278661187315 10356038502268917991780973)
                  ·
                    refine ⟨3883514438350844246917865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10356038502268917991780973 3883514438350844246917865)
                    ·
                      refine ⟨2912635828763133185188399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3883514438350844246917865 2912635828763133185188399)
                      ·
                        rfl

theorem cell23_5672338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_5672338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672338 prefixEnd_5672338 := by exact prefixLift 5672338
  have htrace : WordTrace (prefixWord ++ tailWord_5672338) baseStart_5672338 baseEnd_5672338 := by
    simpa [prefixWord, tailWord_5672338, baseEnd_5672338] using wordTrace_append hprefix tailTrace_5672338
  have hstable : (prefixWord ++ tailWord_5672338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672338).length < 2 ^ (prefixWord ++ tailWord_5672338).sum := by decide
  have hdescent : baseEnd_5672338 < baseStart_5672338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672363 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 5]
def baseStart_5672363 : Nat := 118140960795 + 5672363 * 2 ^ 59
def prefixEnd_5672363 : Nat := 4983230072969 + 3 ^ 40 * 5672363 * 2
def baseEnd_5672363 : Nat := 2912648665779495587375783

theorem tailTrace_5672363 : CollatzResearch.WordTrace tailWord_5672363 prefixEnd_5672363 2912648665779495587375783 := by
  unfold tailWord_5672363
  simp only [CollatzResearch.WordTrace]
  refine ⟨206888075149005088318389743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137925383432670058878926495 206888075149005088318389743)
  ·
    refine ⟨310332112723507632477584615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206888075149005088318389743 310332112723507632477584615)
    ·
      refine ⟨465498169085261448716376923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310332112723507632477584615 465498169085261448716376923)
      ·
        refine ⟨698247253627892173074565385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465498169085261448716376923 698247253627892173074565385)
        ·
          refine ⟨523685440220919129805924039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 698247253627892173074565385 523685440220919129805924039)
          ·
            refine ⟨785528160331378694708886059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523685440220919129805924039 785528160331378694708886059)
            ·
              refine ⟨1178292240497068042063329089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785528160331378694708886059 1178292240497068042063329089)
              ·
                refine ⟨883719180372801031547496817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1178292240497068042063329089 883719180372801031547496817)
                ·
                  refine ⟨662789385279600773660622613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 883719180372801031547496817 662789385279600773660622613)
                  ·
                    refine ⟨31068252434981286265341685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 662789385279600773660622613 31068252434981286265341685)
                    ·
                      refine ⟨2912648665779495587375783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31068252434981286265341685 2912648665779495587375783)
                      ·
                        rfl

theorem cell23_5672363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 5].length) (baseStart_5672363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672363 prefixEnd_5672363 := by exact prefixLift 5672363
  have htrace : WordTrace (prefixWord ++ tailWord_5672363) baseStart_5672363 baseEnd_5672363 := by
    simpa [prefixWord, tailWord_5672363, baseEnd_5672363] using wordTrace_append hprefix tailTrace_5672363
  have hstable : (prefixWord ++ tailWord_5672363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672363).length < 2 ^ (prefixWord ++ tailWord_5672363).sum := by decide
  have hdescent : baseEnd_5672363 < baseStart_5672363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672404 : List Nat := [2, 4, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_5672404 : Nat := 118140960795 + 5672404 * 2 ^ 59
def prefixEnd_5672404 : Nat := 4983230072969 + 3 ^ 40 * 5672404 * 2
def baseEnd_5672404 : Nat := 970889906162109975654365

theorem tailTrace_5672404 : CollatzResearch.WordTrace tailWord_5672404 prefixEnd_5672404 970889906162109975654365 := by
  unfold tailWord_5672404
  simp only [CollatzResearch.WordTrace]
  refine ⟨103444785270928276160316133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137926380361237701547088177 103444785270928276160316133)
  ·
    refine ⟨19395897238299051780059275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103444785270928276160316133 19395897238299051780059275)
    ·
      refine ⟨29093845857448577670088913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19395897238299051780059275 29093845857448577670088913)
      ·
        refine ⟨21820384393086433252566685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29093845857448577670088913 21820384393086433252566685)
        ·
          refine ⟨8182644147407412469712507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21820384393086433252566685 8182644147407412469712507)
          ·
            refine ⟨12273966221111118704568761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8182644147407412469712507 12273966221111118704568761)
            ·
              refine ⟨9205474665833339028426571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12273966221111118704568761 9205474665833339028426571)
              ·
                refine ⟨13808211998750008542639857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9205474665833339028426571 13808211998750008542639857)
                ·
                  refine ⟨10356158999062506406979893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13808211998750008542639857 10356158999062506406979893)
                  ·
                    refine ⟨970889906162109975654365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10356158999062506406979893 970889906162109975654365)
                    ·
                      rfl

theorem cell23_5672404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_5672404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672404 prefixEnd_5672404 := by exact prefixLift 5672404
  have htrace : WordTrace (prefixWord ++ tailWord_5672404) baseStart_5672404 baseEnd_5672404 := by
    simpa [prefixWord, tailWord_5672404, baseEnd_5672404] using wordTrace_append hprefix tailTrace_5672404
  have hstable : (prefixWord ++ tailWord_5672404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672404).length < 2 ^ (prefixWord ++ tailWord_5672404).sum := by decide
  have hdescent : baseEnd_5672404 < baseStart_5672404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672548 : List Nat := [2, 3, 1, 1, 2, 5, 1, 1, 3, 2, 2]
def baseStart_5672548 : Nat := 118140960795 + 5672548 * 2 ^ 59
def prefixEnd_5672548 : Nat := 4983230072969 + 3 ^ 40 * 5672548 * 2
def baseEnd_5672548 : Nat := 2912743659700577363562433

theorem tailTrace_5672548 : CollatzResearch.WordTrace tailWord_5672548 prefixEnd_5672548 2912743659700577363562433 := by
  unfold tailWord_5672548
  simp only [CollatzResearch.WordTrace]
  refine ⟨103447411326667432456937149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137929881768889909942582865 103447411326667432456937149)
  ·
    refine ⟨38792779247500287171351431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103447411326667432456937149 38792779247500287171351431)
    ·
      refine ⟨58189168871250430757027147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38792779247500287171351431 58189168871250430757027147)
      ·
        refine ⟨87283753306875646135540721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58189168871250430757027147 87283753306875646135540721)
        ·
          refine ⟨65462814980156734601655541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87283753306875646135540721 65462814980156734601655541)
          ·
            refine ⟨6137138904389693868905207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65462814980156734601655541 6137138904389693868905207)
            ·
              refine ⟨9205708356584540803357811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6137138904389693868905207 9205708356584540803357811)
              ·
                refine ⟨13808562534876811205036717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9205708356584540803357811 13808562534876811205036717)
                ·
                  refine ⟨5178210950578804201888769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13808562534876811205036717 5178210950578804201888769)
                  ·
                    refine ⟨3883658212934103151416577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5178210950578804201888769 3883658212934103151416577)
                    ·
                      refine ⟨2912743659700577363562433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3883658212934103151416577 2912743659700577363562433)
                      ·
                        rfl

theorem cell23_5672548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_5672548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672548 prefixEnd_5672548 := by exact prefixLift 5672548
  have htrace : WordTrace (prefixWord ++ tailWord_5672548) baseStart_5672548 baseEnd_5672548 := by
    simpa [prefixWord, tailWord_5672548, baseEnd_5672548] using wordTrace_append hprefix tailTrace_5672548
  have hstable : (prefixWord ++ tailWord_5672548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672548).length < 2 ^ (prefixWord ++ tailWord_5672548).sum := by decide
  have hdescent : baseEnd_5672548 < baseStart_5672548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672627 : List Nat := [1, 1, 1, 2, 3, 3, 3, 2, 7]
def baseStart_5672627 : Nat := 118140960795 + 5672627 * 2 ^ 59
def prefixEnd_5672627 : Nat := 4983230072969 + 3 ^ 40 * 5672627 * 2
def baseEnd_5672627 : Nat := 323642691630253617163841

theorem tailTrace_5672627 : CollatzResearch.WordTrace tailWord_5672627 prefixEnd_5672627 323642691630253617163841 := by
  unfold tailWord_5672627
  simp only [CollatzResearch.WordTrace]
  refine ⟨206897704020048661406000135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137931802680032440937333423 206897704020048661406000135)
  ·
    refine ⟨310346556030072992109000203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206897704020048661406000135 310346556030072992109000203)
    ·
      refine ⟨465519834045109488163500305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310346556030072992109000203 465519834045109488163500305)
      ·
        refine ⟨349139875533832116122625229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 465519834045109488163500305 349139875533832116122625229)
        ·
          refine ⟨130927453325187043545984461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 349139875533832116122625229 130927453325187043545984461)
          ·
            refine ⟨49097794996945141329744173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130927453325187043545984461 49097794996945141329744173)
            ·
              refine ⟨18411673123854427998654065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49097794996945141329744173 18411673123854427998654065)
              ·
                refine ⟨13808754842890820998990549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18411673123854427998654065 13808754842890820998990549)
                ·
                  refine ⟨323642691630253617163841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13808754842890820998990549 323642691630253617163841)
                  ·
                    rfl

theorem cell23_5672627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 7].length) (baseStart_5672627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672627 prefixEnd_5672627 := by exact prefixLift 5672627
  have htrace : WordTrace (prefixWord ++ tailWord_5672627) baseStart_5672627 baseEnd_5672627 := by
    simpa [prefixWord, tailWord_5672627, baseEnd_5672627] using wordTrace_append hprefix tailTrace_5672627
  have hstable : (prefixWord ++ tailWord_5672627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672627).length < 2 ^ (prefixWord ++ tailWord_5672627).sum := by decide
  have hdescent : baseEnd_5672627 < baseStart_5672627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672654 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3]
def baseStart_5672654 : Nat := 118140960795 + 5672654 * 2 ^ 59
def prefixEnd_5672654 : Nat := 4983230072969 + 3 ^ 40 * 5672654 * 2
def baseEnd_5672654 : Nat := 2912798088649953948836945

theorem tailTrace_5672654 : CollatzResearch.WordTrace tailWord_5672654 prefixEnd_5672654 2912798088649953948836945 := by
  unfold tailWord_5672654
  simp only [CollatzResearch.WordTrace]
  refine ⟨25862336098868855627154127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137932459193967230011488677 25862336098868855627154127)
  ·
    refine ⟨38793504148303283440731191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25862336098868855627154127 38793504148303283440731191)
    ·
      refine ⟨58190256222454925161096787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38793504148303283440731191 58190256222454925161096787)
      ·
        refine ⟨87285384333682387741645181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58190256222454925161096787 87285384333682387741645181)
        ·
          refine ⟨32732019125130895403116943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87285384333682387741645181 32732019125130895403116943)
          ·
            refine ⟨49098028687696343104675415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32732019125130895403116943 49098028687696343104675415)
            ·
              refine ⟨73647043031544514657013123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49098028687696343104675415 73647043031544514657013123)
              ·
                refine ⟨110470564547316771985519685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73647043031544514657013123 110470564547316771985519685)
                ·
                  refine ⟨20713230852621894747284941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110470564547316771985519685 20713230852621894747284941)
                  ·
                    refine ⟨7767461569733210530231853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20713230852621894747284941 7767461569733210530231853)
                    ·
                      refine ⟨2912798088649953948836945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7767461569733210530231853 2912798088649953948836945)
                      ·
                        rfl

theorem cell23_5672654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_5672654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672654 prefixEnd_5672654 := by exact prefixLift 5672654
  have htrace : WordTrace (prefixWord ++ tailWord_5672654) baseStart_5672654 baseEnd_5672654 := by
    simpa [prefixWord, tailWord_5672654, baseEnd_5672654] using wordTrace_append hprefix tailTrace_5672654
  have hstable : (prefixWord ++ tailWord_5672654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672654).length < 2 ^ (prefixWord ++ tailWord_5672654).sum := by decide
  have hdescent : baseEnd_5672654 < baseStart_5672654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672687 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 2, 8]
def baseStart_5672687 : Nat := 118140960795 + 5672687 * 2 ^ 59
def prefixEnd_5672687 : Nat := 4983230072969 + 3 ^ 40 * 5672687 * 2
def baseEnd_5672687 : Nat := 970938344503850773241431

theorem tailTrace_5672687 : CollatzResearch.WordTrace tailWord_5672687 prefixEnd_5672687 970938344503850773241431 := by
  unfold tailWord_5672687
  simp only [CollatzResearch.WordTrace]
  refine ⟨206899892399831291653184315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137933261599887527768789543 206899892399831291653184315)
  ·
    refine ⟨310349838599746937479776473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206899892399831291653184315 310349838599746937479776473)
    ·
      refine ⟨232762378949810203109832355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310349838599746937479776473 232762378949810203109832355)
      ·
        refine ⟨349143568424715304664748533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232762378949810203109832355 349143568424715304664748533)
        ·
          refine ⟨32732209539817059812320175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 349143568424715304664748533 32732209539817059812320175)
          ·
            refine ⟨49098314309725589718480263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32732209539817059812320175 49098314309725589718480263)
            ·
              refine ⟨73647471464588384577720395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49098314309725589718480263 73647471464588384577720395)
              ·
                refine ⟨110471207196882576866580593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73647471464588384577720395 110471207196882576866580593)
                ·
                  refine ⟨82853405397661932649935445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110471207196882576866580593 82853405397661932649935445)
                  ·
                    refine ⟨970938344503850773241431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82853405397661932649935445 970938344503850773241431)
                    ·
                      rfl

theorem cell23_5672687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 8].length) (baseStart_5672687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672687 prefixEnd_5672687 := by exact prefixLift 5672687
  have htrace : WordTrace (prefixWord ++ tailWord_5672687) baseStart_5672687 baseEnd_5672687 := by
    simpa [prefixWord, tailWord_5672687, baseEnd_5672687] using wordTrace_append hprefix tailTrace_5672687
  have hstable : (prefixWord ++ tailWord_5672687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672687).length < 2 ^ (prefixWord ++ tailWord_5672687).sum := by decide
  have hdescent : baseEnd_5672687 < baseStart_5672687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672697 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 4, 3, 5]
def baseStart_5672697 : Nat := 118140960795 + 5672697 * 2 ^ 59
def prefixEnd_5672697 : Nat := 4983230072969 + 3 ^ 40 * 5672697 * 2
def baseEnd_5672697 : Nat := 2912820168318097280599247

theorem tailTrace_5672697 : CollatzResearch.WordTrace tailWord_5672697 prefixEnd_5672697 2912820168318097280599247 := by
  unfold tailWord_5672697
  simp only [CollatzResearch.WordTrace]
  refine ⟨206900257129795063361048345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137933504753196708907365563 206900257129795063361048345)
  ·
    refine ⟨155175192847346297520786259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206900257129795063361048345 155175192847346297520786259)
    ·
      refine ⟨232762789271019446281179389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155175192847346297520786259 232762789271019446281179389)
      ·
        refine ⟨87286045976632292355442271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232762789271019446281179389 87286045976632292355442271)
        ·
          refine ⟨130929068964948438533163407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87286045976632292355442271 130929068964948438533163407)
          ·
            refine ⟨196393603447422657799745111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130929068964948438533163407 196393603447422657799745111)
            ·
              refine ⟨294590405171133986699617667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196393603447422657799745111 294590405171133986699617667)
              ·
                refine ⟨441885607756700980049426501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294590405171133986699617667 441885607756700980049426501)
                ·
                  refine ⟨82853551454381433759267469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441885607756700980049426501 82853551454381433759267469)
                  ·
                    refine ⟨31070081795393037659725301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82853551454381433759267469 31070081795393037659725301)
                    ·
                      refine ⟨2912820168318097280599247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31070081795393037659725301 2912820168318097280599247)
                      ·
                        rfl

theorem cell23_5672697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_5672697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672697 prefixEnd_5672697 := by exact prefixLift 5672697
  have htrace : WordTrace (prefixWord ++ tailWord_5672697) baseStart_5672697 baseEnd_5672697 := by
    simpa [prefixWord, tailWord_5672697, baseEnd_5672697] using wordTrace_append hprefix tailTrace_5672697
  have hstable : (prefixWord ++ tailWord_5672697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672697).length < 2 ^ (prefixWord ++ tailWord_5672697).sum := by decide
  have hdescent : baseEnd_5672697 < baseStart_5672697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672707 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 6]
def baseStart_5672707 : Nat := 118140960795 + 5672707 * 2 ^ 59
def prefixEnd_5672707 : Nat := 4983230072969 + 3 ^ 40 * 5672707 * 2
def baseEnd_5672707 : Nat := 2912825303124642241474201

theorem tailTrace_5672707 : CollatzResearch.WordTrace tailWord_5672707 prefixEnd_5672707 2912825303124642241474201 := by
  unfold tailWord_5672707
  simp only [CollatzResearch.WordTrace]
  refine ⟨206900621859758835068912375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137933747906505890045941583 206900621859758835068912375)
  ·
    refine ⟨310350932789638252603368563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206900621859758835068912375 310350932789638252603368563)
    ·
      refine ⟨465526399184457378905052845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310350932789638252603368563 465526399184457378905052845)
      ·
        refine ⟨174572399694171517089394817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 465526399184457378905052845 174572399694171517089394817)
        ·
          refine ⟨130929299770628637817046113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174572399694171517089394817 130929299770628637817046113)
          ·
            refine ⟨98196974827971478362784585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130929299770628637817046113 98196974827971478362784585)
            ·
              refine ⟨73647731120978608772088439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98196974827971478362784585 73647731120978608772088439)
              ·
                refine ⟨110471596681467913158132659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73647731120978608772088439 110471596681467913158132659)
                ·
                  refine ⟨165707395022201869737198989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110471596681467913158132659 165707395022201869737198989)
                  ·
                    refine ⟨62140273133325701151449621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165707395022201869737198989 62140273133325701151449621)
                    ·
                      refine ⟨2912825303124642241474201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62140273133325701151449621 2912825303124642241474201)
                      ·
                        rfl

theorem cell23_5672707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_5672707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672707 prefixEnd_5672707 := by exact prefixLift 5672707
  have htrace : WordTrace (prefixWord ++ tailWord_5672707) baseStart_5672707 baseEnd_5672707 := by
    simpa [prefixWord, tailWord_5672707, baseEnd_5672707] using wordTrace_append hprefix tailTrace_5672707
  have hstable : (prefixWord ++ tailWord_5672707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672707).length < 2 ^ (prefixWord ++ tailWord_5672707).sum := by decide
  have hdescent : baseEnd_5672707 < baseStart_5672707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672801 : List Nat := [1, 2, 3, 1, 1, 1, 4, 4, 1, 1, 4]
def baseStart_5672801 : Nat := 118140960795 + 5672801 * 2 ^ 59
def prefixEnd_5672801 : Nat := 4983230072969 + 3 ^ 40 * 5672801 * 2
def baseEnd_5672801 : Nat := 2912873570306164873698769

theorem tailTrace_5672801 : CollatzResearch.WordTrace tailWord_5672801 prefixEnd_5672801 2912873570306164873698769 := by
  unfold tailWord_5672801
  simp only [CollatzResearch.WordTrace]
  refine ⟨206904050321418289122834257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137936033547612192748556171 206904050321418289122834257)
  ·
    refine ⟨155178037741063716842125693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206904050321418289122834257 155178037741063716842125693)
    ·
      refine ⟨58191764152898893815797135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155178037741063716842125693 58191764152898893815797135)
      ·
        refine ⟨87287646229348340723695703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58191764152898893815797135 87287646229348340723695703)
        ·
          refine ⟨130931469344022511085543555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87287646229348340723695703 130931469344022511085543555)
          ·
            refine ⟨196397204016033766628315333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130931469344022511085543555 196397204016033766628315333)
            ·
              refine ⟨36824475753006331242809125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196397204016033766628315333 36824475753006331242809125)
              ·
                refine ⟨6904589203688687108026711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36824475753006331242809125 6904589203688687108026711)
                ·
                  refine ⟨10356883805533030662040067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6904589203688687108026711 10356883805533030662040067)
                  ·
                    refine ⟨15535325708299545993060101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10356883805533030662040067 15535325708299545993060101)
                    ·
                      refine ⟨2912873570306164873698769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15535325708299545993060101 2912873570306164873698769)
                      ·
                        rfl

theorem cell23_5672801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_5672801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672801 prefixEnd_5672801 := by exact prefixLift 5672801
  have htrace : WordTrace (prefixWord ++ tailWord_5672801) baseStart_5672801 baseEnd_5672801 := by
    simpa [prefixWord, tailWord_5672801, baseEnd_5672801] using wordTrace_append hprefix tailTrace_5672801
  have hstable : (prefixWord ++ tailWord_5672801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672801).length < 2 ^ (prefixWord ++ tailWord_5672801).sum := by decide
  have hdescent : baseEnd_5672801 < baseStart_5672801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672818 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 7, 2, 2]
def baseStart_5672818 : Nat := 118140960795 + 5672818 * 2 ^ 59
def prefixEnd_5672818 : Nat := 4983230072969 + 3 ^ 40 * 5672818 * 2
def baseEnd_5672818 : Nat := 2912882299477291307186191

theorem tailTrace_5672818 : CollatzResearch.WordTrace tailWord_5672818 prefixEnd_5672818 2912882299477291307186191 := by
  unfold tailWord_5672818
  simp only [CollatzResearch.WordTrace]
  refine ⟨51726167590589175256550777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137936446908237800684135405 51726167590589175256550777)
  ·
    refine ⟨38794625692941881442413083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51726167590589175256550777 38794625692941881442413083)
    ·
      refine ⟨58191938539412822163619625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38794625692941881442413083 58191938539412822163619625)
      ·
        refine ⟨43643953904559616622714719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58191938539412822163619625 43643953904559616622714719)
        ·
          refine ⟨65465930856839424934072079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43643953904559616622714719 65465930856839424934072079)
          ·
            refine ⟨98198896285259137401108119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65465930856839424934072079 98198896285259137401108119)
            ·
              refine ⟨147298344427888706101662179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98198896285259137401108119 147298344427888706101662179)
              ·
                refine ⟨220947516641833059152493269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147298344427888706101662179 220947516641833059152493269)
                ·
                  refine ⟨5178457421292962323886561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 220947516641833059152493269 5178457421292962323886561)
                  ·
                    refine ⟨3883843065969721742914921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5178457421292962323886561 3883843065969721742914921)
                    ·
                      refine ⟨2912882299477291307186191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3883843065969721742914921 2912882299477291307186191)
                      ·
                        rfl

theorem cell23_5672818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_5672818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672818 prefixEnd_5672818 := by exact prefixLift 5672818
  have htrace : WordTrace (prefixWord ++ tailWord_5672818) baseStart_5672818 baseEnd_5672818 := by
    simpa [prefixWord, tailWord_5672818, baseEnd_5672818] using wordTrace_append hprefix tailTrace_5672818
  have hstable : (prefixWord ++ tailWord_5672818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672818).length < 2 ^ (prefixWord ++ tailWord_5672818).sum := by decide
  have hdescent : baseEnd_5672818 < baseStart_5672818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672821 : List Nat := [1, 3, 4, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_5672821 : Nat := 118140960795 + 5672821 * 2 ^ 59
def prefixEnd_5672821 : Nat := 4983230072969 + 3 ^ 40 * 5672821 * 2
def baseEnd_5672821 : Nat := 2912883839919254795448677

theorem tailTrace_5672821 : CollatzResearch.WordTrace tailWord_5672821 prefixEnd_5672821 2912883839919254795448677 := by
  unfold tailWord_5672821
  simp only [CollatzResearch.WordTrace]
  refine ⟨206904779781345832538562317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137936519854230555025708211 206904779781345832538562317)
  ·
    refine ⟨77589292418004687201960869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206904779781345832538562317 77589292418004687201960869)
    ·
      refine ⟨14547992328375878850367663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77589292418004687201960869 14547992328375878850367663)
      ·
        refine ⟨21821988492563818275551495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14547992328375878850367663 21821988492563818275551495)
        ·
          refine ⟨32732982738845727413327243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21821988492563818275551495 32732982738845727413327243)
          ·
            refine ⟨49099474108268591119990865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32732982738845727413327243 49099474108268591119990865)
            ·
              refine ⟨36824605581201443339993149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49099474108268591119990865 36824605581201443339993149)
              ·
                refine ⟨13809227092950541252497431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36824605581201443339993149 13809227092950541252497431)
                ·
                  refine ⟨20713840639425811878746147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13809227092950541252497431 20713840639425811878746147)
                  ·
                    refine ⟨31070760959138717818119221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20713840639425811878746147 31070760959138717818119221)
                    ·
                      refine ⟨2912883839919254795448677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31070760959138717818119221 2912883839919254795448677)
                      ·
                        rfl

theorem cell23_5672821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_5672821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672821 prefixEnd_5672821 := by exact prefixLift 5672821
  have htrace : WordTrace (prefixWord ++ tailWord_5672821) baseStart_5672821 baseEnd_5672821 := by
    simpa [prefixWord, tailWord_5672821, baseEnd_5672821] using wordTrace_append hprefix tailTrace_5672821
  have hstable : (prefixWord ++ tailWord_5672821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672821).length < 2 ^ (prefixWord ++ tailWord_5672821).sum := by decide
  have hdescent : baseEnd_5672821 < baseStart_5672821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672835 : List Nat := [1, 1, 1, 3, 4, 3, 2, 1, 3, 2, 2]
def baseStart_5672835 : Nat := 118140960795 + 5672835 * 2 ^ 59
def prefixEnd_5672835 : Nat := 4983230072969 + 3 ^ 40 * 5672835 * 2
def baseEnd_5672835 : Nat := 2912891028648417740673613

theorem tailTrace_5672835 : CollatzResearch.WordTrace tailWord_5672835 prefixEnd_5672835 2912891028648417740673613 := by
  unfold tailWord_5672835
  simp only [CollatzResearch.WordTrace]
  refine ⟨206905290403295112929571959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137936860268863408619714639 206905290403295112929571959)
  ·
    refine ⟨310357935604942669394357939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206905290403295112929571959 310357935604942669394357939)
    ·
      refine ⟨465536903407414004091536909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310357935604942669394357939 465536903407414004091536909)
      ·
        refine ⟨174576338777780251534326341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 465536903407414004091536909 174576338777780251534326341)
        ·
          refine ⟨32733063520833797162686189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174576338777780251534326341 32733063520833797162686189)
          ·
            refine ⟨12274898820312673936007321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32733063520833797162686189 12274898820312673936007321)
            ·
              refine ⟨9206174115234505452005491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12274898820312673936007321 9206174115234505452005491)
              ·
                refine ⟨13809261172851758178008237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9206174115234505452005491 13809261172851758178008237)
                ·
                  refine ⟨5178472939819409316753089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13809261172851758178008237 5178472939819409316753089)
                  ·
                    refine ⟨3883854704864556987564817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5178472939819409316753089 3883854704864556987564817)
                    ·
                      refine ⟨2912891028648417740673613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3883854704864556987564817 2912891028648417740673613)
                      ·
                        rfl

theorem cell23_5672835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 2, 2].length) (baseStart_5672835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672835 prefixEnd_5672835 := by exact prefixLift 5672835
  have htrace : WordTrace (prefixWord ++ tailWord_5672835) baseStart_5672835 baseEnd_5672835 := by
    simpa [prefixWord, tailWord_5672835, baseEnd_5672835] using wordTrace_append hprefix tailTrace_5672835
  have hstable : (prefixWord ++ tailWord_5672835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672835).length < 2 ^ (prefixWord ++ tailWord_5672835).sum := by decide
  have hdescent : baseEnd_5672835 < baseStart_5672835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672858 : List Nat := [3, 1, 1, 4, 2, 3, 2, 7]
def baseStart_5672858 : Nat := 118140960795 + 5672858 * 2 ^ 59
def prefixEnd_5672858 : Nat := 4983230072969 + 3 ^ 40 * 5672858 * 2
def baseEnd_5672858 : Nat := 107885290322350783358741

theorem tailTrace_5672858 : CollatzResearch.WordTrace tailWord_5672858 prefixEnd_5672858 107885290322350783358741 := by
  unfold tailWord_5672858
  simp only [CollatzResearch.WordTrace]
  refine ⟨51726532320552946964414807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137937419521474525238439485 51726532320552946964414807)
  ·
    refine ⟨77589798480829420446622211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51726532320552946964414807 77589798480829420446622211)
    ·
      refine ⟨116384697721244130669933317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77589798480829420446622211 116384697721244130669933317)
      ·
        refine ⟨21822130822733274500612497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116384697721244130669933317 21822130822733274500612497)
        ·
          refine ⟨16366598117049955875459373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21822130822733274500612497 16366598117049955875459373)
          ·
            refine ⟨6137474293893733453297265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16366598117049955875459373 6137474293893733453297265)
            ·
              refine ⟨4603105720420300089972949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6137474293893733453297265 4603105720420300089972949)
              ·
                refine ⟨107885290322350783358741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4603105720420300089972949 107885290322350783358741)
                ·
                  rfl

theorem cell23_5672858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 7].length) (baseStart_5672858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672858 prefixEnd_5672858 := by exact prefixLift 5672858
  have htrace : WordTrace (prefixWord ++ tailWord_5672858) baseStart_5672858 baseEnd_5672858 := by
    simpa [prefixWord, tailWord_5672858, baseEnd_5672858] using wordTrace_append hprefix tailTrace_5672858
  have hstable : (prefixWord ++ tailWord_5672858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672858).length < 2 ^ (prefixWord ++ tailWord_5672858).sum := by decide
  have hdescent : baseEnd_5672858 < baseStart_5672858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672868 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 4, 1, 3]
def baseStart_5672868 : Nat := 118140960795 + 5672868 * 2 ^ 59
def prefixEnd_5672868 : Nat := 4983230072969 + 3 ^ 40 * 5672868 * 2
def baseEnd_5672868 : Nat := 2912907973510016111560961

theorem tailTrace_5672868 : CollatzResearch.WordTrace tailWord_5672868 prefixEnd_5672868 2912907973510016111560961 := by
  unfold tailWord_5672868
  simp only [CollatzResearch.WordTrace]
  refine ⟨103453247006087779782761629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137937662674783706377015505 103453247006087779782761629)
  ·
    refine ⟨38794967627282917418535611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103453247006087779782761629 38794967627282917418535611)
    ·
      refine ⟨58192451440924376127803417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38794967627282917418535611 58192451440924376127803417)
      ·
        refine ⟨43644338580693282095852563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58192451440924376127803417 43644338580693282095852563)
        ·
          refine ⟨65466507871039923143778845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43644338580693282095852563 65466507871039923143778845)
          ·
            refine ⟨24549940451639971178917067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65466507871039923143778845 24549940451639971178917067)
            ·
              refine ⟨36824910677459956768375601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24549940451639971178917067 36824910677459956768375601)
              ·
                refine ⟨27618683008094967576281701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36824910677459956768375601 27618683008094967576281701)
                ·
                  refine ⟨5178503064017806420552819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27618683008094967576281701 5178503064017806420552819)
                  ·
                    refine ⟨7767754596026709630829229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5178503064017806420552819 7767754596026709630829229)
                    ·
                      refine ⟨2912907973510016111560961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7767754596026709630829229 2912907973510016111560961)
                      ·
                        rfl

theorem cell23_5672868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_5672868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672868 prefixEnd_5672868 := by exact prefixLift 5672868
  have htrace : WordTrace (prefixWord ++ tailWord_5672868) baseStart_5672868 baseEnd_5672868 := by
    simpa [prefixWord, tailWord_5672868, baseEnd_5672868] using wordTrace_append hprefix tailTrace_5672868
  have hstable : (prefixWord ++ tailWord_5672868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672868).length < 2 ^ (prefixWord ++ tailWord_5672868).sum := by decide
  have hdescent : baseEnd_5672868 < baseStart_5672868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672942 : List Nat := [4, 1, 2, 1, 3, 1, 1, 4, 2, 2, 2]
def baseStart_5672942 : Nat := 118140960795 + 5672942 * 2 ^ 59
def prefixEnd_5672942 : Nat := 4983230072969 + 3 ^ 40 * 5672942 * 2
def baseEnd_5672942 : Nat := 2912945971078448822035621

theorem tailTrace_5672942 : CollatzResearch.WordTrace tailWord_5672942 prefixEnd_5672942 2912945971078448822035621 := by
  unfold tailWord_5672942
  simp only [CollatzResearch.WordTrace]
  refine ⟨25863649126738433775464635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137939462009271646802478053 25863649126738433775464635)
  ·
    refine ⟨38795473690107650663196953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25863649126738433775464635 38795473690107650663196953)
    ·
      refine ⟨29096605267580737997397715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38795473690107650663196953 29096605267580737997397715)
      ·
        refine ⟨43644907901371106996096573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29096605267580737997397715 43644907901371106996096573)
        ·
          refine ⟨16366840463014165123536215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43644907901371106996096573 16366840463014165123536215)
          ·
            refine ⟨24550260694521247685304323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16366840463014165123536215 24550260694521247685304323)
            ·
              refine ⟨36825391041781871527956485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24550260694521247685304323 36825391041781871527956485)
              ·
                refine ⟨6904760820334100911491841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36825391041781871527956485 6904760820334100911491841)
                ·
                  refine ⟨5178570615250575683618881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6904760820334100911491841 5178570615250575683618881)
                  ·
                    refine ⟨3883927961437931762714161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5178570615250575683618881 3883927961437931762714161)
                    ·
                      refine ⟨2912945971078448822035621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3883927961437931762714161 2912945971078448822035621)
                      ·
                        rfl

theorem cell23_5672942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_5672942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672942 prefixEnd_5672942 := by exact prefixLift 5672942
  have htrace : WordTrace (prefixWord ++ tailWord_5672942) baseStart_5672942 baseEnd_5672942 := by
    simpa [prefixWord, tailWord_5672942, baseEnd_5672942] using wordTrace_append hprefix tailTrace_5672942
  have hstable : (prefixWord ++ tailWord_5672942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672942).length < 2 ^ (prefixWord ++ tailWord_5672942).sum := by decide
  have hdescent : baseEnd_5672942 < baseStart_5672942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672961 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 1, 7]
def baseStart_5672961 : Nat := 118140960795 + 5672961 * 2 ^ 59
def prefixEnd_5672961 : Nat := 4983230072969 + 3 ^ 40 * 5672961 * 2
def baseEnd_5672961 : Nat := 970985242403628082566011

theorem tailTrace_5672961 : CollatzResearch.WordTrace tailWord_5672961 prefixEnd_5672961 970985242403628082566011 := by
  unfold tailWord_5672961
  simp only [CollatzResearch.WordTrace]
  refine ⟨206909886000838636448658737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137939924000559090965772491 206909886000838636448658737)
  ·
    refine ⟨155182414500628977336494053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206909886000838636448658737 155182414500628977336494053)
    ·
      refine ⟨29096702718867933250592635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155182414500628977336494053 29096702718867933250592635)
      ·
        refine ⟨43645054078301899875888953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29096702718867933250592635 43645054078301899875888953)
        ·
          refine ⟨32733790558726424906916715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43645054078301899875888953 32733790558726424906916715)
          ·
            refine ⟨49100685838089637360375073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32733790558726424906916715 49100685838089637360375073)
            ·
              refine ⟨36825514378567228020281305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49100685838089637360375073 36825514378567228020281305)
              ·
                refine ⟨27619135783925421015210979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36825514378567228020281305 27619135783925421015210979)
                ·
                  refine ⟨41428703675888131522816469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27619135783925421015210979 41428703675888131522816469)
                  ·
                    refine ⟨970985242403628082566011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41428703675888131522816469 970985242403628082566011)
                    ·
                      rfl

theorem cell23_5672961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_5672961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672961 prefixEnd_5672961 := by exact prefixLift 5672961
  have htrace : WordTrace (prefixWord ++ tailWord_5672961) baseStart_5672961 baseEnd_5672961 := by
    simpa [prefixWord, tailWord_5672961, baseEnd_5672961] using wordTrace_append hprefix tailTrace_5672961
  have hstable : (prefixWord ++ tailWord_5672961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672961).length < 2 ^ (prefixWord ++ tailWord_5672961).sum := by decide
  have hdescent : baseEnd_5672961 < baseStart_5672961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672968 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 2, 5, 2]
def baseStart_5672968 : Nat := 118140960795 + 5672968 * 2 ^ 59
def prefixEnd_5672968 : Nat := 4983230072969 + 3 ^ 40 * 5672968 * 2
def baseEnd_5672968 : Nat := 2912959321575465720310501

theorem tailTrace_5672968 : CollatzResearch.WordTrace tailWord_5672968 prefixEnd_5672968 2912959321575465720310501 := by
  unfold tailWord_5672968
  simp only [CollatzResearch.WordTrace]
  refine ⟨103455070655906638322081779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137940094207875517762775705 103455070655906638322081779)
  ·
    refine ⟨155182605983859957483122669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103455070655906638322081779 155182605983859957483122669)
    ·
      refine ⟨58193477243947484056171001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155182605983859957483122669 58193477243947484056171001)
      ·
        refine ⟨43645107932960613042128251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58193477243947484056171001 43645107932960613042128251)
        ·
          refine ⟨65467661899440919563192377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43645107932960613042128251 65467661899440919563192377)
          ·
            refine ⟨49100746424580689672394283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65467661899440919563192377 49100746424580689672394283)
            ·
              refine ⟨73651119636871034508591425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49100746424580689672394283 73651119636871034508591425)
              ·
                refine ⟨55238339727653275881443569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73651119636871034508591425 55238339727653275881443569)
                ·
                  refine ⟨41428754795739956911082677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55238339727653275881443569 41428754795739956911082677)
                  ·
                    refine ⟨3883945762100620960414001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41428754795739956911082677 3883945762100620960414001)
                    ·
                      refine ⟨2912959321575465720310501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3883945762100620960414001 2912959321575465720310501)
                      ·
                        rfl

theorem cell23_5672968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_5672968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672968 prefixEnd_5672968 := by exact prefixLift 5672968
  have htrace : WordTrace (prefixWord ++ tailWord_5672968) baseStart_5672968 baseEnd_5672968 := by
    simpa [prefixWord, tailWord_5672968, baseEnd_5672968] using wordTrace_append hprefix tailTrace_5672968
  have hstable : (prefixWord ++ tailWord_5672968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672968).length < 2 ^ (prefixWord ++ tailWord_5672968).sum := by decide
  have hdescent : baseEnd_5672968 < baseStart_5672968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673008 : List Nat := [2, 1, 1, 1, 2, 5, 1, 3, 3, 4]
def baseStart_5673008 : Nat := 118140960795 + 5673008 * 2 ^ 59
def prefixEnd_5673008 : Nat := 4983230072969 + 3 ^ 40 * 5673008 * 2
def baseEnd_5673008 : Nat := 970993286933881854603439

theorem tailTrace_5673008 : CollatzResearch.WordTrace tailWord_5673008 prefixEnd_5673008 970993286933881854603439 := by
  unfold tailWord_5673008
  simp only [CollatzResearch.WordTrace]
  refine ⟨103455800115834181737809839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137941066821112242317079785 103455800115834181737809839)
  ·
    refine ⟨155183700173751272606714759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103455800115834181737809839 155183700173751272606714759)
    ·
      refine ⟨232775550260626908910072139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155183700173751272606714759 232775550260626908910072139)
      ·
        refine ⟨349163325390940363365108209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232775550260626908910072139 349163325390940363365108209)
        ·
          refine ⟨261872494043205272523831157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349163325390940363365108209 261872494043205272523831157)
          ·
            refine ⟨24550546316550494299109171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 261872494043205272523831157 24550546316550494299109171)
            ·
              refine ⟨36825819474825741448663757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24550546316550494299109171 36825819474825741448663757)
              ·
                refine ⟨13809682303059653043248909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36825819474825741448663757 13809682303059653043248909)
                ·
                  refine ⟨5178630863647369891218341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13809682303059653043248909 5178630863647369891218341)
                  ·
                    refine ⟨970993286933881854603439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5178630863647369891218341 970993286933881854603439)
                    ·
                      rfl

theorem cell23_5673008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 3, 4].length) (baseStart_5673008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673008 prefixEnd_5673008 := by exact prefixLift 5673008
  have htrace : WordTrace (prefixWord ++ tailWord_5673008) baseStart_5673008 baseEnd_5673008 := by
    simpa [prefixWord, tailWord_5673008, baseEnd_5673008] using wordTrace_append hprefix tailTrace_5673008
  have hstable : (prefixWord ++ tailWord_5673008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673008).length < 2 ^ (prefixWord ++ tailWord_5673008).sum := by decide
  have hdescent : baseEnd_5673008 < baseStart_5673008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673025 : List Nat := [1, 2, 5, 1, 2, 1, 2, 2, 3, 4]
def baseStart_5673025 : Nat := 118140960795 + 5673025 * 2 ^ 59
def prefixEnd_5673025 : Nat := 4983230072969 + 3 ^ 40 * 5673025 * 2
def baseEnd_5673025 : Nat := 970996196657590665765913

theorem tailTrace_5673025 : CollatzResearch.WordTrace tailWord_5673025 prefixEnd_5673025 970996196657590665765913 := by
  unfold tailWord_5673025
  simp only [CollatzResearch.WordTrace]
  refine ⟨206912220272606775378988529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137941480181737850252659019 206912220272606775378988529)
  ·
    refine ⟨155184165204455081534241397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206912220272606775378988529 155184165204455081534241397)
    ·
      refine ⟨14548515487917663893835131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155184165204455081534241397 14548515487917663893835131)
      ·
        refine ⟨21822773231876495840752697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14548515487917663893835131 21822773231876495840752697)
        ·
          refine ⟨16367079923907371880564523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21822773231876495840752697 16367079923907371880564523)
          ·
            refine ⟨24550619885861057820846785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16367079923907371880564523 24550619885861057820846785)
            ·
              refine ⟨18412964914395793365635089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24550619885861057820846785 18412964914395793365635089)
              ·
                refine ⟨13809723685796845024226317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18412964914395793365635089 13809723685796845024226317)
                ·
                  refine ⟨5178646382173816884084869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13809723685796845024226317 5178646382173816884084869)
                  ·
                    refine ⟨970996196657590665765913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5178646382173816884084869 970996196657590665765913)
                    ·
                      rfl

theorem cell23_5673025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_5673025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673025 prefixEnd_5673025 := by exact prefixLift 5673025
  have htrace : WordTrace (prefixWord ++ tailWord_5673025) baseStart_5673025 baseEnd_5673025 := by
    simpa [prefixWord, tailWord_5673025, baseEnd_5673025] using wordTrace_append hprefix tailTrace_5673025
  have hstable : (prefixWord ++ tailWord_5673025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673025).length < 2 ^ (prefixWord ++ tailWord_5673025).sum := by decide
  have hdescent : baseEnd_5673025 < baseStart_5673025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673085 : List Nat := [1, 4, 1, 1, 3, 2, 3, 2, 1, 5]
def baseStart_5673085 : Nat := 118140960795 + 5673085 * 2 ^ 59
def prefixEnd_5673085 : Nat := 4983230072969 + 3 ^ 40 * 5673085 * 2
def baseEnd_5673085 : Nat := 971006466270680587515821

theorem tailTrace_5673085 : CollatzResearch.WordTrace tailWord_5673085 prefixEnd_5673085 971006466270680587515821 := by
  unfold tailWord_5673085
  simp only [CollatzResearch.WordTrace]
  refine ⟨206914408652389405626172709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137942939101592937084115139 206914408652389405626172709)
  ·
    refine ⟨38796451622323013554907383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206914408652389405626172709 38796451622323013554907383)
    ·
      refine ⟨58194677433484520332361075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38796451622323013554907383 58194677433484520332361075)
      ·
        refine ⟨87292016150226780498541613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58194677433484520332361075 87292016150226780498541613)
        ·
          refine ⟨32734506056335042686953105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87292016150226780498541613 32734506056335042686953105)
          ·
            refine ⟨24550879542251282015214829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32734506056335042686953105 24550879542251282015214829)
            ·
              refine ⟨9206579828344230755705561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24550879542251282015214829 9206579828344230755705561)
              ·
                refine ⟨6904934871258173066779171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9206579828344230755705561 6904934871258173066779171)
                ·
                  refine ⟨10357402306887259600168757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6904934871258173066779171 10357402306887259600168757)
                  ·
                    refine ⟨971006466270680587515821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10357402306887259600168757 971006466270680587515821)
                    ·
                      rfl

theorem cell23_5673085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_5673085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673085 prefixEnd_5673085 := by exact prefixLift 5673085
  have htrace : WordTrace (prefixWord ++ tailWord_5673085) baseStart_5673085 baseEnd_5673085 := by
    simpa [prefixWord, tailWord_5673085, baseEnd_5673085] using wordTrace_append hprefix tailTrace_5673085
  have hstable : (prefixWord ++ tailWord_5673085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673085).length < 2 ^ (prefixWord ++ tailWord_5673085).sum := by decide
  have hdescent : baseEnd_5673085 < baseStart_5673085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673092 : List Nat := [2, 3, 2, 1, 2, 1, 4, 1, 2, 3, 2]
def baseStart_5673092 : Nat := 118140960795 + 5673092 * 2 ^ 59
def prefixEnd_5673092 : Nat := 4983230072969 + 3 ^ 40 * 5673092 * 2
def baseEnd_5673092 : Nat := 2913022993176623235159931

theorem tailTrace_5673092 : CollatzResearch.WordTrace tailWord_5673092 prefixEnd_5673092 2913022993176623235159931 := by
  unfold tailWord_5673092
  simp only [CollatzResearch.WordTrace]
  refine ⟨103457331981682022910838765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137943109308909363881118353 103457331981682022910838765)
  ·
    refine ⟨38796499493130758591564537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103457331981682022910838765 38796499493130758591564537)
    ·
      refine ⟨29097374619848068943673403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38796499493130758591564537 29097374619848068943673403)
      ·
        refine ⟨43646061929772103415510105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29097374619848068943673403 43646061929772103415510105)
        ·
          refine ⟨32734546447329077561632579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43646061929772103415510105 32734546447329077561632579)
          ·
            refine ⟨49101819670993616342448869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32734546447329077561632579 49101819670993616342448869)
            ·
              refine ⟨9206591188311303064209163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49101819670993616342448869 9206591188311303064209163)
              ·
                refine ⟨13809886782466954596313745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9206591188311303064209163 13809886782466954596313745)
                ·
                  refine ⟨10357415086850215947235309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13809886782466954596313745 10357415086850215947235309)
                  ·
                    refine ⟨3884030657568830980213241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10357415086850215947235309 3884030657568830980213241)
                    ·
                      refine ⟨2913022993176623235159931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3884030657568830980213241 2913022993176623235159931)
                      ·
                        rfl

theorem cell23_5673092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_5673092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673092 prefixEnd_5673092 := by exact prefixLift 5673092
  have htrace : WordTrace (prefixWord ++ tailWord_5673092) baseStart_5673092 baseEnd_5673092 := by
    simpa [prefixWord, tailWord_5673092, baseEnd_5673092] using wordTrace_append hprefix tailTrace_5673092
  have hstable : (prefixWord ++ tailWord_5673092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673092).length < 2 ^ (prefixWord ++ tailWord_5673092).sum := by decide
  have hdescent : baseEnd_5673092 < baseStart_5673092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673098 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 3, 6]
def baseStart_5673098 : Nat := 118140960795 + 5673098 * 2 ^ 59
def prefixEnd_5673098 : Nat := 4983230072969 + 3 ^ 40 * 5673098 * 2
def baseEnd_5673098 : Nat := 971008691353516737228301

theorem tailTrace_5673098 : CollatzResearch.WordTrace tailWord_5673098 prefixEnd_5673098 971008691353516737228301 := by
  unfold tailWord_5673098
  simp only [CollatzResearch.WordTrace]
  refine ⟨51728720700335577211598987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137943255200894872564263965 51728720700335577211598987)
  ·
    refine ⟨77593081050503365817398481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51728720700335577211598987 77593081050503365817398481)
    ·
      refine ⟨58194810787877524363048861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77593081050503365817398481 58194810787877524363048861)
      ·
        refine ⟨21823054045454071636143323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58194810787877524363048861 21823054045454071636143323)
        ·
          refine ⟨32734581068181107454214985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21823054045454071636143323 32734581068181107454214985)
          ·
            refine ⟨24550935801135830590661239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32734581068181107454214985 24550935801135830590661239)
            ·
              refine ⟨36826403701703745885991859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24550935801135830590661239 36826403701703745885991859)
              ·
                refine ⟨55239605552555618828987789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36826403701703745885991859 55239605552555618828987789)
                ·
                  refine ⟨20714852082208357060870421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55239605552555618828987789 20714852082208357060870421)
                  ·
                    refine ⟨971008691353516737228301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20714852082208357060870421 971008691353516737228301)
                    ·
                      rfl

theorem cell23_5673098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_5673098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673098 prefixEnd_5673098 := by exact prefixLift 5673098
  have htrace : WordTrace (prefixWord ++ tailWord_5673098) baseStart_5673098 baseEnd_5673098 := by
    simpa [prefixWord, tailWord_5673098, baseEnd_5673098] using wordTrace_append hprefix tailTrace_5673098
  have hstable : (prefixWord ++ tailWord_5673098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673098).length < 2 ^ (prefixWord ++ tailWord_5673098).sum := by decide
  have hdescent : baseEnd_5673098 < baseStart_5673098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673110 : List Nat := [5, 3, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_5673110 : Nat := 118140960795 + 5673110 * 2 ^ 59
def prefixEnd_5673110 : Nat := 4983230072969 + 3 ^ 40 * 5673110 * 2
def baseEnd_5673110 : Nat := 971010745276134721578283

theorem tailTrace_5673110 : CollatzResearch.WordTrace tailWord_5673110 prefixEnd_5673110 971010745276134721578283 := by
  unfold tailWord_5673110
  simp only [CollatzResearch.WordTrace]
  refine ⟨12932207529831177180989549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137943546984865889930555189 12932207529831177180989549)
  ·
    refine ⟨4849577823686691442871081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12932207529831177180989549 4849577823686691442871081)
    ·
      refine ⟨3637183367765018582153311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4849577823686691442871081 3637183367765018582153311)
      ·
        refine ⟨5455775051647527873229967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3637183367765018582153311 5455775051647527873229967)
        ·
          refine ⟨8183662577471291809844951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5455775051647527873229967 8183662577471291809844951)
          ·
            refine ⟨12275493866206937714767427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8183662577471291809844951 12275493866206937714767427)
            ·
              refine ⟨18413240799310406572151141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12275493866206937714767427 18413240799310406572151141)
              ·
                refine ⟨3452482649870701232278339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18413240799310406572151141 3452482649870701232278339)
                ·
                  refine ⟨5178723974806051848417509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3452482649870701232278339 5178723974806051848417509)
                  ·
                    refine ⟨971010745276134721578283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5178723974806051848417509 971010745276134721578283)
                    ·
                      rfl

theorem cell23_5673110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_5673110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673110 prefixEnd_5673110 := by exact prefixLift 5673110
  have htrace : WordTrace (prefixWord ++ tailWord_5673110) baseStart_5673110 baseEnd_5673110 := by
    simpa [prefixWord, tailWord_5673110, baseEnd_5673110] using wordTrace_append hprefix tailTrace_5673110
  have hstable : (prefixWord ++ tailWord_5673110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673110).length < 2 ^ (prefixWord ++ tailWord_5673110).sum := by decide
  have hdescent : baseEnd_5673110 < baseStart_5673110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673111 : List Nat := [1, 1, 3, 3, 15]
def baseStart_5673111 : Nat := 118140960795 + 5673111 * 2 ^ 59
def prefixEnd_5673111 : Nat := 4983230072969 + 3 ^ 40 * 5673111 * 2
def baseEnd_5673111 : Nat := 3995929697268941921567

theorem tailTrace_5673111 : CollatzResearch.WordTrace tailWord_5673111 prefixEnd_5673111 3995929697268941921567 := by
  unfold tailWord_5673111
  simp only [CollatzResearch.WordTrace]
  refine ⟨206915356950295212066619187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137943571300196808044412791 206915356950295212066619187)
  ·
    refine ⟨310373035425442818099928781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206915356950295212066619187 310373035425442818099928781)
    ·
      refine ⟨116389888284541056787473293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310373035425442818099928781 116389888284541056787473293)
      ·
        refine ⟨43646208106702896295302485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116389888284541056787473293 43646208106702896295302485)
        ·
          refine ⟨3995929697268941921567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 43646208106702896295302485 3995929697268941921567)
          ·
            rfl

theorem cell23_5673111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 15].length) (baseStart_5673111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673111 prefixEnd_5673111 := by exact prefixLift 5673111
  have htrace : WordTrace (prefixWord ++ tailWord_5673111) baseStart_5673111 baseEnd_5673111 := by
    simpa [prefixWord, tailWord_5673111, baseEnd_5673111] using wordTrace_append hprefix tailTrace_5673111
  have hstable : (prefixWord ++ tailWord_5673111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673111).length < 2 ^ (prefixWord ++ tailWord_5673111).sum := by decide
  have hdescent : baseEnd_5673111 < baseStart_5673111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673156 : List Nat := [2, 3, 3, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_5673156 : Nat := 118140960795 + 5673156 * 2 ^ 59
def prefixEnd_5673156 : Nat := 4983230072969 + 3 ^ 40 * 5673156 * 2
def baseEnd_5673156 : Nat := 2913055855938510984759637

theorem tailTrace_5673156 : CollatzResearch.WordTrace tailWord_5673156 prefixEnd_5673156 2913055855938510984759637 := by
  unfold tailWord_5673156
  simp only [CollatzResearch.WordTrace]
  refine ⟨103458499117566092376003661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137944665490088123168004881 103458499117566092376003661)
  ·
    refine ⟨38796937169087284641001373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103458499117566092376003661 38796937169087284641001373)
    ·
      refine ⟨14548851438407731740375515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38796937169087284641001373 14548851438407731740375515)
      ·
        refine ⟨21823277157611597610563273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14548851438407731740375515 21823277157611597610563273)
        ·
          refine ⟨16367457868208698207922455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21823277157611597610563273 16367457868208698207922455)
          ·
            refine ⟨24551186802313047311883683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16367457868208698207922455 24551186802313047311883683)
            ·
              refine ⟨36826780203469570967825525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24551186802313047311883683 36826780203469570967825525)
              ·
                refine ⟨3452510644075272278233643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36826780203469570967825525 3452510644075272278233643)
                ·
                  refine ⟨5178765966112908417350465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3452510644075272278233643 5178765966112908417350465)
                  ·
                    refine ⟨3884074474584681313012849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5178765966112908417350465 3884074474584681313012849)
                    ·
                      refine ⟨2913055855938510984759637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3884074474584681313012849 2913055855938510984759637)
                      ·
                        rfl

theorem cell23_5673156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_5673156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673156 prefixEnd_5673156 := by exact prefixLift 5673156
  have htrace : WordTrace (prefixWord ++ tailWord_5673156) baseStart_5673156 baseEnd_5673156 := by
    simpa [prefixWord, tailWord_5673156, baseEnd_5673156] using wordTrace_append hprefix tailTrace_5673156
  have hstable : (prefixWord ++ tailWord_5673156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673156).length < 2 ^ (prefixWord ++ tailWord_5673156).sum := by decide
  have hdescent : baseEnd_5673156 < baseStart_5673156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673178 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4]
def baseStart_5673178 : Nat := 118140960795 + 5673178 * 2 ^ 59
def prefixEnd_5673178 : Nat := 4983230072969 + 3 ^ 40 * 5673178 * 2
def baseEnd_5673178 : Nat := 2913067152512909898684535

theorem tailTrace_5673178 : CollatzResearch.WordTrace tailWord_5673178 prefixEnd_5673178 2913067152512909898684535 := by
  unfold tailWord_5673178
  simp only [CollatzResearch.WordTrace]
  refine ⟨51729450160263120627327047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137945200427368321672872125 51729450160263120627327047)
  ·
    refine ⟨77594175240394680940990571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51729450160263120627327047 77594175240394680940990571)
    ·
      refine ⟨116391262860592021411485857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77594175240394680940990571 116391262860592021411485857)
      ·
        refine ⟨87293447145444016058614393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116391262860592021411485857 87293447145444016058614393)
        ·
          refine ⟨65470085359083012043960795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87293447145444016058614393 65470085359083012043960795)
          ·
            refine ⟨98205128038624518065941193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65470085359083012043960795 98205128038624518065941193)
            ·
              refine ⟨73653846028968388549455895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98205128038624518065941193 73653846028968388549455895)
              ·
                refine ⟨110480769043452582824183843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73653846028968388549455895 110480769043452582824183843)
                ·
                  refine ⟨165721153565178874236275765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110480769043452582824183843 165721153565178874236275765)
                  ·
                    refine ⟨15536358146735519459650853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 165721153565178874236275765 15536358146735519459650853)
                    ·
                      refine ⟨2913067152512909898684535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15536358146735519459650853 2913067152512909898684535)
                      ·
                        rfl

theorem cell23_5673178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_5673178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673178 prefixEnd_5673178 := by exact prefixLift 5673178
  have htrace : WordTrace (prefixWord ++ tailWord_5673178) baseStart_5673178 baseEnd_5673178 := by
    simpa [prefixWord, tailWord_5673178, baseEnd_5673178] using wordTrace_append hprefix tailTrace_5673178
  have hstable : (prefixWord ++ tailWord_5673178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673178).length < 2 ^ (prefixWord ++ tailWord_5673178).sum := by decide
  have hdescent : baseEnd_5673178 < baseStart_5673178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673199 : List Nat := [1, 1, 2, 1, 6, 2, 2, 2, 1, 3, 2]
def baseStart_5673199 : Nat := 118140960795 + 5673199 * 2 ^ 59
def prefixEnd_5673199 : Nat := 4983230072969 + 3 ^ 40 * 5673199 * 2
def baseEnd_5673199 : Nat := 2913077935606654316521939

theorem tailTrace_5673199 : CollatzResearch.WordTrace tailWord_5673199 prefixEnd_5673199 2913077935606654316521939 := by
  unfold tailWord_5673199
  simp only [CollatzResearch.WordTrace]
  refine ⟨206918566573976403095822651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137945711049317602063881767 206918566573976403095822651)
  ·
    refine ⟨310377849860964604643733977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206918566573976403095822651 310377849860964604643733977)
    ·
      refine ⟨232783387395723453482800483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310377849860964604643733977 232783387395723453482800483)
      ·
        refine ⟨349175081093585180224200725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232783387395723453482800483 349175081093585180224200725)
        ·
          refine ⟨16367581926261805323009409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 349175081093585180224200725 16367581926261805323009409)
          ·
            refine ⟨12275686444696353992257057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16367581926261805323009409 12275686444696353992257057)
            ·
              refine ⟨9206764833522265494192793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12275686444696353992257057 9206764833522265494192793)
              ·
                refine ⟨6905073625141699120644595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9206764833522265494192793 6905073625141699120644595)
                ·
                  refine ⟨10357610437712548680966893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6905073625141699120644595 10357610437712548680966893)
                  ·
                    refine ⟨3884103914142205755362585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10357610437712548680966893 3884103914142205755362585)
                    ·
                      refine ⟨2913077935606654316521939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3884103914142205755362585 2913077935606654316521939)
                      ·
                        rfl

theorem cell23_5673199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 3, 2].length) (baseStart_5673199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673199 prefixEnd_5673199 := by exact prefixLift 5673199
  have htrace : WordTrace (prefixWord ++ tailWord_5673199) baseStart_5673199 baseEnd_5673199 := by
    simpa [prefixWord, tailWord_5673199, baseEnd_5673199] using wordTrace_append hprefix tailTrace_5673199
  have hstable : (prefixWord ++ tailWord_5673199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673199).length < 2 ^ (prefixWord ++ tailWord_5673199).sum := by decide
  have hdescent : baseEnd_5673199 < baseStart_5673199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673208 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 1, 4, 4]
def baseStart_5673208 : Nat := 118140960795 + 5673208 * 2 ^ 59
def prefixEnd_5673208 : Nat := 4983230072969 + 3 ^ 40 * 5673208 * 2
def baseEnd_5673208 : Nat := 2913082556932544781309397

theorem tailTrace_5673208 : CollatzResearch.WordTrace tailWord_5673208 prefixEnd_5673208 2913082556932544781309397 := by
  unfold tailWord_5673208
  simp only [CollatzResearch.WordTrace]
  refine ⟨103459447415471898816450139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137945929887295865088600185 103459447415471898816450139)
  ·
    refine ⟨155189171123207848224675209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103459447415471898816450139 155189171123207848224675209)
    ·
      refine ⟨116391878342405886168506407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155189171123207848224675209 116391878342405886168506407)
      ·
        refine ⟨174587817513608829252759611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116391878342405886168506407 174587817513608829252759611)
        ·
          refine ⟨261881726270413243879139417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174587817513608829252759611 261881726270413243879139417)
          ·
            refine ⟨196411294702809932909354563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261881726270413243879139417 196411294702809932909354563)
            ·
              refine ⟨294616942054214899364031845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196411294702809932909354563 294616942054214899364031845)
              ·
                refine ⟨55240676635165293630755971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 294616942054214899364031845 55240676635165293630755971)
                ·
                  refine ⟨82861014952747940446133957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55240676635165293630755971 82861014952747940446133957)
                  ·
                    refine ⟨15536440303640238833650117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82861014952747940446133957 15536440303640238833650117)
                    ·
                      refine ⟨2913082556932544781309397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15536440303640238833650117 2913082556932544781309397)
                      ·
                        rfl

theorem cell23_5673208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_5673208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673208 prefixEnd_5673208 := by exact prefixLift 5673208
  have htrace : WordTrace (prefixWord ++ tailWord_5673208) baseStart_5673208 baseEnd_5673208 := by
    simpa [prefixWord, tailWord_5673208, baseEnd_5673208] using wordTrace_append hprefix tailTrace_5673208
  have hstable : (prefixWord ++ tailWord_5673208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673208).length < 2 ^ (prefixWord ++ tailWord_5673208).sum := by decide
  have hdescent : baseEnd_5673208 < baseStart_5673208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673228 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 1, 2, 7]
def baseStart_5673228 : Nat := 118140960795 + 5673228 * 2 ^ 59
def prefixEnd_5673228 : Nat := 4983230072969 + 3 ^ 40 * 5673228 * 2
def baseEnd_5673228 : Nat := 2913092826545634703059305

theorem tailTrace_5673228 : CollatzResearch.WordTrace tailWord_5673228 prefixEnd_5673228 2913092826545634703059305 := by
  unfold tailWord_5673228
  simp only [CollatzResearch.WordTrace]
  refine ⟨103459812145435670524314169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137946416193914227365752225 103459812145435670524314169)
  ·
    refine ⟨77594859109076752893235627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103459812145435670524314169 77594859109076752893235627)
    ·
      refine ⟨116392288663615129339853441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77594859109076752893235627 116392288663615129339853441)
      ·
        refine ⟨87294216497711347004890081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116392288663615129339853441 87294216497711347004890081)
        ·
          refine ⟨65470662373283510253667561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87294216497711347004890081 65470662373283510253667561)
          ·
            refine ⟨49102996779962632690250671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65470662373283510253667561 49102996779962632690250671)
            ·
              refine ⟨73654495169943949035376007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49102996779962632690250671 73654495169943949035376007)
              ·
                refine ⟨110481742754915923553064011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73654495169943949035376007 110481742754915923553064011)
                ·
                  refine ⟨165722614132373885329596017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110481742754915923553064011 165722614132373885329596017)
                  ·
                    refine ⟨124291960599280413997197013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 165722614132373885329596017 124291960599280413997197013)
                    ·
                      refine ⟨2913092826545634703059305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124291960599280413997197013 2913092826545634703059305)
                      ·
                        rfl

theorem cell23_5673228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_5673228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673228 prefixEnd_5673228 := by exact prefixLift 5673228
  have htrace : WordTrace (prefixWord ++ tailWord_5673228) baseStart_5673228 baseEnd_5673228 := by
    simpa [prefixWord, tailWord_5673228, baseEnd_5673228] using wordTrace_append hprefix tailTrace_5673228
  have hstable : (prefixWord ++ tailWord_5673228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673228).length < 2 ^ (prefixWord ++ tailWord_5673228).sum := by decide
  have hdescent : baseEnd_5673228 < baseStart_5673228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673235 : List Nat := [1, 1, 1, 2, 1, 3, 1, 8, 5]
def baseStart_5673235 : Nat := 118140960795 + 5673235 * 2 ^ 59
def prefixEnd_5673235 : Nat := 4983230072969 + 3 ^ 40 * 5673235 * 2
def baseEnd_5673235 : Nat := 323677380101135130630197

theorem tailTrace_5673235 : CollatzResearch.WordTrace tailWord_5673235 prefixEnd_5673235 323677380101135130630197 := by
  unfold tailWord_5673235
  simp only [CollatzResearch.WordTrace]
  refine ⟨206919879601845981244133159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137946586401230654162755439 206919879601845981244133159)
  ·
    refine ⟨310379819402768971866199739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206919879601845981244133159 310379819402768971866199739)
    ·
      refine ⟨465569729104153457799299609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310379819402768971866199739 465569729104153457799299609)
      ·
        refine ⟨349177296828115093349474707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 465569729104153457799299609 349177296828115093349474707)
        ·
          refine ⟨523765945242172640024212061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349177296828115093349474707 523765945242172640024212061)
          ·
            refine ⟨196412229465814740009079523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 523765945242172640024212061 196412229465814740009079523)
            ·
              refine ⟨294618344198722110013619285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196412229465814740009079523 294618344198722110013619285)
              ·
                refine ⟨3452558721078774726722101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 294618344198722110013619285 3452558721078774726722101)
                ·
                  refine ⟨323677380101135130630197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3452558721078774726722101 323677380101135130630197)
                  ·
                    rfl

theorem cell23_5673235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 5].length) (baseStart_5673235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673235 prefixEnd_5673235 := by exact prefixLift 5673235
  have htrace : WordTrace (prefixWord ++ tailWord_5673235) baseStart_5673235 baseEnd_5673235 := by
    simpa [prefixWord, tailWord_5673235, baseEnd_5673235] using wordTrace_append hprefix tailTrace_5673235
  have hstable : (prefixWord ++ tailWord_5673235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673235).length < 2 ^ (prefixWord ++ tailWord_5673235).sum := by decide
  have hdescent : baseEnd_5673235 < baseStart_5673235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673305 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 1, 4, 3]
def baseStart_5673305 : Nat := 118140960795 + 5673305 * 2 ^ 59
def prefixEnd_5673305 : Nat := 4983230072969 + 3 ^ 40 * 5673305 * 2
def baseEnd_5673305 : Nat := 2913132364556030901796451

theorem tailTrace_5673305 : CollatzResearch.WordTrace tailWord_5673305 prefixEnd_5673305 2913132364556030901796451 := by
  unfold tailWord_5673305
  simp only [CollatzResearch.WordTrace]
  refine ⟨206922432711592383199181369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137948288474394922132787579 206922432711592383199181369)
  ·
    refine ⟨155191824533694287399386027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206922432711592383199181369 155191824533694287399386027)
    ·
      refine ⟨232787736800541431099079041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155191824533694287399386027 232787736800541431099079041)
      ·
        refine ⟨174590802600406073324309281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232787736800541431099079041 174590802600406073324309281)
        ·
          refine ⟨130943101950304554993231961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174590802600406073324309281 130943101950304554993231961)
          ·
            refine ⟨98207326462728416244923971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130943101950304554993231961 98207326462728416244923971)
            ·
              refine ⟨147310989694092624367385957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98207326462728416244923971 147310989694092624367385957)
              ·
                refine ⟨27620810567642367068884867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147310989694092624367385957 27620810567642367068884867)
                ·
                  refine ⟨41431215851463550603327301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27620810567642367068884867 41431215851463550603327301)
                  ·
                    refine ⟨7768352972149415738123869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41431215851463550603327301 7768352972149415738123869)
                    ·
                      refine ⟨2913132364556030901796451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7768352972149415738123869 2913132364556030901796451)
                      ·
                        rfl

theorem cell23_5673305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_5673305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673305 prefixEnd_5673305 := by exact prefixLift 5673305
  have htrace : WordTrace (prefixWord ++ tailWord_5673305) baseStart_5673305 baseEnd_5673305 := by
    simpa [prefixWord, tailWord_5673305, baseEnd_5673305] using wordTrace_append hprefix tailTrace_5673305
  have hstable : (prefixWord ++ tailWord_5673305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673305).length < 2 ^ (prefixWord ++ tailWord_5673305).sum := by decide
  have hdescent : baseEnd_5673305 < baseStart_5673305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673319 : List Nat := [1, 1, 5, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_5673319 : Nat := 118140960795 + 5673319 * 2 ^ 59
def prefixEnd_5673319 : Nat := 4983230072969 + 3 ^ 40 * 5673319 * 2
def baseEnd_5673319 : Nat := 2913139553285193847021387

theorem tailTrace_5673319 : CollatzResearch.WordTrace tailWord_5673319 prefixEnd_5673319 2913139553285193847021387 := by
  unfold tailWord_5673319
  simp only [CollatzResearch.WordTrace]
  refine ⟨206922943333541663590191011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137948628889027775726794007 206922943333541663590191011)
  ·
    refine ⟨310384415000312495385286517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206922943333541663590191011 310384415000312495385286517)
    ·
      refine ⟨29098538906279296442370611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 310384415000312495385286517 29098538906279296442370611)
      ·
        refine ⟨43647808359418944663555917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29098538906279296442370611 43647808359418944663555917)
        ·
          refine ⟨16367928134782104248833469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43647808359418944663555917 16367928134782104248833469)
          ·
            refine ⟨6137973050543289093312551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16367928134782104248833469 6137973050543289093312551)
            ·
              refine ⟨9206959575814933639968827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6137973050543289093312551 9206959575814933639968827)
              ·
                refine ⟨13810439363722400459953241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9206959575814933639968827 13810439363722400459953241)
                ·
                  refine ⟨10357829522791800344964931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13810439363722400459953241 10357829522791800344964931)
                  ·
                    refine ⟨15536744284187700517447397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10357829522791800344964931 15536744284187700517447397)
                    ·
                      refine ⟨2913139553285193847021387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15536744284187700517447397 2913139553285193847021387)
                      ·
                        rfl

theorem cell23_5673319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_5673319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673319 prefixEnd_5673319 := by exact prefixLift 5673319
  have htrace : WordTrace (prefixWord ++ tailWord_5673319) baseStart_5673319 baseEnd_5673319 := by
    simpa [prefixWord, tailWord_5673319, baseEnd_5673319] using wordTrace_append hprefix tailTrace_5673319
  have hstable : (prefixWord ++ tailWord_5673319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673319).length < 2 ^ (prefixWord ++ tailWord_5673319).sum := by decide
  have hdescent : baseEnd_5673319 < baseStart_5673319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673325 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 8]
def baseStart_5673325 : Nat := 118140960795 + 5673325 * 2 ^ 59
def prefixEnd_5673325 : Nat := 4983230072969 + 3 ^ 40 * 5673325 * 2
def baseEnd_5673325 : Nat := 323682514907680091505151

theorem tailTrace_5673325 : CollatzResearch.WordTrace tailWord_5673325 prefixEnd_5673325 323682514907680091505151 := by
  unfold tailWord_5673325
  simp only [CollatzResearch.WordTrace]
  refine ⟨206923162171519926614909429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137948774781013284409939619 206923162171519926614909429)
  ·
    refine ⟨19399046453579993120147759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206923162171519926614909429 19399046453579993120147759)
    ·
      refine ⟨29098569680369989680221639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19399046453579993120147759 29098569680369989680221639)
      ·
        refine ⟨43647854520554984520332459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29098569680369989680221639 43647854520554984520332459)
        ·
          refine ⟨65471781780832476780498689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43647854520554984520332459 65471781780832476780498689)
          ·
            refine ⟨49103836335624357585374017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65471781780832476780498689 49103836335624357585374017)
            ·
              refine ⟨36827877251718268189030513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49103836335624357585374017 36827877251718268189030513)
              ·
                refine ⟨27620907938788701141772885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36827877251718268189030513 27620907938788701141772885)
                ·
                  refine ⟨323682514907680091505151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27620907938788701141772885 323682514907680091505151)
                  ·
                    rfl

theorem cell23_5673325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_5673325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673325 prefixEnd_5673325 := by exact prefixLift 5673325
  have htrace : WordTrace (prefixWord ++ tailWord_5673325) baseStart_5673325 baseEnd_5673325 := by
    simpa [prefixWord, tailWord_5673325, baseEnd_5673325] using wordTrace_append hprefix tailTrace_5673325
  have hstable : (prefixWord ++ tailWord_5673325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673325).length < 2 ^ (prefixWord ++ tailWord_5673325).sum := by decide
  have hdescent : baseEnd_5673325 < baseStart_5673325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673385 : List Nat := [1, 2, 1, 1, 1, 1, 3, 6, 1, 6]
def baseStart_5673385 : Nat := 118140960795 + 5673385 * 2 ^ 59
def prefixEnd_5673385 : Nat := 4983230072969 + 3 ^ 40 * 5673385 * 2
def baseEnd_5673385 : Nat := 971057814336130196265361

theorem tailTrace_5673385 : CollatzResearch.WordTrace tailWord_5673385 prefixEnd_5673385 971057814336130196265361 := by
  unfold tailWord_5673385
  simp only [CollatzResearch.WordTrace]
  refine ⟨206925350551302556862093609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137950233700868371241395739 206925350551302556862093609)
  ·
    refine ⟨155194012913476917646570207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206925350551302556862093609 155194012913476917646570207)
    ·
      refine ⟨232791019370215376469855311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155194012913476917646570207 232791019370215376469855311)
      ·
        refine ⟨349186529055323064704782967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232791019370215376469855311 349186529055323064704782967)
        ·
          refine ⟨523779793582984597057174451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349186529055323064704782967 523779793582984597057174451)
          ·
            refine ⟨785669690374476895585761677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523779793582984597057174451 785669690374476895585761677)
            ·
              refine ⟨294626133890428835844660629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 785669690374476895585761677 294626133890428835844660629)
              ·
                refine ⟨13810600026113851680218467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 294626133890428835844660629 13810600026113851680218467)
                ·
                  refine ⟨20715900039170777520327701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13810600026113851680218467 20715900039170777520327701)
                  ·
                    refine ⟨971057814336130196265361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20715900039170777520327701 971057814336130196265361)
                    ·
                      rfl

theorem cell23_5673385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 6].length) (baseStart_5673385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673385 prefixEnd_5673385 := by exact prefixLift 5673385
  have htrace : WordTrace (prefixWord ++ tailWord_5673385) baseStart_5673385 baseEnd_5673385 := by
    simpa [prefixWord, tailWord_5673385, baseEnd_5673385] using wordTrace_append hprefix tailTrace_5673385
  have hstable : (prefixWord ++ tailWord_5673385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673385).length < 2 ^ (prefixWord ++ tailWord_5673385).sum := by decide
  have hdescent : baseEnd_5673385 < baseStart_5673385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673415 : List Nat := [1, 1, 4, 1, 1, 4, 1, 10]
def baseStart_5673415 : Nat := 118140960795 + 5673415 * 2 ^ 59
def prefixEnd_5673415 : Nat := 4983230072969 + 3 ^ 40 * 5673415 * 2
def baseEnd_5673415 : Nat := 107895883238075017460035

theorem tailTrace_5673415 : CollatzResearch.WordTrace tailWord_5673415 prefixEnd_5673415 107895883238075017460035 := by
  unfold tailWord_5673415
  simp only [CollatzResearch.WordTrace]
  refine ⟨206926444741193871985685699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137950963160795914657123799 206926444741193871985685699)
  ·
    refine ⟨310389667111790807978528549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206926444741193871985685699 310389667111790807978528549)
    ·
      refine ⟨58198062583460776495974103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310389667111790807978528549 58198062583460776495974103)
      ·
        refine ⟨87297093875191164743961155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58198062583460776495974103 87297093875191164743961155)
        ·
          refine ⟨130945640812786747115941733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87297093875191164743961155 130945640812786747115941733)
          ·
            refine ⟨24552307652397515084239075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130945640812786747115941733 24552307652397515084239075)
            ·
              refine ⟨36828461478596272626358613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24552307652397515084239075 36828461478596272626358613)
              ·
                refine ⟨107895883238075017460035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36828461478596272626358613 107895883238075017460035)
                ·
                  rfl

theorem cell23_5673415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 10].length) (baseStart_5673415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673415 prefixEnd_5673415 := by exact prefixLift 5673415
  have htrace : WordTrace (prefixWord ++ tailWord_5673415) baseStart_5673415 baseEnd_5673415 := by
    simpa [prefixWord, tailWord_5673415, baseEnd_5673415] using wordTrace_append hprefix tailTrace_5673415
  have hstable : (prefixWord ++ tailWord_5673415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673415).length < 2 ^ (prefixWord ++ tailWord_5673415).sum := by decide
  have hdescent : baseEnd_5673415 < baseStart_5673415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673422 : List Nat := [4, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_5673422 : Nat := 118140960795 + 5673422 * 2 ^ 59
def prefixEnd_5673422 : Nat := 4983230072969 + 3 ^ 40 * 5673422 * 2
def baseEnd_5673422 : Nat := 2913192441792606944033413

theorem tailTrace_5673422 : CollatzResearch.WordTrace tailWord_5673422 prefixEnd_5673422 2913192441792606944033413 := by
  unfold tailWord_5673422
  simp only [CollatzResearch.WordTrace]
  refine ⟨25865837506521064022648815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137951133368112341454127013 25865837506521064022648815)
  ·
    refine ⟨38798756259781596033973223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25865837506521064022648815 38798756259781596033973223)
    ·
      refine ⟨58198134389672394050959835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38798756259781596033973223 58198134389672394050959835)
      ·
        refine ⟨87297201584508591076439753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58198134389672394050959835 87297201584508591076439753)
        ·
          refine ⟨65472901188381443307329815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87297201584508591076439753 65472901188381443307329815)
          ·
            refine ⟨98209351782572164960994723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65472901188381443307329815 98209351782572164960994723)
            ·
              refine ⟨147314027673858247441492085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98209351782572164960994723 147314027673858247441492085)
              ·
                refine ⟨13810690094424210697639883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147314027673858247441492085 13810690094424210697639883)
                ·
                  refine ⟨20716035141636316046459825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13810690094424210697639883 20716035141636316046459825)
                  ·
                    refine ⟨15537026356227237034844869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20716035141636316046459825 15537026356227237034844869)
                    ·
                      refine ⟨2913192441792606944033413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15537026356227237034844869 2913192441792606944033413)
                      ·
                        rfl

theorem cell23_5673422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_5673422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673422 prefixEnd_5673422 := by exact prefixLift 5673422
  have htrace : WordTrace (prefixWord ++ tailWord_5673422) baseStart_5673422 baseEnd_5673422 := by
    simpa [prefixWord, tailWord_5673422, baseEnd_5673422] using wordTrace_append hprefix tailTrace_5673422
  have hstable : (prefixWord ++ tailWord_5673422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673422).length < 2 ^ (prefixWord ++ tailWord_5673422).sum := by decide
  have hdescent : baseEnd_5673422 < baseStart_5673422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673426 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_5673426 : Nat := 118140960795 + 5673426 * 2 ^ 59
def prefixEnd_5673426 : Nat := 4983230072969 + 3 ^ 40 * 5673426 * 2
def baseEnd_5673426 : Nat := 2913194495715224928383395

theorem tailTrace_5673426 : CollatzResearch.WordTrace tailWord_5673426 prefixEnd_5673426 2913194495715224928383395 := by
  unfold tailWord_5673426
  simp only [CollatzResearch.WordTrace]
  refine ⟨51731711486038505216084033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137951230629436013909557421 51731711486038505216084033)
  ·
    refine ⟨38798783614528878912063025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51731711486038505216084033 38798783614528878912063025)
    ·
      refine ⟨29099087710896659184047269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38798783614528878912063025 29099087710896659184047269)
      ·
        refine ⟨5456078945793123597008863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29099087710896659184047269 5456078945793123597008863)
        ·
          refine ⟨8184118418689685395513295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5456078945793123597008863 8184118418689685395513295)
          ·
            refine ⟨12276177628034528093269943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8184118418689685395513295 12276177628034528093269943)
            ·
              refine ⟨18414266442051792139904915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12276177628034528093269943 18414266442051792139904915)
              ·
                refine ⟨27621399663077688209857373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18414266442051792139904915 27621399663077688209857373)
                ·
                  refine ⟨10358024873654133078696515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27621399663077688209857373 10358024873654133078696515)
                  ·
                    refine ⟨15537037310481199618044773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10358024873654133078696515 15537037310481199618044773)
                    ·
                      refine ⟨2913194495715224928383395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15537037310481199618044773 2913194495715224928383395)
                      ·
                        rfl

theorem cell23_5673426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_5673426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673426 prefixEnd_5673426 := by exact prefixLift 5673426
  have htrace : WordTrace (prefixWord ++ tailWord_5673426) baseStart_5673426 baseEnd_5673426 := by
    simpa [prefixWord, tailWord_5673426, baseEnd_5673426] using wordTrace_append hprefix tailTrace_5673426
  have hstable : (prefixWord ++ tailWord_5673426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673426).length < 2 ^ (prefixWord ++ tailWord_5673426).sum := by decide
  have hdescent : baseEnd_5673426 < baseStart_5673426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673429 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 3, 2, 3]
def baseStart_5673429 : Nat := 118140960795 + 5673429 * 2 ^ 59
def prefixEnd_5673429 : Nat := 4983230072969 + 3 ^ 40 * 5673429 * 2
def baseEnd_5673429 : Nat := 2913196036157188416645881

theorem tailTrace_5673429 : CollatzResearch.WordTrace tailWord_5673429 prefixEnd_5673429 2913196036157188416645881 := by
  unfold tailWord_5673429
  simp only [CollatzResearch.WordTrace]
  refine ⟨206926955363143152376695341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137951303575428768251130227 206926955363143152376695341)
  ·
    refine ⟨77597608261178682141260753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206926955363143152376695341 77597608261178682141260753)
    ·
      refine ⟨58198206195884011605945565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77597608261178682141260753 58198206195884011605945565)
      ·
        refine ⟨21824327323456504352229587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58198206195884011605945565 21824327323456504352229587)
        ·
          refine ⟨32736490985184756528344381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21824327323456504352229587 32736490985184756528344381)
          ·
            refine ⟨12276184119444283698129143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32736490985184756528344381 12276184119444283698129143)
            ·
              refine ⟨18414276179166425547193715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12276184119444283698129143 18414276179166425547193715)
              ·
                refine ⟨27621414268749638320790573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18414276179166425547193715 27621414268749638320790573)
                ·
                  refine ⟨10358030350781114370296465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27621414268749638320790573 10358030350781114370296465)
                  ·
                    refine ⟨7768522763085835777722349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10358030350781114370296465 7768522763085835777722349)
                    ·
                      refine ⟨2913196036157188416645881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7768522763085835777722349 2913196036157188416645881)
                      ·
                        rfl

theorem cell23_5673429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_5673429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673429 prefixEnd_5673429 := by exact prefixLift 5673429
  have htrace : WordTrace (prefixWord ++ tailWord_5673429) baseStart_5673429 baseEnd_5673429 := by
    simpa [prefixWord, tailWord_5673429, baseEnd_5673429] using wordTrace_append hprefix tailTrace_5673429
  have hstable : (prefixWord ++ tailWord_5673429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673429).length < 2 ^ (prefixWord ++ tailWord_5673429).sum := by decide
  have hdescent : baseEnd_5673429 < baseStart_5673429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673462 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_5673462 : Nat := 118140960795 + 5673462 * 2 ^ 59
def prefixEnd_5673462 : Nat := 4983230072969 + 3 ^ 40 * 5673462 * 2
def baseEnd_5673462 : Nat := 971070993672928929177743

theorem tailTrace_5673462 : CollatzResearch.WordTrace tailWord_5673462 prefixEnd_5673462 971070993672928929177743 := by
  unfold tailWord_5673462
  simp only [CollatzResearch.WordTrace]
  refine ⟨12933009935751474938290415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137952105981349066008431093 12933009935751474938290415)
  ·
    refine ⟨19399514903627212407435623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12933009935751474938290415 19399514903627212407435623)
    ·
      refine ⟨29099272355440818611153435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19399514903627212407435623 29099272355440818611153435)
      ·
        refine ⟨43648908533161227916730153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29099272355440818611153435 43648908533161227916730153)
        ·
          refine ⟨32736681399870920937547615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43648908533161227916730153 32736681399870920937547615)
          ·
            refine ⟨49105022099806381406321423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32736681399870920937547615 49105022099806381406321423)
            ·
              refine ⟨73657533149709572109482135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49105022099806381406321423 73657533149709572109482135)
              ·
                refine ⟨110486299724564358164223203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73657533149709572109482135 110486299724564358164223203)
                ·
                  refine ⟨165729449586846537246334805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110486299724564358164223203 165729449586846537246334805)
                  ·
                    refine ⟨971070993672928929177743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 165729449586846537246334805 971070993672928929177743)
                    ·
                      rfl

theorem cell23_5673462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_5673462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673462 prefixEnd_5673462 := by exact prefixLift 5673462
  have htrace : WordTrace (prefixWord ++ tailWord_5673462) baseStart_5673462 baseEnd_5673462 := by
    simpa [prefixWord, tailWord_5673462, baseEnd_5673462] using wordTrace_append hprefix tailTrace_5673462
  have hstable : (prefixWord ++ tailWord_5673462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673462).length < 2 ^ (prefixWord ++ tailWord_5673462).sum := by decide
  have hdescent : baseEnd_5673462 < baseStart_5673462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673469 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 5, 3, 2]
def baseStart_5673469 : Nat := 118140960795 + 5673469 * 2 ^ 59
def prefixEnd_5673469 : Nat := 4983230072969 + 3 ^ 40 * 5673469 * 2
def baseEnd_5673469 : Nat := 2913216575383368260145697

theorem tailTrace_5673469 : CollatzResearch.WordTrace tailWord_5673469 prefixEnd_5673469 2913216575383368260145697 := by
  unfold tailWord_5673469
  simp only [CollatzResearch.WordTrace]
  refine ⟨206928414282998239208151461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137952276188665492805434307 206928414282998239208151461)
  ·
    refine ⟨38799077678062169851528399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206928414282998239208151461 38799077678062169851528399)
    ·
      refine ⟨58198616517093254777292599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38799077678062169851528399 58198616517093254777292599)
      ·
        refine ⟨87297924775639882165938899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58198616517093254777292599 87297924775639882165938899)
        ·
          refine ⟨130946887163459823248908349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87297924775639882165938899 130946887163459823248908349)
          ·
            refine ⟨49105082686297433718340631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130946887163459823248908349 49105082686297433718340631)
            ·
              refine ⟨73657624029446150577510947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49105082686297433718340631 73657624029446150577510947)
              ·
                refine ⟨110486436044169225866266421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73657624029446150577510947 110486436044169225866266421)
                ·
                  refine ⟨10358103379140864924962477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110486436044169225866266421 10358103379140864924962477)
                  ·
                    refine ⟨3884288767177824346860929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10358103379140864924962477 3884288767177824346860929)
                    ·
                      refine ⟨2913216575383368260145697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3884288767177824346860929 2913216575383368260145697)
                      ·
                        rfl

theorem cell23_5673469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_5673469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673469 prefixEnd_5673469 := by exact prefixLift 5673469
  have htrace : WordTrace (prefixWord ++ tailWord_5673469) baseStart_5673469 baseEnd_5673469 := by
    simpa [prefixWord, tailWord_5673469, baseEnd_5673469] using wordTrace_append hprefix tailTrace_5673469
  have hstable : (prefixWord ++ tailWord_5673469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673469).length < 2 ^ (prefixWord ++ tailWord_5673469).sum := by decide
  have hdescent : baseEnd_5673469 < baseStart_5673469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673476 : List Nat := [2, 3, 2, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_5673476 : Nat := 118140960795 + 5673476 * 2 ^ 59
def prefixEnd_5673476 : Nat := 4983230072969 + 3 ^ 40 * 5673476 * 2
def baseEnd_5673476 : Nat := 2913220169747949732758165

theorem tailTrace_5673476 : CollatzResearch.WordTrace tailWord_5673476 prefixEnd_5673476 2913220169747949732758165 := by
  unfold tailWord_5673476
  simp only [CollatzResearch.WordTrace]
  refine ⟨103464334796986439701828141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137952446395981919602437521 103464334796986439701828141)
  ·
    refine ⟨38799125548869914888185553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103464334796986439701828141 38799125548869914888185553)
    ·
      refine ⟨29099344161652436166139165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38799125548869914888185553 29099344161652436166139165)
      ·
        refine ⟨10912254060619663562302187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29099344161652436166139165 10912254060619663562302187)
        ·
          refine ⟨16368381090929495343453281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10912254060619663562302187 16368381090929495343453281)
          ·
            refine ⟨12276285818197121507589961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16368381090929495343453281 12276285818197121507589961)
            ·
              refine ⟨9207214363647841130692471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12276285818197121507589961 9207214363647841130692471)
              ·
                refine ⟨13810821545471761696038707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9207214363647841130692471 13810821545471761696038707)
                ·
                  refine ⟨20716232318207642544058061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13810821545471761696038707 20716232318207642544058061)
                  ·
                    refine ⟨7768587119327865954021773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20716232318207642544058061 7768587119327865954021773)
                    ·
                      refine ⟨2913220169747949732758165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7768587119327865954021773 2913220169747949732758165)
                      ·
                        rfl

theorem cell23_5673476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_5673476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673476 prefixEnd_5673476 := by exact prefixLift 5673476
  have htrace : WordTrace (prefixWord ++ tailWord_5673476) baseStart_5673476 baseEnd_5673476 := by
    simpa [prefixWord, tailWord_5673476, baseEnd_5673476] using wordTrace_append hprefix tailTrace_5673476
  have hstable : (prefixWord ++ tailWord_5673476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673476).length < 2 ^ (prefixWord ++ tailWord_5673476).sum := by decide
  have hdescent : baseEnd_5673476 < baseStart_5673476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673482 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_5673482 : Nat := 118140960795 + 5673482 * 2 ^ 59
def prefixEnd_5673482 : Nat := 4983230072969 + 3 ^ 40 * 5673482 * 2
def baseEnd_5673482 : Nat := 2913223250631876709283137

theorem tailTrace_5673482 : CollatzResearch.WordTrace tailWord_5673482 prefixEnd_5673482 2913223250631876709283137 := by
  unfold tailWord_5673482
  simp only [CollatzResearch.WordTrace]
  refine ⟨51732222107987785607093675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137952592287967428285583133 51732222107987785607093675)
  ·
    refine ⟨77598333161981678410640513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51732222107987785607093675 77598333161981678410640513)
    ·
      refine ⟨58198749871486258807980385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77598333161981678410640513 58198749871486258807980385)
      ·
        refine ⟨43649062403614694105985289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58198749871486258807980385 43649062403614694105985289)
        ·
          refine ⟨32736796802711020579488967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43649062403614694105985289 32736796802711020579488967)
          ·
            refine ⟨49105195204066530869233451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32736796802711020579488967 49105195204066530869233451)
            ·
              refine ⟨73657792806099796303850177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49105195204066530869233451 73657792806099796303850177)
              ·
                refine ⟨55243344604574847227887633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73657792806099796303850177 55243344604574847227887633)
                ·
                  refine ⟨41432508453431135420915725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55243344604574847227887633 41432508453431135420915725)
                  ·
                    refine ⟨15537190670036675782843397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41432508453431135420915725 15537190670036675782843397)
                    ·
                      refine ⟨2913223250631876709283137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15537190670036675782843397 2913223250631876709283137)
                      ·
                        rfl

theorem cell23_5673482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_5673482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673482 prefixEnd_5673482 := by exact prefixLift 5673482
  have htrace : WordTrace (prefixWord ++ tailWord_5673482) baseStart_5673482 baseEnd_5673482 := by
    simpa [prefixWord, tailWord_5673482, baseEnd_5673482] using wordTrace_append hprefix tailTrace_5673482
  have hstable : (prefixWord ++ tailWord_5673482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673482).length < 2 ^ (prefixWord ++ tailWord_5673482).sum := by decide
  have hdescent : baseEnd_5673482 < baseStart_5673482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673486 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2]
def baseStart_5673486 : Nat := 118140960795 + 5673486 * 2 ^ 59
def prefixEnd_5673486 : Nat := 4983230072969 + 3 ^ 40 * 5673486 * 2
def baseEnd_5673486 : Nat := 2913225304554494693633119

theorem tailTrace_5673486 : CollatzResearch.WordTrace tailWord_5673486 prefixEnd_5673486 2913225304554494693633119 := by
  unfold tailWord_5673486
  simp only [CollatzResearch.WordTrace]
  refine ⟨25866129290492081388940039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137952689549291100741013541 25866129290492081388940039)
  ·
    refine ⟨38799193935738122083410059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25866129290492081388940039 38799193935738122083410059)
    ·
      refine ⟨58198790903607183125115089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38799193935738122083410059 58198790903607183125115089)
      ·
        refine ⟨43649093177705387343836317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58198790903607183125115089 43649093177705387343836317)
        ·
          refine ⟨16368409941639520253938619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43649093177705387343836317 16368409941639520253938619)
          ·
            refine ⟨24552614912459280380907929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16368409941639520253938619 24552614912459280380907929)
            ·
              refine ⟨18414461184344460285680947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24552614912459280380907929 18414461184344460285680947)
              ·
                refine ⟨27621691776516690428521421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18414461184344460285680947 27621691776516690428521421)
                ·
                  refine ⟨10358134416193758910695533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27621691776516690428521421 10358134416193758910695533)
                  ·
                    refine ⟨3884300406072659591510825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10358134416193758910695533 3884300406072659591510825)
                    ·
                      refine ⟨2913225304554494693633119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3884300406072659591510825 2913225304554494693633119)
                      ·
                        rfl

theorem cell23_5673486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_5673486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673486 prefixEnd_5673486 := by exact prefixLift 5673486
  have htrace : WordTrace (prefixWord ++ tailWord_5673486) baseStart_5673486 baseEnd_5673486 := by
    simpa [prefixWord, tailWord_5673486, baseEnd_5673486] using wordTrace_append hprefix tailTrace_5673486
  have hstable : (prefixWord ++ tailWord_5673486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673486).length < 2 ^ (prefixWord ++ tailWord_5673486).sum := by decide
  have hdescent : baseEnd_5673486 < baseStart_5673486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673522 : List Nat := [3, 2, 1, 1, 2, 1, 3, 3, 7]
def baseStart_5673522 : Nat := 118140960795 + 5673522 * 2 ^ 59
def prefixEnd_5673522 : Nat := 4983230072969 + 3 ^ 40 * 5673522 * 2
def baseEnd_5673522 : Nat := 323693754428672950309217

theorem tailTrace_5673522 : CollatzResearch.WordTrace tailWord_5673522 prefixEnd_5673522 323693754428672950309217 := by
  unfold tailWord_5673522
  simp only [CollatzResearch.WordTrace]
  refine ⟨51732586837951557314957705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137953564901204152839887213 51732586837951557314957705)
  ·
    refine ⟨38799440128463667986218279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51732586837951557314957705 38799440128463667986218279)
    ·
      refine ⟨58199160192695501979327419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38799440128463667986218279 58199160192695501979327419)
      ·
        refine ⟨87298740289043252968991129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58199160192695501979327419 87298740289043252968991129)
        ·
          refine ⟨65474055216782439726743347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87298740289043252968991129 65474055216782439726743347)
          ·
            refine ⟨98211082825173659590115021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65474055216782439726743347 98211082825173659590115021)
            ·
              refine ⟨36829156059440122346293133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98211082825173659590115021 36829156059440122346293133)
              ·
                refine ⟨13810933522290045879859925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36829156059440122346293133 13810933522290045879859925)
                ·
                  refine ⟨323693754428672950309217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13810933522290045879859925 323693754428672950309217)
                  ·
                    rfl

theorem cell23_5673522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_5673522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673522 prefixEnd_5673522 := by exact prefixLift 5673522
  have htrace : WordTrace (prefixWord ++ tailWord_5673522) baseStart_5673522 baseEnd_5673522 := by
    simpa [prefixWord, tailWord_5673522, baseEnd_5673522] using wordTrace_append hprefix tailTrace_5673522
  have hstable : (prefixWord ++ tailWord_5673522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673522).length < 2 ^ (prefixWord ++ tailWord_5673522).sum := by decide
  have hdescent : baseEnd_5673522 < baseStart_5673522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673533 : List Nat := [1, 4, 1, 3, 2, 3, 1, 1, 1, 4, 2]
def baseStart_5673533 : Nat := 118140960795 + 5673533 * 2 ^ 59
def prefixEnd_5673533 : Nat := 4983230072969 + 3 ^ 40 * 5673533 * 2
def baseEnd_5673533 : Nat := 2913249438145256009745403

theorem tailTrace_5673533 : CollatzResearch.WordTrace tailWord_5673533 prefixEnd_5673533 2913249438145256009745403 := by
  unfold tailWord_5673533
  simp only [CollatzResearch.WordTrace]
  refine ⟨206930748554766378138481253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137953832369844252092320835 206930748554766378138481253)
  ·
    refine ⟨38799515354018695900965235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206930748554766378138481253 38799515354018695900965235)
    ·
      refine ⟨58199273031028043851447853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38799515354018695900965235 58199273031028043851447853)
      ·
        refine ⟨21824727386635516444292945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58199273031028043851447853 21824727386635516444292945)
        ·
          refine ⟨16368545539976637333219709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21824727386635516444292945 16368545539976637333219709)
          ·
            refine ⟨6138204577491238999957391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16368545539976637333219709 6138204577491238999957391)
            ·
              refine ⟨9207306866236858499936087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6138204577491238999957391 9207306866236858499936087)
              ·
                refine ⟨13810960299355287749904131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9207306866236858499936087 13810960299355287749904131)
                ·
                  refine ⟨20716440449032931624856197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13810960299355287749904131 20716440449032931624856197)
                  ·
                    refine ⟨3884332584193674679660537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20716440449032931624856197 3884332584193674679660537)
                    ·
                      refine ⟨2913249438145256009745403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3884332584193674679660537 2913249438145256009745403)
                      ·
                        rfl

theorem cell23_5673533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_5673533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673533 prefixEnd_5673533 := by exact prefixLift 5673533
  have htrace : WordTrace (prefixWord ++ tailWord_5673533) baseStart_5673533 baseEnd_5673533 := by
    simpa [prefixWord, tailWord_5673533, baseEnd_5673533] using wordTrace_append hprefix tailTrace_5673533
  have hstable : (prefixWord ++ tailWord_5673533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673533).length < 2 ^ (prefixWord ++ tailWord_5673533).sum := by decide
  have hdescent : baseEnd_5673533 < baseStart_5673533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673556 : List Nat := [2, 4, 1, 1, 1, 3, 3, 3, 5]
def baseStart_5673556 : Nat := 118140960795 + 5673556 * 2 ^ 59
def prefixEnd_5673556 : Nat := 4983230072969 + 3 ^ 40 * 5673556 * 2
def baseEnd_5673556 : Nat := 323695694244478824417533

theorem tailTrace_5673556 : CollatzResearch.WordTrace tailWord_5673556 prefixEnd_5673556 323695694244478824417533 := by
  unfold tailWord_5673556
  simp only [CollatzResearch.WordTrace]
  refine ⟨103465793716841526533284261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137954391622455368711045681 103465793716841526533284261)
  ·
    refine ⟨19399836321907786224990799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103465793716841526533284261 19399836321907786224990799)
    ·
      refine ⟨29099754482861679337486199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19399836321907786224990799 29099754482861679337486199)
      ·
        refine ⟨43649631724292519006229299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29099754482861679337486199 43649631724292519006229299)
        ·
          refine ⟨65474447586438778509343949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43649631724292519006229299 65474447586438778509343949)
          ·
            refine ⟨24552917844914541941003981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65474447586438778509343949 24552917844914541941003981)
            ·
              refine ⟨9207344191842953227876493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24552917844914541941003981 9207344191842953227876493)
              ·
                refine ⟨3452754071941107460453685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9207344191842953227876493 3452754071941107460453685)
                ·
                  refine ⟨323695694244478824417533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3452754071941107460453685 323695694244478824417533)
                  ·
                    rfl

theorem cell23_5673556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_5673556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673556 prefixEnd_5673556 := by exact prefixLift 5673556
  have htrace : WordTrace (prefixWord ++ tailWord_5673556) baseStart_5673556 baseEnd_5673556 := by
    simpa [prefixWord, tailWord_5673556, baseEnd_5673556] using wordTrace_append hprefix tailTrace_5673556
  have hstable : (prefixWord ++ tailWord_5673556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673556).length < 2 ^ (prefixWord ++ tailWord_5673556).sum := by decide
  have hdescent : baseEnd_5673556 < baseStart_5673556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673569 : List Nat := [1, 2, 3, 1, 1, 5, 1, 2, 2, 5]
def baseStart_5673569 : Nat := 118140960795 + 5673569 * 2 ^ 59
def prefixEnd_5673569 : Nat := 4983230072969 + 3 ^ 40 * 5673569 * 2
def baseEnd_5673569 : Nat := 971089307816272622965079

theorem tailTrace_5673569 : CollatzResearch.WordTrace tailWord_5673569 prefixEnd_5673569 971089307816272622965079 := by
  unfold tailWord_5673569
  simp only [CollatzResearch.WordTrace]
  refine ⟨206932061582635956286791761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137954707721757304191194507 206932061582635956286791761)
  ·
    refine ⟨155199046186976967215093821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206932061582635956286791761 155199046186976967215093821)
    ·
      refine ⟨58199642320116362705660183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155199046186976967215093821 58199642320116362705660183)
      ·
        refine ⟨87299463480174544058490275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58199642320116362705660183 87299463480174544058490275)
        ·
          refine ⟨130949195220261816087735413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87299463480174544058490275 130949195220261816087735413)
          ·
            refine ⟨12276487051899545258225195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 130949195220261816087735413 12276487051899545258225195)
            ·
              refine ⟨18414730577849317887337793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12276487051899545258225195 18414730577849317887337793)
              ·
                refine ⟨13811047933386988415503345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18414730577849317887337793 13811047933386988415503345)
                ·
                  refine ⟨10358285950040241311627509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13811047933386988415503345 10358285950040241311627509)
                  ·
                    refine ⟨971089307816272622965079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10358285950040241311627509 971089307816272622965079)
                    ·
                      rfl

theorem cell23_5673569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_5673569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673569 prefixEnd_5673569 := by exact prefixLift 5673569
  have htrace : WordTrace (prefixWord ++ tailWord_5673569) baseStart_5673569 baseEnd_5673569 := by
    simpa [prefixWord, tailWord_5673569, baseEnd_5673569] using wordTrace_append hprefix tailTrace_5673569
  have hstable : (prefixWord ++ tailWord_5673569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673569).length < 2 ^ (prefixWord ++ tailWord_5673569).sum := by decide
  have hdescent : baseEnd_5673569 < baseStart_5673569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673573 : List Nat := [1, 3, 1, 3, 4, 1, 3, 2, 5]
def baseStart_5673573 : Nat := 118140960795 + 5673573 * 2 ^ 59
def prefixEnd_5673573 : Nat := 4983230072969 + 3 ^ 40 * 5673573 * 2
def baseEnd_5673573 : Nat := 323696664152381761471691

theorem tailTrace_5673573 : CollatzResearch.WordTrace tailWord_5673573 prefixEnd_5673573 323696664152381761471691 := by
  unfold tailWord_5673573
  simp only [CollatzResearch.WordTrace]
  refine ⟨206932207474621464969937373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137954804983080976646624915 206932207474621464969937373)
  ·
    refine ⟨77599577802983049363726515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206932207474621464969937373 77599577802983049363726515)
    ·
      refine ⟨116399366704474574045589773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77599577802983049363726515 116399366704474574045589773)
      ·
        refine ⟨43649762514177965267096165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116399366704474574045589773 43649762514177965267096165)
        ·
          refine ⟨8184330471408368487580531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43649762514177965267096165 8184330471408368487580531)
          ·
            refine ⟨12276495707112552731370797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8184330471408368487580531 12276495707112552731370797)
            ·
              refine ⟨4603685890167207274264049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12276495707112552731370797 4603685890167207274264049)
              ·
                refine ⟨3452764417625405455698037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4603685890167207274264049 3452764417625405455698037)
                ·
                  refine ⟨323696664152381761471691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3452764417625405455698037 323696664152381761471691)
                  ·
                    rfl

theorem cell23_5673573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 5].length) (baseStart_5673573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673573 prefixEnd_5673573 := by exact prefixLift 5673573
  have htrace : WordTrace (prefixWord ++ tailWord_5673573) baseStart_5673573 baseEnd_5673573 := by
    simpa [prefixWord, tailWord_5673573, baseEnd_5673573] using wordTrace_append hprefix tailTrace_5673573
  have hstable : (prefixWord ++ tailWord_5673573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673573).length < 2 ^ (prefixWord ++ tailWord_5673573).sum := by decide
  have hdescent : baseEnd_5673573 < baseStart_5673573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673612 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 8]
def baseStart_5673612 : Nat := 118140960795 + 5673612 * 2 ^ 59
def prefixEnd_5673612 : Nat := 4983230072969 + 3 ^ 40 * 5673612 * 2
def baseEnd_5673612 : Nat := 323698889235217911184171

theorem tailTrace_5673612 : CollatzResearch.WordTrace tailWord_5673612 prefixEnd_5673612 323698889235217911184171 := by
  unfold tailWord_5673612
  simp only [CollatzResearch.WordTrace]
  refine ⟨103466814960740087315303545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137955753280986783087071393 103466814960740087315303545)
  ·
    refine ⟨77600111220555065486477659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103466814960740087315303545 77600111220555065486477659)
    ·
      refine ⟨116400166830832598229716489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77600111220555065486477659 116400166830832598229716489)
      ·
        refine ⟨87300125123124448672287367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116400166830832598229716489 87300125123124448672287367)
        ·
          refine ⟨130950187684686673008431051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87300125123124448672287367 130950187684686673008431051)
          ·
            refine ⟨196425281527030009512646577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130950187684686673008431051 196425281527030009512646577)
            ·
              refine ⟨147318961145272507134484933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196425281527030009512646577 147318961145272507134484933)
              ·
                refine ⟨27622305214738595087715925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147318961145272507134484933 27622305214738595087715925)
                ·
                  refine ⟨323698889235217911184171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27622305214738595087715925 323698889235217911184171)
                  ·
                    rfl

theorem cell23_5673612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 8].length) (baseStart_5673612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673612 prefixEnd_5673612 := by exact prefixLift 5673612
  have htrace : WordTrace (prefixWord ++ tailWord_5673612) baseStart_5673612 baseEnd_5673612 := by
    simpa [prefixWord, tailWord_5673612, baseEnd_5673612] using wordTrace_append hprefix tailTrace_5673612
  have hstable : (prefixWord ++ tailWord_5673612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673612).length < 2 ^ (prefixWord ++ tailWord_5673612).sum := by decide
  have hdescent : baseEnd_5673612 < baseStart_5673612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673629 : List Nat := [1, 4, 2, 1, 1, 1, 3, 4, 6]
def baseStart_5673629 : Nat := 118140960795 + 5673629 * 2 ^ 59
def prefixEnd_5673629 : Nat := 4983230072969 + 3 ^ 40 * 5673629 * 2
def baseEnd_5673629 : Nat := 323699859143120848238329

theorem tailTrace_5673629 : CollatzResearch.WordTrace tailWord_5673629 prefixEnd_5673629 323699859143120848238329 := by
  unfold tailWord_5673629
  simp only [CollatzResearch.WordTrace]
  refine ⟨206934249962418586533975941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137956166641612391022650627 206934249962418586533975941)
  ·
    refine ⟨38800171867953484975120489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206934249962418586533975941 38800171867953484975120489)
    ·
      refine ⟨29100128900965113731340367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38800171867953484975120489 29100128900965113731340367)
      ·
        refine ⟨43650193351447670597010551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29100128900965113731340367 43650193351447670597010551)
        ·
          refine ⟨65475290027171505895515827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43650193351447670597010551 65475290027171505895515827)
          ·
            refine ⟨98212935040757258843273741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65475290027171505895515827 98212935040757258843273741)
            ·
              refine ⟨36829850640283972066227653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98212935040757258843273741 36829850640283972066227653)
              ·
                refine ⟨6905596995053244762417685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36829850640283972066227653 6905596995053244762417685)
                ·
                  refine ⟨323699859143120848238329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6905596995053244762417685 323699859143120848238329)
                  ·
                    rfl

theorem cell23_5673629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_5673629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673629 prefixEnd_5673629 := by exact prefixLift 5673629
  have htrace : WordTrace (prefixWord ++ tailWord_5673629) baseStart_5673629 baseEnd_5673629 := by
    simpa [prefixWord, tailWord_5673629, baseEnd_5673629] using wordTrace_append hprefix tailTrace_5673629
  have hstable : (prefixWord ++ tailWord_5673629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673629).length < 2 ^ (prefixWord ++ tailWord_5673629).sum := by decide
  have hdescent : baseEnd_5673629 < baseStart_5673629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673713 : List Nat := [1, 2, 2, 2, 2, 2, 1, 4, 3, 2, 2]
def baseStart_5673713 : Nat := 118140960795 + 5673713 * 2 ^ 59
def prefixEnd_5673713 : Nat := 4983230072969 + 3 ^ 40 * 5673713 * 2
def baseEnd_5673713 : Nat := 2913341864663065305494575

theorem tailTrace_5673713 : CollatzResearch.WordTrace tailWord_5673713 prefixEnd_5673713 2913341864663065305494575 := by
  unfold tailWord_5673713
  simp only [CollatzResearch.WordTrace]
  refine ⟨206937313694114268880033793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137958209129409512586689195 206937313694114268880033793)
  ·
    refine ⟨155202985270585701660025345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206937313694114268880033793 155202985270585701660025345)
    ·
      refine ⟨116402238952939276245019009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155202985270585701660025345 116402238952939276245019009)
      ·
        refine ⟨87301679214704457183764257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116402238952939276245019009 87301679214704457183764257)
        ·
          refine ⟨65476259411028342887823193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87301679214704457183764257 65476259411028342887823193)
          ·
            refine ⟨49107194558271257165867395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65476259411028342887823193 49107194558271257165867395)
            ·
              refine ⟨73660791837406885748801093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49107194558271257165867395 73660791837406885748801093)
              ·
                refine ⟨13811398469513791077900205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73660791837406885748801093 13811398469513791077900205)
                ·
                  refine ⟨5179274426067671654212577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13811398469513791077900205 5179274426067671654212577)
                  ·
                    refine ⟨3884455819550753740659433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5179274426067671654212577 3884455819550753740659433)
                    ·
                      refine ⟨2913341864663065305494575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3884455819550753740659433 2913341864663065305494575)
                      ·
                        rfl

theorem cell23_5673713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_5673713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673713 prefixEnd_5673713 := by exact prefixLift 5673713
  have htrace : WordTrace (prefixWord ++ tailWord_5673713) baseStart_5673713 baseEnd_5673713 := by
    simpa [prefixWord, tailWord_5673713, baseEnd_5673713] using wordTrace_append hprefix tailTrace_5673713
  have hstable : (prefixWord ++ tailWord_5673713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673713).length < 2 ^ (prefixWord ++ tailWord_5673713).sum := by decide
  have hdescent : baseEnd_5673713 < baseStart_5673713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673747 : List Nat := [1, 1, 1, 2, 1, 3, 7, 2, 1, 2, 2]
def baseStart_5673747 : Nat := 118140960795 + 5673747 * 2 ^ 59
def prefixEnd_5673747 : Nat := 4983230072969 + 3 ^ 40 * 5673747 * 2
def baseEnd_5673747 : Nat := 2913359323005318172469419

theorem tailTrace_5673747 : CollatzResearch.WordTrace tailWord_5673747 prefixEnd_5673747 2913359323005318172469419 := by
  unfold tailWord_5673747
  simp only [CollatzResearch.WordTrace]
  refine ⟨206938553775991092686771495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137959035850660728457847663 206938553775991092686771495)
  ·
    refine ⟨310407830663986639030157243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206938553775991092686771495 310407830663986639030157243)
    ·
      refine ⟨465611745995979958545235865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310407830663986639030157243 465611745995979958545235865)
      ·
        refine ⟨349208809496984968908926899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 465611745995979958545235865 349208809496984968908926899)
        ·
          refine ⟨523813214245477453363390349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349208809496984968908926899 523813214245477453363390349)
          ·
            refine ⟨196429955342054045011271381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 523813214245477453363390349 196429955342054045011271381)
            ·
              refine ⟨4603827078329391679951673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 196429955342054045011271381 4603827078329391679951673)
              ·
                refine ⟨3452870308747043759963755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4603827078329391679951673 3452870308747043759963755)
                ·
                  refine ⟨5179305463120565639945633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3452870308747043759963755 5179305463120565639945633)
                  ·
                    refine ⟨3884479097340424229959225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5179305463120565639945633 3884479097340424229959225)
                    ·
                      refine ⟨2913359323005318172469419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3884479097340424229959225 2913359323005318172469419)
                      ·
                        rfl

theorem cell23_5673747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 1, 2, 2].length) (baseStart_5673747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673747 prefixEnd_5673747 := by exact prefixLift 5673747
  have htrace : WordTrace (prefixWord ++ tailWord_5673747) baseStart_5673747 baseEnd_5673747 := by
    simpa [prefixWord, tailWord_5673747, baseEnd_5673747] using wordTrace_append hprefix tailTrace_5673747
  have hstable : (prefixWord ++ tailWord_5673747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673747).length < 2 ^ (prefixWord ++ tailWord_5673747).sum := by decide
  have hdescent : baseEnd_5673747 < baseStart_5673747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673749 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 2, 7]
def baseStart_5673749 : Nat := 118140960795 + 5673749 * 2 ^ 59
def prefixEnd_5673749 : Nat := 4983230072969 + 3 ^ 40 * 5673749 * 2
def baseEnd_5673749 : Nat := 971120116655542388214803

theorem tailTrace_5673749 : CollatzResearch.WordTrace tailWord_5673749 prefixEnd_5673749 971120116655542388214803 := by
  unfold tailWord_5673749
  simp only [CollatzResearch.WordTrace]
  refine ⟨206938626721983847028344301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137959084481322564685562867 206938626721983847028344301)
  ·
    refine ⟨77601985020743942635629113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206938626721983847028344301 77601985020743942635629113)
    ·
      refine ⟨58201488765557956976721835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77601985020743942635629113 58201488765557956976721835)
      ·
        refine ⟨87302233148336935465082753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58201488765557956976721835 87302233148336935465082753)
        ·
          refine ⟨65476674861252701598812065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87302233148336935465082753 65476674861252701598812065)
          ·
            refine ⟨49107506145939526199109049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65476674861252701598812065 49107506145939526199109049)
            ·
              refine ⟨36830629609454644649331787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49107506145939526199109049 36830629609454644649331787)
              ·
                refine ⟨55245944414181966973997681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36830629609454644649331787 55245944414181966973997681)
                ·
                  refine ⟨41434458310636475230498261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55245944414181966973997681 41434458310636475230498261)
                  ·
                    refine ⟨971120116655542388214803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41434458310636475230498261 971120116655542388214803)
                    ·
                      rfl

theorem cell23_5673749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_5673749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673749 prefixEnd_5673749 := by exact prefixLift 5673749
  have htrace : WordTrace (prefixWord ++ tailWord_5673749) baseStart_5673749 baseEnd_5673749 := by
    simpa [prefixWord, tailWord_5673749, baseEnd_5673749] using wordTrace_append hprefix tailTrace_5673749
  have hstable : (prefixWord ++ tailWord_5673749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673749).length < 2 ^ (prefixWord ++ tailWord_5673749).sum := by decide
  have hdescent : baseEnd_5673749 < baseStart_5673749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673769 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 2, 3, 4]
def baseStart_5673769 : Nat := 118140960795 + 5673769 * 2 ^ 59
def prefixEnd_5673769 : Nat := 4983230072969 + 3 ^ 40 * 5673769 * 2
def baseEnd_5673769 : Nat := 2913370619579717086394317

theorem tailTrace_5673769 : CollatzResearch.WordTrace tailWord_5673769 prefixEnd_5673769 2913370619579717086394317 := by
  unfold tailWord_5673769
  simp only [CollatzResearch.WordTrace]
  refine ⟨206939356181911390444072361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137959570787940926962714907 206939356181911390444072361)
  ·
    refine ⟨155204517136433542833054271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206939356181911390444072361 155204517136433542833054271)
    ·
      refine ⟨232806775704650314249581407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155204517136433542833054271 232806775704650314249581407)
      ·
        refine ⟨349210163556975471374372111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232806775704650314249581407 349210163556975471374372111)
        ·
          refine ⟨523815245335463207061558167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349210163556975471374372111 523815245335463207061558167)
          ·
            refine ⟨785722868003194810592337251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523815245335463207061558167 785722868003194810592337251)
            ·
              refine ⟨1178584302004792215888505877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785722868003194810592337251 1178584302004792215888505877)
              ·
                refine ⟨55246139156474635119773713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1178584302004792215888505877 55246139156474635119773713)
                ·
                  refine ⟨41434604367355976339830285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55246139156474635119773713 41434604367355976339830285)
                  ·
                    refine ⟨15537976637758491127436357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41434604367355976339830285 15537976637758491127436357)
                    ·
                      refine ⟨2913370619579717086394317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15537976637758491127436357 2913370619579717086394317)
                      ·
                        rfl

theorem cell23_5673769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_5673769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673769 prefixEnd_5673769 := by exact prefixLift 5673769
  have htrace : WordTrace (prefixWord ++ tailWord_5673769) baseStart_5673769 baseEnd_5673769 := by
    simpa [prefixWord, tailWord_5673769, baseEnd_5673769] using wordTrace_append hprefix tailTrace_5673769
  have hstable : (prefixWord ++ tailWord_5673769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673769).length < 2 ^ (prefixWord ++ tailWord_5673769).sum := by decide
  have hdescent : baseEnd_5673769 < baseStart_5673769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673780 : List Nat := [2, 5, 1, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_5673780 : Nat := 118140960795 + 5673780 * 2 ^ 59
def prefixEnd_5673780 : Nat := 4983230072969 + 3 ^ 40 * 5673780 * 2
def baseEnd_5673780 : Nat := 2913376267866916543356767

theorem tailTrace_5673780 : CollatzResearch.WordTrace tailWord_5673780 prefixEnd_5673780 2913376267866916543356767 := by
  unfold tailWord_5673780
  simp only [CollatzResearch.WordTrace]
  refine ⟨103469878692435769661361397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137959838256581026215148529 103469878692435769661361397)
  ·
    refine ⟨9700301127415853405752631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103469878692435769661361397 9700301127415853405752631)
    ·
      refine ⟨14550451691123780108628947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9700301127415853405752631 14550451691123780108628947)
      ·
        refine ⟨21825677536685670162943421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14550451691123780108628947 21825677536685670162943421)
        ·
          refine ⟨8184629076257126311103783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21825677536685670162943421 8184629076257126311103783)
          ·
            refine ⟨12276943614385689466655675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8184629076257126311103783 12276943614385689466655675)
            ·
              refine ⟨18415415421578534199983513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12276943614385689466655675 18415415421578534199983513)
              ·
                refine ⟨13811561566183900649987635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18415415421578534199983513 13811561566183900649987635)
                ·
                  refine ⟨20717342349275850974981453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13811561566183900649987635 20717342349275850974981453)
                  ·
                    refine ⟨7769003380978444115618045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20717342349275850974981453 7769003380978444115618045)
                    ·
                      refine ⟨2913376267866916543356767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7769003380978444115618045 2913376267866916543356767)
                      ·
                        rfl

theorem cell23_5673780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_5673780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673780 prefixEnd_5673780 := by exact prefixLift 5673780
  have htrace : WordTrace (prefixWord ++ tailWord_5673780) baseStart_5673780 baseEnd_5673780 := by
    simpa [prefixWord, tailWord_5673780, baseEnd_5673780] using wordTrace_append hprefix tailTrace_5673780
  have hstable : (prefixWord ++ tailWord_5673780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673780).length < 2 ^ (prefixWord ++ tailWord_5673780).sum := by decide
  have hdescent : baseEnd_5673780 < baseStart_5673780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673799 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_5673799 : Nat := 118140960795 + 5673799 * 2 ^ 59
def prefixEnd_5673799 : Nat := 4983230072969 + 3 ^ 40 * 5673799 * 2
def baseEnd_5673799 : Nat := 2913386023999351969019179

theorem tailTrace_5673799 : CollatzResearch.WordTrace tailWord_5673799 prefixEnd_5673799 2913386023999351969019179 := by
  unfold tailWord_5673799
  simp only [CollatzResearch.WordTrace]
  refine ⟨206940450371802705567664451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137960300247868470378442967 206940450371802705567664451)
  ·
    refine ⟨310410675557704058351496677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206940450371802705567664451 310410675557704058351496677)
    ·
      refine ⟨58202001667069510940905627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310410675557704058351496677 58202001667069510940905627)
      ·
        refine ⟨87303002500604266411358441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58202001667069510940905627 87303002500604266411358441)
        ·
          refine ⟨65477251875453199808518831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87303002500604266411358441 65477251875453199808518831)
          ·
            refine ⟨98215877813179799712778247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65477251875453199808518831 98215877813179799712778247)
            ·
              refine ⟨147323816719769699569167371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98215877813179799712778247 147323816719769699569167371)
              ·
                refine ⟨220985725079654549353751057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147323816719769699569167371 220985725079654549353751057)
                ·
                  refine ⟨165739293809740912015313293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220985725079654549353751057 165739293809740912015313293)
                  ·
                    refine ⟨62152235178652842005742485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165739293809740912015313293 62152235178652842005742485)
                    ·
                      refine ⟨2913386023999351969019179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62152235178652842005742485 2913386023999351969019179)
                      ·
                        rfl

theorem cell23_5673799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_5673799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673799 prefixEnd_5673799 := by exact prefixLift 5673799
  have htrace : WordTrace (prefixWord ++ tailWord_5673799) baseStart_5673799 baseEnd_5673799 := by
    simpa [prefixWord, tailWord_5673799, baseEnd_5673799] using wordTrace_append hprefix tailTrace_5673799
  have hstable : (prefixWord ++ tailWord_5673799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673799).length < 2 ^ (prefixWord ++ tailWord_5673799).sum := by decide
  have hdescent : baseEnd_5673799 < baseStart_5673799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673820 : List Nat := [2, 2, 4, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_5673820 : Nat := 118140960795 + 5673820 * 2 ^ 59
def prefixEnd_5673820 : Nat := 4983230072969 + 3 ^ 40 * 5673820 * 2
def baseEnd_5673820 : Nat := 2913396807093096386856583

theorem tailTrace_5673820 : CollatzResearch.WordTrace tailWord_5673820 prefixEnd_5673820 2913396807093096386856583 := by
  unfold tailWord_5673820
  simp only [CollatzResearch.WordTrace]
  refine ⟨103470608152363313077089457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137960810869817750769452609 103470608152363313077089457)
  ·
    refine ⟨77602956114272484807817093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103470608152363313077089457 77602956114272484807817093)
    ·
      refine ⟨14550554271426090901465705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77602956114272484807817093 14550554271426090901465705)
      ·
        refine ⟨10912915703569568176099279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14550554271426090901465705 10912915703569568176099279)
        ·
          refine ⟨16369373555354352264148919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10912915703569568176099279 16369373555354352264148919)
          ·
            refine ⟨24554060333031528396223379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16369373555354352264148919 24554060333031528396223379)
            ·
              refine ⟨36831090499547292594335069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24554060333031528396223379 36831090499547292594335069)
              ·
                refine ⟨13811658937330234722875651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36831090499547292594335069 13811658937330234722875651)
                ·
                  refine ⟨20717488405995352084313477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13811658937330234722875651 20717488405995352084313477)
                  ·
                    refine ⟨3884529076124128515808777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20717488405995352084313477 3884529076124128515808777)
                    ·
                      refine ⟨2913396807093096386856583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3884529076124128515808777 2913396807093096386856583)
                      ·
                        rfl

theorem cell23_5673820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_5673820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673820 prefixEnd_5673820 := by exact prefixLift 5673820
  have htrace : WordTrace (prefixWord ++ tailWord_5673820) baseStart_5673820 baseEnd_5673820 := by
    simpa [prefixWord, tailWord_5673820, baseEnd_5673820] using wordTrace_append hprefix tailTrace_5673820
  have hstable : (prefixWord ++ tailWord_5673820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673820).length < 2 ^ (prefixWord ++ tailWord_5673820).sum := by decide
  have hdescent : baseEnd_5673820 < baseStart_5673820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673836 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 3]
def baseStart_5673836 : Nat := 118140960795 + 5673836 * 2 ^ 59
def prefixEnd_5673836 : Nat := 4983230072969 + 3 ^ 40 * 5673836 * 2
def baseEnd_5673836 : Nat := 2913405022783568324256509

theorem tailTrace_5673836 : CollatzResearch.WordTrace tailWord_5673836 prefixEnd_5673836 2913405022783568324256509 := by
  unfold tailWord_5673836
  simp only [CollatzResearch.WordTrace]
  refine ⟨103470899936334330443380681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137961199915112440591174241 103470899936334330443380681)
  ·
    refine ⟨77603174952250747832535511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103470899936334330443380681 77603174952250747832535511)
    ·
      refine ⟨116404762428376121748803267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77603174952250747832535511 116404762428376121748803267)
      ·
        refine ⟨174607143642564182623204901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116404762428376121748803267 174607143642564182623204901)
        ·
          refine ⟨32738839432980784241850919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174607143642564182623204901 32738839432980784241850919)
          ·
            refine ⟨49108259149471176362776379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32738839432980784241850919 49108259149471176362776379)
            ·
              refine ⟨73662388724206764544164569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49108259149471176362776379 73662388724206764544164569)
              ·
                refine ⟨55246791543155073408123427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73662388724206764544164569 55246791543155073408123427)
                ·
                  refine ⟨82870187314732610112185141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55246791543155073408123427 82870187314732610112185141)
                  ·
                    refine ⟨7769080060756182198017357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82870187314732610112185141 7769080060756182198017357)
                    ·
                      refine ⟨2913405022783568324256509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7769080060756182198017357 2913405022783568324256509)
                      ·
                        rfl

theorem cell23_5673836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_5673836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673836 prefixEnd_5673836 := by exact prefixLift 5673836
  have htrace : WordTrace (prefixWord ++ tailWord_5673836) baseStart_5673836 baseEnd_5673836 := by
    simpa [prefixWord, tailWord_5673836, baseEnd_5673836] using wordTrace_append hprefix tailTrace_5673836
  have hstable : (prefixWord ++ tailWord_5673836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673836).length < 2 ^ (prefixWord ++ tailWord_5673836).sum := by decide
  have hdescent : baseEnd_5673836 < baseStart_5673836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673854 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_5673854 : Nat := 118140960795 + 5673854 * 2 ^ 59
def prefixEnd_5673854 : Nat := 4983230072969 + 3 ^ 40 * 5673854 * 2
def baseEnd_5673854 : Nat := 2913414265435349253831427

theorem tailTrace_5673854 : CollatzResearch.WordTrace tailWord_5673854 prefixEnd_5673854 2913414265435349253831427 := by
  unfold tailWord_5673854
  simp only [CollatzResearch.WordTrace]
  refine ⟨25867807048325431245114577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137961637591068966640611077 25867807048325431245114577)
  ·
    refine ⟨19400855286244073433835933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25867807048325431245114577 19400855286244073433835933)
    ·
      refine ⟨7275320732341527537688475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19400855286244073433835933 7275320732341527537688475)
      ·
        refine ⟨10912981098512291306532713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7275320732341527537688475 10912981098512291306532713)
        ·
          refine ⟨8184735823884218479899535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10912981098512291306532713 8184735823884218479899535)
          ·
            refine ⟨12277103735826327719849303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8184735823884218479899535 12277103735826327719849303)
            ·
              refine ⟨18415655603739491579773955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12277103735826327719849303 18415655603739491579773955)
              ·
                refine ⟨27623483405609237369660933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18415655603739491579773955 27623483405609237369660933)
                ·
                  refine ⟨5179403138551732006811425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27623483405609237369660933 5179403138551732006811425)
                  ·
                    refine ⟨3884552353913799005108569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5179403138551732006811425 3884552353913799005108569)
                    ·
                      refine ⟨2913414265435349253831427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3884552353913799005108569 2913414265435349253831427)
                      ·
                        rfl

theorem cell23_5673854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_5673854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673854 prefixEnd_5673854 := by exact prefixLift 5673854
  have htrace : WordTrace (prefixWord ++ tailWord_5673854) baseStart_5673854 baseEnd_5673854 := by
    simpa [prefixWord, tailWord_5673854, baseEnd_5673854] using wordTrace_append hprefix tailTrace_5673854
  have hstable : (prefixWord ++ tailWord_5673854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673854).length < 2 ^ (prefixWord ++ tailWord_5673854).sum := by decide
  have hdescent : baseEnd_5673854 < baseStart_5673854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673913 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 4, 2, 3]
def baseStart_5673913 : Nat := 118140960795 + 5673913 * 2 ^ 59
def prefixEnd_5673913 : Nat := 4983230072969 + 3 ^ 40 * 5673913 * 2
def baseEnd_5673913 : Nat := 2913444560793964522993655

theorem tailTrace_5673913 : CollatzResearch.WordTrace tailWord_5673913 prefixEnd_5673913 2913444560793964522993655 := by
  unfold tailWord_5673913
  simp only [CollatzResearch.WordTrace]
  refine ⟨206944608293389703037314393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137963072195593135358209595 206944608293389703037314393)
  ·
    refine ⟨155208456220042277277985795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206944608293389703037314393 155208456220042277277985795)
    ·
      refine ⟨232812684330063415916978693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155208456220042277277985795 232812684330063415916978693)
      ·
        refine ⟨43652378311886890484433505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232812684330063415916978693 43652378311886890484433505)
        ·
          refine ⟨32739283733915167863325129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43652378311886890484433505 32739283733915167863325129)
          ·
            refine ⟨24554462800436375897493847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32739283733915167863325129 24554462800436375897493847)
            ·
              refine ⟨36831694200654563846240771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24554462800436375897493847 36831694200654563846240771)
              ·
                refine ⟨55247541300981845769361157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36831694200654563846240771 55247541300981845769361157)
                ·
                  refine ⟨10358913993934096081755217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55247541300981845769361157 10358913993934096081755217)
                  ·
                    refine ⟨7769185495450572061316413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10358913993934096081755217 7769185495450572061316413)
                    ·
                      refine ⟨2913444560793964522993655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7769185495450572061316413 2913444560793964522993655)
                      ·
                        rfl

theorem cell23_5673913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_5673913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673913 prefixEnd_5673913 := by exact prefixLift 5673913
  have htrace : WordTrace (prefixWord ++ tailWord_5673913) baseStart_5673913 baseEnd_5673913 := by
    simpa [prefixWord, tailWord_5673913, baseEnd_5673913] using wordTrace_append hprefix tailTrace_5673913
  have hstable : (prefixWord ++ tailWord_5673913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673913).length < 2 ^ (prefixWord ++ tailWord_5673913).sum := by decide
  have hdescent : baseEnd_5673913 < baseStart_5673913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673920 : List Nat := [2, 1, 1, 2, 3, 5, 1, 1, 3, 4]
def baseStart_5673920 : Nat := 118140960795 + 5673920 * 2 ^ 59
def prefixEnd_5673920 : Nat := 4983230072969 + 3 ^ 40 * 5673920 * 2
def baseEnd_5673920 : Nat := 971149385052848665202041

theorem tailTrace_5673920 : CollatzResearch.WordTrace tailWord_5673920 prefixEnd_5673920 971149385052848665202041 := by
  unfold tailWord_5673920
  simp only [CollatzResearch.WordTrace]
  refine ⟨103472431802182171616409607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137963242402909562155212809 103472431802182171616409607)
  ·
    refine ⟨155208647703273257424614411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103472431802182171616409607 155208647703273257424614411)
    ·
      refine ⟨232812971554909886136921617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155208647703273257424614411 232812971554909886136921617)
      ·
        refine ⟨174609728666182414602691213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232812971554909886136921617 174609728666182414602691213)
        ·
          refine ⟨65478648249818405476009205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174609728666182414602691213 65478648249818405476009205)
          ·
            refine ⟨6138623273420475513375863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65478648249818405476009205 6138623273420475513375863)
            ·
              refine ⟨9207934910130713270063795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6138623273420475513375863 9207934910130713270063795)
              ·
                refine ⟨13811902365196069905095693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9207934910130713270063795 13811902365196069905095693)
                ·
                  refine ⟨5179463386948526214410885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13811902365196069905095693 5179463386948526214410885)
                  ·
                    refine ⟨971149385052848665202041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5179463386948526214410885 971149385052848665202041)
                    ·
                      rfl

theorem cell23_5673920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 3, 4].length) (baseStart_5673920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673920 prefixEnd_5673920 := by exact prefixLift 5673920
  have htrace : WordTrace (prefixWord ++ tailWord_5673920) baseStart_5673920 baseEnd_5673920 := by
    simpa [prefixWord, tailWord_5673920, baseEnd_5673920] using wordTrace_append hprefix tailTrace_5673920
  have hstable : (prefixWord ++ tailWord_5673920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673920).length < 2 ^ (prefixWord ++ tailWord_5673920).sum := by decide
  have hdescent : baseEnd_5673920 < baseStart_5673920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673956 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_5673956 : Nat := 118140960795 + 5673956 * 2 ^ 59
def prefixEnd_5673956 : Nat := 4983230072969 + 3 ^ 40 * 5673956 * 2
def baseEnd_5673956 : Nat := 2913466640462107854755957

theorem tailTrace_5673956 : CollatzResearch.WordTrace tailWord_5673956 prefixEnd_5673956 2913466640462107854755957 := by
  unfold tailWord_5673956
  simp only [CollatzResearch.WordTrace]
  refine ⟨103473088316116960690564861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137964117754822614254086481 103473088316116960690564861)
  ·
    refine ⟨38802408118543860258961823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103473088316116960690564861 38802408118543860258961823)
    ·
      refine ⟨58203612177815790388442735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38802408118543860258961823 58203612177815790388442735)
      ·
        refine ⟨87305418266723685582664103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58203612177815790388442735 87305418266723685582664103)
        ·
          refine ⟨130958127400085528373996155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87305418266723685582664103 130958127400085528373996155)
          ·
            refine ⟨196437191100128292560994233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130958127400085528373996155 196437191100128292560994233)
            ·
              refine ⟨147327893325096219420745675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196437191100128292560994233 147327893325096219420745675)
              ·
                refine ⟨220991839987644329131118513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147327893325096219420745675 220991839987644329131118513)
                ·
                  refine ⟨165743879990733246848338885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220991839987644329131118513 165743879990733246848338885)
                  ·
                    refine ⟨31076977498262483784063541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 165743879990733246848338885 31076977498262483784063541)
                    ·
                      refine ⟨2913466640462107854755957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31076977498262483784063541 2913466640462107854755957)
                      ·
                        rfl

theorem cell23_5673956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_5673956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673956 prefixEnd_5673956 := by exact prefixLift 5673956
  have htrace : WordTrace (prefixWord ++ tailWord_5673956) baseStart_5673956 baseEnd_5673956 := by
    simpa [prefixWord, tailWord_5673956, baseEnd_5673956] using wordTrace_append hprefix tailTrace_5673956
  have hstable : (prefixWord ++ tailWord_5673956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673956).length < 2 ^ (prefixWord ++ tailWord_5673956).sum := by decide
  have hdescent : baseEnd_5673956 < baseStart_5673956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673976 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 5, 6]
def baseStart_5673976 : Nat := 118140960795 + 5673976 * 2 ^ 59
def prefixEnd_5673976 : Nat := 4983230072969 + 3 ^ 40 * 5673976 * 2
def baseEnd_5673976 : Nat := 971158970025065925501955

theorem tailTrace_5673976 : CollatzResearch.WordTrace tailWord_5673976 prefixEnd_5673976 971158970025065925501955 := by
  unfold tailWord_5673976
  simp only [CollatzResearch.WordTrace]
  refine ⟨103473453046080732398428891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137964604061440976531238521 103473453046080732398428891)
  ·
    refine ⟨155210179569121098597643337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103473453046080732398428891 155210179569121098597643337)
    ·
      refine ⟨116407634676840823948232503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155210179569121098597643337 116407634676840823948232503)
      ·
        refine ⟨174611452015261235922348755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116407634676840823948232503 174611452015261235922348755)
        ·
          refine ⟨261917178022891853883523133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174611452015261235922348755 261917178022891853883523133)
          ·
            refine ⟨98218941758584445206321175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261917178022891853883523133 98218941758584445206321175)
            ·
              refine ⟨147328412637876667809481763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98218941758584445206321175 147328412637876667809481763)
              ·
                refine ⟨220992618956815001714222645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147328412637876667809481763 220992618956815001714222645)
                ·
                  refine ⟨20718058027201406410708373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 220992618956815001714222645 20718058027201406410708373)
                  ·
                    refine ⟨971158970025065925501955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20718058027201406410708373 971158970025065925501955)
                    ·
                      rfl

theorem cell23_5673976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_5673976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673976 prefixEnd_5673976 := by exact prefixLift 5673976
  have htrace : WordTrace (prefixWord ++ tailWord_5673976) baseStart_5673976 baseEnd_5673976 := by
    simpa [prefixWord, tailWord_5673976, baseEnd_5673976] using wordTrace_append hprefix tailTrace_5673976
  have hstable : (prefixWord ++ tailWord_5673976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673976).length < 2 ^ (prefixWord ++ tailWord_5673976).sum := by decide
  have hdescent : baseEnd_5673976 < baseStart_5673976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673977 : List Nat := [1, 2, 1, 3, 1, 3, 3, 4, 1, 1, 3]
def baseStart_5673977 : Nat := 118140960795 + 5673977 * 2 ^ 59
def prefixEnd_5673977 : Nat := 4983230072969 + 3 ^ 40 * 5673977 * 2
def baseEnd_5673977 : Nat := 2913477423555852272593361

theorem tailTrace_5673977 : CollatzResearch.WordTrace tailWord_5673977 prefixEnd_5673977 2913477423555852272593361 := by
  unfold tailWord_5673977
  simp only [CollatzResearch.WordTrace]
  refine ⟨206946942565157841967644185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137964628376771894645096123 206946942565157841967644185)
  ·
    refine ⟨155210206923868381475733139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206946942565157841967644185 155210206923868381475733139)
    ·
      refine ⟨232815310385802572213599709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155210206923868381475733139 232815310385802572213599709)
      ·
        refine ⟨87305741394675964580099891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232815310385802572213599709 87305741394675964580099891)
        ·
          refine ⟨130958612092013946870149837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87305741394675964580099891 130958612092013946870149837)
          ·
            refine ⟨49109479534505230076306189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130958612092013946870149837 49109479534505230076306189)
            ·
              refine ⟨18416054825439461278614821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49109479534505230076306189 18416054825439461278614821)
              ·
                refine ⟨3453010279769898989740279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18416054825439461278614821 3453010279769898989740279)
                ·
                  refine ⟨5179515419654848484610419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3453010279769898989740279 5179515419654848484610419)
                  ·
                    refine ⟨7769273129482272726915629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5179515419654848484610419 7769273129482272726915629)
                    ·
                      refine ⟨2913477423555852272593361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7769273129482272726915629 2913477423555852272593361)
                      ·
                        rfl

theorem cell23_5673977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_5673977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673977 prefixEnd_5673977 := by exact prefixLift 5673977
  have htrace : WordTrace (prefixWord ++ tailWord_5673977) baseStart_5673977 baseEnd_5673977 := by
    simpa [prefixWord, tailWord_5673977, baseEnd_5673977] using wordTrace_append hprefix tailTrace_5673977
  have hstable : (prefixWord ++ tailWord_5673977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673977).length < 2 ^ (prefixWord ++ tailWord_5673977).sum := by decide
  have hdescent : baseEnd_5673977 < baseStart_5673977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5673983 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 4, 6, 2]
def baseStart_5673983 : Nat := 118140960795 + 5673983 * 2 ^ 59
def prefixEnd_5673983 : Nat := 4983230072969 + 3 ^ 40 * 5673983 * 2
def baseEnd_5673983 : Nat := 2913480504439779249118333

theorem tailTrace_5673983 : CollatzResearch.WordTrace tailWord_5673983 prefixEnd_5673983 2913480504439779249118333 := by
  unfold tailWord_5673983
  simp only [CollatzResearch.WordTrace]
  refine ⟨206947161403136104992362603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137964774268757403328241735 206947161403136104992362603)
  ·
    refine ⟨310420742104704157488543905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206947161403136104992362603 310420742104704157488543905)
    ·
      refine ⟨232815556578528118116407929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310420742104704157488543905 232815556578528118116407929)
      ·
        refine ⟨174611667433896088587305947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232815556578528118116407929 174611667433896088587305947)
        ·
          refine ⟨261917501150844132880958921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174611667433896088587305947 261917501150844132880958921)
          ·
            refine ⟨196438125863133099660719191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261917501150844132880958921 196438125863133099660719191)
            ·
              refine ⟨294657188794699649491078787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196438125863133099660719191 294657188794699649491078787)
              ·
                refine ⟨441985783192049474236618181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294657188794699649491078787 441985783192049474236618181)
                ·
                  refine ⟨82872334348509276419365909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441985783192049474236618181 82872334348509276419365909)
                  ·
                    refine ⟨3884640672586372332157777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82872334348509276419365909 3884640672586372332157777)
                    ·
                      refine ⟨2913480504439779249118333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3884640672586372332157777 2913480504439779249118333)
                      ·
                        rfl

theorem cell23_5673983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 6, 2].length) (baseStart_5673983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5673983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5673983 prefixEnd_5673983 := by exact prefixLift 5673983
  have htrace : WordTrace (prefixWord ++ tailWord_5673983) baseStart_5673983 baseEnd_5673983 := by
    simpa [prefixWord, tailWord_5673983, baseEnd_5673983] using wordTrace_append hprefix tailTrace_5673983
  have hstable : (prefixWord ++ tailWord_5673983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5673983).length < 2 ^ (prefixWord ++ tailWord_5673983).sum := by decide
  have hdescent : baseEnd_5673983 < baseStart_5673983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5673983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674017 : List Nat := [1, 2, 3, 2, 3, 1, 4, 1, 1, 1, 4]
def baseStart_5674017 : Nat := 118140960795 + 5674017 * 2 ^ 59
def prefixEnd_5674017 : Nat := 4983230072969 + 3 ^ 40 * 5674017 * 2
def baseEnd_5674017 : Nat := 2913497962782032116093177

theorem tailTrace_5674017 : CollatzResearch.WordTrace tailWord_5674017 prefixEnd_5674017 2913497962782032116093177 := by
  unfold tailWord_5674017
  simp only [CollatzResearch.WordTrace]
  refine ⟨206948401485012928799100305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137965600990008619199400203 206948401485012928799100305)
  ·
    refine ⟨155211301113759696599325229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206948401485012928799100305 155211301113759696599325229)
    ·
      refine ⟨58204237917659886224746961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155211301113759696599325229 58204237917659886224746961)
      ·
        refine ⟨43653178438244914668560221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58204237917659886224746961 43653178438244914668560221)
        ·
          refine ⟨16369941914341843000710083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43653178438244914668560221 16369941914341843000710083)
          ·
            refine ⟨24554912871512764501065125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16369941914341843000710083 24554912871512764501065125)
            ·
              refine ⟨4604046163408643343949711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24554912871512764501065125 4604046163408643343949711)
              ·
                refine ⟨6906069245112965015924567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4604046163408643343949711 6906069245112965015924567)
                ·
                  refine ⟨10359103867669447523886851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6906069245112965015924567 10359103867669447523886851)
                  ·
                    refine ⟨15538655801504171285830277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10359103867669447523886851 15538655801504171285830277)
                    ·
                      refine ⟨2913497962782032116093177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15538655801504171285830277 2913497962782032116093177)
                      ·
                        rfl

theorem cell23_5674017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_5674017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674017 prefixEnd_5674017 := by exact prefixLift 5674017
  have htrace : WordTrace (prefixWord ++ tailWord_5674017) baseStart_5674017 baseEnd_5674017 := by
    simpa [prefixWord, tailWord_5674017, baseEnd_5674017] using wordTrace_append hprefix tailTrace_5674017
  have hstable : (prefixWord ++ tailWord_5674017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674017).length < 2 ^ (prefixWord ++ tailWord_5674017).sum := by decide
  have hdescent : baseEnd_5674017 < baseStart_5674017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674034 : List Nat := [3, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2]
def baseStart_5674034 : Nat := 118140960795 + 5674034 * 2 ^ 59
def prefixEnd_5674034 : Nat := 4983230072969 + 3 ^ 40 * 5674034 * 2
def baseEnd_5674034 : Nat := 2913506691953158549580599

theorem tailTrace_5674034 : CollatzResearch.WordTrace tailWord_5674034 prefixEnd_5674034 2913506691953158549580599 := by
  unfold tailWord_5674034
  simp only [CollatzResearch.WordTrace]
  refine ⟨51737255381487835175617289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137966014350634227134979437 51737255381487835175617289)
  ·
    refine ⟨38802941536115876381712967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51737255381487835175617289 38802941536115876381712967)
    ·
      refine ⟨58204412304173814572569451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38802941536115876381712967 58204412304173814572569451)
      ·
        refine ⟨87306618456260721858854177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58204412304173814572569451 87306618456260721858854177)
        ·
          refine ⟨65479963842195541394140633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87306618456260721858854177 65479963842195541394140633)
          ·
            refine ⟨49109972881646656045605475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65479963842195541394140633 49109972881646656045605475)
            ·
              refine ⟨73664959322469984068408213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49109972881646656045605475 73664959322469984068408213)
              ·
                refine ⟨3453044968240780503206635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73664959322469984068408213 3453044968240780503206635)
                ·
                  refine ⟨5179567452361170754809953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3453044968240780503206635 5179567452361170754809953)
                  ·
                    refine ⟨3884675589270878066107465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5179567452361170754809953 3884675589270878066107465)
                    ·
                      refine ⟨2913506691953158549580599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3884675589270878066107465 2913506691953158549580599)
                      ·
                        rfl

theorem cell23_5674034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_5674034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674034 prefixEnd_5674034 := by exact prefixLift 5674034
  have htrace : WordTrace (prefixWord ++ tailWord_5674034) baseStart_5674034 baseEnd_5674034 := by
    simpa [prefixWord, tailWord_5674034, baseEnd_5674034] using wordTrace_append hprefix tailTrace_5674034
  have hstable : (prefixWord ++ tailWord_5674034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674034).length < 2 ^ (prefixWord ++ tailWord_5674034).sum := by decide
  have hdescent : baseEnd_5674034 < baseStart_5674034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674054 : List Nat := [6, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_5674054 : Nat := 118140960795 + 5674054 * 2 ^ 59
def prefixEnd_5674054 : Nat := 4983230072969 + 3 ^ 40 * 5674054 * 2
def baseEnd_5674054 : Nat := 2913516961566248471330507

theorem tailTrace_5674054 : CollatzResearch.WordTrace tailWord_5674054 prefixEnd_5674054 2913516961566248471330507 := by
  unfold tailWord_5674054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6467179718308715128693663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 137966500657252589412131477 6467179718308715128693663)
  ·
    refine ⟨9700769577463072693040495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6467179718308715128693663 9700769577463072693040495)
    ·
      refine ⟨14551154366194609039560743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9700769577463072693040495 14551154366194609039560743)
      ·
        refine ⟨21826731549291913559341115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14551154366194609039560743 21826731549291913559341115)
        ·
          refine ⟨32740097323937870339011673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21826731549291913559341115 32740097323937870339011673)
          ·
            refine ⟨24555072992953402754258755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32740097323937870339011673 24555072992953402754258755)
            ·
              refine ⟨36832609489430104131388133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24555072992953402754258755 36832609489430104131388133)
              ·
                refine ⟨6906114279268144524635275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36832609489430104131388133 6906114279268144524635275)
                ·
                  refine ⟨10359171418902216786952913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6906114279268144524635275 10359171418902216786952913)
                  ·
                    refine ⟨7769378564176662590214685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10359171418902216786952913 7769378564176662590214685)
                    ·
                      refine ⟨2913516961566248471330507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7769378564176662590214685 2913516961566248471330507)
                      ·
                        rfl

theorem cell23_5674054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_5674054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674054 prefixEnd_5674054 := by exact prefixLift 5674054
  have htrace : WordTrace (prefixWord ++ tailWord_5674054) baseStart_5674054 baseEnd_5674054 := by
    simpa [prefixWord, tailWord_5674054, baseEnd_5674054] using wordTrace_append hprefix tailTrace_5674054
  have hstable : (prefixWord ++ tailWord_5674054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674054).length < 2 ^ (prefixWord ++ tailWord_5674054).sum := by decide
  have hdescent : baseEnd_5674054 < baseStart_5674054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674101 : List Nat := [1, 3, 4, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_5674101 : Nat := 118140960795 + 5674101 * 2 ^ 59
def prefixEnd_5674101 : Nat := 4983230072969 + 3 ^ 40 * 5674101 * 2
def baseEnd_5674101 : Nat := 2913541095157009787442791

theorem tailTrace_5674101 : CollatzResearch.WordTrace tailWord_5674101 prefixEnd_5674101 2913541095157009787442791 := by
  unfold tailWord_5674101
  simp only [CollatzResearch.WordTrace]
  refine ⟨206951465216708611145158157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137967643477805740763438771 206951465216708611145158157)
  ·
    refine ⟨77606799456265729179434309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206951465216708611145158157 77606799456265729179434309)
    ·
      refine ⟨14551274898049824221143933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77606799456265729179434309 14551274898049824221143933)
      ·
        refine ⟨5456728086768684082928975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14551274898049824221143933 5456728086768684082928975)
        ·
          refine ⟨8185092130153026124393463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5456728086768684082928975 8185092130153026124393463)
          ·
            refine ⟨12277638195229539186590195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8185092130153026124393463 12277638195229539186590195)
            ·
              refine ⟨18416457292844308779885293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12277638195229539186590195 18416457292844308779885293)
              ·
                refine ⟨6906171484816615792456985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18416457292844308779885293 6906171484816615792456985)
                ·
                  refine ⟨5179628613612461844342739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6906171484816615792456985 5179628613612461844342739)
                  ·
                    refine ⟨7769442920418692766514109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5179628613612461844342739 7769442920418692766514109)
                    ·
                      refine ⟨2913541095157009787442791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7769442920418692766514109 2913541095157009787442791)
                      ·
                        rfl

theorem cell23_5674101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_5674101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674101 prefixEnd_5674101 := by exact prefixLift 5674101
  have htrace : WordTrace (prefixWord ++ tailWord_5674101) baseStart_5674101 baseEnd_5674101 := by
    simpa [prefixWord, tailWord_5674101, baseEnd_5674101] using wordTrace_append hprefix tailTrace_5674101
  have hstable : (prefixWord ++ tailWord_5674101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674101).length < 2 ^ (prefixWord ++ tailWord_5674101).sum := by decide
  have hdescent : baseEnd_5674101 < baseStart_5674101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674103 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 4]
def baseStart_5674103 : Nat := 118140960795 + 5674103 * 2 ^ 59
def prefixEnd_5674103 : Nat := 4983230072969 + 3 ^ 40 * 5674103 * 2
def baseEnd_5674103 : Nat := 2913542122118318779617781

theorem tailTrace_5674103 : CollatzResearch.WordTrace tailWord_5674103 prefixEnd_5674103 2913542122118318779617781 := by
  unfold tailWord_5674103
  simp only [CollatzResearch.WordTrace]
  refine ⟨206951538162701365486730963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137967692108467576991153975 206951538162701365486730963)
  ·
    refine ⟨310427307244052048230096445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206951538162701365486730963 310427307244052048230096445)
    ·
      refine ⟨116410240216519518086286167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310427307244052048230096445 116410240216519518086286167)
      ·
        refine ⟨174615360324779277129429251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116410240216519518086286167 174615360324779277129429251)
        ·
          refine ⟨261923040487168915694143877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174615360324779277129429251 261923040487168915694143877)
          ·
            refine ⟨49110570091344171692651977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 261923040487168915694143877 49110570091344171692651977)
            ·
              refine ⟨36832927568508128769488983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49110570091344171692651977 36832927568508128769488983)
              ·
                refine ⟨55249391352762193154233475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36832927568508128769488983 55249391352762193154233475)
                ·
                  refine ⟨82874087029143289731350213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55249391352762193154233475 82874087029143289731350213)
                  ·
                    refine ⟨15538891317964366824628165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82874087029143289731350213 15538891317964366824628165)
                    ·
                      refine ⟨2913542122118318779617781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15538891317964366824628165 2913542122118318779617781)
                      ·
                        rfl

theorem cell23_5674103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_5674103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674103 prefixEnd_5674103 := by exact prefixLift 5674103
  have htrace : WordTrace (prefixWord ++ tailWord_5674103) baseStart_5674103 baseEnd_5674103 := by
    simpa [prefixWord, tailWord_5674103, baseEnd_5674103] using wordTrace_append hprefix tailTrace_5674103
  have hstable : (prefixWord ++ tailWord_5674103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674103).length < 2 ^ (prefixWord ++ tailWord_5674103).sum := by decide
  have hdescent : baseEnd_5674103 < baseStart_5674103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674177 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 1, 7]
def baseStart_5674177 : Nat := 118140960795 + 5674177 * 2 ^ 59
def prefixEnd_5674177 : Nat := 4983230072969 + 3 ^ 40 * 5674177 * 2
def baseEnd_5674177 : Nat := 971193373228917163364147

theorem tailTrace_5674177 : CollatzResearch.WordTrace tailWord_5674177 prefixEnd_5674177 971193373228917163364147 := by
  unfold tailWord_5674177
  simp only [CollatzResearch.WordTrace]
  refine ⟨206954237164433276124924785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137969491442955517416616523 206954237164433276124924785)
  ·
    refine ⟨155215677873324957093693589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206954237164433276124924785 155215677873324957093693589)
    ·
      refine ⟨7275734900312107363766887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 155215677873324957093693589 7275734900312107363766887)
      ·
        refine ⟨10913602350468161045650331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7275734900312107363766887 10913602350468161045650331)
        ·
          refine ⟨16370403525702241568475497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10913602350468161045650331 16370403525702241568475497)
          ·
            refine ⟨12277802644276681176356623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16370403525702241568475497 12277802644276681176356623)
            ·
              refine ⟨18416703966415021764534935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12277802644276681176356623 18416703966415021764534935)
              ·
                refine ⟨27625055949622532646802403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18416703966415021764534935 27625055949622532646802403)
                ·
                  refine ⟨41437583924433798970203605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27625055949622532646802403 41437583924433798970203605)
                  ·
                    refine ⟨971193373228917163364147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41437583924433798970203605 971193373228917163364147)
                    ·
                      rfl

theorem cell23_5674177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_5674177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674177 prefixEnd_5674177 := by exact prefixLift 5674177
  have htrace : WordTrace (prefixWord ++ tailWord_5674177) baseStart_5674177 baseEnd_5674177 := by
    simpa [prefixWord, tailWord_5674177, baseEnd_5674177] using wordTrace_append hprefix tailTrace_5674177
  have hstable : (prefixWord ++ tailWord_5674177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674177).length < 2 ^ (prefixWord ++ tailWord_5674177).sum := by decide
  have hdescent : baseEnd_5674177 < baseStart_5674177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674241 : List Nat := [1, 2, 4, 1, 1, 5, 1, 3, 1, 4]
def baseStart_5674241 : Nat := 118140960795 + 5674241 * 2 ^ 59
def prefixEnd_5674241 : Nat := 4983230072969 + 3 ^ 40 * 5674241 * 2
def baseEnd_5674241 : Nat := 971204327482879746564049

theorem tailTrace_5674241 : CollatzResearch.WordTrace tailWord_5674241 prefixEnd_5674241 971204327482879746564049 := by
  unfold tailWord_5674241
  simp only [CollatzResearch.WordTrace]
  refine ⟨206956571436201415055254577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137971047624134276703503051 206956571436201415055254577)
  ·
    refine ⟨155217428577151061291440933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206956571436201415055254577 155217428577151061291440933)
    ·
      refine ⟨29103267858215823992145175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155217428577151061291440933 29103267858215823992145175)
      ·
        refine ⟨43654901787323735988217763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29103267858215823992145175 43654901787323735988217763)
        ·
          refine ⟨65482352680985603982326645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43654901787323735988217763 65482352680985603982326645)
          ·
            refine ⟨6138970563842400373343123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65482352680985603982326645 6138970563842400373343123)
            ·
              refine ⟨9208455845763600560014685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6138970563842400373343123 9208455845763600560014685)
              ·
                refine ⟨3453170942161350210005507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9208455845763600560014685 3453170942161350210005507)
                ·
                  refine ⟨5179756413242025315008261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3453170942161350210005507 5179756413242025315008261)
                  ·
                    refine ⟨971204327482879746564049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5179756413242025315008261 971204327482879746564049)
                    ·
                      rfl

theorem cell23_5674241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_5674241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674241 prefixEnd_5674241 := by exact prefixLift 5674241
  have htrace : WordTrace (prefixWord ++ tailWord_5674241) baseStart_5674241 baseEnd_5674241 := by
    simpa [prefixWord, tailWord_5674241, baseEnd_5674241] using wordTrace_append hprefix tailTrace_5674241
  have hstable : (prefixWord ++ tailWord_5674241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674241).length < 2 ^ (prefixWord ++ tailWord_5674241).sum := by decide
  have hdescent : baseEnd_5674241 < baseStart_5674241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674250 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 5, 5]
def baseStart_5674250 : Nat := 118140960795 + 5674250 * 2 ^ 59
def prefixEnd_5674250 : Nat := 4983230072969 + 3 ^ 40 * 5674250 * 2
def baseEnd_5674250 : Nat := 971205867924843234826535

theorem tailTrace_5674250 : CollatzResearch.WordTrace tailWord_5674250 prefixEnd_5674250 971205867924843234826535 := by
  unfold tailWord_5674250
  simp only [CollatzResearch.WordTrace]
  refine ⟨51739224923292202398083051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137971266462112539728221469 51739224923292202398083051)
  ·
    refine ⟨77608837384938303597124577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51739224923292202398083051 77608837384938303597124577)
    ·
      refine ⟨58206628038703727697843433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77608837384938303597124577 58206628038703727697843433)
      ·
        refine ⟨43654971029027795773382575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58206628038703727697843433 43654971029027795773382575)
        ·
          refine ⟨65482456543541693660073863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43654971029027795773382575 65482456543541693660073863)
          ·
            refine ⟨98223684815312540490110795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65482456543541693660073863 98223684815312540490110795)
            ·
              refine ⟨147335527222968810735166193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98223684815312540490110795 147335527222968810735166193)
              ·
                refine ⟨110501645417226608051374645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147335527222968810735166193 110501645417226608051374645)
                ·
                  refine ⟨10359529257864994504816373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110501645417226608051374645 10359529257864994504816373)
                  ·
                    refine ⟨971205867924843234826535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10359529257864994504816373 971205867924843234826535)
                    ·
                      rfl

theorem cell23_5674250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_5674250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674250 prefixEnd_5674250 := by exact prefixLift 5674250
  have htrace : WordTrace (prefixWord ++ tailWord_5674250) baseStart_5674250 baseEnd_5674250 := by
    simpa [prefixWord, tailWord_5674250, baseEnd_5674250] using wordTrace_append hprefix tailTrace_5674250
  have hstable : (prefixWord ++ tailWord_5674250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674250).length < 2 ^ (prefixWord ++ tailWord_5674250).sum := by decide
  have hdescent : baseEnd_5674250 < baseStart_5674250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674258 : List Nat := [3, 2, 4, 2, 1, 2, 1, 1, 3, 4]
def baseStart_5674258 : Nat := 118140960795 + 5674258 * 2 ^ 59
def prefixEnd_5674258 : Nat := 4983230072969 + 3 ^ 40 * 5674258 * 2
def baseEnd_5674258 : Nat := 971207237206588557726523

theorem tailTrace_5674258 : CollatzResearch.WordTrace tailWord_5674258 prefixEnd_5674258 971207237206588557726523 := by
  unfold tailWord_5674258
  simp only [CollatzResearch.WordTrace]
  refine ⟨51739297869284956739655857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137971460984759884639082285 51739297869284956739655857)
  ·
    refine ⟨38804473401963717554741893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51739297869284956739655857 38804473401963717554741893)
    ·
      refine ⟨7275838762868197041514105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38804473401963717554741893 7275838762868197041514105)
      ·
        refine ⟨5456879072151147781135579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7275838762868197041514105 5456879072151147781135579)
        ·
          refine ⟨8185318608226721671703369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5456879072151147781135579 8185318608226721671703369)
          ·
            refine ⟨6138988956170041253777527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8185318608226721671703369 6138988956170041253777527)
            ·
              refine ⟨9208483434255061880666291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6138988956170041253777527 9208483434255061880666291)
              ·
                refine ⟨13812725151382592820999437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9208483434255061880666291 13812725151382592820999437)
                ·
                  refine ⟨5179771931768472307874789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13812725151382592820999437 5179771931768472307874789)
                  ·
                    refine ⟨971207237206588557726523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5179771931768472307874789 971207237206588557726523)
                    ·
                      rfl

theorem cell23_5674258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_5674258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674258 prefixEnd_5674258 := by exact prefixLift 5674258
  have htrace : WordTrace (prefixWord ++ tailWord_5674258) baseStart_5674258 baseEnd_5674258 := by
    simpa [prefixWord, tailWord_5674258, baseEnd_5674258] using wordTrace_append hprefix tailTrace_5674258
  have hstable : (prefixWord ++ tailWord_5674258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674258).length < 2 ^ (prefixWord ++ tailWord_5674258).sum := by decide
  have hdescent : baseEnd_5674258 < baseStart_5674258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674264 : List Nat := [2, 1, 2, 3, 1, 3, 3, 1, 3, 1, 3]
def baseStart_5674264 : Nat := 118140960795 + 5674264 * 2 ^ 59
def prefixEnd_5674264 : Nat := 4983230072969 + 3 ^ 40 * 5674264 * 2
def baseEnd_5674264 : Nat := 2913624792503692649704541

theorem tailTrace_5674264 : CollatzResearch.WordTrace tailWord_5674264 prefixEnd_5674264 2913624792503692649704541 := by
  unfold tailWord_5674264
  simp only [CollatzResearch.WordTrace]
  refine ⟨103478705157559044991670923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137971606876745393322227897 103478705157559044991670923)
  ·
    refine ⟨155218057736338567487506385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103478705157559044991670923 155218057736338567487506385)
    ·
      refine ⟨116413543302253925615629789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155218057736338567487506385 116413543302253925615629789)
      ·
        refine ⟨43655078738345222105861171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116413543302253925615629789 43655078738345222105861171)
        ·
          refine ⟨65482618107517833158791757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43655078738345222105861171 65482618107517833158791757)
          ·
            refine ⟨24555981790319187434546909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65482618107517833158791757 24555981790319187434546909)
            ·
              refine ⟨9208493171369695287955091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24555981790319187434546909 9208493171369695287955091)
              ·
                refine ⟨13812739757054542931932637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9208493171369695287955091 13812739757054542931932637)
                ·
                  refine ⟨5179777408895453599474739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13812739757054542931932637 5179777408895453599474739)
                  ·
                    refine ⟨7769666113343180399212109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5179777408895453599474739 7769666113343180399212109)
                    ·
                      refine ⟨2913624792503692649704541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7769666113343180399212109 2913624792503692649704541)
                      ·
                        rfl

theorem cell23_5674264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_5674264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674264 prefixEnd_5674264 := by exact prefixLift 5674264
  have htrace : WordTrace (prefixWord ++ tailWord_5674264) baseStart_5674264 baseEnd_5674264 := by
    simpa [prefixWord, tailWord_5674264, baseEnd_5674264] using wordTrace_append hprefix tailTrace_5674264
  have hstable : (prefixWord ++ tailWord_5674264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674264).length < 2 ^ (prefixWord ++ tailWord_5674264).sum := by decide
  have hdescent : baseEnd_5674264 < baseStart_5674264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674271 : List Nat := [1, 1, 2, 4, 5, 1, 2, 1, 6]
def baseStart_5674271 : Nat := 118140960795 + 5674271 * 2 ^ 59
def prefixEnd_5674271 : Nat := 4983230072969 + 3 ^ 40 * 5674271 * 2
def baseEnd_5674271 : Nat := 323736487429808235813001

theorem tailTrace_5674271 : CollatzResearch.WordTrace tailWord_5674271 prefixEnd_5674271 323736487429808235813001 := by
  unfold tailWord_5674271
  simp only [CollatzResearch.WordTrace]
  refine ⟨206957665626092730178846667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137971777084061820119231111 206957665626092730178846667)
  ·
    refine ⟨310436498439139095268270001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206957665626092730178846667 310436498439139095268270001)
    ·
      refine ⟨232827373829354321451202501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310436498439139095268270001 232827373829354321451202501)
      ·
        refine ⟨43655132593003935272100469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232827373829354321451202501 43655132593003935272100469)
        ·
          refine ⟨4092668680594118931759419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43655132593003935272100469 4092668680594118931759419)
          ·
            refine ⟨6139003020891178397639129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4092668680594118931759419 6139003020891178397639129)
            ·
              refine ⟨4604252265668383798229347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6139003020891178397639129 4604252265668383798229347)
              ·
                refine ⟨6906378398502575697344021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4604252265668383798229347 6906378398502575697344021)
                ·
                  refine ⟨323736487429808235813001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6906378398502575697344021 323736487429808235813001)
                  ·
                    rfl

theorem cell23_5674271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 6].length) (baseStart_5674271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674271 prefixEnd_5674271 := by exact prefixLift 5674271
  have htrace : WordTrace (prefixWord ++ tailWord_5674271) baseStart_5674271 baseEnd_5674271 := by
    simpa [prefixWord, tailWord_5674271, baseEnd_5674271] using wordTrace_append hprefix tailTrace_5674271
  have hstable : (prefixWord ++ tailWord_5674271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674271).length < 2 ^ (prefixWord ++ tailWord_5674271).sum := by decide
  have hdescent : baseEnd_5674271 < baseStart_5674271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674304 : List Nat := [2, 1, 1, 2, 2, 1, 7, 1, 1, 1, 4]
def baseStart_5674304 : Nat := 118140960795 + 5674304 * 2 ^ 59
def prefixEnd_5674304 : Nat := 4983230072969 + 3 ^ 40 * 5674304 * 2
def baseEnd_5674304 : Nat := 2913645331729872493204357

theorem tailTrace_5674304 : CollatzResearch.WordTrace tailWord_5674304 prefixEnd_5674304 2913645331729872493204357 := by
  unfold tailWord_5674304
  simp only [CollatzResearch.WordTrace]
  refine ⟨103479434617486588407398983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137972579489982117876531977 103479434617486588407398983)
  ·
    refine ⟨155219151926229882611098475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103479434617486588407398983 155219151926229882611098475)
    ·
      refine ⟨232828727889344823916647713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155219151926229882611098475 232828727889344823916647713)
      ·
        refine ⟨174621545917008617937485785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232828727889344823916647713 174621545917008617937485785)
        ·
          refine ⟨130966159437756463453114339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174621545917008617937485785 130966159437756463453114339)
          ·
            refine ⟨196449239156634695179671509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130966159437756463453114339 196449239156634695179671509)
            ·
              refine ⟨4604279042733625668273551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 196449239156634695179671509 4604279042733625668273551)
              ·
                refine ⟨6906418564100438502410327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4604279042733625668273551 6906418564100438502410327)
                ·
                  refine ⟨10359627846150657753615491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6906418564100438502410327 10359627846150657753615491)
                  ·
                    refine ⟨15539441769225986630423237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10359627846150657753615491 15539441769225986630423237)
                    ·
                      refine ⟨2913645331729872493204357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15539441769225986630423237 2913645331729872493204357)
                      ·
                        rfl

theorem cell23_5674304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 1, 1, 4].length) (baseStart_5674304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674304 prefixEnd_5674304 := by exact prefixLift 5674304
  have htrace : WordTrace (prefixWord ++ tailWord_5674304) baseStart_5674304 baseEnd_5674304 := by
    simpa [prefixWord, tailWord_5674304, baseEnd_5674304] using wordTrace_append hprefix tailTrace_5674304
  have hstable : (prefixWord ++ tailWord_5674304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674304).length < 2 ^ (prefixWord ++ tailWord_5674304).sum := by decide
  have hdescent : baseEnd_5674304 < baseStart_5674304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674327 : List Nat := [1, 1, 3, 2, 3, 4, 1, 8]
def baseStart_5674327 : Nat := 118140960795 + 5674327 * 2 ^ 59
def prefixEnd_5674327 : Nat := 4983230072969 + 3 ^ 40 * 5674327 * 2
def baseEnd_5674327 : Nat := 107913227473515774193213

theorem tailTrace_5674327 : CollatzResearch.WordTrace tailWord_5674327 prefixEnd_5674327 107913227473515774193213 := by
  unfold tailWord_5674327
  simp only [CollatzResearch.WordTrace]
  refine ⟨206959708113889851742885235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137973138742593234495256823 206959708113889851742885235)
  ·
    refine ⟨310439562170834777614327853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206959708113889851742885235 310439562170834777614327853)
    ·
      refine ⟨116414835814063041605372945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310439562170834777614327853 116414835814063041605372945)
      ·
        refine ⟨87311126860547281204029709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116414835814063041605372945 87311126860547281204029709)
        ·
          refine ⟨32741672572705230451511141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87311126860547281204029709 32741672572705230451511141)
          ·
            refine ⟨6139063607382230709658339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32741672572705230451511141 6139063607382230709658339)
            ·
              refine ⟨9208595411073346064487509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6139063607382230709658339 9208595411073346064487509)
              ·
                refine ⟨107913227473515774193213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9208595411073346064487509 107913227473515774193213)
                ·
                  rfl

theorem cell23_5674327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 8].length) (baseStart_5674327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674327 prefixEnd_5674327 := by exact prefixLift 5674327
  have htrace : WordTrace (prefixWord ++ tailWord_5674327) baseStart_5674327 baseEnd_5674327 := by
    simpa [prefixWord, tailWord_5674327, baseEnd_5674327] using wordTrace_append hprefix tailTrace_5674327
  have hstable : (prefixWord ++ tailWord_5674327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674327).length < 2 ^ (prefixWord ++ tailWord_5674327).sum := by decide
  have hdescent : baseEnd_5674327 < baseStart_5674327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674330 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6]
def baseStart_5674330 : Nat := 118140960795 + 5674330 * 2 ^ 59
def prefixEnd_5674330 : Nat := 4983230072969 + 3 ^ 40 * 5674330 * 2
def baseEnd_5674330 : Nat := 2913658682226889391479237

theorem tailTrace_5674330 : CollatzResearch.WordTrace tailWord_5674330 prefixEnd_5674330 2913658682226889391479237 := by
  unfold tailWord_5674330
  simp only [CollatzResearch.WordTrace]
  refine ⟨51739954383219745813811111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137973211688585988836829629 51739954383219745813811111)
  ·
    refine ⟨77609931574829618720716667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51739954383219745813811111 77609931574829618720716667)
    ·
      refine ⟨116414897362244428081075001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77609931574829618720716667 116414897362244428081075001)
      ·
        refine ⟨87311173021683321060806251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116414897362244428081075001 87311173021683321060806251)
        ·
          refine ⟨130966759532524981591209377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87311173021683321060806251 130966759532524981591209377)
          ·
            refine ⟨98225069649393736193407033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130966759532524981591209377 98225069649393736193407033)
            ·
              refine ⟨73668802237045302145055275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98225069649393736193407033 73668802237045302145055275)
              ·
                refine ⟨110503203355567953217582913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73668802237045302145055275 110503203355567953217582913)
                ·
                  refine ⟨82877402516675964913187185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110503203355567953217582913 82877402516675964913187185)
                  ·
                    refine ⟨62158051887506973684890389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82877402516675964913187185 62158051887506973684890389)
                    ·
                      refine ⟨2913658682226889391479237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62158051887506973684890389 2913658682226889391479237)
                      ·
                        rfl

theorem cell23_5674330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_5674330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674330 prefixEnd_5674330 := by exact prefixLift 5674330
  have htrace : WordTrace (prefixWord ++ tailWord_5674330) baseStart_5674330 baseEnd_5674330 := by
    simpa [prefixWord, tailWord_5674330, baseEnd_5674330] using wordTrace_append hprefix tailTrace_5674330
  have hstable : (prefixWord ++ tailWord_5674330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674330).length < 2 ^ (prefixWord ++ tailWord_5674330).sum := by decide
  have hdescent : baseEnd_5674330 < baseStart_5674330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674344 : List Nat := [2, 1, 4, 2, 3, 1, 3, 7]
def baseStart_5674344 : Nat := 118140960795 + 5674344 * 2 ^ 59
def prefixEnd_5674344 : Nat := 4983230072969 + 3 ^ 40 * 5674344 * 2
def baseEnd_5674344 : Nat := 107913550776150086544599

theorem tailTrace_5674344 : CollatzResearch.WordTrace tailWord_5674344 prefixEnd_5674344 107913550776150086544599 := by
  unfold tailWord_5674344
  simp only [CollatzResearch.WordTrace]
  refine ⟨103480164077414131823127043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137973552103218842430836057 103480164077414131823127043)
  ·
    refine ⟨155220246116121197734690565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103480164077414131823127043 155220246116121197734690565)
    ·
      refine ⟨29103796146772724575254481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155220246116121197734690565 29103796146772724575254481)
      ·
        refine ⟨21827847110079543431440861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29103796146772724575254481 21827847110079543431440861)
        ·
          refine ⟨8185442666279828786790323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21827847110079543431440861 8185442666279828786790323)
          ·
            refine ⟨12278163999419743180185485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8185442666279828786790323 12278163999419743180185485)
            ·
              refine ⟨4604311499782403692569557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12278163999419743180185485 4604311499782403692569557)
              ·
                refine ⟨107913550776150086544599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4604311499782403692569557 107913550776150086544599)
                ·
                  rfl

theorem cell23_5674344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 7].length) (baseStart_5674344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674344 prefixEnd_5674344 := by exact prefixLift 5674344
  have htrace : WordTrace (prefixWord ++ tailWord_5674344) baseStart_5674344 baseEnd_5674344 := by
    simpa [prefixWord, tailWord_5674344, baseEnd_5674344] using wordTrace_append hprefix tailTrace_5674344
  have hstable : (prefixWord ++ tailWord_5674344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674344).length < 2 ^ (prefixWord ++ tailWord_5674344).sum := by decide
  have hdescent : baseEnd_5674344 < baseStart_5674344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674354 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 4, 1, 3]
def baseStart_5674354 : Nat := 118140960795 + 5674354 * 2 ^ 59
def prefixEnd_5674354 : Nat := 4983230072969 + 3 ^ 40 * 5674354 * 2
def baseEnd_5674354 : Nat := 2913671005762597297579127

theorem tailTrace_5674354 : CollatzResearch.WordTrace tailWord_5674354 prefixEnd_5674354 2913671005762597297579127 := by
  unfold tailWord_5674354
  simp only [CollatzResearch.WordTrace]
  refine ⟨51740173221198008838529529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137973795256528023569412077 51740173221198008838529529)
  ·
    refine ⟨38805129915898506628897147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51740173221198008838529529 38805129915898506628897147)
    ·
      refine ⟨58207694873847759943345721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38805129915898506628897147 58207694873847759943345721)
      ·
        refine ⟨43655771155385819957509291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58207694873847759943345721 43655771155385819957509291)
        ·
          refine ⟨65483656733078729936263937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43655771155385819957509291 65483656733078729936263937)
          ·
            refine ⟨49112742549809047452197953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65483656733078729936263937 49112742549809047452197953)
            ·
              refine ⟨36834556912356785589148465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49112742549809047452197953 36834556912356785589148465)
              ·
                refine ⟨27625917684267589191861349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36834556912356785589148465 27625917684267589191861349)
                ·
                  refine ⟨5179859565800172973474003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27625917684267589191861349 5179859565800172973474003)
                  ·
                    refine ⟨7769789348700259460211005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5179859565800172973474003 7769789348700259460211005)
                    ·
                      refine ⟨2913671005762597297579127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7769789348700259460211005 2913671005762597297579127)
                      ·
                        rfl

theorem cell23_5674354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_5674354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674354 prefixEnd_5674354 := by exact prefixLift 5674354
  have htrace : WordTrace (prefixWord ++ tailWord_5674354) baseStart_5674354 baseEnd_5674354 := by
    simpa [prefixWord, tailWord_5674354, baseEnd_5674354] using wordTrace_append hprefix tailTrace_5674354
  have hstable : (prefixWord ++ tailWord_5674354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674354).length < 2 ^ (prefixWord ++ tailWord_5674354).sum := by decide
  have hdescent : baseEnd_5674354 < baseStart_5674354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674371 : List Nat := [1, 1, 1, 3, 5, 1, 3, 2, 2, 1, 3]
def baseStart_5674371 : Nat := 118140960795 + 5674371 * 2 ^ 59
def prefixEnd_5674371 : Nat := 4983230072969 + 3 ^ 40 * 5674371 * 2
def baseEnd_5674371 : Nat := 2913679734933723731066549

theorem tailTrace_5674371 : CollatzResearch.WordTrace tailWord_5674371 prefixEnd_5674371 2913679734933723731066549 := by
  unfold tailWord_5674371
  simp only [CollatzResearch.WordTrace]
  refine ⟨206961312925730447257486967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137974208617153631504991311 206961312925730447257486967)
  ·
    refine ⟨310441969388595670886230451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206961312925730447257486967 310441969388595670886230451)
    ·
      refine ⟨465662954082893506329345677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310441969388595670886230451 465662954082893506329345677)
      ·
        refine ⟨174623607781085064873504629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 465662954082893506329345677 174623607781085064873504629)
        ·
          refine ⟨16370963229476724831891059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174623607781085064873504629 16370963229476724831891059)
          ·
            refine ⟨24556444844215087247836589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16370963229476724831891059 24556444844215087247836589)
            ·
              refine ⟨9208666816580657717938721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24556444844215087247836589 9208666816580657717938721)
              ·
                refine ⟨6906500112435493288454041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9208666816580657717938721 6906500112435493288454041)
                ·
                  refine ⟨5179875084326619966340531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6906500112435493288454041 5179875084326619966340531)
                  ·
                    refine ⟨7769812626489929949510797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5179875084326619966340531 7769812626489929949510797)
                    ·
                      refine ⟨2913679734933723731066549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7769812626489929949510797 2913679734933723731066549)
                      ·
                        rfl

theorem cell23_5674371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 1, 3].length) (baseStart_5674371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674371 prefixEnd_5674371 := by exact prefixLift 5674371
  have htrace : WordTrace (prefixWord ++ tailWord_5674371) baseStart_5674371 baseEnd_5674371 := by
    simpa [prefixWord, tailWord_5674371, baseEnd_5674371] using wordTrace_append hprefix tailTrace_5674371
  have hstable : (prefixWord ++ tailWord_5674371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674371).length < 2 ^ (prefixWord ++ tailWord_5674371).sum := by decide
  have hdescent : baseEnd_5674371 < baseStart_5674371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674485 : List Nat := [1, 3, 5, 1, 1, 3, 2, 2, 5]
def baseStart_5674485 : Nat := 118140960795 + 5674485 * 2 ^ 59
def prefixEnd_5674485 : Nat := 4983230072969 + 3 ^ 40 * 5674485 * 2
def baseEnd_5674485 : Nat := 323748696858704031671225

theorem tailTrace_5674485 : CollatzResearch.WordTrace tailWord_5674485 prefixEnd_5674485 323748696858704031671225 := by
  unfold tailWord_5674485
  simp only [CollatzResearch.WordTrace]
  refine ⟨206965470847317444727136909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137976980564878296484757939 206965470847317444727136909)
  ·
    refine ⟨77612051567744041772676341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206965470847317444727136909 77612051567744041772676341)
    ·
      refine ⟨7276129834476003916188407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77612051567744041772676341 7276129834476003916188407)
      ·
        refine ⟨10914194751714005874282611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7276129834476003916188407 10914194751714005874282611)
        ·
          refine ⟨16371292127571008811423917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10914194751714005874282611 16371292127571008811423917)
          ·
            refine ⟨6139234547839128304283969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16371292127571008811423917 6139234547839128304283969)
            ·
              refine ⟨4604425910879346228212977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6139234547839128304283969 4604425910879346228212977)
              ·
                refine ⟨3453319433159509671159733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4604425910879346228212977 3453319433159509671159733)
                ·
                  refine ⟨323748696858704031671225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3453319433159509671159733 323748696858704031671225)
                  ·
                    rfl

theorem cell23_5674485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 5].length) (baseStart_5674485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674485 prefixEnd_5674485 := by exact prefixLift 5674485
  have htrace : WordTrace (prefixWord ++ tailWord_5674485) baseStart_5674485 baseEnd_5674485 := by
    simpa [prefixWord, tailWord_5674485, baseEnd_5674485] using wordTrace_append hprefix tailTrace_5674485
  have hstable : (prefixWord ++ tailWord_5674485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674485).length < 2 ^ (prefixWord ++ tailWord_5674485).sum := by decide
  have hdescent : baseEnd_5674485 < baseStart_5674485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674504 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 4, 2, 3]
def baseStart_5674504 : Nat := 118140960795 + 5674504 * 2 ^ 59
def prefixEnd_5674504 : Nat := 4983230072969 + 3 ^ 40 * 5674504 * 2
def baseEnd_5674504 : Nat := 2913748027860771710703437

theorem tailTrace_5674504 : CollatzResearch.WordTrace tailWord_5674504 prefixEnd_5674504 2913748027860771710703437 := by
  unfold tailWord_5674504
  simp only [CollatzResearch.WordTrace]
  refine ⟨103483081917124305486039283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137977442556165740648052377 103483081917124305486039283)
  ·
    refine ⟨155224622875686458229058925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103483081917124305486039283 155224622875686458229058925)
    ·
      refine ⟨58209233578382421835897097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155224622875686458229058925 58209233578382421835897097)
      ·
        refine ⟨43656925183786816376922823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58209233578382421835897097 43656925183786816376922823)
        ·
          refine ⟨65485387775680224565384235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43656925183786816376922823 65485387775680224565384235)
          ·
            refine ⟨98228081663520336848076353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65485387775680224565384235 98228081663520336848076353)
            ·
              refine ⟨73671061247640252636057265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98228081663520336848076353 73671061247640252636057265)
              ·
                refine ⟨55253295935730189477042949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73671061247640252636057265 55253295935730189477042949)
                ·
                  refine ⟨10359992987949410526945553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55253295935730189477042949 10359992987949410526945553)
                  ·
                    refine ⟨7769994740962057895209165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10359992987949410526945553 7769994740962057895209165)
                    ·
                      refine ⟨2913748027860771710703437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7769994740962057895209165 2913748027860771710703437)
                      ·
                        rfl

theorem cell23_5674504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_5674504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674504 prefixEnd_5674504 := by exact prefixLift 5674504
  have htrace : WordTrace (prefixWord ++ tailWord_5674504) baseStart_5674504 baseEnd_5674504 := by
    simpa [prefixWord, tailWord_5674504, baseEnd_5674504] using wordTrace_append hprefix tailTrace_5674504
  have hstable : (prefixWord ++ tailWord_5674504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674504).length < 2 ^ (prefixWord ++ tailWord_5674504).sum := by decide
  have hdescent : baseEnd_5674504 < baseStart_5674504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674528 : List Nat := [2, 1, 1, 6, 1, 1, 1, 5, 1, 4]
def baseStart_5674528 : Nat := 118140960795 + 5674528 * 2 ^ 59
def prefixEnd_5674528 : Nat := 4983230072969 + 3 ^ 40 * 5674528 * 2
def baseEnd_5674528 : Nat := 971253450465493205601109

theorem tailTrace_5674528 : CollatzResearch.WordTrace tailWord_5674528 prefixEnd_5674528 971253450465493205601109 := by
  unfold tailWord_5674528
  simp only [CollatzResearch.WordTrace]
  refine ⟨103483519593080831535476119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137978026124107775380634825 103483519593080831535476119)
  ·
    refine ⟨155225279389621247303214179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103483519593080831535476119 155225279389621247303214179)
    ·
      refine ⟨232837919084431870954821269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155225279389621247303214179 232837919084431870954821269)
      ·
        refine ⟨10914277457082743951007247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 232837919084431870954821269 10914277457082743951007247)
        ·
          refine ⟨16371416185624115926510871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10914277457082743951007247 16371416185624115926510871)
          ·
            refine ⟨24557124278436173889766307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16371416185624115926510871 24557124278436173889766307)
            ·
              refine ⟨36835686417654260834649461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24557124278436173889766307 36835686417654260834649461)
              ·
                refine ⟨3453345601655086953248387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36835686417654260834649461 3453345601655086953248387)
                ·
                  refine ⟨5180018402482630429872581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3453345601655086953248387 5180018402482630429872581)
                  ·
                    refine ⟨971253450465493205601109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5180018402482630429872581 971253450465493205601109)
                    ·
                      rfl

theorem cell23_5674528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 1, 4].length) (baseStart_5674528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674528 prefixEnd_5674528 := by exact prefixLift 5674528
  have htrace : WordTrace (prefixWord ++ tailWord_5674528) baseStart_5674528 baseEnd_5674528 := by
    simpa [prefixWord, tailWord_5674528, baseEnd_5674528] using wordTrace_append hprefix tailTrace_5674528
  have hstable : (prefixWord ++ tailWord_5674528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674528).length < 2 ^ (prefixWord ++ tailWord_5674528).sum := by decide
  have hdescent : baseEnd_5674528 < baseStart_5674528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674551 : List Nat := [1, 1, 3, 1, 2, 4, 1, 3, 3, 1, 3]
def baseStart_5674551 : Nat := 118140960795 + 5674551 * 2 ^ 59
def prefixEnd_5674551 : Nat := 4983230072969 + 3 ^ 40 * 5674551 * 2
def baseEnd_5674551 : Nat := 2913772161451533026815721

theorem tailTrace_5674551 : CollatzResearch.WordTrace tailWord_5674551 prefixEnd_5674551 2913772161451533026815721 := by
  unfold tailWord_5674551
  simp only [CollatzResearch.WordTrace]
  refine ⟨206967878065078337999039507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137978585376718891999359671 206967878065078337999039507)
  ·
    refine ⟨310451817097617506998559261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206967878065078337999039507 310451817097617506998559261)
    ·
      refine ⟨116419431411606565124459723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310451817097617506998559261 116419431411606565124459723)
      ·
        refine ⟨174629147117409847686689585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116419431411606565124459723 174629147117409847686689585)
        ·
          refine ⟨130971860338057385765017189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174629147117409847686689585 130971860338057385765017189)
          ·
            refine ⟨24557223813385759830940723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130971860338057385765017189 24557223813385759830940723)
            ·
              refine ⟨36835835720078639746411085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24557223813385759830940723 36835835720078639746411085)
              ·
                refine ⟨13813438395029489904904157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36835835720078639746411085 13813438395029489904904157)
                ·
                  refine ⟨5180039398136058714339059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13813438395029489904904157 5180039398136058714339059)
                  ·
                    refine ⟨7770059097204088071508589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5180039398136058714339059 7770059097204088071508589)
                    ·
                      refine ⟨2913772161451533026815721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7770059097204088071508589 2913772161451533026815721)
                      ·
                        rfl

theorem cell23_5674551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 1, 3].length) (baseStart_5674551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674551 prefixEnd_5674551 := by exact prefixLift 5674551
  have htrace : WordTrace (prefixWord ++ tailWord_5674551) baseStart_5674551 baseEnd_5674551 := by
    simpa [prefixWord, tailWord_5674551, baseEnd_5674551] using wordTrace_append hprefix tailTrace_5674551
  have hstable : (prefixWord ++ tailWord_5674551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674551).length < 2 ^ (prefixWord ++ tailWord_5674551).sum := by decide
  have hdescent : baseEnd_5674551 < baseStart_5674551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674561 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_5674561 : Nat := 118140960795 + 5674561 * 2 ^ 59
def prefixEnd_5674561 : Nat := 4983230072969 + 3 ^ 40 * 5674561 * 2
def baseEnd_5674561 : Nat := 2913777296258077987690675

theorem tailTrace_5674561 : CollatzResearch.WordTrace tailWord_5674561 prefixEnd_5674561 2913777296258077987690675 := by
  unfold tailWord_5674561
  simp only [CollatzResearch.WordTrace]
  refine ⟨206968242795042109706903537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137978828530028073137935691 206968242795042109706903537)
  ·
    refine ⟨155226182096281582280177653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206968242795042109706903537 155226182096281582280177653)
    ·
      refine ⟨14552454571526398338766655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155226182096281582280177653 14552454571526398338766655)
      ·
        refine ⟨21828681857289597508149983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14552454571526398338766655 21828681857289597508149983)
        ·
          refine ⟨32743022785934396262224975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21828681857289597508149983 32743022785934396262224975)
          ·
            refine ⟨49114534178901594393337463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32743022785934396262224975 49114534178901594393337463)
            ·
              refine ⟨73671801268352391590006195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49114534178901594393337463 73671801268352391590006195)
              ·
                refine ⟨110507701902528587385009293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73671801268352391590006195 110507701902528587385009293)
                ·
                  refine ⟨41440388213448220269378485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110507701902528587385009293 41440388213448220269378485)
                  ·
                    refine ⟨3885036395010770650254233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41440388213448220269378485 3885036395010770650254233)
                    ·
                      refine ⟨2913777296258077987690675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3885036395010770650254233 2913777296258077987690675)
                      ·
                        rfl

theorem cell23_5674561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_5674561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674561 prefixEnd_5674561 := by exact prefixLift 5674561
  have htrace : WordTrace (prefixWord ++ tailWord_5674561) baseStart_5674561 baseEnd_5674561 := by
    simpa [prefixWord, tailWord_5674561, baseEnd_5674561] using wordTrace_append hprefix tailTrace_5674561
  have hstable : (prefixWord ++ tailWord_5674561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674561).length < 2 ^ (prefixWord ++ tailWord_5674561).sum := by decide
  have hdescent : baseEnd_5674561 < baseStart_5674561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674602 : List Nat := [3, 1, 3, 2, 1, 3, 3, 2, 1, 1, 3]
def baseStart_5674602 : Nat := 118140960795 + 5674602 * 2 ^ 59
def prefixEnd_5674602 : Nat := 4983230072969 + 3 ^ 40 * 5674602 * 2
def baseEnd_5674602 : Nat := 2913798348964912327277987

theorem tailTrace_5674602 : CollatzResearch.WordTrace tailWord_5674602 prefixEnd_5674602 2913798348964912327277987 := by
  unfold tailWord_5674602
  simp only [CollatzResearch.WordTrace]
  refine ⟨51742434546973393427286515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137979825458595715806097373 51742434546973393427286515)
  ·
    refine ⟨77613651820460090140929773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51742434546973393427286515 77613651820460090140929773)
    ·
      refine ⟨29105119432672533802848665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77613651820460090140929773 29105119432672533802848665)
      ·
        refine ⟨21828839574504400352136499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29105119432672533802848665 21828839574504400352136499)
        ·
          refine ⟨32743259361756600528204749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21828839574504400352136499 32743259361756600528204749)
          ·
            refine ⟨12278722260658725198076781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32743259361756600528204749 12278722260658725198076781)
            ·
              refine ⟨4604520847747021949278793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12278722260658725198076781 4604520847747021949278793)
              ·
                refine ⟨3453390635810266461959095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4604520847747021949278793 3453390635810266461959095)
                ·
                  refine ⟨5180085953715399692938643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3453390635810266461959095 5180085953715399692938643)
                  ·
                    refine ⟨7770128930573099539407965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5180085953715399692938643 7770128930573099539407965)
                    ·
                      refine ⟨2913798348964912327277987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7770128930573099539407965 2913798348964912327277987)
                      ·
                        rfl

theorem cell23_5674602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_5674602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674602 prefixEnd_5674602 := by exact prefixLift 5674602
  have htrace : WordTrace (prefixWord ++ tailWord_5674602) baseStart_5674602 baseEnd_5674602 := by
    simpa [prefixWord, tailWord_5674602, baseEnd_5674602] using wordTrace_append hprefix tailTrace_5674602
  have hstable : (prefixWord ++ tailWord_5674602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674602).length < 2 ^ (prefixWord ++ tailWord_5674602).sum := by decide
  have hdescent : baseEnd_5674602 < baseStart_5674602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674628 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_5674628 : Nat := 118140960795 + 5674628 * 2 ^ 59
def prefixEnd_5674628 : Nat := 4983230072969 + 3 ^ 40 * 5674628 * 2
def baseEnd_5674628 : Nat := 2913811699461929225552867

theorem tailTrace_5674628 : CollatzResearch.WordTrace tailWord_5674628 prefixEnd_5674628 2913811699461929225552867 := by
  unfold tailWord_5674628
  simp only [CollatzResearch.WordTrace]
  refine ⟨103485343242899690074796269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137980457657199586766395025 103485343242899690074796269)
  ·
    refine ⟨38807003716087383778048601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103485343242899690074796269 38807003716087383778048601)
    ·
      refine ⟨29105252787065537833536451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38807003716087383778048601 29105252787065537833536451)
      ·
        refine ⟨43657879180598306750304677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29105252787065537833536451 43657879180598306750304677)
        ·
          refine ⟨8185852346362182515682127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43657879180598306750304677 8185852346362182515682127)
          ·
            refine ⟨12278778519543273773523191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8185852346362182515682127 12278778519543273773523191)
            ·
              refine ⟨18418167779314910660284787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12278778519543273773523191 18418167779314910660284787)
              ·
                refine ⟨27627251668972365990427181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18418167779314910660284787 27627251668972365990427181)
                ·
                  refine ⟨10360219375864637246410193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27627251668972365990427181 10360219375864637246410193)
                  ·
                    refine ⟨7770164531898477934807645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10360219375864637246410193 7770164531898477934807645)
                    ·
                      refine ⟨2913811699461929225552867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7770164531898477934807645 2913811699461929225552867)
                      ·
                        rfl

theorem cell23_5674628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_5674628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674628 prefixEnd_5674628 := by exact prefixLift 5674628
  have htrace : WordTrace (prefixWord ++ tailWord_5674628) baseStart_5674628 baseEnd_5674628 := by
    simpa [prefixWord, tailWord_5674628, baseEnd_5674628] using wordTrace_append hprefix tailTrace_5674628
  have hstable : (prefixWord ++ tailWord_5674628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674628).length < 2 ^ (prefixWord ++ tailWord_5674628).sum := by decide
  have hdescent : baseEnd_5674628 < baseStart_5674628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674641 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 4, 1, 3]
def baseStart_5674641 : Nat := 118140960795 + 5674641 * 2 ^ 59
def prefixEnd_5674641 : Nat := 4983230072969 + 3 ^ 40 * 5674641 * 2
def baseEnd_5674641 : Nat := 2913818374710437674690307

theorem tailTrace_5674641 : CollatzResearch.WordTrace tailWord_5674641 prefixEnd_5674641 2913818374710437674690307 := by
  unfold tailWord_5674641
  simp only [CollatzResearch.WordTrace]
  refine ⟨206971160634752283369815777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137980773756501522246543851 206971160634752283369815777)
  ·
    refine ⟨155228370476064212527361833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206971160634752283369815777 155228370476064212527361833)
    ·
      refine ⟨116421277857048159395521375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155228370476064212527361833 116421277857048159395521375)
      ·
        refine ⟨174631916785572239093282063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116421277857048159395521375 174631916785572239093282063)
        ·
          refine ⟨261947875178358358639923095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174631916785572239093282063 261947875178358358639923095)
          ·
            refine ⟨392921812767537537959884643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261947875178358358639923095 392921812767537537959884643)
            ·
              refine ⟨589382719151306306939826965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392921812767537537959884643 589382719151306306939826965)
              ·
                refine ⟨27627314960217483137804389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 589382719151306306939826965 27627314960217483137804389)
                ·
                  refine ⟨5180121555040778088338323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27627314960217483137804389 5180121555040778088338323)
                  ·
                    refine ⟨7770182332561167132507485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5180121555040778088338323 7770182332561167132507485)
                    ·
                      refine ⟨2913818374710437674690307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7770182332561167132507485 2913818374710437674690307)
                      ·
                        rfl

theorem cell23_5674641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 1, 3].length) (baseStart_5674641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674641 prefixEnd_5674641 := by exact prefixLift 5674641
  have htrace : WordTrace (prefixWord ++ tailWord_5674641) baseStart_5674641 baseEnd_5674641 := by
    simpa [prefixWord, tailWord_5674641, baseEnd_5674641] using wordTrace_append hprefix tailTrace_5674641
  have hstable : (prefixWord ++ tailWord_5674641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674641).length < 2 ^ (prefixWord ++ tailWord_5674641).sum := by decide
  have hdescent : baseEnd_5674641 < baseStart_5674641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674674 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 1, 8]
def baseStart_5674674 : Nat := 118140960795 + 5674674 * 2 ^ 59
def prefixEnd_5674674 : Nat := 4983230072969 + 3 ^ 40 * 5674674 * 2
def baseEnd_5674674 : Nat := 971278439857345348525885

theorem tailTrace_5674674 : CollatzResearch.WordTrace tailWord_5674674 prefixEnd_5674674 971278439857345348525885 := by
  unfold tailWord_5674674
  simp only [CollatzResearch.WordTrace]
  refine ⟨51743091060908182501441769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137981576162421820003844717 51743091060908182501441769)
  ·
    refine ⟨38807318295681136876081327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51743091060908182501441769 38807318295681136876081327)
    ·
      refine ⟨58210977443521705314121991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38807318295681136876081327 58210977443521705314121991)
      ·
        refine ⟨87316466165282557971182987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58210977443521705314121991 87316466165282557971182987)
        ·
          refine ⟨130974699247923836956774481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87316466165282557971182987 130974699247923836956774481)
          ·
            refine ⟨98231024435942877717580861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130974699247923836956774481 98231024435942877717580861)
            ·
              refine ⟨36836634163478579144092823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98231024435942877717580861 36836634163478579144092823)
              ·
                refine ⟨55254951245217868716139235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36836634163478579144092823 55254951245217868716139235)
                ·
                  refine ⟨82882426867826803074208853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55254951245217868716139235 82882426867826803074208853)
                  ·
                    refine ⟨971278439857345348525885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82882426867826803074208853 971278439857345348525885)
                    ·
                      rfl

theorem cell23_5674674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_5674674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674674 prefixEnd_5674674 := by exact prefixLift 5674674
  have htrace : WordTrace (prefixWord ++ tailWord_5674674) baseStart_5674674 baseEnd_5674674 := by
    simpa [prefixWord, tailWord_5674674, baseEnd_5674674] using wordTrace_append hprefix tailTrace_5674674
  have hstable : (prefixWord ++ tailWord_5674674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674674).length < 2 ^ (prefixWord ++ tailWord_5674674).sum := by decide
  have hdescent : baseEnd_5674674 < baseStart_5674674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674731 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 3]
def baseStart_5674731 : Nat := 118140960795 + 5674731 * 2 ^ 59
def prefixEnd_5674731 : Nat := 4983230072969 + 3 ^ 40 * 5674731 * 2
def baseEnd_5674731 : Nat := 2913864587969342322564893

theorem tailTrace_5674731 : CollatzResearch.WordTrace tailWord_5674731 prefixEnd_5674731 2913864587969342322564893 := by
  unfold tailWord_5674731
  simp only [CollatzResearch.WordTrace]
  refine ⟨206974443204426228740592047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137982962136284152493728031 206974443204426228740592047)
  ·
    refine ⟨310461664806639343110888071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206974443204426228740592047 310461664806639343110888071)
    ·
      refine ⟨465692497209959014666332107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310461664806639343110888071 465692497209959014666332107)
      ·
        refine ⟨698538745814938521999498161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465692497209959014666332107 698538745814938521999498161)
        ·
          refine ⟨523904059361203891499623621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 698538745814938521999498161 523904059361203891499623621)
          ·
            refine ⟨98232011130225729656179429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 523904059361203891499623621 98232011130225729656179429)
            ·
              refine ⟨18418502086917324310533643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98232011130225729656179429 18418502086917324310533643)
              ·
                refine ⟨27627753130375986465800465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18418502086917324310533643 27627753130375986465800465)
                ·
                  refine ⟨20720814847781989849350349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27627753130375986465800465 20720814847781989849350349)
                  ·
                    refine ⟨7770305567918246193506381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20720814847781989849350349 7770305567918246193506381)
                    ·
                      refine ⟨2913864587969342322564893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7770305567918246193506381 2913864587969342322564893)
                      ·
                        rfl

theorem cell23_5674731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 3].length) (baseStart_5674731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674731 prefixEnd_5674731 := by exact prefixLift 5674731
  have htrace : WordTrace (prefixWord ++ tailWord_5674731) baseStart_5674731 baseEnd_5674731 := by
    simpa [prefixWord, tailWord_5674731, baseEnd_5674731] using wordTrace_append hprefix tailTrace_5674731
  have hstable : (prefixWord ++ tailWord_5674731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674731).length < 2 ^ (prefixWord ++ tailWord_5674731).sum := by decide
  have hdescent : baseEnd_5674731 < baseStart_5674731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674744 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 3, 1, 7]
def baseStart_5674744 : Nat := 118140960795 + 5674744 * 2 ^ 59
def prefixEnd_5674744 : Nat := 4983230072969 + 3 ^ 40 * 5674744 * 2
def baseEnd_5674744 : Nat := 2913871263217850771702333

theorem tailTrace_5674744 : CollatzResearch.WordTrace tailWord_5674744 prefixEnd_5674744 2913871263217850771702333 := by
  unfold tailWord_5674744
  simp only [CollatzResearch.WordTrace]
  refine ⟨103487458676689565980407643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137983278235586087973876857 103487458676689565980407643)
  ·
    refine ⟨155231188015034348970611465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103487458676689565980407643 155231188015034348970611465)
    ·
      refine ⟨116423391011275761727958599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155231188015034348970611465 116423391011275761727958599)
      ·
        refine ⟨174635086516913642591937899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116423391011275761727958599 174635086516913642591937899)
        ·
          refine ⟨261952629775370463887906849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174635086516913642591937899 261952629775370463887906849)
          ·
            refine ⟨196464472331527847915930137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261952629775370463887906849 196464472331527847915930137)
            ·
              refine ⟨147348354248645885936947603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196464472331527847915930137 147348354248645885936947603)
              ·
                refine ⟨221022531372968828905421405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147348354248645885936947603 221022531372968828905421405)
                ·
                  refine ⟨82883449264863310839533027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221022531372968828905421405 82883449264863310839533027)
                  ·
                    refine ⟨124325173897294966259299541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82883449264863310839533027 124325173897294966259299541)
                    ·
                      refine ⟨2913871263217850771702333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124325173897294966259299541 2913871263217850771702333)
                      ·
                        rfl

theorem cell23_5674744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_5674744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674744 prefixEnd_5674744 := by exact prefixLift 5674744
  have htrace : WordTrace (prefixWord ++ tailWord_5674744) baseStart_5674744 baseEnd_5674744 := by
    simpa [prefixWord, tailWord_5674744, baseEnd_5674744] using wordTrace_append hprefix tailTrace_5674744
  have hstable : (prefixWord ++ tailWord_5674744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674744).length < 2 ^ (prefixWord ++ tailWord_5674744).sum := by decide
  have hdescent : baseEnd_5674744 < baseStart_5674744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674805 : List Nat := [1, 3, 3, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_5674805 : Nat := 118140960795 + 5674805 * 2 ^ 59
def prefixEnd_5674805 : Nat := 4983230072969 + 3 ^ 40 * 5674805 * 2
def baseEnd_5674805 : Nat := 2913902585537775033039553

theorem tailTrace_5674805 : CollatzResearch.WordTrace tailWord_5674805 prefixEnd_5674805 2913902585537775033039553 := by
  unfold tailWord_5674805
  simp only [CollatzResearch.WordTrace]
  refine ⟨206977142206158139378785869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137984761470772092919190579 206977142206158139378785869)
  ·
    refine ⟨77616428327309302267044701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206977142206158139378785869 77616428327309302267044701)
    ·
      refine ⟨29106160622740988350141763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77616428327309302267044701 29106160622740988350141763)
      ·
        refine ⟨43659240934111482525212645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29106160622740988350141763 43659240934111482525212645)
        ·
          refine ⟨8186107675145902973477371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43659240934111482525212645 8186107675145902973477371)
          ·
            refine ⟨12279161512718854460216057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8186107675145902973477371 12279161512718854460216057)
            ·
              refine ⟨9209371134539140845162043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12279161512718854460216057 9209371134539140845162043)
              ·
                refine ⟨13814056701808711267743065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9209371134539140845162043 13814056701808711267743065)
                ·
                  refine ⟨10360542526356533450807299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13814056701808711267743065 10360542526356533450807299)
                  ·
                    refine ⟨15540813789534800176210949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10360542526356533450807299 15540813789534800176210949)
                    ·
                      refine ⟨2913902585537775033039553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15540813789534800176210949 2913902585537775033039553)
                      ·
                        rfl

theorem cell23_5674805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_5674805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674805 prefixEnd_5674805 := by exact prefixLift 5674805
  have htrace : WordTrace (prefixWord ++ tailWord_5674805) baseStart_5674805 baseEnd_5674805 := by
    simpa [prefixWord, tailWord_5674805, baseEnd_5674805] using wordTrace_append hprefix tailTrace_5674805
  have hstable : (prefixWord ++ tailWord_5674805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674805).length < 2 ^ (prefixWord ++ tailWord_5674805).sum := by decide
  have hdescent : baseEnd_5674805 < baseStart_5674805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674808 : List Nat := [2, 1, 2, 1, 3, 3, 1, 3, 2, 2, 3]
def baseStart_5674808 : Nat := 118140960795 + 5674808 * 2 ^ 59
def prefixEnd_5674808 : Nat := 4983230072969 + 3 ^ 40 * 5674808 * 2
def baseEnd_5674808 : Nat := 2913904125979738521302039

theorem tailTrace_5674808 : CollatzResearch.WordTrace tailWord_5674808 prefixEnd_5674808 2913904125979738521302039 := by
  unfold tailWord_5674808
  simp only [CollatzResearch.WordTrace]
  refine ⟨103488625812573635445572539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137984834416764847260763385 103488625812573635445572539)
  ·
    refine ⟨155232938718860453168358809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103488625812573635445572539 155232938718860453168358809)
    ·
      refine ⟨116424704039145339876269107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155232938718860453168358809 116424704039145339876269107)
      ·
        refine ⟨174637056058718009814403661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116424704039145339876269107 174637056058718009814403661)
        ·
          refine ⟨65488896022019253680401373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174637056058718009814403661 65488896022019253680401373)
          ·
            refine ⟨24558336008257220130150515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65488896022019253680401373 24558336008257220130150515)
            ·
              refine ⟨36837504012385830195225773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24558336008257220130150515 36837504012385830195225773)
              ·
                refine ⟨13814064004644686323209665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36837504012385830195225773 13814064004644686323209665)
                ·
                  refine ⟨10360548003483514742407249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13814064004644686323209665 10360548003483514742407249)
                  ·
                    refine ⟨7770411002612636056805437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10360548003483514742407249 7770411002612636056805437)
                    ·
                      refine ⟨2913904125979738521302039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7770411002612636056805437 2913904125979738521302039)
                      ·
                        rfl

theorem cell23_5674808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_5674808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674808 prefixEnd_5674808 := by exact prefixLift 5674808
  have htrace : WordTrace (prefixWord ++ tailWord_5674808) baseStart_5674808 baseEnd_5674808 := by
    simpa [prefixWord, tailWord_5674808, baseEnd_5674808] using wordTrace_append hprefix tailTrace_5674808
  have hstable : (prefixWord ++ tailWord_5674808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674808).length < 2 ^ (prefixWord ++ tailWord_5674808).sum := by decide
  have hdescent : baseEnd_5674808 < baseStart_5674808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674822 : List Nat := [6, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_5674822 : Nat := 118140960795 + 5674822 * 2 ^ 59
def prefixEnd_5674822 : Nat := 4983230072969 + 3 ^ 40 * 5674822 * 2
def baseEnd_5674822 : Nat := 2913911314708901466526975

theorem tailTrace_5674822 : CollatzResearch.WordTrace tailWord_5674822 prefixEnd_5674822 2913911314708901466526975 := by
  unfold tailWord_5674822
  simp only [CollatzResearch.WordTrace]
  refine ⟨6468055070221767227567335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 137985174831397700854769813 6468055070221767227567335)
  ·
    refine ⟨9702082605332650841351003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6468055070221767227567335 9702082605332650841351003)
    ·
      refine ⟨14553123907998976262026505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9702082605332650841351003 14553123907998976262026505)
      ·
        refine ⟨10914842930999232196519879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14553123907998976262026505 10914842930999232196519879)
        ·
          refine ⟨16372264396498848294779819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10914842930999232196519879 16372264396498848294779819)
          ·
            refine ⟨24558396594748272442169729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16372264396498848294779819 24558396594748272442169729)
            ·
              refine ⟨18418797446061204331627297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24558396594748272442169729 18418797446061204331627297)
              ·
                refine ⟨13814098084545903248720473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18418797446061204331627297 13814098084545903248720473)
                ·
                  refine ⟨10360573563409427436540355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13814098084545903248720473 10360573563409427436540355)
                  ·
                    refine ⟨15540860345114141154810533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10360573563409427436540355 15540860345114141154810533)
                    ·
                      refine ⟨2913911314708901466526975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15540860345114141154810533 2913911314708901466526975)
                      ·
                        rfl

theorem cell23_5674822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_5674822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674822 prefixEnd_5674822 := by exact prefixLift 5674822
  have htrace : WordTrace (prefixWord ++ tailWord_5674822) baseStart_5674822 baseEnd_5674822 := by
    simpa [prefixWord, tailWord_5674822, baseEnd_5674822] using wordTrace_append hprefix tailTrace_5674822
  have hstable : (prefixWord ++ tailWord_5674822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674822).length < 2 ^ (prefixWord ++ tailWord_5674822).sum := by decide
  have hdescent : baseEnd_5674822 < baseStart_5674822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674841 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 5, 5]
def baseStart_5674841 : Nat := 118140960795 + 5674841 * 2 ^ 59
def prefixEnd_5674841 : Nat := 4983230072969 + 3 ^ 40 * 5674841 * 2
def baseEnd_5674841 : Nat := 971307023613778964063129

theorem tailTrace_5674841 : CollatzResearch.WordTrace tailWord_5674841 prefixEnd_5674841 971307023613778964063129 := by
  unfold tailWord_5674841
  simp only [CollatzResearch.WordTrace]
  refine ⟨206978455234027717527096377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137985636822685145018064251 206978455234027717527096377)
  ·
    refine ⟨155233841425520788145322283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206978455234027717527096377 155233841425520788145322283)
    ·
      refine ⟨232850762138281182217983425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155233841425520788145322283 232850762138281182217983425)
      ·
        refine ⟨174638071603710886663487569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232850762138281182217983425 174638071603710886663487569)
        ·
          refine ⟨130978553702783164997615677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174638071603710886663487569 130978553702783164997615677)
          ·
            refine ⟨49116957638543686874105879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130978553702783164997615677 49116957638543686874105879)
            ·
              refine ⟨73675436457815530311158819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49116957638543686874105879 73675436457815530311158819)
              ·
                refine ⟨110513154686723295466738229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73675436457815530311158819 110513154686723295466738229)
                ·
                  refine ⟨10360608251880308950006709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110513154686723295466738229 10360608251880308950006709)
                  ·
                    refine ⟨971307023613778964063129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10360608251880308950006709 971307023613778964063129)
                    ·
                      rfl

theorem cell23_5674841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 5].length) (baseStart_5674841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674841 prefixEnd_5674841 := by exact prefixLift 5674841
  have htrace : WordTrace (prefixWord ++ tailWord_5674841) baseStart_5674841 baseEnd_5674841 := by
    simpa [prefixWord, tailWord_5674841, baseEnd_5674841] using wordTrace_append hprefix tailTrace_5674841
  have hstable : (prefixWord ++ tailWord_5674841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674841).length < 2 ^ (prefixWord ++ tailWord_5674841).sum := by decide
  have hdescent : baseEnd_5674841 < baseStart_5674841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674855 : List Nat := [1, 1, 5, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_5674855 : Nat := 118140960795 + 5674855 * 2 ^ 59
def prefixEnd_5674855 : Nat := 4983230072969 + 3 ^ 40 * 5674855 * 2
def baseEnd_5674855 : Nat := 2913928259570499837414323

theorem tailTrace_5674855 : CollatzResearch.WordTrace tailWord_5674855 prefixEnd_5674855 2913928259570499837414323 := by
  unfold tailWord_5674855
  simp only [CollatzResearch.WordTrace]
  refine ⟨206978965855976997918106019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137985977237317998612070679 206978965855976997918106019)
  ·
    refine ⟨310468448783965496877159029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206978965855976997918106019 310468448783965496877159029)
    ·
      refine ⟨29106417073496765332233659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 310468448783965496877159029 29106417073496765332233659)
      ·
        refine ⟨43659625610245147998350489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29106417073496765332233659 43659625610245147998350489)
        ·
          refine ⟨32744719207683860998762867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43659625610245147998350489 32744719207683860998762867)
          ·
            refine ⟨49117078811525791498144301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32744719207683860998762867 49117078811525791498144301)
            ·
              refine ⟨18418904554322171811804113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49117078811525791498144301 18418904554322171811804113)
              ·
                refine ⟨13814178415741628858853085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18418904554322171811804113 13814178415741628858853085)
                ·
                  refine ⟨5180316905903110822069907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13814178415741628858853085 5180316905903110822069907)
                  ·
                    refine ⟨7770475358854666233104861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5180316905903110822069907 7770475358854666233104861)
                    ·
                      refine ⟨2913928259570499837414323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7770475358854666233104861 2913928259570499837414323)
                      ·
                        rfl

theorem cell23_5674855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_5674855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674855 prefixEnd_5674855 := by exact prefixLift 5674855
  have htrace : WordTrace (prefixWord ++ tailWord_5674855) baseStart_5674855 baseEnd_5674855 := by
    simpa [prefixWord, tailWord_5674855, baseEnd_5674855] using wordTrace_append hprefix tailTrace_5674855
  have hstable : (prefixWord ++ tailWord_5674855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674855).length < 2 ^ (prefixWord ++ tailWord_5674855).sum := by decide
  have hdescent : baseEnd_5674855 < baseStart_5674855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674891 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 6]
def baseStart_5674891 : Nat := 118140960795 + 5674891 * 2 ^ 59
def prefixEnd_5674891 : Nat := 4983230072969 + 3 ^ 40 * 5674891 * 2
def baseEnd_5674891 : Nat := 2913946744874061696564157

theorem tailTrace_5674891 : CollatzResearch.WordTrace tailWord_5674891 prefixEnd_5674891 2913946744874061696564157 := by
  unfold tailWord_5674891
  simp only [CollatzResearch.WordTrace]
  refine ⟨206980278883846576066416527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137986852589231050710944351 206980278883846576066416527)
  ·
    refine ⟨310470418325769864099624791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206980278883846576066416527 310470418325769864099624791)
    ·
      refine ⟨465705627488654796149437187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310470418325769864099624791 465705627488654796149437187)
      ·
        refine ⟨698558441232982194224155781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465705627488654796149437187 698558441232982194224155781)
        ·
          refine ⟨130979707731184161417029209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 698558441232982194224155781 130979707731184161417029209)
          ·
            refine ⟨98234780798388121062771907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130979707731184161417029209 98234780798388121062771907)
            ·
              refine ⟨147352171197582181594157861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98234780798388121062771907 147352171197582181594157861)
              ·
                refine ⟨27628532099546659048904599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147352171197582181594157861 27628532099546659048904599)
                ·
                  refine ⟨41442798149319988573356899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27628532099546659048904599 41442798149319988573356899)
                  ·
                    refine ⟨62164197223979982860035349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41442798149319988573356899 62164197223979982860035349)
                    ·
                      refine ⟨2913946744874061696564157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62164197223979982860035349 2913946744874061696564157)
                      ·
                        rfl

theorem cell23_5674891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 6].length) (baseStart_5674891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674891 prefixEnd_5674891 := by exact prefixLift 5674891
  have htrace : WordTrace (prefixWord ++ tailWord_5674891) baseStart_5674891 baseEnd_5674891 := by
    simpa [prefixWord, tailWord_5674891, baseEnd_5674891] using wordTrace_append hprefix tailTrace_5674891
  have hstable : (prefixWord ++ tailWord_5674891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674891).length < 2 ^ (prefixWord ++ tailWord_5674891).sum := by decide
  have hdescent : baseEnd_5674891 < baseStart_5674891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674901 : List Nat := [1, 3, 2, 1, 1, 3, 2, 10]
def baseStart_5674901 : Nat := 118140960795 + 5674901 * 2 ^ 59
def prefixEnd_5674901 : Nat := 4983230072969 + 3 ^ 40 * 5674901 * 2
def baseEnd_5674901 : Nat := 107924143691874320645893

theorem tailTrace_5674901 : CollatzResearch.WordTrace tailWord_5674901 prefixEnd_5674901 107924143691874320645893 := by
  unfold tailWord_5674901
  simp only [CollatzResearch.WordTrace]
  refine ⟨206980643613810347774280557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137987095742540231849520371 206980643613810347774280557)
  ·
    refine ⟨77617741355178880415355209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206980643613810347774280557 77617741355178880415355209)
    ·
      refine ⟨58213306016384160311516407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77617741355178880415355209 58213306016384160311516407)
      ·
        refine ⟨87319959024576240467274611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58213306016384160311516407 87319959024576240467274611)
        ·
          refine ⟨130979938536864360700911917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87319959024576240467274611 130979938536864360700911917)
          ·
            refine ⟨49117476951324135262841969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130979938536864360700911917 49117476951324135262841969)
            ·
              refine ⟨36838107713493101447131477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49117476951324135262841969 36838107713493101447131477)
              ·
                refine ⟨107924143691874320645893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36838107713493101447131477 107924143691874320645893)
                ·
                  rfl

theorem cell23_5674901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 10].length) (baseStart_5674901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674901 prefixEnd_5674901 := by exact prefixLift 5674901
  have htrace : WordTrace (prefixWord ++ tailWord_5674901) baseStart_5674901 baseEnd_5674901 := by
    simpa [prefixWord, tailWord_5674901, baseEnd_5674901] using wordTrace_append hprefix tailTrace_5674901
  have hstable : (prefixWord ++ tailWord_5674901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674901).length < 2 ^ (prefixWord ++ tailWord_5674901).sum := by decide
  have hdescent : baseEnd_5674901 < baseStart_5674901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674955 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 3, 3, 2]
def baseStart_5674955 : Nat := 118140960795 + 5674955 * 2 ^ 59
def prefixEnd_5674955 : Nat := 4983230072969 + 3 ^ 40 * 5674955 * 2
def baseEnd_5674955 : Nat := 2913979607635949446163863

theorem tailTrace_5674955 : CollatzResearch.WordTrace tailWord_5674955 prefixEnd_5674955 2913979607635949446163863 := by
  unfold tailWord_5674955
  simp only [CollatzResearch.WordTrace]
  refine ⟨206982613155614714996746319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137988408770409809997830879 206982613155614714996746319)
  ·
    refine ⟨310473919733422072495119479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206982613155614714996746319 310473919733422072495119479)
    ·
      refine ⟨465710879600133108742679219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310473919733422072495119479 465710879600133108742679219)
      ·
        refine ⟨698566319400199663114018829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465710879600133108742679219 698566319400199663114018829)
        ·
          refine ⟨261962369775074873667757061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 698566319400199663114018829 261962369775074873667757061)
          ·
            refine ⟨49117944332826538812704449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 261962369775074873667757061 49117944332826538812704449)
            ·
              refine ⟨36838458249619904109528337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49117944332826538812704449 36838458249619904109528337)
              ·
                refine ⟨27628843687214928082146253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36838458249619904109528337 27628843687214928082146253)
                ·
                  refine ⟨10360816382705598030804845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27628843687214928082146253 10360816382705598030804845)
                  ·
                    refine ⟨3885306143514599261551817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10360816382705598030804845 3885306143514599261551817)
                    ·
                      refine ⟨2913979607635949446163863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3885306143514599261551817 2913979607635949446163863)
                      ·
                        rfl

theorem cell23_5674955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 3, 2].length) (baseStart_5674955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674955 prefixEnd_5674955 := by exact prefixLift 5674955
  have htrace : WordTrace (prefixWord ++ tailWord_5674955) baseStart_5674955 baseEnd_5674955 := by
    simpa [prefixWord, tailWord_5674955, baseEnd_5674955] using wordTrace_append hprefix tailTrace_5674955
  have hstable : (prefixWord ++ tailWord_5674955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674955).length < 2 ^ (prefixWord ++ tailWord_5674955).sum := by decide
  have hdescent : baseEnd_5674955 < baseStart_5674955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674966 : List Nat := [5, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_5674966 : Nat := 118140960795 + 5674966 * 2 ^ 59
def prefixEnd_5674966 : Nat := 4983230072969 + 3 ^ 40 * 5674966 * 2
def baseEnd_5674966 : Nat := 2913985255923148903126313

theorem tailTrace_5674966 : CollatzResearch.WordTrace tailWord_5674966 prefixEnd_5674966 2913985255923148903126313 := by
  unfold tailWord_5674966
  simp only [CollatzResearch.WordTrace]
  refine ⟨12936438397410928992212297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137988676239049909250264501 12936438397410928992212297)
  ·
    refine ⟨9702328798058196744159223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12936438397410928992212297 9702328798058196744159223)
    ·
      refine ⟨14553493197087295116238835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9702328798058196744159223 14553493197087295116238835)
      ·
        refine ⟨21830239795630942674358253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14553493197087295116238835 21830239795630942674358253)
        ·
          refine ⟨8186339923361603502884345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21830239795630942674358253 8186339923361603502884345)
          ·
            refine ⟨6139754942521202627163259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8186339923361603502884345 6139754942521202627163259)
            ·
              refine ⟨9209632413781803940744889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6139754942521202627163259 9209632413781803940744889)
              ·
                refine ⟨6907224310336352955558667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9209632413781803940744889 6907224310336352955558667)
                ·
                  refine ⟨10360836465504529433338001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6907224310336352955558667 10360836465504529433338001)
                  ·
                    refine ⟨7770627349128397075003501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10360836465504529433338001 7770627349128397075003501)
                    ·
                      refine ⟨2913985255923148903126313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7770627349128397075003501 2913985255923148903126313)
                      ·
                        rfl

theorem cell23_5674966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_5674966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674966 prefixEnd_5674966 := by exact prefixLift 5674966
  have htrace : WordTrace (prefixWord ++ tailWord_5674966) baseStart_5674966 baseEnd_5674966 := by
    simpa [prefixWord, tailWord_5674966, baseEnd_5674966] using wordTrace_append hprefix tailTrace_5674966
  have hstable : (prefixWord ++ tailWord_5674966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674966).length < 2 ^ (prefixWord ++ tailWord_5674966).sum := by decide
  have hdescent : baseEnd_5674966 < baseStart_5674966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5674988 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 3]
def baseStart_5674988 : Nat := 118140960795 + 5674988 * 2 ^ 59
def prefixEnd_5674988 : Nat := 4983230072969 + 3 ^ 40 * 5674988 * 2
def baseEnd_5674988 : Nat := 2913996552497547817051211

theorem tailTrace_5674988 : CollatzResearch.WordTrace tailWord_5674988 prefixEnd_5674988 2913996552497547817051211 := by
  unfold tailWord_5674988
  simp only [CollatzResearch.WordTrace]
  refine ⟨103491908382247580816348809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137989211176330107755131745 103491908382247580816348809)
  ·
    refine ⟨77618931286685685612261607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103491908382247580816348809 77618931286685685612261607)
    ·
      refine ⟨116428396930028528418392411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77618931286685685612261607 116428396930028528418392411)
      ·
        refine ⟨174642595395042792627588617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116428396930028528418392411 174642595395042792627588617)
        ·
          refine ⟨130981946546282094470691463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174642595395042792627588617 130981946546282094470691463)
          ·
            refine ⟨196472919819423141706037195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130981946546282094470691463 196472919819423141706037195)
            ·
              refine ⟨294709379729134712559055793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196472919819423141706037195 294709379729134712559055793)
              ·
                refine ⟨221032034796851034419291845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294709379729134712559055793 221032034796851034419291845)
                ·
                  refine ⟨41443506524409568953617221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 221032034796851034419291845 41443506524409568953617221)
                  ·
                    refine ⟨7770657473326794178803229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41443506524409568953617221 7770657473326794178803229)
                    ·
                      refine ⟨2913996552497547817051211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7770657473326794178803229 2913996552497547817051211)
                      ·
                        rfl

theorem cell23_5674988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_5674988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5674988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5674988 prefixEnd_5674988 := by exact prefixLift 5674988
  have htrace : WordTrace (prefixWord ++ tailWord_5674988) baseStart_5674988 baseEnd_5674988 := by
    simpa [prefixWord, tailWord_5674988, baseEnd_5674988] using wordTrace_append hprefix tailTrace_5674988
  have hstable : (prefixWord ++ tailWord_5674988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5674988).length < 2 ^ (prefixWord ++ tailWord_5674988).sum := by decide
  have hdescent : baseEnd_5674988 < baseStart_5674988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5674988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675012 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 2, 6]
def baseStart_5675012 : Nat := 118140960795 + 5675012 * 2 ^ 59
def prefixEnd_5675012 : Nat := 4983230072969 + 3 ^ 40 * 5675012 * 2
def baseEnd_5675012 : Nat := 971336292011085241050367

theorem tailTrace_5675012 : CollatzResearch.WordTrace tailWord_5675012 prefixEnd_5675012 971336292011085241050367 := by
  unfold tailWord_5675012
  simp only [CollatzResearch.WordTrace]
  refine ⟨103492346058204106865785645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137989794744272142487714193 103492346058204106865785645)
  ·
    refine ⟨38809629771826540074669617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103492346058204106865785645 38809629771826540074669617)
    ·
      refine ⟨29107222328869905056002213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38809629771826540074669617 29107222328869905056002213)
      ·
        refine ⟨5457604186663107198000415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29107222328869905056002213 5457604186663107198000415)
        ·
          refine ⟨8186406279994660797000623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5457604186663107198000415 8186406279994660797000623)
          ·
            refine ⟨12279609419991991195500935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8186406279994660797000623 12279609419991991195500935)
            ·
              refine ⟨18419414129987986793251403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12279609419991991195500935 18419414129987986793251403)
              ·
                refine ⟨27629121194981980189877105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18419414129987986793251403 27629121194981980189877105)
                ·
                  refine ⟨20721840896236485142407829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27629121194981980189877105 20721840896236485142407829)
                  ·
                    refine ⟨971336292011085241050367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20721840896236485142407829 971336292011085241050367)
                    ·
                      rfl

theorem cell23_5675012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_5675012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675012 prefixEnd_5675012 := by exact prefixLift 5675012
  have htrace : WordTrace (prefixWord ++ tailWord_5675012) baseStart_5675012 baseEnd_5675012 := by
    simpa [prefixWord, tailWord_5675012, baseEnd_5675012] using wordTrace_append hprefix tailTrace_5675012
  have hstable : (prefixWord ++ tailWord_5675012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675012).length < 2 ^ (prefixWord ++ tailWord_5675012).sum := by decide
  have hdescent : baseEnd_5675012 < baseStart_5675012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675015 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_5675015 : Nat := 118140960795 + 5675015 * 2 ^ 59
def prefixEnd_5675015 : Nat := 4983230072969 + 3 ^ 40 * 5675015 * 2
def baseEnd_5675015 : Nat := 2914010416475219211413587

theorem tailTrace_5675015 : CollatzResearch.WordTrace tailWord_5675015 prefixEnd_5675015 2914010416475219211413587 := by
  unfold tailWord_5675015
  simp only [CollatzResearch.WordTrace]
  refine ⟨206984801535397345243930499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137989867690264896829286999 206984801535397345243930499)
  ·
    refine ⟨310477202303096017865895749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206984801535397345243930499 310477202303096017865895749)
    ·
      refine ⟨58214475431830503349855453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310477202303096017865895749 58214475431830503349855453)
      ·
        refine ⟨21830428286936438756195795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58214475431830503349855453 21830428286936438756195795)
        ·
          refine ⟨32745642430404658134293693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21830428286936438756195795 32745642430404658134293693)
          ·
            refine ⟨12279615911401746800360135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32745642430404658134293693 12279615911401746800360135)
            ·
              refine ⟨18419423867102620200540203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12279615911401746800360135 18419423867102620200540203)
              ·
                refine ⟨27629135800653930300810305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18419423867102620200540203 27629135800653930300810305)
                ·
                  refine ⟨20721851850490447725607729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27629135800653930300810305 20721851850490447725607729)
                  ·
                    refine ⟨15541388887867835794205797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20721851850490447725607729 15541388887867835794205797)
                    ·
                      refine ⟨2914010416475219211413587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15541388887867835794205797 2914010416475219211413587)
                      ·
                        rfl

theorem cell23_5675015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_5675015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675015 prefixEnd_5675015 := by exact prefixLift 5675015
  have htrace : WordTrace (prefixWord ++ tailWord_5675015) baseStart_5675015 baseEnd_5675015 := by
    simpa [prefixWord, tailWord_5675015, baseEnd_5675015] using wordTrace_append hprefix tailTrace_5675015
  have hstable : (prefixWord ++ tailWord_5675015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675015).length < 2 ^ (prefixWord ++ tailWord_5675015).sum := by decide
  have hdescent : baseEnd_5675015 < baseStart_5675015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675042 : List Nat := [3, 3, 1, 1, 1, 2, 4, 3, 5]
def baseStart_5675042 : Nat := 118140960795 + 5675042 * 2 ^ 59
def prefixEnd_5675042 : Nat := 4983230072969 + 3 ^ 40 * 5675042 * 2
def baseEnd_5675042 : Nat := 323780475605876733975107

theorem tailTrace_5675042 : CollatzResearch.WordTrace tailWord_5675042 prefixEnd_5675042 323780475605876733975107 := by
  unfold tailWord_5675042
  simp only [CollatzResearch.WordTrace]
  refine ⟨51746446576574882213790845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137990524204199685903442253 51746446576574882213790845)
  ·
    refine ⟨19404917466215580830171567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51746446576574882213790845 19404917466215580830171567)
    ·
      refine ⟨29107376199323371245257351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19404917466215580830171567 29107376199323371245257351)
      ·
        refine ⟨43661064298985056867886027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29107376199323371245257351 43661064298985056867886027)
        ·
          refine ⟨65491596448477585301829041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43661064298985056867886027 65491596448477585301829041)
          ·
            refine ⟨49118697336358188976371781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65491596448477585301829041 49118697336358188976371781)
            ·
              refine ⟨9209755750567160433069709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49118697336358188976371781 9209755750567160433069709)
              ·
                refine ⟨3453658406462685162401141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9209755750567160433069709 3453658406462685162401141)
                ·
                  refine ⟨323780475605876733975107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3453658406462685162401141 323780475605876733975107)
                  ·
                    rfl

theorem cell23_5675042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_5675042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675042 prefixEnd_5675042 := by exact prefixLift 5675042
  have htrace : WordTrace (prefixWord ++ tailWord_5675042) baseStart_5675042 baseEnd_5675042 := by
    simpa [prefixWord, tailWord_5675042, baseEnd_5675042] using wordTrace_append hprefix tailTrace_5675042
  have hstable : (prefixWord ++ tailWord_5675042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675042).length < 2 ^ (prefixWord ++ tailWord_5675042).sum := by decide
  have hdescent : baseEnd_5675042 < baseStart_5675042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675075 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 1, 6, 2]
def baseStart_5675075 : Nat := 118140960795 + 5675075 * 2 ^ 59
def prefixEnd_5675075 : Nat := 4983230072969 + 3 ^ 40 * 5675075 * 2
def baseEnd_5675075 : Nat := 2914041225314488976663311

theorem tailTrace_5675075 : CollatzResearch.WordTrace tailWord_5675075 prefixEnd_5675075 2914041225314488976663311 := by
  unfold tailWord_5675075
  simp only [CollatzResearch.WordTrace]
  refine ⟨206986989915179975491114679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137991326610119983660743119 206986989915179975491114679)
  ·
    refine ⟨310480484872769963236672019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206986989915179975491114679 310480484872769963236672019)
    ·
      refine ⟨465720727309154944855008029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310480484872769963236672019 465720727309154944855008029)
      ·
        refine ⟨174645272740933104320628011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 465720727309154944855008029 174645272740933104320628011)
        ·
          refine ⟨261967909111399656480942017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174645272740933104320628011 261967909111399656480942017)
          ·
            refine ⟨196475931833549742360706513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261967909111399656480942017 196475931833549742360706513)
            ·
              refine ⟨147356948875162306770529885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196475931833549742360706513 147356948875162306770529885)
              ·
                refine ⟨55258855828185865038948707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147356948875162306770529885 55258855828185865038948707)
                ·
                  refine ⟨82888283742278797558423061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55258855828185865038948707 82888283742278797558423061)
                  ·
                    refine ⟨3885388300419318635551081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82888283742278797558423061 3885388300419318635551081)
                    ·
                      refine ⟨2914041225314488976663311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3885388300419318635551081 2914041225314488976663311)
                      ·
                        rfl

theorem cell23_5675075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 6, 2].length) (baseStart_5675075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675075 prefixEnd_5675075 := by exact prefixLift 5675075
  have htrace : WordTrace (prefixWord ++ tailWord_5675075) baseStart_5675075 baseEnd_5675075 := by
    simpa [prefixWord, tailWord_5675075, baseEnd_5675075] using wordTrace_append hprefix tailTrace_5675075
  have hstable : (prefixWord ++ tailWord_5675075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675075).length < 2 ^ (prefixWord ++ tailWord_5675075).sum := by decide
  have hdescent : baseEnd_5675075 < baseStart_5675075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675085 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_5675085 : Nat := 118140960795 + 5675085 * 2 ^ 59
def prefixEnd_5675085 : Nat := 4983230072969 + 3 ^ 40 * 5675085 * 2
def baseEnd_5675085 : Nat := 971348786707011312512755

theorem tailTrace_5675085 : CollatzResearch.WordTrace tailWord_5675085 prefixEnd_5675085 971348786707011312512755 := by
  unfold tailWord_5675085
  simp only [CollatzResearch.WordTrace]
  refine ⟨206987354645143747198978709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137991569763429164799319139 206987354645143747198978709)
  ·
    refine ⟨9702532248991113149952127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 206987354645143747198978709 9702532248991113149952127)
    ·
      refine ⟨14553798373486669724928191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9702532248991113149952127 14553798373486669724928191)
      ·
        refine ⟨21830697560230004587392287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14553798373486669724928191 21830697560230004587392287)
        ·
          refine ⟨32746046340345006881088431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21830697560230004587392287 32746046340345006881088431)
          ·
            refine ⟨49119069510517510321632647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32746046340345006881088431 49119069510517510321632647)
            ·
              refine ⟨73678604265776265482448971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49119069510517510321632647 73678604265776265482448971)
              ·
                refine ⟨110517906398664398223673457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73678604265776265482448971 110517906398664398223673457)
                ·
                  refine ⟨82888429798998298667755093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110517906398664398223673457 82888429798998298667755093)
                  ·
                    refine ⟨971348786707011312512755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82888429798998298667755093 971348786707011312512755)
                    ·
                      rfl

theorem cell23_5675085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_5675085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675085 prefixEnd_5675085 := by exact prefixLift 5675085
  have htrace : WordTrace (prefixWord ++ tailWord_5675085) baseStart_5675085 baseEnd_5675085 := by
    simpa [prefixWord, tailWord_5675085, baseEnd_5675085] using wordTrace_append hprefix tailTrace_5675085
  have hstable : (prefixWord ++ tailWord_5675085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675085).length < 2 ^ (prefixWord ++ tailWord_5675085).sum := by decide
  have hdescent : baseEnd_5675085 < baseStart_5675085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675095 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 3]
def baseStart_5675095 : Nat := 118140960795 + 5675095 * 2 ^ 59
def prefixEnd_5675095 : Nat := 4983230072969 + 3 ^ 40 * 5675095 * 2
def baseEnd_5675095 : Nat := 2914051494927578898413219

theorem tailTrace_5675095 : CollatzResearch.WordTrace tailWord_5675095 prefixEnd_5675095 2914051494927578898413219 := by
  unfold tailWord_5675095
  simp only [CollatzResearch.WordTrace]
  refine ⟨206987719375107518906842739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137991812916738345937895159 206987719375107518906842739)
  ·
    refine ⟨310481579062661278360264109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206987719375107518906842739 310481579062661278360264109)
    ·
      refine ⟨116430592148497979385099041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310481579062661278360264109 116430592148497979385099041)
      ·
        refine ⟨87322944111373484538824281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116430592148497979385099041 87322944111373484538824281)
        ·
          refine ⟨65492208083530113404118211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87322944111373484538824281 65492208083530113404118211)
          ·
            refine ⟨98238312125295170106177317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65492208083530113404118211 98238312125295170106177317)
            ·
              refine ⟨18419683523492844394908247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98238312125295170106177317 18419683523492844394908247)
              ·
                refine ⟨27629525285239266592362371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18419683523492844394908247 27629525285239266592362371)
                ·
                  refine ⟨41444287927858899888543557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27629525285239266592362371 41444287927858899888543557)
                  ·
                    refine ⟨7770803986473543729101917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41444287927858899888543557 7770803986473543729101917)
                    ·
                      refine ⟨2914051494927578898413219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7770803986473543729101917 2914051494927578898413219)
                      ·
                        rfl

theorem cell23_5675095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_5675095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675095 prefixEnd_5675095 := by exact prefixLift 5675095
  have htrace : WordTrace (prefixWord ++ tailWord_5675095) baseStart_5675095 baseEnd_5675095 := by
    simpa [prefixWord, tailWord_5675095, baseEnd_5675095] using wordTrace_append hprefix tailTrace_5675095
  have hstable : (prefixWord ++ tailWord_5675095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675095).length < 2 ^ (prefixWord ++ tailWord_5675095).sum := by decide
  have hdescent : baseEnd_5675095 < baseStart_5675095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675098 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 10]
def baseStart_5675098 : Nat := 118140960795 + 5675098 * 2 ^ 59
def prefixEnd_5675098 : Nat := 4983230072969 + 3 ^ 40 * 5675098 * 2
def baseEnd_5675098 : Nat := 323783670596615820741745

theorem tailTrace_5675098 : CollatzResearch.WordTrace tailWord_5675098 prefixEnd_5675098 323783670596615820741745 := by
  unfold tailWord_5675098
  simp only [CollatzResearch.WordTrace]
  refine ⟨51746957198524162604800487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137991885862731100279467965 51746957198524162604800487)
  ·
    refine ⟨77620435797786243907200731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51746957198524162604800487 77620435797786243907200731)
    ·
      refine ⟨116430653696679365860801097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77620435797786243907200731 116430653696679365860801097)
      ·
        refine ⟨87322990272509524395600823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116430653696679365860801097 87322990272509524395600823)
        ·
          refine ⟨130984485408764286593401235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87322990272509524395600823 130984485408764286593401235)
          ·
            refine ⟨196476728113146429890101853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130984485408764286593401235 196476728113146429890101853)
            ·
              refine ⟨73678773042429911208788195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196476728113146429890101853 73678773042429911208788195)
              ·
                refine ⟨110518159563644866813182293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73678773042429911208788195 110518159563644866813182293)
                ·
                  refine ⟨323783670596615820741745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 110518159563644866813182293 323783670596615820741745)
                  ·
                    rfl

theorem cell23_5675098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 10].length) (baseStart_5675098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675098 prefixEnd_5675098 := by exact prefixLift 5675098
  have htrace : WordTrace (prefixWord ++ tailWord_5675098) baseStart_5675098 baseEnd_5675098 := by
    simpa [prefixWord, tailWord_5675098, baseEnd_5675098] using wordTrace_append hprefix tailTrace_5675098
  have hstable : (prefixWord ++ tailWord_5675098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675098).length < 2 ^ (prefixWord ++ tailWord_5675098).sum := by decide
  have hdescent : baseEnd_5675098 < baseStart_5675098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675128 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 2, 9]
def baseStart_5675128 : Nat := 118140960795 + 5675128 * 2 ^ 59
def prefixEnd_5675128 : Nat := 4983230072969 + 3 ^ 40 * 5675128 * 2
def baseEnd_5675128 : Nat := 971356146596392423100189

theorem tailTrace_5675128 : CollatzResearch.WordTrace tailWord_5675128 prefixEnd_5675128 971356146596392423100189 := by
  unfold tailWord_5675128
  simp only [CollatzResearch.WordTrace]
  refine ⟨103494461491993982771397019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137992615322658643695196025 103494461491993982771397019)
  ·
    refine ⟨155241692237990974157095529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103494461491993982771397019 155241692237990974157095529)
    ·
      refine ⟨116431269178493230617821647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155241692237990974157095529 116431269178493230617821647)
      ·
        refine ⟨174646903767739845926732471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116431269178493230617821647 174646903767739845926732471)
        ·
          refine ⟨261970355651609768890098707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174646903767739845926732471 261970355651609768890098707)
          ·
            refine ⟨392955533477414653335148061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261970355651609768890098707 392955533477414653335148061)
            ·
              refine ⟨147358325054030495000680523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 392955533477414653335148061 147358325054030495000680523)
              ·
                refine ⟨221037487581045742501020785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147358325054030495000680523 221037487581045742501020785)
                ·
                  refine ⟨165778115685784306875765589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221037487581045742501020785 165778115685784306875765589)
                  ·
                    refine ⟨971356146596392423100189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 165778115685784306875765589 971356146596392423100189)
                    ·
                      rfl

theorem cell23_5675128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_5675128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675128 prefixEnd_5675128 := by exact prefixLift 5675128
  have htrace : WordTrace (prefixWord ++ tailWord_5675128) baseStart_5675128 baseEnd_5675128 := by
    simpa [prefixWord, tailWord_5675128, baseEnd_5675128] using wordTrace_append hprefix tailTrace_5675128
  have hstable : (prefixWord ++ tailWord_5675128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675128).length < 2 ^ (prefixWord ++ tailWord_5675128).sum := by decide
  have hdescent : baseEnd_5675128 < baseStart_5675128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675132 : List Nat := [2, 2, 2, 1, 1, 4, 4, 1, 6]
def baseStart_5675132 : Nat := 118140960795 + 5675132 * 2 ^ 59
def prefixEnd_5675132 : Nat := 4983230072969 + 3 ^ 40 * 5675132 * 2
def baseEnd_5675132 : Nat := 323785610412421694850061

theorem tailTrace_5675132 : CollatzResearch.WordTrace tailWord_5675132 prefixEnd_5675132 323785610412421694850061 := by
  unfold tailWord_5675132
  simp only [CollatzResearch.WordTrace]
  refine ⟨103494534437986737112969825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137992712583982316150626433 103494534437986737112969825)
  ·
    refine ⟨77620900828490052834727369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103494534437986737112969825 77620900828490052834727369)
    ·
      refine ⟨58215675621367539626045527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77620900828490052834727369 58215675621367539626045527)
      ·
        refine ⟨87323513432051309439068291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58215675621367539626045527 87323513432051309439068291)
        ·
          refine ⟨130985270148076964158602437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87323513432051309439068291 130985270148076964158602437)
          ·
            refine ⟨24559738152764430779737957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130985270148076964158602437 24559738152764430779737957)
            ·
              refine ⟨4604950903643330771200867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24559738152764430779737957 4604950903643330771200867)
              ·
                refine ⟨6907426355464996156801301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4604950903643330771200867 6907426355464996156801301)
                ·
                  refine ⟨323785610412421694850061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6907426355464996156801301 323785610412421694850061)
                  ·
                    rfl

theorem cell23_5675132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 6].length) (baseStart_5675132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675132 prefixEnd_5675132 := by exact prefixLift 5675132
  have htrace : WordTrace (prefixWord ++ tailWord_5675132) baseStart_5675132 baseEnd_5675132 := by
    simpa [prefixWord, tailWord_5675132, baseEnd_5675132] using wordTrace_append hprefix tailTrace_5675132
  have hstable : (prefixWord ++ tailWord_5675132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675132).length < 2 ^ (prefixWord ++ tailWord_5675132).sum := by decide
  have hdescent : baseEnd_5675132 < baseStart_5675132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675145 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 3, 5]
def baseStart_5675145 : Nat := 118140960795 + 5675145 * 2 ^ 59
def prefixEnd_5675145 : Nat := 4983230072969 + 3 ^ 40 * 5675145 * 2
def baseEnd_5675145 : Nat := 971359056320101234262663

theorem tailTrace_5675145 : CollatzResearch.WordTrace tailWord_5675145 prefixEnd_5675145 971359056320101234262663 := by
  unfold tailWord_5675145
  simp only [CollatzResearch.WordTrace]
  refine ⟨206989543024926377446162889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137993028683284251630775259 206989543024926377446162889)
  ·
    refine ⟨155242157268694783084622167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206989543024926377446162889 155242157268694783084622167)
    ·
      refine ⟨232863235903042174626933251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155242157268694783084622167 232863235903042174626933251)
      ·
        refine ⟨349294853854563261940399877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232863235903042174626933251 349294853854563261940399877)
        ·
          refine ⟨65492785097730611613824977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 349294853854563261940399877 65492785097730611613824977)
          ·
            refine ⟨49119588823297958710368733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65492785097730611613824977 49119588823297958710368733)
            ·
              refine ⟨18419845808736734516388275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49119588823297958710368733 18419845808736734516388275)
              ·
                refine ⟨27629768713105101774582413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18419845808736734516388275 27629768713105101774582413)
                ·
                  refine ⟨10361163267414413165468405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27629768713105101774582413 10361163267414413165468405)
                  ·
                    refine ⟨971359056320101234262663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10361163267414413165468405 971359056320101234262663)
                    ·
                      rfl

theorem cell23_5675145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 5].length) (baseStart_5675145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675145 prefixEnd_5675145 := by exact prefixLift 5675145
  have htrace : WordTrace (prefixWord ++ tailWord_5675145) baseStart_5675145 baseEnd_5675145 := by
    simpa [prefixWord, tailWord_5675145, baseEnd_5675145] using wordTrace_append hprefix tailTrace_5675145
  have hstable : (prefixWord ++ tailWord_5675145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675145).length < 2 ^ (prefixWord ++ tailWord_5675145).sum := by decide
  have hdescent : baseEnd_5675145 < baseStart_5675145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675169 : List Nat := [1, 2, 3, 3, 1, 2, 2, 2, 2, 3, 2]
def baseStart_5675169 : Nat := 118140960795 + 5675169 * 2 ^ 59
def prefixEnd_5675169 : Nat := 4983230072969 + 3 ^ 40 * 5675169 * 2
def baseEnd_5675169 : Nat := 2914089492496011608887879

theorem tailTrace_5675169 : CollatzResearch.WordTrace tailWord_5675169 prefixEnd_5675169 2914089492496011608887879 := by
  unfold tailWord_5675169
  simp only [CollatzResearch.WordTrace]
  refine ⟨206990418376839429545036561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137993612251226286363357707 206990418376839429545036561)
  ·
    refine ⟨155242813782629572158777421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206990418376839429545036561 155242813782629572158777421)
    ·
      refine ⟨58216055168486089559541533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155242813782629572158777421 58216055168486089559541533)
      ·
        refine ⟨21831020688182283584828075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58216055168486089559541533 21831020688182283584828075)
        ·
          refine ⟨32746531032273425377242113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21831020688182283584828075 32746531032273425377242113)
          ·
            refine ⟨24559898274205069032931585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32746531032273425377242113 24559898274205069032931585)
            ·
              refine ⟨18419923705653801774698689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24559898274205069032931585 18419923705653801774698689)
              ·
                refine ⟨13814942779240351331024017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18419923705653801774698689 13814942779240351331024017)
                ·
                  refine ⟨10361207084430263498268013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13814942779240351331024017 10361207084430263498268013)
                  ·
                    refine ⟨3885452656661348811850505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10361207084430263498268013 3885452656661348811850505)
                    ·
                      refine ⟨2914089492496011608887879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3885452656661348811850505 2914089492496011608887879)
                      ·
                        rfl

theorem cell23_5675169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_5675169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675169 prefixEnd_5675169 := by exact prefixLift 5675169
  have htrace : WordTrace (prefixWord ++ tailWord_5675169) baseStart_5675169 baseEnd_5675169 := by
    simpa [prefixWord, tailWord_5675169, baseEnd_5675169] using wordTrace_append hprefix tailTrace_5675169
  have hstable : (prefixWord ++ tailWord_5675169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675169).length < 2 ^ (prefixWord ++ tailWord_5675169).sum := by decide
  have hdescent : baseEnd_5675169 < baseStart_5675169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675192 : List Nat := [2, 1, 2, 1, 2, 1, 3, 5, 2, 4]
def baseStart_5675192 : Nat := 118140960795 + 5675192 * 2 ^ 59
def prefixEnd_5675192 : Nat := 4983230072969 + 3 ^ 40 * 5675192 * 2
def baseEnd_5675192 : Nat := 971367100850355006300091

theorem tailTrace_5675192 : CollatzResearch.WordTrace tailWord_5675192 prefixEnd_5675192 971367100850355006300091 := by
  unfold tailWord_5675192
  simp only [CollatzResearch.WordTrace]
  refine ⟨103495628627878052236561915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137994171503837402982082553 103495628627878052236561915)
  ·
    refine ⟨155243442941817078354842873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103495628627878052236561915 155243442941817078354842873)
    ·
      refine ⟨116432582206362808766132155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155243442941817078354842873 116432582206362808766132155)
      ·
        refine ⟨174648873309544213149198233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116432582206362808766132155 174648873309544213149198233)
        ·
          refine ⟨130986654982158159861898675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174648873309544213149198233 130986654982158159861898675)
          ·
            refine ⟨196479982473237239792848013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130986654982158159861898675 196479982473237239792848013)
            ·
              refine ⟨73679993427463964922318005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196479982473237239792848013 73679993427463964922318005)
              ·
                refine ⟨6907499383824746711467313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73679993427463964922318005 6907499383824746711467313)
                ·
                  refine ⟨5180624537868560033600485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6907499383824746711467313 5180624537868560033600485)
                  ·
                    refine ⟨971367100850355006300091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5180624537868560033600485 971367100850355006300091)
                    ·
                      rfl

theorem cell23_5675192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_5675192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675192 prefixEnd_5675192 := by exact prefixLift 5675192
  have htrace : WordTrace (prefixWord ++ tailWord_5675192) baseStart_5675192 baseEnd_5675192 := by
    simpa [prefixWord, tailWord_5675192, baseEnd_5675192] using wordTrace_append hprefix tailTrace_5675192
  have hstable : (prefixWord ++ tailWord_5675192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675192).length < 2 ^ (prefixWord ++ tailWord_5675192).sum := by decide
  have hdescent : baseEnd_5675192 < baseStart_5675192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675249 : List Nat := [1, 2, 2, 2, 2, 1, 2, 5, 2, 1, 3]
def baseStart_5675249 : Nat := 118140960795 + 5675249 * 2 ^ 59
def prefixEnd_5675249 : Nat := 4983230072969 + 3 ^ 40 * 5675249 * 2
def baseEnd_5675249 : Nat := 2914130570948371295887511

theorem tailTrace_5675249 : CollatzResearch.WordTrace tailWord_5675249 prefixEnd_5675249 2914130570948371295887511 := by
  unfold tailWord_5675249
  simp only [CollatzResearch.WordTrace]
  refine ⟨206993336216549603207948801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137995557477699735471965867 206993336216549603207948801)
  ·
    refine ⟨155245002162412202405961601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206993336216549603207948801 155245002162412202405961601)
    ·
      refine ⟨116433751621809151804471201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155245002162412202405961601 116433751621809151804471201)
      ·
        refine ⟨87325313716356863853353401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116433751621809151804471201 87325313716356863853353401)
        ·
          refine ⟨65493985287267647890015051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87325313716356863853353401 65493985287267647890015051)
          ·
            refine ⟨98240977930901471835022577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65493985287267647890015051 98240977930901471835022577)
            ·
              refine ⟨73680733448176103876266933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98240977930901471835022577 73680733448176103876266933)
              ·
                refine ⟨6907568760766509738400025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73680733448176103876266933 6907568760766509738400025)
                ·
                  refine ⟨5180676570574882303800019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6907568760766509738400025 5180676570574882303800019)
                  ·
                    refine ⟨7771014855862323455700029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5180676570574882303800019 7771014855862323455700029)
                    ·
                      refine ⟨2914130570948371295887511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7771014855862323455700029 2914130570948371295887511)
                      ·
                        rfl

theorem cell23_5675249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_5675249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675249 prefixEnd_5675249 := by exact prefixLift 5675249
  have htrace : WordTrace (prefixWord ++ tailWord_5675249) baseStart_5675249 baseEnd_5675249 := by
    simpa [prefixWord, tailWord_5675249, baseEnd_5675249] using wordTrace_append hprefix tailTrace_5675249
  have hstable : (prefixWord ++ tailWord_5675249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675249).length < 2 ^ (prefixWord ++ tailWord_5675249).sum := by decide
  have hdescent : baseEnd_5675249 < baseStart_5675249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675262 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_5675262 : Nat := 118140960795 + 5675262 * 2 ^ 59
def prefixEnd_5675262 : Nat := 4983230072969 + 3 ^ 40 * 5675262 * 2
def baseEnd_5675262 : Nat := 2914137246196879745024951

theorem tailTrace_5675262 : CollatzResearch.WordTrace tailWord_5675262 prefixEnd_5675262 2914137246196879745024951 := by
  unfold tailWord_5675262
  simp only [CollatzResearch.WordTrace]
  refine ⟨25874226295687813303521505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137995873577001670952114693 25874226295687813303521505)
  ·
    refine ⟨19405669721765859977641129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25874226295687813303521505 19405669721765859977641129)
    ·
      refine ⟨14554252291324394983230847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19405669721765859977641129 14554252291324394983230847)
      ·
        refine ⟨21831378436986592474846271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14554252291324394983230847 21831378436986592474846271)
        ·
          refine ⟨32747067655479888712269407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21831378436986592474846271 32747067655479888712269407)
          ·
            refine ⟨49120601483219833068404111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32747067655479888712269407 49120601483219833068404111)
            ·
              refine ⟨73680902224829749602606167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49120601483219833068404111 73680902224829749602606167)
              ·
                refine ⟨110521353337244624403909251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73680902224829749602606167 110521353337244624403909251)
                ·
                  refine ⟨165782030005866936605863877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110521353337244624403909251 165782030005866936605863877)
                  ·
                    refine ⟨31084130626100050613599477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 165782030005866936605863877 31084130626100050613599477)
                    ·
                      refine ⟨2914137246196879745024951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31084130626100050613599477 2914137246196879745024951)
                      ·
                        rfl

theorem cell23_5675262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_5675262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675262 prefixEnd_5675262 := by exact prefixLift 5675262
  have htrace : WordTrace (prefixWord ++ tailWord_5675262) baseStart_5675262 baseEnd_5675262 := by
    simpa [prefixWord, tailWord_5675262, baseEnd_5675262] using wordTrace_append hprefix tailTrace_5675262
  have hstable : (prefixWord ++ tailWord_5675262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675262).length < 2 ^ (prefixWord ++ tailWord_5675262).sum := by decide
  have hdescent : baseEnd_5675262 < baseStart_5675262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675266 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_5675266 : Nat := 118140960795 + 5675266 * 2 ^ 59
def prefixEnd_5675266 : Nat := 4983230072969 + 3 ^ 40 * 5675266 * 2
def baseEnd_5675266 : Nat := 2914139300119497729374933

theorem tailTrace_5675266 : CollatzResearch.WordTrace tailWord_5675266 prefixEnd_5675266 2914139300119497729374933 := by
  unfold tailWord_5675266
  simp only [CollatzResearch.WordTrace]
  refine ⟨51748489064372003777829413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137995970838325343407545101 51748489064372003777829413)
  ·
    refine ⟨9702841699569750708343015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51748489064372003777829413 9702841699569750708343015)
    ·
      refine ⟨14554262549354626062514523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9702841699569750708343015 14554262549354626062514523)
      ·
        refine ⟨21831393824031939093771785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14554262549354626062514523 21831393824031939093771785)
        ·
          refine ⟨16373545368023954320328839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21831393824031939093771785 16373545368023954320328839)
          ·
            refine ⟨24560318052035931480493259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16373545368023954320328839 24560318052035931480493259)
            ·
              refine ⟨36840477078053897220739889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24560318052035931480493259 36840477078053897220739889)
              ·
                refine ⟨27630357808540422915554917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36840477078053897220739889 27630357808540422915554917)
                ·
                  refine ⟨5180692089101329296666547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27630357808540422915554917 5180692089101329296666547)
                  ·
                    refine ⟨7771038133651993944999821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5180692089101329296666547 7771038133651993944999821)
                    ·
                      refine ⟨2914139300119497729374933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7771038133651993944999821 2914139300119497729374933)
                      ·
                        rfl

theorem cell23_5675266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_5675266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675266 prefixEnd_5675266 := by exact prefixLift 5675266
  have htrace : WordTrace (prefixWord ++ tailWord_5675266) baseStart_5675266 baseEnd_5675266 := by
    simpa [prefixWord, tailWord_5675266, baseEnd_5675266] using wordTrace_append hprefix tailTrace_5675266
  have hstable : (prefixWord ++ tailWord_5675266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675266).length < 2 ^ (prefixWord ++ tailWord_5675266).sum := by decide
  have hdescent : baseEnd_5675266 < baseStart_5675266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675292 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_5675292 : Nat := 118140960795 + 5675292 * 2 ^ 59
def prefixEnd_5675292 : Nat := 4983230072969 + 3 ^ 40 * 5675292 * 2
def baseEnd_5675292 : Nat := 2914152650616514627649813

theorem tailTrace_5675292 : CollatzResearch.WordTrace tailWord_5675292 prefixEnd_5675292 2914152650616514627649813 := by
  unfold tailWord_5675292
  simp only [CollatzResearch.WordTrace]
  refine ⟨103497452277696910775882065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137996603036929214367842753 103497452277696910775882065)
  ·
    refine ⟨77623089208272683081911549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103497452277696910775882065 77623089208272683081911549)
    ·
      refine ⟨29108658453102256155716831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77623089208272683081911549 29108658453102256155716831)
      ·
        refine ⟨43662987679653384233575247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29108658453102256155716831 43662987679653384233575247)
        ·
          refine ⟨65494481519480076350362871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43662987679653384233575247 65494481519480076350362871)
          ·
            refine ⟨98241722279220114525544307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65494481519480076350362871 98241722279220114525544307)
            ·
              refine ⟨147362583418830171788316461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98241722279220114525544307 147362583418830171788316461)
              ·
                refine ⟨55260968782061314420618673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147362583418830171788316461 55260968782061314420618673)
                ·
                  refine ⟨41445726586545985815464005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55260968782061314420618673 41445726586545985815464005)
                  ·
                    refine ⟨7771073734977372340399501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41445726586545985815464005 7771073734977372340399501)
                    ·
                      refine ⟨2914152650616514627649813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7771073734977372340399501 2914152650616514627649813)
                      ·
                        rfl

theorem cell23_5675292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_5675292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675292 prefixEnd_5675292 := by exact prefixLift 5675292
  have htrace : WordTrace (prefixWord ++ tailWord_5675292) baseStart_5675292 baseEnd_5675292 := by
    simpa [prefixWord, tailWord_5675292, baseEnd_5675292] using wordTrace_append hprefix tailTrace_5675292
  have hstable : (prefixWord ++ tailWord_5675292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675292).length < 2 ^ (prefixWord ++ tailWord_5675292).sum := by decide
  have hdescent : baseEnd_5675292 < baseStart_5675292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675342 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 4, 5]
def baseStart_5675342 : Nat := 118140960795 + 5675342 * 2 ^ 59
def prefixEnd_5675342 : Nat := 4983230072969 + 3 ^ 40 * 5675342 * 2
def baseEnd_5675342 : Nat := 971392774883079810674861

theorem tailTrace_5675342 : CollatzResearch.WordTrace tailWord_5675342 prefixEnd_5675342 971392774883079810674861 := by
  unfold tailWord_5675342
  simp only [CollatzResearch.WordTrace]
  refine ⟨25874591025651585011385535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137997818803475120060722853 25874591025651585011385535)
  ·
    refine ⟨38811886538477377517078303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25874591025651585011385535 38811886538477377517078303)
    ·
      refine ⟨58217829807716066275617455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38811886538477377517078303 58217829807716066275617455)
      ·
        refine ⟨87326744711574099413426183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58217829807716066275617455 87326744711574099413426183)
        ·
          refine ⟨130990117067361149120139275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87326744711574099413426183 130990117067361149120139275)
          ·
            refine ⟨196485175601041723680208913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130990117067361149120139275 196485175601041723680208913)
            ·
              refine ⟨147363881700781292760156685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196485175601041723680208913 147363881700781292760156685)
              ·
                refine ⟨55261455637792984785058757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147363881700781292760156685 55261455637792984785058757)
                ·
                  refine ⟨10361522932086184647198517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55261455637792984785058757 10361522932086184647198517)
                  ·
                    refine ⟨971392774883079810674861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10361522932086184647198517 971392774883079810674861)
                    ·
                      rfl

theorem cell23_5675342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_5675342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675342 prefixEnd_5675342 := by exact prefixLift 5675342
  have htrace : WordTrace (prefixWord ++ tailWord_5675342) baseStart_5675342 baseEnd_5675342 := by
    simpa [prefixWord, tailWord_5675342, baseEnd_5675342] using wordTrace_append hprefix tailTrace_5675342
  have hstable : (prefixWord ++ tailWord_5675342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675342).length < 2 ^ (prefixWord ++ tailWord_5675342).sum := by decide
  have hdescent : baseEnd_5675342 < baseStart_5675342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675346 : List Nat := [3, 2, 2, 1, 1, 1, 6, 2, 5]
def baseStart_5675346 : Nat := 118140960795 + 5675346 * 2 ^ 59
def prefixEnd_5675346 : Nat := 4983230072969 + 3 ^ 40 * 5675346 * 2
def baseEnd_5675346 : Nat := 323797819841317490708285

theorem tailTrace_5675346 : CollatzResearch.WordTrace tailWord_5675346 prefixEnd_5675346 323797819841317490708285 := by
  unfold tailWord_5675346
  simp only [CollatzResearch.WordTrace]
  refine ⟨51749218524299547193557473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137997916064798792516153261 51749218524299547193557473)
  ·
    refine ⟨38811913893224660395168105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51749218524299547193557473 38811913893224660395168105)
    ·
      refine ⟨29108935419918495296376079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38811913893224660395168105 29108935419918495296376079)
      ·
        refine ⟨43663403129877742944564119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29108935419918495296376079 43663403129877742944564119)
        ·
          refine ⟨65495104694816614416846179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43663403129877742944564119 65495104694816614416846179)
          ·
            refine ⟨98242657042224921625269269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65495104694816614416846179 98242657042224921625269269)
            ·
              refine ⟨4605124548854293201184497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98242657042224921625269269 4605124548854293201184497)
              ·
                refine ⟨3453843411640719900888373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4605124548854293201184497 3453843411640719900888373)
                ·
                  refine ⟨323797819841317490708285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3453843411640719900888373 323797819841317490708285)
                  ·
                    rfl

theorem cell23_5675346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_5675346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675346 prefixEnd_5675346 := by exact prefixLift 5675346
  have htrace : WordTrace (prefixWord ++ tailWord_5675346) baseStart_5675346 baseEnd_5675346 := by
    simpa [prefixWord, tailWord_5675346, baseEnd_5675346] using wordTrace_append hprefix tailTrace_5675346
  have hstable : (prefixWord ++ tailWord_5675346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675346).length < 2 ^ (prefixWord ++ tailWord_5675346).sum := by decide
  have hdescent : baseEnd_5675346 < baseStart_5675346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675399 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 3]
def baseStart_5675399 : Nat := 118140960795 + 5675399 * 2 ^ 59
def prefixEnd_5675399 : Nat := 4983230072969 + 3 ^ 40 * 5675399 * 2
def baseEnd_5675399 : Nat := 2914207593046545709011821

theorem tailTrace_5675399 : CollatzResearch.WordTrace tailWord_5675399 prefixEnd_5675399 2914207593046545709011821 := by
  unfold tailWord_5675399
  simp only [CollatzResearch.WordTrace]
  refine ⟨206998807166006178825909251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137999204777337452550606167 206998807166006178825909251)
  ·
    refine ⟨310498210749009268238863877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206998807166006178825909251 310498210749009268238863877)
    ·
      refine ⟨58218414515439237794786977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310498210749009268238863877 58218414515439237794786977)
      ·
        refine ⟨43663810886579428346090233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58218414515439237794786977 43663810886579428346090233)
        ·
          refine ⟨32747858164934571259567675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43663810886579428346090233 32747858164934571259567675)
          ·
            refine ⟨49121787247401856889351513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32747858164934571259567675 49121787247401856889351513)
            ·
              refine ⟨36841340435551392667013635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49121787247401856889351513 36841340435551392667013635)
              ·
                refine ⟨55262010653327089000520453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36841340435551392667013635 55262010653327089000520453)
                ·
                  refine ⟨10361626997498829187597585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55262010653327089000520453 10361626997498829187597585)
                  ·
                    refine ⟨7771220248124121890698189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10361626997498829187597585 7771220248124121890698189)
                    ·
                      refine ⟨2914207593046545709011821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7771220248124121890698189 2914207593046545709011821)
                      ·
                        rfl

theorem cell23_5675399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_5675399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675399 prefixEnd_5675399 := by exact prefixLift 5675399
  have htrace : WordTrace (prefixWord ++ tailWord_5675399) baseStart_5675399 baseEnd_5675399 := by
    simpa [prefixWord, tailWord_5675399, baseEnd_5675399] using wordTrace_append hprefix tailTrace_5675399
  have hstable : (prefixWord ++ tailWord_5675399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675399).length < 2 ^ (prefixWord ++ tailWord_5675399).sum := by decide
  have hdescent : baseEnd_5675399 < baseStart_5675399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675406 : List Nat := [4, 1, 1, 4, 1, 1, 1, 3, 3, 4]
def baseStart_5675406 : Nat := 118140960795 + 5675406 * 2 ^ 59
def prefixEnd_5675406 : Nat := 4983230072969 + 3 ^ 40 * 5675406 * 2
def baseEnd_5675406 : Nat := 971403729137042393874763

theorem tailTrace_5675406 : CollatzResearch.WordTrace tailWord_5675406 prefixEnd_5675406 971403729137042393874763 := by
  unfold tailWord_5675406
  simp only [CollatzResearch.WordTrace]
  refine ⟨25874882809622602377676759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137999374984653879347609381 25874882809622602377676759)
  ·
    refine ⟨38812324214433903566515139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25874882809622602377676759 38812324214433903566515139)
    ·
      refine ⟨58218486321650855349772709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38812324214433903566515139 58218486321650855349772709)
      ·
        refine ⟨10915966185309535378082383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58218486321650855349772709 10915966185309535378082383)
        ·
          refine ⟨16373949277964303067123575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10915966185309535378082383 16373949277964303067123575)
          ·
            refine ⟨24560923916946454600685363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16373949277964303067123575 24560923916946454600685363)
            ·
              refine ⟨36841385875419681901028045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24560923916946454600685363 36841385875419681901028045)
              ·
                refine ⟨13815519703282380712885517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36841385875419681901028045 13815519703282380712885517)
                ·
                  refine ⟨5180819888730892767332069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13815519703282380712885517 5180819888730892767332069)
                  ·
                    refine ⟨971403729137042393874763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5180819888730892767332069 971403729137042393874763)
                    ·
                      rfl

theorem cell23_5675406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_5675406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675406 prefixEnd_5675406 := by exact prefixLift 5675406
  have htrace : WordTrace (prefixWord ++ tailWord_5675406) baseStart_5675406 baseEnd_5675406 := by
    simpa [prefixWord, tailWord_5675406, baseEnd_5675406] using wordTrace_append hprefix tailTrace_5675406
  have hstable : (prefixWord ++ tailWord_5675406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675406).length < 2 ^ (prefixWord ++ tailWord_5675406).sum := by decide
  have hdescent : baseEnd_5675406 < baseStart_5675406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675457 : List Nat := [1, 2, 7, 1, 1, 2, 1, 1, 3, 4]
def baseStart_5675457 : Nat := 118140960795 + 5675457 * 2 ^ 59
def prefixEnd_5675457 : Nat := 4983230072969 + 3 ^ 40 * 5675457 * 2
def baseEnd_5675457 : Nat := 971412458308168827362185

theorem tailTrace_5675457 : CollatzResearch.WordTrace tailWord_5675457 prefixEnd_5675457 971412458308168827362185 := by
  unfold tailWord_5675457
  simp only [CollatzResearch.WordTrace]
  refine ⟨207000922599796054731520625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138000615066530703154347083 207000922599796054731520625)
  ·
    refine ⟨155250691949847041048640469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207000922599796054731520625 155250691949847041048640469)
    ·
      refine ⟨3638688092574540024577511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 155250691949847041048640469 3638688092574540024577511)
      ·
        refine ⟨5458032138861810036866267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3638688092574540024577511 5458032138861810036866267)
        ·
          refine ⟨8187048208292715055299401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5458032138861810036866267 8187048208292715055299401)
          ·
            refine ⟨6140286156219536291474551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8187048208292715055299401 6140286156219536291474551)
            ·
              refine ⟨9210429234329304437211827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6140286156219536291474551 9210429234329304437211827)
              ·
                refine ⟨13815643851493956655817741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9210429234329304437211827 13815643851493956655817741)
                ·
                  refine ⟨5180866444310233745931653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13815643851493956655817741 5180866444310233745931653)
                  ·
                    refine ⟨971412458308168827362185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5180866444310233745931653 971412458308168827362185)
                    ·
                      rfl

theorem cell23_5675457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_5675457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675457 prefixEnd_5675457 := by exact prefixLift 5675457
  have htrace : WordTrace (prefixWord ++ tailWord_5675457) baseStart_5675457 baseEnd_5675457 := by
    simpa [prefixWord, tailWord_5675457, baseEnd_5675457] using wordTrace_append hprefix tailTrace_5675457
  have hstable : (prefixWord ++ tailWord_5675457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675457).length < 2 ^ (prefixWord ++ tailWord_5675457).sum := by decide
  have hdescent : baseEnd_5675457 < baseStart_5675457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675463 : List Nat := [1, 1, 4, 1, 1, 6, 1, 1, 3, 1, 3]
def baseStart_5675463 : Nat := 118140960795 + 5675463 * 2 ^ 59
def prefixEnd_5675463 : Nat := 4983230072969 + 3 ^ 40 * 5675463 * 2
def baseEnd_5675463 : Nat := 2914240455808433458611527

theorem tailTrace_5675463 : CollatzResearch.WordTrace tailWord_5675463 prefixEnd_5675463 2914240455808433458611527 := by
  unfold tailWord_5675463
  simp only [CollatzResearch.WordTrace]
  refine ⟨207001141437774317756239043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138000760958516211837492695 207001141437774317756239043)
  ·
    refine ⟨310501712156661476634358565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207001141437774317756239043 310501712156661476634358565)
    ·
      refine ⟨58219071029374026868942231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310501712156661476634358565 58219071029374026868942231)
      ·
        refine ⟨87328606544061040303413347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58219071029374026868942231 87328606544061040303413347)
        ·
          refine ⟨130992909816091560455120021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87328606544061040303413347 130992909816091560455120021)
          ·
            refine ⟨6140292647629291896333751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 130992909816091560455120021 6140292647629291896333751)
            ·
              refine ⟨9210438971443937844500627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6140292647629291896333751 9210438971443937844500627)
              ·
                refine ⟨13815658457165906766750941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9210438971443937844500627 13815658457165906766750941)
                ·
                  refine ⟨5180871921437215037531603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13815658457165906766750941 5180871921437215037531603)
                  ·
                    refine ⟨7771307882155822556297405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5180871921437215037531603 7771307882155822556297405)
                    ·
                      refine ⟨2914240455808433458611527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7771307882155822556297405 2914240455808433458611527)
                      ·
                        rfl

theorem cell23_5675463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_5675463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675463 prefixEnd_5675463 := by exact prefixLift 5675463
  have htrace : WordTrace (prefixWord ++ tailWord_5675463) baseStart_5675463 baseEnd_5675463 := by
    simpa [prefixWord, tailWord_5675463, baseEnd_5675463] using wordTrace_append hprefix tailTrace_5675463
  have hstable : (prefixWord ++ tailWord_5675463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675463).length < 2 ^ (prefixWord ++ tailWord_5675463).sum := by decide
  have hdescent : baseEnd_5675463 < baseStart_5675463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675499 : List Nat := [1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 4]
def baseStart_5675499 : Nat := 118140960795 + 5675499 * 2 ^ 59
def prefixEnd_5675499 : Nat := 4983230072969 + 3 ^ 40 * 5675499 * 2
def baseEnd_5675499 : Nat := 2914258941111995317761361

theorem tailTrace_5675499 : CollatzResearch.WordTrace tailWord_5675499 prefixEnd_5675499 2914258941111995317761361 := by
  unfold tailWord_5675499
  simp only [CollatzResearch.WordTrace]
  refine ⟨207002454465643895904549551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138001636310429263936366367 207002454465643895904549551)
  ·
    refine ⟨310503681698465843856824327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207002454465643895904549551 310503681698465843856824327)
    ·
      refine ⟨465755522547698765785236491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310503681698465843856824327 465755522547698765785236491)
      ·
        refine ⟨698633283821548148677854737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465755522547698765785236491 698633283821548148677854737)
        ·
          refine ⟨523974962866161111508391053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 698633283821548148677854737 523974962866161111508391053)
          ·
            refine ⟨196490611074810416815646645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 523974962866161111508391053 196490611074810416815646645)
            ·
              refine ⟨18420994788263476576466873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 196490611074810416815646645 18420994788263476576466873)
              ·
                refine ⟨13815746091197607432350155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18420994788263476576466873 13815746091197607432350155)
                ·
                  refine ⟨20723619136796411148525233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13815746091197607432350155 20723619136796411148525233)
                  ·
                    refine ⟨15542714352597308361393925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20723619136796411148525233 15542714352597308361393925)
                    ·
                      refine ⟨2914258941111995317761361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15542714352597308361393925 2914258941111995317761361)
                      ·
                        rfl

theorem cell23_5675499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 4].length) (baseStart_5675499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675499 prefixEnd_5675499 := by exact prefixLift 5675499
  have htrace : WordTrace (prefixWord ++ tailWord_5675499) baseStart_5675499 baseEnd_5675499 := by
    simpa [prefixWord, tailWord_5675499, baseEnd_5675499] using wordTrace_append hprefix tailTrace_5675499
  have hstable : (prefixWord ++ tailWord_5675499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675499).length < 2 ^ (prefixWord ++ tailWord_5675499).sum := by decide
  have hdescent : baseEnd_5675499 < baseStart_5675499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675509 : List Nat := [1, 3, 5, 1, 13]
def baseStart_5675509 : Nat := 118140960795 + 5675509 * 2 ^ 59
def prefixEnd_5675509 : Nat := 4983230072969 + 3 ^ 40 * 5675509 * 2
def baseEnd_5675509 : Nat := 3997618759833388585235

theorem tailTrace_5675509 : CollatzResearch.WordTrace tailWord_5675509 prefixEnd_5675509 3997618759833388585235 := by
  unfold tailWord_5675509
  simp only [CollatzResearch.WordTrace]
  refine ⟨207002819195607667612413581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138001879463738445074942387 207002819195607667612413581)
  ·
    refine ⟨77626057198352875354655093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207002819195607667612413581 77626057198352875354655093)
    ·
      refine ⟨7277442862345582064498915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77626057198352875354655093 7277442862345582064498915)
      ·
        refine ⟨10916164293518373096748373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7277442862345582064498915 10916164293518373096748373)
        ·
          refine ⟨3997618759833388585235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 10916164293518373096748373 3997618759833388585235)
          ·
            rfl

theorem cell23_5675509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 13].length) (baseStart_5675509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675509 prefixEnd_5675509 := by exact prefixLift 5675509
  have htrace : WordTrace (prefixWord ++ tailWord_5675509) baseStart_5675509 baseEnd_5675509 := by
    simpa [prefixWord, tailWord_5675509, baseEnd_5675509] using wordTrace_append hprefix tailTrace_5675509
  have hstable : (prefixWord ++ tailWord_5675509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675509).length < 2 ^ (prefixWord ++ tailWord_5675509).sum := by decide
  have hdescent : baseEnd_5675509 < baseStart_5675509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675519 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 3]
def baseStart_5675519 : Nat := 118140960795 + 5675519 * 2 ^ 59
def prefixEnd_5675519 : Nat := 4983230072969 + 3 ^ 40 * 5675519 * 2
def baseEnd_5675519 : Nat := 2914269210725085239511269

theorem tailTrace_5675519 : CollatzResearch.WordTrace tailWord_5675519 prefixEnd_5675519 2914269210725085239511269 := by
  unfold tailWord_5675519
  simp only [CollatzResearch.WordTrace]
  refine ⟨207003183925571439320277611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138002122617047626213518407 207003183925571439320277611)
  ·
    refine ⟨310504775888357158980416417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207003183925571439320277611 310504775888357158980416417)
    ·
      refine ⟨232878581916267869235312313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310504775888357158980416417 232878581916267869235312313)
      ·
        refine ⟨174658936437200901926484235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232878581916267869235312313 174658936437200901926484235)
        ·
          refine ⟨261988404655801352889726353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174658936437200901926484235 261988404655801352889726353)
          ·
            refine ⟨196491303491851014667294765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261988404655801352889726353 196491303491851014667294765)
            ·
              refine ⟨73684238809444130500235537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196491303491851014667294765 73684238809444130500235537)
              ·
                refine ⟨55263179107083097875176653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73684238809444130500235537 55263179107083097875176653)
                ·
                  refine ⟨20723692165156161703191245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55263179107083097875176653 20723692165156161703191245)
                  ·
                    refine ⟨7771384561933560638696717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20723692165156161703191245 7771384561933560638696717)
                    ·
                      refine ⟨2914269210725085239511269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7771384561933560638696717 2914269210725085239511269)
                      ·
                        rfl

theorem cell23_5675519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_5675519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675519 prefixEnd_5675519 := by exact prefixLift 5675519
  have htrace : WordTrace (prefixWord ++ tailWord_5675519) baseStart_5675519 baseEnd_5675519 := by
    simpa [prefixWord, tailWord_5675519, baseEnd_5675519] using wordTrace_append hprefix tailTrace_5675519
  have hstable : (prefixWord ++ tailWord_5675519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675519).length < 2 ^ (prefixWord ++ tailWord_5675519).sum := by decide
  have hdescent : baseEnd_5675519 < baseStart_5675519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675543 : List Nat := [1, 1, 3, 6, 1, 1, 3, 7]
def baseStart_5675543 : Nat := 118140960795 + 5675543 * 2 ^ 59
def prefixEnd_5675543 : Nat := 4983230072969 + 3 ^ 40 * 5675543 * 2
def baseEnd_5675543 : Nat := 107936353120770116504117

theorem tailTrace_5675543 : CollatzResearch.WordTrace tailWord_5675543 prefixEnd_5675543 107936353120770116504117 := by
  unfold tailWord_5675543
  simp only [CollatzResearch.WordTrace]
  refine ⟨207004059277484491419151283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138002706184989660946100855 207004059277484491419151283)
  ·
    refine ⟨310506088916226737128726925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207004059277484491419151283 310506088916226737128726925)
    ·
      refine ⟨116439783343585026423272597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310506088916226737128726925 116439783343585026423272597)
      ·
        refine ⟨5458114844230548113590903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 116439783343585026423272597 5458114844230548113590903)
        ·
          refine ⟨8187172266345822170386355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5458114844230548113590903 8187172266345822170386355)
          ·
            refine ⟨12280758399518733255579533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8187172266345822170386355 12280758399518733255579533)
            ·
              refine ⟨4605284399819524970842325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12280758399518733255579533 4605284399819524970842325)
              ·
                refine ⟨107936353120770116504117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4605284399819524970842325 107936353120770116504117)
                ·
                  rfl

theorem cell23_5675543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 7].length) (baseStart_5675543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675543 prefixEnd_5675543 := by exact prefixLift 5675543
  have htrace : WordTrace (prefixWord ++ tailWord_5675543) baseStart_5675543 baseEnd_5675543 := by
    simpa [prefixWord, tailWord_5675543, baseEnd_5675543] using wordTrace_append hprefix tailTrace_5675543
  have hstable : (prefixWord ++ tailWord_5675543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675543).length < 2 ^ (prefixWord ++ tailWord_5675543).sum := by decide
  have hdescent : baseEnd_5675543 < baseStart_5675543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675569 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 2, 6]
def baseStart_5675569 : Nat := 118140960795 + 5675569 * 2 ^ 59
def prefixEnd_5675569 : Nat := 4983230072969 + 3 ^ 40 * 5675569 * 2
def baseEnd_5675569 : Nat := 971431628252603347962013

theorem tailTrace_5675569 : CollatzResearch.WordTrace tailWord_5675569 prefixEnd_5675569 971431628252603347962013 := by
  unfold tailWord_5675569
  simp only [CollatzResearch.WordTrace]
  refine ⟨207005007575390297859597761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138003338383593531906398507 207005007575390297859597761)
  ·
    refine ⟨155253755681542723394698321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207005007575390297859597761 155253755681542723394698321)
    ·
      refine ⟨116440316761157042546023741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155253755681542723394698321 116440316761157042546023741)
      ·
        refine ⟨43665118785433890954758903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116440316761157042546023741 43665118785433890954758903)
        ·
          refine ⟨65497678178150836432138355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43665118785433890954758903 65497678178150836432138355)
          ·
            refine ⟨98246517267226254648207533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65497678178150836432138355 98246517267226254648207533)
            ·
              refine ⟨36842443975209845493077825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98246517267226254648207533 36842443975209845493077825)
              ·
                refine ⟨27631832981407384119808369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36842443975209845493077825 27631832981407384119808369)
                ·
                  refine ⟨20723874736055538089856277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27631832981407384119808369 20723874736055538089856277)
                  ·
                    refine ⟨971431628252603347962013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20723874736055538089856277 971431628252603347962013)
                    ·
                      rfl

theorem cell23_5675569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_5675569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675569 prefixEnd_5675569 := by exact prefixLift 5675569
  have htrace : WordTrace (prefixWord ++ tailWord_5675569) baseStart_5675569 baseEnd_5675569 := by
    simpa [prefixWord, tailWord_5675569, baseEnd_5675569] using wordTrace_append hprefix tailTrace_5675569
  have hstable : (prefixWord ++ tailWord_5675569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675569).length < 2 ^ (prefixWord ++ tailWord_5675569).sum := by decide
  have hdescent : baseEnd_5675569 < baseStart_5675569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675579 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 3]
def baseStart_5675579 : Nat := 118140960795 + 5675579 * 2 ^ 59
def prefixEnd_5675579 : Nat := 4983230072969 + 3 ^ 40 * 5675579 * 2
def baseEnd_5675579 : Nat := 2914300019564355004760993

theorem tailTrace_5675579 : CollatzResearch.WordTrace tailWord_5675579 prefixEnd_5675579 2914300019564355004760993 := by
  unfold tailWord_5675579
  simp only [CollatzResearch.WordTrace]
  refine ⟨207005372305354069567461791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138003581536902713044974527 207005372305354069567461791)
  ·
    refine ⟨310508058458031104351192687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207005372305354069567461791 310508058458031104351192687)
    ·
      refine ⟨465762087687046656526789031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310508058458031104351192687 465762087687046656526789031)
      ·
        refine ⟨698643131530569984790183547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465762087687046656526789031 698643131530569984790183547)
        ·
          refine ⟨1047964697295854977185275321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 698643131530569984790183547 1047964697295854977185275321)
          ·
            refine ⟨785973522971891232888956491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1047964697295854977185275321 785973522971891232888956491)
            ·
              refine ⟨1178960284457836849333434737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785973522971891232888956491 1178960284457836849333434737)
              ·
                refine ⟨884220213343377637000076053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1178960284457836849333434737 884220213343377637000076053)
                ·
                  refine ⟨41447822500470826734378565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 884220213343377637000076053 41447822500470826734378565)
                  ·
                    refine ⟨7771466718838280012695981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41447822500470826734378565 7771466718838280012695981)
                    ·
                      refine ⟨2914300019564355004760993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7771466718838280012695981 2914300019564355004760993)
                      ·
                        rfl

theorem cell23_5675579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 3].length) (baseStart_5675579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675579 prefixEnd_5675579 := by exact prefixLift 5675579
  have htrace : WordTrace (prefixWord ++ tailWord_5675579) baseStart_5675579 baseEnd_5675579 := by
    simpa [prefixWord, tailWord_5675579, baseEnd_5675579] using wordTrace_append hprefix tailTrace_5675579
  have hstable : (prefixWord ++ tailWord_5675579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675579).length < 2 ^ (prefixWord ++ tailWord_5675579).sum := by decide
  have hdescent : baseEnd_5675579 < baseStart_5675579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675597 : List Nat := [1, 6, 1, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_5675597 : Nat := 118140960795 + 5675597 * 2 ^ 59
def prefixEnd_5675597 : Nat := 4983230072969 + 3 ^ 40 * 5675597 * 2
def baseEnd_5675597 : Nat := 2914309262216135934335911

theorem tailTrace_5675597 : CollatzResearch.WordTrace tailWord_5675597 prefixEnd_5675597 2914309262216135934335911 := by
  unfold tailWord_5675597
  simp only [CollatzResearch.WordTrace]
  refine ⟨207006028819288858641617045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138004019212859239094411363 207006028819288858641617045)
  ·
    refine ⟨9703407600904165248825799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 207006028819288858641617045 9703407600904165248825799)
    ·
      refine ⟨14555111401356247873238699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9703407600904165248825799 14555111401356247873238699)
      ·
        refine ⟨21832667102034371809858049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14555111401356247873238699 21832667102034371809858049)
        ·
          refine ⟨16374500326525778857393537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21832667102034371809858049 16374500326525778857393537)
          ·
            refine ⟨12280875244894334143045153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16374500326525778857393537 12280875244894334143045153)
            ·
              refine ⟨9210656433670750607283865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12280875244894334143045153 9210656433670750607283865)
              ·
                refine ⟨6907992325253062955462899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9210656433670750607283865 6907992325253062955462899)
                ·
                  refine ⟨10361988487879594433194349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6907992325253062955462899 10361988487879594433194349)
                  ·
                    refine ⟨3885745682954847912447881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10361988487879594433194349 3885745682954847912447881)
                    ·
                      refine ⟨2914309262216135934335911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3885745682954847912447881 2914309262216135934335911)
                      ·
                        rfl

theorem cell23_5675597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_5675597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675597 prefixEnd_5675597 := by exact prefixLift 5675597
  have htrace : WordTrace (prefixWord ++ tailWord_5675597) baseStart_5675597 baseEnd_5675597 := by
    simpa [prefixWord, tailWord_5675597, baseEnd_5675597] using wordTrace_append hprefix tailTrace_5675597
  have hstable : (prefixWord ++ tailWord_5675597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675597).length < 2 ^ (prefixWord ++ tailWord_5675597).sum := by decide
  have hdescent : baseEnd_5675597 < baseStart_5675597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675599 : List Nat := [1, 1, 2, 1, 1, 2, 6, 2, 7]
def baseStart_5675599 : Nat := 118140960795 + 5675599 * 2 ^ 59
def prefixEnd_5675599 : Nat := 4983230072969 + 3 ^ 40 * 5675599 * 2
def baseEnd_5675599 : Nat := 323812254353049436278989

theorem tailTrace_5675599 : CollatzResearch.WordTrace tailWord_5675599 prefixEnd_5675599 323812254353049436278989 := by
  unfold tailWord_5675599
  simp only [CollatzResearch.WordTrace]
  refine ⟨207006101765281612983189851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138004067843521075322126567 207006101765281612983189851)
  ·
    refine ⟨310509152647922419474784777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207006101765281612983189851 310509152647922419474784777)
    ·
      refine ⟨232881864485941814606088583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310509152647922419474784777 232881864485941814606088583)
      ·
        refine ⟨349322796728912721909132875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232881864485941814606088583 349322796728912721909132875)
        ·
          refine ⟨523984195093369082863699313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349322796728912721909132875 523984195093369082863699313)
          ·
            refine ⟨392988146320026812147774485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 523984195093369082863699313 392988146320026812147774485)
            ·
              refine ⟨18421319358751256819426929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 392988146320026812147774485 18421319358751256819426929)
              ·
                refine ⟨13815989519063442614570197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18421319358751256819426929 13815989519063442614570197)
                ·
                  refine ⟨323812254353049436278989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13815989519063442614570197 323812254353049436278989)
                  ·
                    rfl

theorem cell23_5675599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 7].length) (baseStart_5675599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675599 prefixEnd_5675599 := by exact prefixLift 5675599
  have htrace : WordTrace (prefixWord ++ tailWord_5675599) baseStart_5675599 baseEnd_5675599 := by
    simpa [prefixWord, tailWord_5675599, baseEnd_5675599] using wordTrace_append hprefix tailTrace_5675599
  have hstable : (prefixWord ++ tailWord_5675599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675599).length < 2 ^ (prefixWord ++ tailWord_5675599).sum := by decide
  have hdescent : baseEnd_5675599 < baseStart_5675599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675639 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 7]
def baseStart_5675639 : Nat := 118140960795 + 5675639 * 2 ^ 59
def prefixEnd_5675639 : Nat := 4983230072969 + 3 ^ 40 * 5675639 * 2
def baseEnd_5675639 : Nat := 2914330828403624770010717

theorem tailTrace_5675639 : CollatzResearch.WordTrace tailWord_5675639 prefixEnd_5675639 2914330828403624770010717 := by
  unfold tailWord_5675639
  simp only [CollatzResearch.WordTrace]
  refine ⟨207007560685136699814645971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138005040456757799876430647 207007560685136699814645971)
  ·
    refine ⟨310511341027705049721968957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207007560685136699814645971 310511341027705049721968957)
    ·
      refine ⟨116441752885389393645738359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310511341027705049721968957 116441752885389393645738359)
      ·
        refine ⟨174662629328084090468607539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116441752885389393645738359 174662629328084090468607539)
        ·
          refine ⟨261993943992126135702911309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174662629328084090468607539 261993943992126135702911309)
          ·
            refine ⟨98247728997047300888591741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261993943992126135702911309 98247728997047300888591741)
            ·
              refine ⟨36842898373892737833221903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98247728997047300888591741 36842898373892737833221903)
              ·
                refine ⟨55264347560839106749832855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36842898373892737833221903 55264347560839106749832855)
                ·
                  refine ⟨82896521341258660124749283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55264347560839106749832855 82896521341258660124749283)
                  ·
                    refine ⟨124344782011887990187123925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82896521341258660124749283 124344782011887990187123925)
                    ·
                      refine ⟨2914330828403624770010717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124344782011887990187123925 2914330828403624770010717)
                      ·
                        rfl

theorem cell23_5675639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_5675639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675639 prefixEnd_5675639 := by exact prefixLift 5675639
  have htrace : WordTrace (prefixWord ++ tailWord_5675639) baseStart_5675639 baseEnd_5675639 := by
    simpa [prefixWord, tailWord_5675639, baseEnd_5675639] using wordTrace_append hprefix tailTrace_5675639
  have hstable : (prefixWord ++ tailWord_5675639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675639).length < 2 ^ (prefixWord ++ tailWord_5675639).sum := by decide
  have hdescent : baseEnd_5675639 < baseStart_5675639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675669 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_5675669 : Nat := 118140960795 + 5675669 * 2 ^ 59
def prefixEnd_5675669 : Nat := 4983230072969 + 3 ^ 40 * 5675669 * 2
def baseEnd_5675669 : Nat := 2914346232823259652635579

theorem tailTrace_5675669 : CollatzResearch.WordTrace tailWord_5675669 prefixEnd_5675669 2914346232823259652635579 := by
  unfold tailWord_5675669
  simp only [CollatzResearch.WordTrace]
  refine ⟨207008654875028014938238061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138005769916685343292158707 207008654875028014938238061)
  ·
    refine ⟨77628245578135505601839273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207008654875028014938238061 77628245578135505601839273)
    ·
      refine ⟨58221184183601629201379455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77628245578135505601839273 58221184183601629201379455)
      ·
        refine ⟨87331776275402443802069183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58221184183601629201379455 87331776275402443802069183)
        ·
          refine ⟨130997664413103665703103775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87331776275402443802069183 130997664413103665703103775)
          ·
            refine ⟨196496496619655498554655663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130997664413103665703103775 196496496619655498554655663)
            ·
              refine ⟨294744744929483247831983495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196496496619655498554655663 294744744929483247831983495)
              ·
                refine ⟨442117117394224871747975243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294744744929483247831983495 442117117394224871747975243)
                ·
                  refine ⟨663175676091337307621962865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442117117394224871747975243 663175676091337307621962865)
                  ·
                    refine ⟨497381757068502980716472149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 663175676091337307621962865 497381757068502980716472149)
                    ·
                      refine ⟨2914346232823259652635579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 497381757068502980716472149 2914346232823259652635579)
                      ·
                        rfl

theorem cell23_5675669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_5675669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675669 prefixEnd_5675669 := by exact prefixLift 5675669
  have htrace : WordTrace (prefixWord ++ tailWord_5675669) baseStart_5675669 baseEnd_5675669 := by
    simpa [prefixWord, tailWord_5675669, baseEnd_5675669] using wordTrace_append hprefix tailTrace_5675669
  have hstable : (prefixWord ++ tailWord_5675669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675669).length < 2 ^ (prefixWord ++ tailWord_5675669).sum := by decide
  have hdescent : baseEnd_5675669 < baseStart_5675669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675706 : List Nat := [3, 1, 1, 1, 2, 3, 1, 5, 6]
def baseStart_5675706 : Nat := 118140960795 + 5675706 * 2 ^ 59
def prefixEnd_5675706 : Nat := 4983230072969 + 3 ^ 40 * 5675706 * 2
def baseEnd_5675706 : Nat := 323818359067497334208101

theorem tailTrace_5675706 : CollatzResearch.WordTrace tailWord_5675706 prefixEnd_5675706 323818359067497334208101 := by
  unfold tailWord_5675706
  simp only [CollatzResearch.WordTrace]
  refine ⟨51752501093973492564333743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138006669583929313504889981 51752501093973492564333743)
  ·
    refine ⟨77628751640960238846500615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51752501093973492564333743 77628751640960238846500615)
    ·
      refine ⟨116443127461440358269750923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77628751640960238846500615 116443127461440358269750923)
      ·
        refine ⟨174664691192160537404626385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116443127461440358269750923 174664691192160537404626385)
        ·
          refine ⟨130998518394120403053469789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174664691192160537404626385 130998518394120403053469789)
          ·
            refine ⟨49124444397795151145051171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130998518394120403053469789 49124444397795151145051171)
            ·
              refine ⟨73686666596692726717576757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49124444397795151145051171 73686666596692726717576757)
              ·
                refine ⟨6908124993439943129772821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73686666596692726717576757 6908124993439943129772821)
                ·
                  refine ⟨323818359067497334208101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6908124993439943129772821 323818359067497334208101)
                  ·
                    rfl

theorem cell23_5675706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 6].length) (baseStart_5675706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675706 prefixEnd_5675706 := by exact prefixLift 5675706
  have htrace : WordTrace (prefixWord ++ tailWord_5675706) baseStart_5675706 baseEnd_5675706 := by
    simpa [prefixWord, tailWord_5675706, baseEnd_5675706] using wordTrace_append hprefix tailTrace_5675706
  have hstable : (prefixWord ++ tailWord_5675706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675706).length < 2 ^ (prefixWord ++ tailWord_5675706).sum := by decide
  have hdescent : baseEnd_5675706 < baseStart_5675706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675720 : List Nat := [2, 1, 3, 1, 2, 5, 1, 1, 2, 2, 3]
def baseStart_5675720 : Nat := 118140960795 + 5675720 * 2 ^ 59
def prefixEnd_5675720 : Nat := 4983230072969 + 3 ^ 40 * 5675720 * 2
def baseEnd_5675720 : Nat := 2914372420336638953097845

theorem tailTrace_5675720 : CollatzResearch.WordTrace tailWord_5675720 prefixEnd_5675720 2914372420336638953097845 := by
  unfold tailWord_5675720
  simp only [CollatzResearch.WordTrace]
  refine ⟨103505257498921625324172307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138007009998562167098896409 103505257498921625324172307)
  ·
    refine ⟨155257886248382437986258461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103505257498921625324172307 155257886248382437986258461)
    ·
      refine ⟨58221707343143414244846923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155257886248382437986258461 58221707343143414244846923)
      ·
        refine ⟨87332561014715121367270385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58221707343143414244846923 87332561014715121367270385)
        ·
          refine ⟨65499420761036341025452789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87332561014715121367270385 65499420761036341025452789)
          ·
            refine ⟨6140570696347156971136199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65499420761036341025452789 6140570696347156971136199)
            ·
              refine ⟨9210856044520735456704299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6140570696347156971136199 9210856044520735456704299)
              ·
                refine ⟨13816284066781103185056449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9210856044520735456704299 13816284066781103185056449)
                ·
                  refine ⟨10362213050085827388792337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13816284066781103185056449 10362213050085827388792337)
                  ·
                    refine ⟨7771659787564370541594253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10362213050085827388792337 7771659787564370541594253)
                    ·
                      refine ⟨2914372420336638953097845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7771659787564370541594253 2914372420336638953097845)
                      ·
                        rfl

theorem cell23_5675720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_5675720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675720 prefixEnd_5675720 := by exact prefixLift 5675720
  have htrace : WordTrace (prefixWord ++ tailWord_5675720) baseStart_5675720 baseEnd_5675720 := by
    simpa [prefixWord, tailWord_5675720, baseEnd_5675720] using wordTrace_append hprefix tailTrace_5675720
  have hstable : (prefixWord ++ tailWord_5675720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675720).length < 2 ^ (prefixWord ++ tailWord_5675720).sum := by decide
  have hdescent : baseEnd_5675720 < baseStart_5675720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675740 : List Nat := [2, 2, 5, 1, 1, 1, 3, 2, 6]
def baseStart_5675740 : Nat := 118140960795 + 5675740 * 2 ^ 59
def prefixEnd_5675740 : Nat := 4983230072969 + 3 ^ 40 * 5675740 * 2
def baseEnd_5675740 : Nat := 323820298883303208316417

theorem tailTrace_5675740 : CollatzResearch.WordTrace tailWord_5675740 prefixEnd_5675740 323820298883303208316417 := by
  unfold tailWord_5675740
  simp only [CollatzResearch.WordTrace]
  refine ⟨103505622228885397032036337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138007496305180529376048449 103505622228885397032036337)
  ·
    refine ⟨77629216671664047774027253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103505622228885397032036337 77629216671664047774027253)
    ·
      refine ⟨7277739062968504478815055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77629216671664047774027253 7277739062968504478815055)
      ·
        refine ⟨10916608594452756718222583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7277739062968504478815055 10916608594452756718222583)
        ·
          refine ⟨16374912891679135077333875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10916608594452756718222583 16374912891679135077333875)
          ·
            refine ⟨24562369337518702616000813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16374912891679135077333875 24562369337518702616000813)
            ·
              refine ⟨9210888501569513481000305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24562369337518702616000813 9210888501569513481000305)
              ·
                refine ⟨6908166376177135110750229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9210888501569513481000305 6908166376177135110750229)
                ·
                  refine ⟨323820298883303208316417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6908166376177135110750229 323820298883303208316417)
                  ·
                    rfl

theorem cell23_5675740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 6].length) (baseStart_5675740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675740 prefixEnd_5675740 := by exact prefixLift 5675740
  have htrace : WordTrace (prefixWord ++ tailWord_5675740) baseStart_5675740 baseEnd_5675740 := by
    simpa [prefixWord, tailWord_5675740, baseEnd_5675740] using wordTrace_append hprefix tailTrace_5675740
  have hstable : (prefixWord ++ tailWord_5675740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675740).length < 2 ^ (prefixWord ++ tailWord_5675740).sum := by decide
  have hdescent : baseEnd_5675740 < baseStart_5675740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675773 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 2, 6, 2]
def baseStart_5675773 : Nat := 118140960795 + 5675773 * 2 ^ 59
def prefixEnd_5675773 : Nat := 4983230072969 + 3 ^ 40 * 5675773 * 2
def baseEnd_5675773 : Nat := 2914399634811327245735101

theorem tailTrace_5675773 : CollatzResearch.WordTrace tailWord_5675773 prefixEnd_5675773 2914399634811327245735101 := by
  unfold tailWord_5675773
  simp only [CollatzResearch.WordTrace]
  refine ⟨207012448066651240700023973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138008298711100827133349315 207012448066651240700023973)
  ·
    refine ⟨38814834012497107631254495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207012448066651240700023973 38814834012497107631254495)
    ·
      refine ⟨58222251018745661446881743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38814834012497107631254495 58222251018745661446881743)
      ·
        refine ⟨87333376528118492170322615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58222251018745661446881743 87333376528118492170322615)
        ·
          refine ⟨131000064792177738255483923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87333376528118492170322615 131000064792177738255483923)
          ·
            refine ⟨196500097188266607383225885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131000064792177738255483923 196500097188266607383225885)
            ·
              refine ⟨73687536445599977768709707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196500097188266607383225885 73687536445599977768709707)
              ·
                refine ⟨110531304668399966653064561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73687536445599977768709707 110531304668399966653064561)
                ·
                  refine ⟨82898478501299974989798421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110531304668399966653064561 82898478501299974989798421)
                  ·
                    refine ⟨3885866179748436327646801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82898478501299974989798421 3885866179748436327646801)
                    ·
                      refine ⟨2914399634811327245735101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3885866179748436327646801 2914399634811327245735101)
                      ·
                        rfl

theorem cell23_5675773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_5675773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675773 prefixEnd_5675773 := by exact prefixLift 5675773
  have htrace : WordTrace (prefixWord ++ tailWord_5675773) baseStart_5675773 baseEnd_5675773 := by
    simpa [prefixWord, tailWord_5675773, baseEnd_5675773] using wordTrace_append hprefix tailTrace_5675773
  have hstable : (prefixWord ++ tailWord_5675773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675773).length < 2 ^ (prefixWord ++ tailWord_5675773).sum := by decide
  have hdescent : baseEnd_5675773 < baseStart_5675773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675784 : List Nat := [2, 1, 3, 2, 2, 4, 1, 3, 1, 1, 3]
def baseStart_5675784 : Nat := 118140960795 + 5675784 * 2 ^ 59
def prefixEnd_5675784 : Nat := 4983230072969 + 3 ^ 40 * 5675784 * 2
def baseEnd_5675784 : Nat := 2914405283098526702697551

theorem tailTrace_5675784 : CollatzResearch.WordTrace tailWord_5675784 prefixEnd_5675784 2914405283098526702697551 := by
  unfold tailWord_5675784
  simp only [CollatzResearch.WordTrace]
  refine ⟨103506424634805694789337203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138008566179740926385782937 103506424634805694789337203)
  ·
    refine ⟨155259636952208542184005805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103506424634805694789337203 155259636952208542184005805)
    ·
      refine ⟨58222363857078203319002177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155259636952208542184005805 58222363857078203319002177)
      ·
        refine ⟨43666772892808652489251633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58222363857078203319002177 43666772892808652489251633)
        ·
          refine ⟨32750079669606489366938725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43666772892808652489251633 32750079669606489366938725)
          ·
            refine ⟨6140639938051216756301011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32750079669606489366938725 6140639938051216756301011)
            ·
              refine ⟨9210959907076825134451517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6140639938051216756301011 9210959907076825134451517)
              ·
                refine ⟨3454109965153809425419319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9210959907076825134451517 3454109965153809425419319)
                ·
                  refine ⟨5181164947730714138128979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3454109965153809425419319 5181164947730714138128979)
                  ·
                    refine ⟨7771747421596071207193469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5181164947730714138128979 7771747421596071207193469)
                    ·
                      refine ⟨2914405283098526702697551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7771747421596071207193469 2914405283098526702697551)
                      ·
                        rfl

theorem cell23_5675784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_5675784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675784 prefixEnd_5675784 := by exact prefixLift 5675784
  have htrace : WordTrace (prefixWord ++ tailWord_5675784) baseStart_5675784 baseEnd_5675784 := by
    simpa [prefixWord, tailWord_5675784, baseEnd_5675784] using wordTrace_append hprefix tailTrace_5675784
  have hstable : (prefixWord ++ tailWord_5675784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675784).length < 2 ^ (prefixWord ++ tailWord_5675784).sum := by decide
  have hdescent : baseEnd_5675784 < baseStart_5675784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675794 : List Nat := [3, 2, 4, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_5675794 : Nat := 118140960795 + 5675794 * 2 ^ 59
def prefixEnd_5675794 : Nat := 4983230072969 + 3 ^ 40 * 5675794 * 2
def baseEnd_5675794 : Nat := 2914410417905071663572505

theorem tailTrace_5675794 : CollatzResearch.WordTrace tailWord_5675794 prefixEnd_5675794 2914410417905071663572505 := by
  unfold tailWord_5675794
  simp only [CollatzResearch.WordTrace]
  refine ⟨51753303499893790321634609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138008809333050107524358957 51753303499893790321634609)
  ·
    refine ⟨38814977624920342741225957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51753303499893790321634609 38814977624920342741225957)
    ·
      refine ⟨7277808304672564263979867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38814977624920342741225957 7277808304672564263979867)
      ·
        refine ⟨10916712457008846395969801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7277808304672564263979867 10916712457008846395969801)
        ·
          refine ⟨8187534342756634796977351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10916712457008846395969801 8187534342756634796977351)
          ·
            refine ⟨12281301514134952195466027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8187534342756634796977351 12281301514134952195466027)
            ·
              refine ⟨18421952271202428293199041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12281301514134952195466027 18421952271202428293199041)
              ·
                refine ⟨13816464203401821219899281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18421952271202428293199041 13816464203401821219899281)
                ·
                  refine ⟨10362348152551365914924461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13816464203401821219899281 10362348152551365914924461)
                  ·
                    refine ⟨3885880557206762218096673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10362348152551365914924461 3885880557206762218096673)
                    ·
                      refine ⟨2914410417905071663572505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3885880557206762218096673 2914410417905071663572505)
                      ·
                        rfl

theorem cell23_5675794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_5675794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675794 prefixEnd_5675794 := by exact prefixLift 5675794
  have htrace : WordTrace (prefixWord ++ tailWord_5675794) baseStart_5675794 baseEnd_5675794 := by
    simpa [prefixWord, tailWord_5675794, baseEnd_5675794] using wordTrace_append hprefix tailTrace_5675794
  have hstable : (prefixWord ++ tailWord_5675794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675794).length < 2 ^ (prefixWord ++ tailWord_5675794).sum := by decide
  have hdescent : baseEnd_5675794 < baseStart_5675794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675807 : List Nat := [1, 1, 2, 4, 2, 2, 3, 1, 3, 2, 2]
def baseStart_5675807 : Nat := 118140960795 + 5675807 * 2 ^ 59
def prefixEnd_5675807 : Nat := 4983230072969 + 3 ^ 40 * 5675807 * 2
def baseEnd_5675807 : Nat := 2914417093153580112709945

theorem tailTrace_5675807 : CollatzResearch.WordTrace tailWord_5675807 prefixEnd_5675807 2914417093153580112709945 := by
  unfold tailWord_5675807
  simp only [CollatzResearch.WordTrace]
  refine ⟨207013688148528064506761675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138009125432352043004507783 207013688148528064506761675)
  ·
    refine ⟨310520532222792096760142513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207013688148528064506761675 310520532222792096760142513)
    ·
      refine ⟨232890399167094072570106885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310520532222792096760142513 232890399167094072570106885)
      ·
        refine ⟨43666949843830138606895041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232890399167094072570106885 43666949843830138606895041)
        ·
          refine ⟨32750212382872603955171281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43666949843830138606895041 32750212382872603955171281)
          ·
            refine ⟨24562659287154452966378461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32750212382872603955171281 24562659287154452966378461)
            ·
              refine ⟨9210997232682919862391923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24562659287154452966378461 9210997232682919862391923)
              ·
                refine ⟨13816495849024379793587885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9210997232682919862391923 13816495849024379793587885)
                ·
                  refine ⟨5181185943384142422595457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13816495849024379793587885 5181185943384142422595457)
                  ·
                    refine ⟨3885889457538106816946593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5181185943384142422595457 3885889457538106816946593)
                    ·
                      refine ⟨2914417093153580112709945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3885889457538106816946593 2914417093153580112709945)
                      ·
                        rfl

theorem cell23_5675807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_5675807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675807 prefixEnd_5675807 := by exact prefixLift 5675807
  have htrace : WordTrace (prefixWord ++ tailWord_5675807) baseStart_5675807 baseEnd_5675807 := by
    simpa [prefixWord, tailWord_5675807, baseEnd_5675807] using wordTrace_append hprefix tailTrace_5675807
  have hstable : (prefixWord ++ tailWord_5675807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675807).length < 2 ^ (prefixWord ++ tailWord_5675807).sum := by decide
  have hdescent : baseEnd_5675807 < baseStart_5675807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675821 : List Nat := [1, 5, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_5675821 : Nat := 118140960795 + 5675821 * 2 ^ 59
def prefixEnd_5675821 : Nat := 4983230072969 + 3 ^ 40 * 5675821 * 2
def baseEnd_5675821 : Nat := 971474760627581019311627

theorem tailTrace_5675821 : CollatzResearch.WordTrace tailWord_5675821 prefixEnd_5675821 971474760627581019311627 := by
  unfold tailWord_5675821
  simp only [CollatzResearch.WordTrace]
  refine ⟨207014198770477344897771317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138009465846984896598514211 207014198770477344897771317)
  ·
    refine ⟨19407581134732251084166061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207014198770477344897771317 19407581134732251084166061)
    ·
      refine ⟨7277842925524594156562273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19407581134732251084166061 7277842925524594156562273)
      ·
        refine ⟨5458382194143445617421705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7277842925524594156562273 5458382194143445617421705)
        ·
          refine ⟨4093786645607584213066279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5458382194143445617421705 4093786645607584213066279)
          ·
            refine ⟨6140679968411376319599419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4093786645607584213066279 6140679968411376319599419)
            ·
              refine ⟨9211019952617064479399129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6140679968411376319599419 9211019952617064479399129)
              ·
                refine ⟨6908264964462798359549347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9211019952617064479399129 6908264964462798359549347)
                ·
                  refine ⟨10362397446694197539324021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6908264964462798359549347 10362397446694197539324021)
                  ·
                    refine ⟨971474760627581019311627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10362397446694197539324021 971474760627581019311627)
                    ·
                      rfl

theorem cell23_5675821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_5675821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675821 prefixEnd_5675821 := by exact prefixLift 5675821
  have htrace : WordTrace (prefixWord ++ tailWord_5675821) baseStart_5675821 baseEnd_5675821 := by
    simpa [prefixWord, tailWord_5675821, baseEnd_5675821] using wordTrace_append hprefix tailTrace_5675821
  have hstable : (prefixWord ++ tailWord_5675821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675821).length < 2 ^ (prefixWord ++ tailWord_5675821).sum := by decide
  have hdescent : baseEnd_5675821 < baseStart_5675821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675827 : List Nat := [1, 1, 1, 2, 6, 3, 1, 2, 1, 2, 3]
def baseStart_5675827 : Nat := 118140960795 + 5675827 * 2 ^ 59
def prefixEnd_5675827 : Nat := 4983230072969 + 3 ^ 40 * 5675827 * 2
def baseEnd_5675827 : Nat := 2914427362766670034459853

theorem tailTrace_5675827 : CollatzResearch.WordTrace tailWord_5675827 prefixEnd_5675827 2914427362766670034459853 := by
  unfold tailWord_5675827
  simp only [CollatzResearch.WordTrace]
  refine ⟨207014417608455607922489735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138009611738970405281659823 207014417608455607922489735)
  ·
    refine ⟨310521626412683411883734603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207014417608455607922489735 310521626412683411883734603)
    ·
      refine ⟨465782439619025117825601905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310521626412683411883734603 465782439619025117825601905)
      ·
        refine ⟨349336829714268838369201429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 465782439619025117825601905 349336829714268838369201429)
        ·
          refine ⟨16375163892856351798556317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 349336829714268838369201429 16375163892856351798556317)
          ·
            refine ⟨6140686459821131924458619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16375163892856351798556317 6140686459821131924458619)
            ·
              refine ⟨9211029689731697886687929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6140686459821131924458619 9211029689731697886687929)
              ·
                refine ⟨6908272267298773415015947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9211029689731697886687929 6908272267298773415015947)
                ·
                  refine ⟨10362408400948160122523921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6908272267298773415015947 10362408400948160122523921)
                  ·
                    refine ⟨7771806300711120091892941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10362408400948160122523921 7771806300711120091892941)
                    ·
                      refine ⟨2914427362766670034459853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7771806300711120091892941 2914427362766670034459853)
                      ·
                        rfl

theorem cell23_5675827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 2, 3].length) (baseStart_5675827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675827 prefixEnd_5675827 := by exact prefixLift 5675827
  have htrace : WordTrace (prefixWord ++ tailWord_5675827) baseStart_5675827 baseEnd_5675827 := by
    simpa [prefixWord, tailWord_5675827, baseEnd_5675827] using wordTrace_append hprefix tailTrace_5675827
  have hstable : (prefixWord ++ tailWord_5675827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675827).length < 2 ^ (prefixWord ++ tailWord_5675827).sum := by decide
  have hdescent : baseEnd_5675827 < baseStart_5675827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675844 : List Nat := [2, 3, 4, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_5675844 : Nat := 118140960795 + 5675844 * 2 ^ 59
def prefixEnd_5675844 : Nat := 4983230072969 + 3 ^ 40 * 5675844 * 2
def baseEnd_5675844 : Nat := 2914436091937796467947275

theorem tailTrace_5675844 : CollatzResearch.WordTrace tailWord_5675844 prefixEnd_5675844 2914436091937796467947275 := by
  unfold tailWord_5675844
  simp only [CollatzResearch.WordTrace]
  refine ⟨103507518824697009912929293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138010025099596013217239057 103507518824697009912929293)
  ·
    refine ⟨38815319559261378717348485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103507518824697009912929293 38815319559261378717348485)
    ·
      refine ⟨7277872417361508509502841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38815319559261378717348485 7277872417361508509502841)
      ·
        refine ⟨5458404313021131382127131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7277872417361508509502841 5458404313021131382127131)
        ·
          refine ⟨8187606469531697073190697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5458404313021131382127131 8187606469531697073190697)
          ·
            refine ⟨6140704852148772804893023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8187606469531697073190697 6140704852148772804893023)
            ·
              refine ⟨9211057278223159207339535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6140704852148772804893023 9211057278223159207339535)
              ·
                refine ⟨13816585917334738811009303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9211057278223159207339535 13816585917334738811009303)
                ·
                  refine ⟨20724878876002108216513955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13816585917334738811009303 20724878876002108216513955)
                  ·
                    refine ⟨31087318314003162324770933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20724878876002108216513955 31087318314003162324770933)
                    ·
                      refine ⟨2914436091937796467947275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31087318314003162324770933 2914436091937796467947275)
                      ·
                        rfl

theorem cell23_5675844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_5675844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675844 prefixEnd_5675844 := by exact prefixLift 5675844
  have htrace : WordTrace (prefixWord ++ tailWord_5675844) baseStart_5675844 baseEnd_5675844 := by
    simpa [prefixWord, tailWord_5675844, baseEnd_5675844] using wordTrace_append hprefix tailTrace_5675844
  have hstable : (prefixWord ++ tailWord_5675844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675844).length < 2 ^ (prefixWord ++ tailWord_5675844).sum := by decide
  have hdescent : baseEnd_5675844 < baseStart_5675844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675863 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 4]
def baseStart_5675863 : Nat := 118140960795 + 5675863 * 2 ^ 59
def prefixEnd_5675863 : Nat := 4983230072969 + 3 ^ 40 * 5675863 * 2
def baseEnd_5675863 : Nat := 2914445848070231893609687

theorem tailTrace_5675863 : CollatzResearch.WordTrace tailWord_5675863 prefixEnd_5675863 2914445848070231893609687 := by
  unfold tailWord_5675863
  simp only [CollatzResearch.WordTrace]
  refine ⟨207015730636325186070800243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138010487090883457380533495 207015730636325186070800243)
  ·
    refine ⟨310523595954487779106200365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207015730636325186070800243 310523595954487779106200365)
    ·
      refine ⟨116446348482932917164825137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310523595954487779106200365 116446348482932917164825137)
      ·
        refine ⟨87334761362199687873618853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116446348482932917164825137 87334761362199687873618853)
        ·
          refine ⟨16375267755412441476303535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87334761362199687873618853 16375267755412441476303535)
          ·
            refine ⟨24562901633118662214455303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16375267755412441476303535 24562901633118662214455303)
            ·
              refine ⟨36844352449677993321682955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24562901633118662214455303 36844352449677993321682955)
              ·
                refine ⟨55266528674516989982524433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36844352449677993321682955 55266528674516989982524433)
                ·
                  refine ⟨41449896505887742486893325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55266528674516989982524433 41449896505887742486893325)
                  ·
                    refine ⟨15543711189707903432584997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41449896505887742486893325 15543711189707903432584997)
                    ·
                      refine ⟨2914445848070231893609687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15543711189707903432584997 2914445848070231893609687)
                      ·
                        rfl

theorem cell23_5675863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_5675863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675863 prefixEnd_5675863 := by exact prefixLift 5675863
  have htrace : WordTrace (prefixWord ++ tailWord_5675863) baseStart_5675863 baseEnd_5675863 := by
    simpa [prefixWord, tailWord_5675863, baseEnd_5675863] using wordTrace_append hprefix tailTrace_5675863
  have hstable : (prefixWord ++ tailWord_5675863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675863).length < 2 ^ (prefixWord ++ tailWord_5675863).sum := by decide
  have hdescent : baseEnd_5675863 < baseStart_5675863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675914 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 4, 2, 2]
def baseStart_5675914 : Nat := 118140960795 + 5675914 * 2 ^ 59
def prefixEnd_5675914 : Nat := 4983230072969 + 3 ^ 40 * 5675914 * 2
def baseEnd_5675914 : Nat := 2914472035583611194071953

theorem tailTrace_5675914 : CollatzResearch.WordTrace tailWord_5675914 prefixEnd_5675914 2914472035583611194071953 := by
  unfold tailWord_5675914
  simp only [CollatzResearch.WordTrace]
  refine ⟨51754397689785105445226699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138011727172760281187271197 51754397689785105445226699)
  ·
    refine ⟨77631596534677658167840049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51754397689785105445226699 77631596534677658167840049)
    ·
      refine ⟨58223697401008243625880037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77631596534677658167840049 58223697401008243625880037)
      ·
        refine ⟨10916943262689045679852507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58223697401008243625880037 10916943262689045679852507)
        ·
          refine ⟨16375414894033568519778761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10916943262689045679852507 16375414894033568519778761)
          ·
            refine ⟨12281561170525176389834071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16375414894033568519778761 12281561170525176389834071)
            ·
              refine ⟨18422341755787764584751107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12281561170525176389834071 18422341755787764584751107)
              ·
                refine ⟨27633512633681646877126661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18422341755787764584751107 27633512633681646877126661)
                ·
                  refine ⟨5181283618815308789461249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27633512633681646877126661 5181283618815308789461249)
                  ·
                    refine ⟨3885962714111481592095937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5181283618815308789461249 3885962714111481592095937)
                    ·
                      refine ⟨2914472035583611194071953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3885962714111481592095937 2914472035583611194071953)
                      ·
                        rfl

theorem cell23_5675914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_5675914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675914 prefixEnd_5675914 := by exact prefixLift 5675914
  have htrace : WordTrace (prefixWord ++ tailWord_5675914) baseStart_5675914 baseEnd_5675914 := by
    simpa [prefixWord, tailWord_5675914, baseEnd_5675914] using wordTrace_append hprefix tailTrace_5675914
  have hstable : (prefixWord ++ tailWord_5675914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675914).length < 2 ^ (prefixWord ++ tailWord_5675914).sum := by decide
  have hdescent : baseEnd_5675914 < baseStart_5675914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5675933 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 3, 7]
def baseStart_5675933 : Nat := 118140960795 + 5675933 * 2 ^ 59
def prefixEnd_5675933 : Nat := 4983230072969 + 3 ^ 40 * 5675933 * 2
def baseEnd_5675933 : Nat := 971493930572015539911455

theorem tailTrace_5675933 : CollatzResearch.WordTrace tailWord_5675933 prefixEnd_5675933 971493930572015539911455 := by
  unfold tailWord_5675933
  simp only [CollatzResearch.WordTrace]
  refine ⟨207018283746071588025848453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138012189164047725350565635 207018283746071588025848453)
  ·
    refine ⟨38815928202388422754846585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207018283746071588025848453 38815928202388422754846585)
    ·
      refine ⟨29111946151791317066134939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38815928202388422754846585 29111946151791317066134939)
      ·
        refine ⟨43667919227686975599202409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29111946151791317066134939 43667919227686975599202409)
        ·
          refine ⟨32750939420765231699401807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43667919227686975599202409 32750939420765231699401807)
          ·
            refine ⟨49126409131147847549102711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32750939420765231699401807 49126409131147847549102711)
            ·
              refine ⟨73689613696721771323654067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49126409131147847549102711 73689613696721771323654067)
              ·
                refine ⟨110534420545082656985481101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73689613696721771323654067 110534420545082656985481101)
                ·
                  refine ⟨41450407704405996369555413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110534420545082656985481101 41450407704405996369555413)
                  ·
                    refine ⟨971493930572015539911455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41450407704405996369555413 971493930572015539911455)
                    ·
                      rfl

theorem cell23_5675933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_5675933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5675933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5675933 prefixEnd_5675933 := by exact prefixLift 5675933
  have htrace : WordTrace (prefixWord ++ tailWord_5675933) baseStart_5675933 baseEnd_5675933 := by
    simpa [prefixWord, tailWord_5675933, baseEnd_5675933] using wordTrace_append hprefix tailTrace_5675933
  have hstable : (prefixWord ++ tailWord_5675933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5675933).length < 2 ^ (prefixWord ++ tailWord_5675933).sum := by decide
  have hdescent : baseEnd_5675933 < baseStart_5675933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5675933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676007 : List Nat := [1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_5676007 : Nat := 118140960795 + 5676007 * 2 ^ 59
def prefixEnd_5676007 : Nat := 4983230072969 + 3 ^ 40 * 5676007 * 2
def baseEnd_5676007 : Nat := 2914519789284479330209025

theorem tailTrace_5676007 : CollatzResearch.WordTrace tailWord_5676007 prefixEnd_5676007 2914519789284479330209025 := by
  unfold tailWord_5676007
  simp only [CollatzResearch.WordTrace]
  refine ⟨207020982747803498664042275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138013988498535665776028183 207020982747803498664042275)
  ·
    refine ⟨310531474121705247996063413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207020982747803498664042275 310531474121705247996063413)
    ·
      refine ⟨29112325698909866999630945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 310531474121705247996063413 29112325698909866999630945)
      ·
        refine ⟨21834244274182400249723209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29112325698909866999630945 21834244274182400249723209)
        ·
          refine ⟨16375683205636800187292407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21834244274182400249723209 16375683205636800187292407)
          ·
            refine ⟨24563524808455200280938611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16375683205636800187292407 24563524808455200280938611)
            ·
              refine ⟨36845287212682800421407917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24563524808455200280938611 36845287212682800421407917)
              ·
                refine ⟨13816982704756050158027969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36845287212682800421407917 13816982704756050158027969)
                ·
                  refine ⟨10362737028567037618520977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13816982704756050158027969 10362737028567037618520977)
                  ·
                    refine ⟨7772052771425278213890733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10362737028567037618520977 7772052771425278213890733)
                    ·
                      refine ⟨2914519789284479330209025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7772052771425278213890733 2914519789284479330209025)
                      ·
                        rfl

theorem cell23_5676007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_5676007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676007 prefixEnd_5676007 := by exact prefixLift 5676007
  have htrace : WordTrace (prefixWord ++ tailWord_5676007) baseStart_5676007 baseEnd_5676007 := by
    simpa [prefixWord, tailWord_5676007, baseEnd_5676007] using wordTrace_append hprefix tailTrace_5676007
  have hstable : (prefixWord ++ tailWord_5676007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676007).length < 2 ^ (prefixWord ++ tailWord_5676007).sum := by decide
  have hdescent : baseEnd_5676007 < baseStart_5676007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676037 : List Nat := [1, 3, 1, 1, 2, 3, 2, 3, 3, 1, 3]
def baseStart_5676037 : Nat := 118140960795 + 5676037 * 2 ^ 59
def prefixEnd_5676037 : Nat := 4983230072969 + 3 ^ 40 * 5676037 * 2
def baseEnd_5676037 : Nat := 2914535193704114212833887

theorem tailTrace_5676037 : CollatzResearch.WordTrace tailWord_5676037 prefixEnd_5676037 2914535193704114212833887 := by
  unfold tailWord_5676037
  simp only [CollatzResearch.WordTrace]
  refine ⟨207022076937694813787634365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138014717958463209191756243 207022076937694813787634365)
  ·
    refine ⟨77633278851635555170362887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207022076937694813787634365 77633278851635555170362887)
    ·
      refine ⟨116449918277453332755544331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77633278851635555170362887 116449918277453332755544331)
      ·
        refine ⟨174674877416179999133316497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116449918277453332755544331 174674877416179999133316497)
        ·
          refine ⟨131006158062134999349987373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174674877416179999133316497 131006158062134999349987373)
          ·
            refine ⟨49127309273300624756245265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131006158062134999349987373 49127309273300624756245265)
            ·
              refine ⟨36845481954975468567183949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49127309273300624756245265 36845481954975468567183949)
              ·
                refine ⟨13817055733115800712693981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36845481954975468567183949 13817055733115800712693981)
                ·
                  refine ⟨5181395899918425267260243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13817055733115800712693981 5181395899918425267260243)
                  ·
                    refine ⟨7772093849877637900890365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5181395899918425267260243 7772093849877637900890365)
                    ·
                      refine ⟨2914535193704114212833887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7772093849877637900890365 2914535193704114212833887)
                      ·
                        rfl

theorem cell23_5676037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 1, 3].length) (baseStart_5676037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676037 prefixEnd_5676037 := by exact prefixLift 5676037
  have htrace : WordTrace (prefixWord ++ tailWord_5676037) baseStart_5676037 baseEnd_5676037 := by
    simpa [prefixWord, tailWord_5676037, baseEnd_5676037] using wordTrace_append hprefix tailTrace_5676037
  have hstable : (prefixWord ++ tailWord_5676037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676037).length < 2 ^ (prefixWord ++ tailWord_5676037).sum := by decide
  have hdescent : baseEnd_5676037 < baseStart_5676037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676040 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 3, 5]
def baseStart_5676040 : Nat := 118140960795 + 5676040 * 2 ^ 59
def prefixEnd_5676040 : Nat := 4983230072969 + 3 ^ 40 * 5676040 * 2
def baseEnd_5676040 : Nat := 971512244715359233698791

theorem tailTrace_5676040 : CollatzResearch.WordTrace tailWord_5676040 prefixEnd_5676040 971512244715359233698791 := by
  unfold tailWord_5676040
  simp only [CollatzResearch.WordTrace]
  refine ⟨103511093178341972649996787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138014790904455963533329049 103511093178341972649996787)
  ·
    refine ⟨155266639767512958974995181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103511093178341972649996787 155266639767512958974995181)
    ·
      refine ⟨58224989912817359615623193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155266639767512958974995181 58224989912817359615623193)
      ·
        refine ⟨43668742434613019711717395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58224989912817359615623193 43668742434613019711717395)
        ·
          refine ⟨65503113651919529567576093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43668742434613019711717395 65503113651919529567576093)
          ·
            refine ⟨24563667619469823587841035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65503113651919529567576093 24563667619469823587841035)
            ·
              refine ⟨36845501429204735381761553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24563667619469823587841035 36845501429204735381761553)
              ·
                refine ⟨27634126071903551536321165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36845501429204735381761553 27634126071903551536321165)
                ·
                  refine ⟨10362797276963831826120437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27634126071903551536321165 10362797276963831826120437)
                  ·
                    refine ⟨971512244715359233698791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10362797276963831826120437 971512244715359233698791)
                    ·
                      rfl

theorem cell23_5676040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_5676040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676040 prefixEnd_5676040 := by exact prefixLift 5676040
  have htrace : WordTrace (prefixWord ++ tailWord_5676040) baseStart_5676040 baseEnd_5676040 := by
    simpa [prefixWord, tailWord_5676040, baseEnd_5676040] using wordTrace_append hprefix tailTrace_5676040
  have hstable : (prefixWord ++ tailWord_5676040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676040).length < 2 ^ (prefixWord ++ tailWord_5676040).sum := by decide
  have hdescent : baseEnd_5676040 < baseStart_5676040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676074 : List Nat := [3, 1, 4, 1, 3, 1, 1, 3, 1, 5]
def baseStart_5676074 : Nat := 118140960795 + 5676074 * 2 ^ 59
def prefixEnd_5676074 : Nat := 4983230072969 + 3 ^ 40 * 5676074 * 2
def baseEnd_5676074 : Nat := 971518064162776856023739

theorem tailTrace_5676074 : CollatzResearch.WordTrace tailWord_5676074 prefixEnd_5676074 971518064162776856023739 := by
  unfold tailWord_5676074
  simp only [CollatzResearch.WordTrace]
  refine ⟨51755856609640192276682819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138015617625707179404487517 51755856609640192276682819)
  ·
    refine ⟨77633784914460288415024229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51755856609640192276682819 77633784914460288415024229)
    ·
      refine ⟨14556334671461304077817043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77633784914460288415024229 14556334671461304077817043)
      ·
        refine ⟨21834502007191956116725565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14556334671461304077817043 21834502007191956116725565)
        ·
          refine ⟨8187938252696983543772087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21834502007191956116725565 8187938252696983543772087)
          ·
            refine ⟨12281907379045475315658131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8187938252696983543772087 12281907379045475315658131)
            ·
              refine ⟨18422861068568212973487197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12281907379045475315658131 18422861068568212973487197)
              ·
                refine ⟨6908572900713079865057699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18422861068568212973487197 6908572900713079865057699)
                ·
                  refine ⟨10362859351069619797586549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6908572900713079865057699 10362859351069619797586549)
                  ·
                    refine ⟨971518064162776856023739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10362859351069619797586549 971518064162776856023739)
                    ·
                      rfl

theorem cell23_5676074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_5676074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676074 prefixEnd_5676074 := by exact prefixLift 5676074
  have htrace : WordTrace (prefixWord ++ tailWord_5676074) baseStart_5676074 baseEnd_5676074 := by
    simpa [prefixWord, tailWord_5676074, baseEnd_5676074] using wordTrace_append hprefix tailTrace_5676074
  have hstable : (prefixWord ++ tailWord_5676074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676074).length < 2 ^ (prefixWord ++ tailWord_5676074).sum := by decide
  have hdescent : baseEnd_5676074 < baseStart_5676074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676080 : List Nat := [2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 5]
def baseStart_5676080 : Nat := 118140960795 + 5676080 * 2 ^ 59
def prefixEnd_5676080 : Nat := 4983230072969 + 3 ^ 40 * 5676080 * 2
def baseEnd_5676080 : Nat := 2914557273372257544596189

theorem tailTrace_5676080 : CollatzResearch.WordTrace tailWord_5676080 prefixEnd_5676080 2914557273372257544596189 := by
  unfold tailWord_5676080
  simp only [CollatzResearch.WordTrace]
  refine ⟨103511822638269516065724847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138015763517692688087633129 103511822638269516065724847)
  ·
    refine ⟨155267733957404274098587271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103511822638269516065724847 155267733957404274098587271)
    ·
      refine ⟨232901600936106411147880907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155267733957404274098587271 232901600936106411147880907)
      ·
        refine ⟨349352401404159616721821361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232901600936106411147880907 349352401404159616721821361)
        ·
          refine ⟨262014301053119712541366021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349352401404159616721821361 262014301053119712541366021)
          ·
            refine ⟨49127681447459946101506129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262014301053119712541366021 49127681447459946101506129)
            ·
              refine ⟨36845761085594959576129597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49127681447459946101506129 36845761085594959576129597)
              ·
                refine ⟨13817160407098109841048599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36845761085594959576129597 13817160407098109841048599)
                ·
                  refine ⟨20725740610647164761572899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13817160407098109841048599 20725740610647164761572899)
                  ·
                    refine ⟨31088610915970747142359349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20725740610647164761572899 31088610915970747142359349)
                    ·
                      refine ⟨2914557273372257544596189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31088610915970747142359349 2914557273372257544596189)
                      ·
                        rfl

theorem cell23_5676080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 5].length) (baseStart_5676080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676080 prefixEnd_5676080 := by exact prefixLift 5676080
  have htrace : WordTrace (prefixWord ++ tailWord_5676080) baseStart_5676080 baseEnd_5676080 := by
    simpa [prefixWord, tailWord_5676080, baseEnd_5676080] using wordTrace_append hprefix tailTrace_5676080
  have hstable : (prefixWord ++ tailWord_5676080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676080).length < 2 ^ (prefixWord ++ tailWord_5676080).sum := by decide
  have hdescent : baseEnd_5676080 < baseStart_5676080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676090 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4]
def baseStart_5676090 : Nat := 118140960795 + 5676090 * 2 ^ 59
def prefixEnd_5676090 : Nat := 4983230072969 + 3 ^ 40 * 5676090 * 2
def baseEnd_5676090 : Nat := 2914562408178802505471143

theorem tailTrace_5676090 : CollatzResearch.WordTrace tailWord_5676090 prefixEnd_5676090 2914562408178802505471143 := by
  unfold tailWord_5676090
  simp only [CollatzResearch.WordTrace]
  refine ⟨51756002501625700959828431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138016006671001869226209149 51756002501625700959828431)
  ·
    refine ⟨77634003752438551439742647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51756002501625700959828431 77634003752438551439742647)
    ·
      refine ⟨116451005628657827159613971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77634003752438551439742647 116451005628657827159613971)
      ·
        refine ⟨174676508442986740739420957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116451005628657827159613971 174676508442986740739420957)
        ·
          refine ⟨65503690666120027777282859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174676508442986740739420957 65503690666120027777282859)
          ·
            refine ⟨98255535999180041665924289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65503690666120027777282859 98255535999180041665924289)
            ·
              refine ⟨73691651999385031249443217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98255535999180041665924289 73691651999385031249443217)
              ·
                refine ⟨55268738999538773437082413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73691651999385031249443217 55268738999538773437082413)
                ·
                  refine ⟨20725777124827040038905905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55268738999538773437082413 20725777124827040038905905)
                  ·
                    refine ⟨15544332843620280029179429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20725777124827040038905905 15544332843620280029179429)
                    ·
                      refine ⟨2914562408178802505471143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15544332843620280029179429 2914562408178802505471143)
                      ·
                        rfl

theorem cell23_5676090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_5676090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676090 prefixEnd_5676090 := by exact prefixLift 5676090
  have htrace : WordTrace (prefixWord ++ tailWord_5676090) baseStart_5676090 baseEnd_5676090 := by
    simpa [prefixWord, tailWord_5676090, baseEnd_5676090] using wordTrace_append hprefix tailTrace_5676090
  have hstable : (prefixWord ++ tailWord_5676090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676090).length < 2 ^ (prefixWord ++ tailWord_5676090).sum := by decide
  have hdescent : baseEnd_5676090 < baseStart_5676090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676104 : List Nat := [2, 1, 3, 1, 1, 1, 7, 1, 2, 4]
def baseStart_5676104 : Nat := 118140960795 + 5676104 * 2 ^ 59
def prefixEnd_5676104 : Nat := 4983230072969 + 3 ^ 40 * 5676104 * 2
def baseEnd_5676104 : Nat := 971523198969321816898693

theorem tailTrace_5676104 : CollatzResearch.WordTrace tailWord_5676104 prefixEnd_5676104 971523198969321816898693 := by
  unfold tailWord_5676104
  simp only [CollatzResearch.WordTrace]
  refine ⟨103512260314226042115161683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138016347085634722820215577 103512260314226042115161683)
  ·
    refine ⟨155268390471339063172742525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103512260314226042115161683 155268390471339063172742525)
    ·
      refine ⟨58225646426752148689778447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155268390471339063172742525 58225646426752148689778447)
      ·
        refine ⟨87338469640128223034667671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58225646426752148689778447 87338469640128223034667671)
        ·
          refine ⟨131007704460192334552001507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87338469640128223034667671 131007704460192334552001507)
          ·
            refine ⟨196511556690288501828002261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131007704460192334552001507 196511556690288501828002261)
            ·
              refine ⟨4605739609928636761593803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 196511556690288501828002261 4605739609928636761593803)
              ·
                refine ⟨6908609414892955142390705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4605739609928636761593803 6908609414892955142390705)
                ·
                  refine ⟨5181457061169716356793029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6908609414892955142390705 5181457061169716356793029)
                  ·
                    refine ⟨971523198969321816898693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5181457061169716356793029 971523198969321816898693)
                    ·
                      rfl

theorem cell23_5676104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_5676104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676104 prefixEnd_5676104 := by exact prefixLift 5676104
  have htrace : WordTrace (prefixWord ++ tailWord_5676104) baseStart_5676104 baseEnd_5676104 := by
    simpa [prefixWord, tailWord_5676104, baseEnd_5676104] using wordTrace_append hprefix tailTrace_5676104
  have hstable : (prefixWord ++ tailWord_5676104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676104).length < 2 ^ (prefixWord ++ tailWord_5676104).sum := by decide
  have hdescent : baseEnd_5676104 < baseStart_5676104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676114 : List Nat := [3, 2, 2, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_5676114 : Nat := 118140960795 + 5676114 * 2 ^ 59
def prefixEnd_5676114 : Nat := 4983230072969 + 3 ^ 40 * 5676114 * 2
def baseEnd_5676114 : Nat := 2914574731714510411571033

theorem tailTrace_5676114 : CollatzResearch.WordTrace tailWord_5676114 prefixEnd_5676114 2914574731714510411571033 := by
  unfold tailWord_5676114
  simp only [CollatzResearch.WordTrace]
  refine ⟨51756221339603963984546849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138016590238943903958791597 51756221339603963984546849)
  ·
    refine ⟨38817166004702972988410137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51756221339603963984546849 38817166004702972988410137)
    ·
      refine ⟨29112874503527229741307603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38817166004702972988410137 29112874503527229741307603)
      ·
        refine ⟨43669311755290844611961405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29112874503527229741307603 43669311755290844611961405)
        ·
          refine ⟨16375991908234066729485527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43669311755290844611961405 16375991908234066729485527)
          ·
            refine ⟨24563987862351100094228291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16375991908234066729485527 24563987862351100094228291)
            ·
              refine ⟨36845981793526650141342437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24563987862351100094228291 36845981793526650141342437)
              ·
                refine ⟨6908621586286246901501707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36845981793526650141342437 6908621586286246901501707)
                ·
                  refine ⟨10362932379429370352252561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6908621586286246901501707 10362932379429370352252561)
                  ·
                    refine ⟨7772199284572027764189421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10362932379429370352252561 7772199284572027764189421)
                    ·
                      refine ⟨2914574731714510411571033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7772199284572027764189421 2914574731714510411571033)
                      ·
                        rfl

theorem cell23_5676114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_5676114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676114 prefixEnd_5676114 := by exact prefixLift 5676114
  have htrace : WordTrace (prefixWord ++ tailWord_5676114) baseStart_5676114 baseEnd_5676114 := by
    simpa [prefixWord, tailWord_5676114, baseEnd_5676114] using wordTrace_append hprefix tailTrace_5676114
  have hstable : (prefixWord ++ tailWord_5676114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676114).length < 2 ^ (prefixWord ++ tailWord_5676114).sum := by decide
  have hdescent : baseEnd_5676114 < baseStart_5676114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676127 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 6, 1, 3]
def baseStart_5676127 : Nat := 118140960795 + 5676127 * 2 ^ 59
def prefixEnd_5676127 : Nat := 4983230072969 + 3 ^ 40 * 5676127 * 2
def baseEnd_5676127 : Nat := 2914581406963018860708473

theorem tailTrace_5676127 : CollatzResearch.WordTrace tailWord_5676127 prefixEnd_5676127 2914581406963018860708473 := by
  unfold tailWord_5676127
  simp only [CollatzResearch.WordTrace]
  refine ⟨207025359507368759158410635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138016906338245839438940423 207025359507368759158410635)
  ·
    refine ⟨310538039261053138737615953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207025359507368759158410635 310538039261053138737615953)
    ·
      refine ⟨232903529445789854053211965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310538039261053138737615953 232903529445789854053211965)
      ·
        refine ⟨87338823542171195269954487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232903529445789854053211965 87338823542171195269954487)
        ·
          refine ⟨131008235313256792904931731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87338823542171195269954487 131008235313256792904931731)
          ·
            refine ⟨196512352969885189357397597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131008235313256792904931731 196512352969885189357397597)
            ·
              refine ⟨73692132363706946009024099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196512352969885189357397597 73692132363706946009024099)
              ·
                refine ⟨110538198545560419013536149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73692132363706946009024099 110538198545560419013536149)
                ·
                  refine ⟨5181478056823144641259507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110538198545560419013536149 5181478056823144641259507)
                  ·
                    refine ⟨7772217085234716961889261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5181478056823144641259507 7772217085234716961889261)
                    ·
                      refine ⟨2914581406963018860708473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7772217085234716961889261 2914581406963018860708473)
                      ·
                        rfl

theorem cell23_5676127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_5676127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676127 prefixEnd_5676127 := by exact prefixLift 5676127
  have htrace : WordTrace (prefixWord ++ tailWord_5676127) baseStart_5676127 baseEnd_5676127 := by
    simpa [prefixWord, tailWord_5676127, baseEnd_5676127] using wordTrace_append hprefix tailTrace_5676127
  have hstable : (prefixWord ++ tailWord_5676127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676127).length < 2 ^ (prefixWord ++ tailWord_5676127).sum := by decide
  have hdescent : baseEnd_5676127 < baseStart_5676127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676140 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 5]
def baseStart_5676140 : Nat := 118140960795 + 5676140 * 2 ^ 59
def prefixEnd_5676140 : Nat := 4983230072969 + 3 ^ 40 * 5676140 * 2
def baseEnd_5676140 : Nat := 2914588082211527309845913

theorem tailTrace_5676140 : CollatzResearch.WordTrace tailWord_5676140 prefixEnd_5676140 2914588082211527309845913 := by
  unfold tailWord_5676140
  simp only [CollatzResearch.WordTrace]
  refine ⟨103512916828160831189316937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138017222437547774919089249 103512916828160831189316937)
  ·
    refine ⟨77634687621120623391987703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103512916828160831189316937 77634687621120623391987703)
    ·
      refine ⟨116452031431680935087981555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77634687621120623391987703 116452031431680935087981555)
      ·
        refine ⟨174678047147521402631972333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116452031431680935087981555 174678047147521402631972333)
        ·
          refine ⟨65504267680320525986989625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174678047147521402631972333 65504267680320525986989625)
          ·
            refine ⟨49128200760240394490242219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65504267680320525986989625 49128200760240394490242219)
            ·
              refine ⟨73692301140360591735363329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49128200760240394490242219 73692301140360591735363329)
              ·
                refine ⟨55269225855270443801522497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73692301140360591735363329 55269225855270443801522497)
                ·
                  refine ⟨41451919391452832851141873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55269225855270443801522497 41451919391452832851141873)
                  ·
                    refine ⟨31088939543589624638356405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41451919391452832851141873 31088939543589624638356405)
                    ·
                      refine ⟨2914588082211527309845913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31088939543589624638356405 2914588082211527309845913)
                      ·
                        rfl

theorem cell23_5676140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_5676140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676140 prefixEnd_5676140 := by exact prefixLift 5676140
  have htrace : WordTrace (prefixWord ++ tailWord_5676140) baseStart_5676140 baseEnd_5676140 := by
    simpa [prefixWord, tailWord_5676140, baseEnd_5676140] using wordTrace_append hprefix tailTrace_5676140
  have hstable : (prefixWord ++ tailWord_5676140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676140).length < 2 ^ (prefixWord ++ tailWord_5676140).sum := by decide
  have hdescent : baseEnd_5676140 < baseStart_5676140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676144 : List Nat := [2, 1, 1, 1, 5, 1, 2, 4, 2, 1, 3]
def baseStart_5676144 : Nat := 118140960795 + 5676144 * 2 ^ 59
def prefixEnd_5676144 : Nat := 4983230072969 + 3 ^ 40 * 5676144 * 2
def baseEnd_5676144 : Nat := 2914590136134145294195895

theorem tailTrace_5676144 : CollatzResearch.WordTrace tailWord_5676144 prefixEnd_5676144 2914590136134145294195895 := by
  unfold tailWord_5676144
  simp only [CollatzResearch.WordTrace]
  refine ⟨103512989774153585530889743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138017319698871447374519657 103512989774153585530889743)
  ·
    refine ⟨155269484661230378296334615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103512989774153585530889743 155269484661230378296334615)
    ·
      refine ⟨232904226991845567444501923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155269484661230378296334615 232904226991845567444501923)
      ·
        refine ⟨349356340487768351166752885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232904226991845567444501923 349356340487768351166752885)
        ·
          refine ⟨32752156920728282921883083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 349356340487768351166752885 32752156920728282921883083)
          ·
            refine ⟨49128235381092424382824625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32752156920728282921883083 49128235381092424382824625)
            ·
              refine ⟨36846176535819318287118469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49128235381092424382824625 36846176535819318287118469)
              ·
                refine ⟨6908658100466122178834713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36846176535819318287118469 6908658100466122178834713)
                ·
                  refine ⟨5181493575349591634126035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6908658100466122178834713 5181493575349591634126035)
                  ·
                    refine ⟨7772240363024387451189053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5181493575349591634126035 7772240363024387451189053)
                    ·
                      refine ⟨2914590136134145294195895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7772240363024387451189053 2914590136134145294195895)
                      ·
                        rfl

theorem cell23_5676144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 2, 1, 3].length) (baseStart_5676144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676144 prefixEnd_5676144 := by exact prefixLift 5676144
  have htrace : WordTrace (prefixWord ++ tailWord_5676144) baseStart_5676144 baseEnd_5676144 := by
    simpa [prefixWord, tailWord_5676144, baseEnd_5676144] using wordTrace_append hprefix tailTrace_5676144
  have hstable : (prefixWord ++ tailWord_5676144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676144).length < 2 ^ (prefixWord ++ tailWord_5676144).sum := by decide
  have hdescent : baseEnd_5676144 < baseStart_5676144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676160 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 2, 6]
def baseStart_5676160 : Nat := 118140960795 + 5676160 * 2 ^ 59
def prefixEnd_5676160 : Nat := 4983230072969 + 3 ^ 40 * 5676160 * 2
def baseEnd_5676160 : Nat := 971532783941539077198607

theorem tailTrace_5676160 : CollatzResearch.WordTrace tailWord_5676160 prefixEnd_5676160 971532783941539077198607 := by
  unfold tailWord_5676160
  simp only [CollatzResearch.WordTrace]
  refine ⟨103513281558124602897180967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138017708744166137196241289 103513281558124602897180967)
  ·
    refine ⟨155269922337186904345771451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103513281558124602897180967 155269922337186904345771451)
    ·
      refine ⟨232904883505780356518657177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155269922337186904345771451 232904883505780356518657177)
      ·
        refine ⟨174678662629335267388992883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232904883505780356518657177 174678662629335267388992883)
        ·
          refine ⟨262017993944002901083489325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174678662629335267388992883 262017993944002901083489325)
          ·
            refine ⟨98256747729001087906308497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 262017993944002901083489325 98256747729001087906308497)
            ·
              refine ⟨73692560796750815929731373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98256747729001087906308497 73692560796750815929731373)
              ·
                refine ⟨27634710298781555973649265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73692560796750815929731373 27634710298781555973649265)
                ·
                  refine ⟨20726032724086166980236949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27634710298781555973649265 20726032724086166980236949)
                  ·
                    refine ⟨971532783941539077198607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20726032724086166980236949 971532783941539077198607)
                    ·
                      rfl

theorem cell23_5676160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 2, 6].length) (baseStart_5676160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676160 prefixEnd_5676160 := by exact prefixLift 5676160
  have htrace : WordTrace (prefixWord ++ tailWord_5676160) baseStart_5676160 baseEnd_5676160 := by
    simpa [prefixWord, tailWord_5676160, baseEnd_5676160] using wordTrace_append hprefix tailTrace_5676160
  have hstable : (prefixWord ++ tailWord_5676160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676160).length < 2 ^ (prefixWord ++ tailWord_5676160).sum := by decide
  have hdescent : baseEnd_5676160 < baseStart_5676160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676161 : List Nat := [1, 2, 4, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_5676161 : Nat := 118140960795 + 5676161 * 2 ^ 59
def prefixEnd_5676161 : Nat := 4983230072969 + 3 ^ 40 * 5676161 * 2
def baseEnd_5676161 : Nat := 2914598865305271727683317

theorem tailTrace_5676161 : CollatzResearch.WordTrace tailWord_5676161 prefixEnd_5676161 2914598865305271727683317 := by
  unfold tailWord_5676161
  simp only [CollatzResearch.WordTrace]
  refine ⟨207026599589245582965148337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138017733059497055310098891 207026599589245582965148337)
  ·
    refine ⟨155269949691934187223861253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207026599589245582965148337 155269949691934187223861253)
    ·
      refine ⟨29113115567237660104473985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155269949691934187223861253 29113115567237660104473985)
      ·
        refine ⟨21834836675428245078355489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29113115567237660104473985 21834836675428245078355489)
        ·
          refine ⟨16376127506571183808766617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21834836675428245078355489 16376127506571183808766617)
          ·
            refine ⟨12282095629928387856574963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16376127506571183808766617 12282095629928387856574963)
            ·
              refine ⟨18423143444892581784862445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12282095629928387856574963 18423143444892581784862445)
              ·
                refine ⟨6908678791834718169323417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18423143444892581784862445 6908678791834718169323417)
                ·
                  refine ⟨5181509093876038626992563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6908678791834718169323417 5181509093876038626992563)
                  ·
                    refine ⟨7772263640814057940488845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5181509093876038626992563 7772263640814057940488845)
                    ·
                      refine ⟨2914598865305271727683317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7772263640814057940488845 2914598865305271727683317)
                      ·
                        rfl

theorem cell23_5676161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_5676161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676161 prefixEnd_5676161 := by exact prefixLift 5676161
  have htrace : WordTrace (prefixWord ++ tailWord_5676161) baseStart_5676161 baseEnd_5676161 := by
    simpa [prefixWord, tailWord_5676161, baseEnd_5676161] using wordTrace_append hprefix tailTrace_5676161
  have hstable : (prefixWord ++ tailWord_5676161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676161).length < 2 ^ (prefixWord ++ tailWord_5676161).sum := by decide
  have hdescent : baseEnd_5676161 < baseStart_5676161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676184 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 3, 4, 2]
def baseStart_5676184 : Nat := 118140960795 + 5676184 * 2 ^ 59
def prefixEnd_5676184 : Nat := 4983230072969 + 3 ^ 40 * 5676184 * 2
def baseEnd_5676184 : Nat := 2914610675360325137695711

theorem tailTrace_5676184 : CollatzResearch.WordTrace tailWord_5676184 prefixEnd_5676184 2914610675360325137695711 := by
  unfold tailWord_5676184
  simp only [CollatzResearch.WordTrace]
  refine ⟨103513719234081128946617803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138018292312108171928823737 103513719234081128946617803)
  ·
    refine ⟨155270578851121693419926705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103513719234081128946617803 155270578851121693419926705)
    ·
      refine ⟨116452934138341270064945029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155270578851121693419926705 116452934138341270064945029)
      ·
        refine ⟨21834925150938988137177193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116452934138341270064945029 21834925150938988137177193)
        ·
          refine ⟨16376193863204241102882895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21834925150938988137177193 16376193863204241102882895)
          ·
            refine ⟨24564290794806361654324343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16376193863204241102882895 24564290794806361654324343)
            ·
              refine ⟨36846436192209542481486515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24564290794806361654324343 36846436192209542481486515)
              ·
                refine ⟨55269654288314313722229773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36846436192209542481486515 55269654288314313722229773)
                ·
                  refine ⟨20726120358117867645836165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55269654288314313722229773 20726120358117867645836165)
                  ·
                    refine ⟨3886147567147100183594281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20726120358117867645836165 3886147567147100183594281)
                    ·
                      refine ⟨2914610675360325137695711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3886147567147100183594281 2914610675360325137695711)
                      ·
                        rfl

theorem cell23_5676184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_5676184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676184 prefixEnd_5676184 := by exact prefixLift 5676184
  have htrace : WordTrace (prefixWord ++ tailWord_5676184) baseStart_5676184 baseEnd_5676184 := by
    simpa [prefixWord, tailWord_5676184, baseEnd_5676184] using wordTrace_append hprefix tailTrace_5676184
  have hstable : (prefixWord ++ tailWord_5676184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676184).length < 2 ^ (prefixWord ++ tailWord_5676184).sum := by decide
  have hdescent : baseEnd_5676184 < baseStart_5676184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676188 : List Nat := [2, 2, 3, 2, 1, 3, 3, 1, 1, 3, 2]
def baseStart_5676188 : Nat := 118140960795 + 5676188 * 2 ^ 59
def prefixEnd_5676188 : Nat := 4983230072969 + 3 ^ 40 * 5676188 * 2
def baseEnd_5676188 : Nat := 2914612729282943122045693

theorem tailTrace_5676188 : CollatzResearch.WordTrace tailWord_5676188 prefixEnd_5676188 2914612729282943122045693 := by
  unfold tailWord_5676188
  simp only [CollatzResearch.WordTrace]
  refine ⟨103513792180073883288190609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138018389573431844384254145 103513792180073883288190609)
  ·
    refine ⟨77635344135055412466142957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103513792180073883288190609 77635344135055412466142957)
    ·
      refine ⟨29113254050645779674803609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77635344135055412466142957 29113254050645779674803609)
      ·
        refine ⟨21834940537984334756102707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29113254050645779674803609 21834940537984334756102707)
        ·
          refine ⟨32752410806976502134154061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21834940537984334756102707 32752410806976502134154061)
          ·
            refine ⟨12282154052616188300307773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32752410806976502134154061 12282154052616188300307773)
            ·
              refine ⟨4605807769731070612615415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12282154052616188300307773 4605807769731070612615415)
              ·
                refine ⟨6908711654596605918923123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4605807769731070612615415 6908711654596605918923123)
                ·
                  refine ⟨10363067481894908878384685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6908711654596605918923123 10363067481894908878384685)
                  ·
                    refine ⟨3886150305710590829394257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10363067481894908878384685 3886150305710590829394257)
                    ·
                      refine ⟨2914612729282943122045693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3886150305710590829394257 2914612729282943122045693)
                      ·
                        rfl

theorem cell23_5676188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_5676188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676188 prefixEnd_5676188 := by exact prefixLift 5676188
  have htrace : WordTrace (prefixWord ++ tailWord_5676188) baseStart_5676188 baseEnd_5676188 := by
    simpa [prefixWord, tailWord_5676188, baseEnd_5676188] using wordTrace_append hprefix tailTrace_5676188
  have hstable : (prefixWord ++ tailWord_5676188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676188).length < 2 ^ (prefixWord ++ tailWord_5676188).sum := by decide
  have hdescent : baseEnd_5676188 < baseStart_5676188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676217 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 1, 5, 3]
def baseStart_5676217 : Nat := 118140960795 + 5676217 * 2 ^ 59
def prefixEnd_5676217 : Nat := 4983230072969 + 3 ^ 40 * 5676217 * 2
def baseEnd_5676217 : Nat := 2914627620221923508583059

theorem tailTrace_5676217 : CollatzResearch.WordTrace tailWord_5676217 prefixEnd_5676217 2914627620221923508583059 := by
  unfold tailWord_5676217
  simp only [CollatzResearch.WordTrace]
  refine ⟨207028642077042704529186905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138019094718028469686124603 207028642077042704529186905)
  ·
    refine ⟨155271481557782028396890179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207028642077042704529186905 155271481557782028396890179)
    ·
      refine ⟨232907222336673042595335269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155271481557782028396890179 232907222336673042595335269)
      ·
        refine ⟨43670104188126195486625363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232907222336673042595335269 43670104188126195486625363)
        ·
          refine ⟨65505156282189293229938045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43670104188126195486625363 65505156282189293229938045)
          ·
            refine ⟨24564433605820984961226767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65505156282189293229938045 24564433605820984961226767)
            ·
              refine ⟨36846650408731477441840151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24564433605820984961226767 36846650408731477441840151)
              ·
                refine ⟨55269975613097216162760227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36846650408731477441840151 55269975613097216162760227)
                ·
                  refine ⟨82904963419645824244140341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55269975613097216162760227 82904963419645824244140341)
                  ·
                    refine ⟨7772340320591796022888157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82904963419645824244140341 7772340320591796022888157)
                    ·
                      refine ⟨2914627620221923508583059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7772340320591796022888157 2914627620221923508583059)
                      ·
                        rfl

theorem cell23_5676217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_5676217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676217 prefixEnd_5676217 := by exact prefixLift 5676217
  have htrace : WordTrace (prefixWord ++ tailWord_5676217) baseStart_5676217 baseEnd_5676217 := by
    simpa [prefixWord, tailWord_5676217, baseEnd_5676217] using wordTrace_append hprefix tailTrace_5676217
  have hstable : (prefixWord ++ tailWord_5676217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676217).length < 2 ^ (prefixWord ++ tailWord_5676217).sum := by decide
  have hdescent : baseEnd_5676217 < baseStart_5676217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676351 : List Nat := [1, 1, 2, 2, 4, 2, 1, 3, 2, 3, 2]
def baseStart_5676351 : Nat := 118140960795 + 5676351 * 2 ^ 59
def prefixEnd_5676351 : Nat := 4983230072969 + 3 ^ 40 * 5676351 * 2
def baseEnd_5676351 : Nat := 2914696426629625984307443

theorem tailTrace_5676351 : CollatzResearch.WordTrace tailWord_5676351 prefixEnd_5676351 2914696426629625984307443 := by
  unfold tailWord_5676351
  simp only [CollatzResearch.WordTrace]
  refine ⟨207033529458557245414564907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138022352972371496943043271 207033529458557245414564907)
  ·
    refine ⟨310550294187835868121847361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207033529458557245414564907 310550294187835868121847361)
    ·
      refine ⟨232912720640876901091385521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310550294187835868121847361 232912720640876901091385521)
      ·
        refine ⟨174684540480657675818539141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232912720640876901091385521 174684540480657675818539141)
        ·
          refine ⟨32753351340123314215976089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174684540480657675818539141 32753351340123314215976089)
          ·
            refine ⟨24565013505092485661982067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32753351340123314215976089 24565013505092485661982067)
            ·
              refine ⟨36847520257638728492973101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24565013505092485661982067 36847520257638728492973101)
              ·
                refine ⟨13817820096614523184864913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36847520257638728492973101 13817820096614523184864913)
                ·
                  refine ⟨10363365072460892388648685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13817820096614523184864913 10363365072460892388648685)
                  ·
                    refine ⟨3886261902172834645743257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10363365072460892388648685 3886261902172834645743257)
                    ·
                      refine ⟨2914696426629625984307443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3886261902172834645743257 2914696426629625984307443)
                      ·
                        rfl

theorem cell23_5676351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 3, 2].length) (baseStart_5676351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676351 prefixEnd_5676351 := by exact prefixLift 5676351
  have htrace : WordTrace (prefixWord ++ tailWord_5676351) baseStart_5676351 baseEnd_5676351 := by
    simpa [prefixWord, tailWord_5676351, baseEnd_5676351] using wordTrace_append hprefix tailTrace_5676351
  have hstable : (prefixWord ++ tailWord_5676351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676351).length < 2 ^ (prefixWord ++ tailWord_5676351).sum := by decide
  have hdescent : baseEnd_5676351 < baseStart_5676351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676375 : List Nat := [1, 1, 3, 2, 3, 2, 4, 2, 1, 1, 3]
def baseStart_5676375 : Nat := 118140960795 + 5676375 * 2 ^ 59
def prefixEnd_5676375 : Nat := 4983230072969 + 3 ^ 40 * 5676375 * 2
def baseEnd_5676375 : Nat := 2914708750165333890407333

theorem tailTrace_5676375 : CollatzResearch.WordTrace tailWord_5676375 prefixEnd_5676375 2914708750165333890407333 := by
  unfold tailWord_5676375
  simp only [CollatzResearch.WordTrace]
  refine ⟨207034404810470297513438579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138022936540313531675625719 207034404810470297513438579)
  ·
    refine ⟨310551607215705446270157869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207034404810470297513438579 310551607215705446270157869)
    ·
      refine ⟨116456852705889542351309201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310551607215705446270157869 116456852705889542351309201)
      ·
        refine ⟨87342639529417156763481901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116456852705889542351309201 87342639529417156763481901)
        ·
          refine ⟨32753489823531433786305713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87342639529417156763481901 32753489823531433786305713)
          ·
            refine ⟨24565117367648575339729285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32753489823531433786305713 24565117367648575339729285)
            ·
              refine ⟨4605959506434107876199241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24565117367648575339729285 4605959506434107876199241)
              ·
                refine ⟨3454469629825580907149431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4605959506434107876199241 3454469629825580907149431)
                ·
                  refine ⟨5181704444738371360724147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3454469629825580907149431 5181704444738371360724147)
                  ·
                    refine ⟨7772556667107557041086221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5181704444738371360724147 7772556667107557041086221)
                    ·
                      refine ⟨2914708750165333890407333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7772556667107557041086221 2914708750165333890407333)
                      ·
                        rfl

theorem cell23_5676375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_5676375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676375 prefixEnd_5676375 := by exact prefixLift 5676375
  have htrace : WordTrace (prefixWord ++ tailWord_5676375) baseStart_5676375 baseEnd_5676375 := by
    simpa [prefixWord, tailWord_5676375, baseEnd_5676375] using wordTrace_append hprefix tailTrace_5676375
  have hstable : (prefixWord ++ tailWord_5676375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676375).length < 2 ^ (prefixWord ++ tailWord_5676375).sum := by decide
  have hdescent : baseEnd_5676375 < baseStart_5676375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676377 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 3, 1, 6]
def baseStart_5676377 : Nat := 118140960795 + 5676377 * 2 ^ 59
def prefixEnd_5676377 : Nat := 4983230072969 + 3 ^ 40 * 5676377 * 2
def baseEnd_5676377 : Nat := 2914709777126642882582323

theorem tailTrace_5676377 : CollatzResearch.WordTrace tailWord_5676377 prefixEnd_5676377 2914709777126642882582323 := by
  unfold tailWord_5676377
  simp only [CollatzResearch.WordTrace]
  refine ⟨207034477756463051855011385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138022985170975367903340923 207034477756463051855011385)
  ·
    refine ⟨155275858317347288891258539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207034477756463051855011385 155275858317347288891258539)
    ·
      refine ⟨232913787476020933336887809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155275858317347288891258539 232913787476020933336887809)
      ·
        refine ⟨174685340607015700002665857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232913787476020933336887809 174685340607015700002665857)
        ·
          refine ⟨131014005455261775001999393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174685340607015700002665857 131014005455261775001999393)
          ·
            refine ⟨98260504091446331251499545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131014005455261775001999393 98260504091446331251499545)
            ·
              refine ⟨73695378068584748438624659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98260504091446331251499545 73695378068584748438624659)
              ·
                refine ⟨110543067102877122657936989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73695378068584748438624659 110543067102877122657936989)
                ·
                  refine ⟨41453650163578920996726371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110543067102877122657936989 41453650163578920996726371)
                  ·
                    refine ⟨62180475245368381495089557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41453650163578920996726371 62180475245368381495089557)
                    ·
                      refine ⟨2914709777126642882582323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62180475245368381495089557 2914709777126642882582323)
                      ·
                        rfl

theorem cell23_5676377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_5676377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676377 prefixEnd_5676377 := by exact prefixLift 5676377
  have htrace : WordTrace (prefixWord ++ tailWord_5676377) baseStart_5676377 baseEnd_5676377 := by
    simpa [prefixWord, tailWord_5676377, baseEnd_5676377] using wordTrace_append hprefix tailTrace_5676377
  have hstable : (prefixWord ++ tailWord_5676377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676377).length < 2 ^ (prefixWord ++ tailWord_5676377).sum := by decide
  have hdescent : baseEnd_5676377 < baseStart_5676377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676391 : List Nat := [1, 1, 5, 1, 4, 1, 2, 1, 1, 6]
def baseStart_5676391 : Nat := 118140960795 + 5676391 * 2 ^ 59
def prefixEnd_5676391 : Nat := 4983230072969 + 3 ^ 40 * 5676391 * 2
def baseEnd_5676391 : Nat := 971572321951935275935753

theorem tailTrace_5676391 : CollatzResearch.WordTrace tailWord_5676391 prefixEnd_5676391 971572321951935275935753 := by
  unfold tailWord_5676391
  simp only [CollatzResearch.WordTrace]
  refine ⟨207034988378412332246021027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138023325585608221497347351 207034988378412332246021027)
  ·
    refine ⟨310552482567618498369031541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207034988378412332246021027 310552482567618498369031541)
    ·
      refine ⟨29114295240714234222096707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 310552482567618498369031541 29114295240714234222096707)
      ·
        refine ⟨43671442861071351333145061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29114295240714234222096707 43671442861071351333145061)
        ·
          refine ⟨8188395536450878374964699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43671442861071351333145061 8188395536450878374964699)
          ·
            refine ⟨12282593304676317562447049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8188395536450878374964699 12282593304676317562447049)
            ·
              refine ⟨9211944978507238171835287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12282593304676317562447049 9211944978507238171835287)
              ·
                refine ⟨13817917467760857257752931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9211944978507238171835287 13817917467760857257752931)
                ·
                  refine ⟨20726876201641285886629397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13817917467760857257752931 20726876201641285886629397)
                  ·
                    refine ⟨971572321951935275935753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20726876201641285886629397 971572321951935275935753)
                    ·
                      rfl

theorem cell23_5676391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_5676391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676391 prefixEnd_5676391 := by exact prefixLift 5676391
  have htrace : WordTrace (prefixWord ++ tailWord_5676391) baseStart_5676391 baseEnd_5676391 := by
    simpa [prefixWord, tailWord_5676391, baseEnd_5676391] using wordTrace_append hprefix tailTrace_5676391
  have hstable : (prefixWord ++ tailWord_5676391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676391).length < 2 ^ (prefixWord ++ tailWord_5676391).sum := by decide
  have hdescent : baseEnd_5676391 < baseStart_5676391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676425 : List Nat := [1, 2, 1, 1, 8, 1, 1, 2, 2, 4]
def baseStart_5676425 : Nat := 118140960795 + 5676425 * 2 ^ 59
def prefixEnd_5676425 : Nat := 4983230072969 + 3 ^ 40 * 5676425 * 2
def baseEnd_5676425 : Nat := 971578141399352898260701

theorem tailTrace_5676425 : CollatzResearch.WordTrace tailWord_5676425 prefixEnd_5676425 971578141399352898260701 := by
  unfold tailWord_5676425
  simp only [CollatzResearch.WordTrace]
  refine ⟨207036228460289156052758729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138024152306859437368505819 207036228460289156052758729)
  ·
    refine ⟨155277171345216867039569047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207036228460289156052758729 155277171345216867039569047)
    ·
      refine ⟨232915757017825300559353571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155277171345216867039569047 232915757017825300559353571)
      ·
        refine ⟨349373635526737950839030357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232915757017825300559353571 349373635526737950839030357)
        ·
          refine ⟨4094222291328960361394887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 349373635526737950839030357 4094222291328960361394887)
          ·
            refine ⟨6141333436993440542092331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4094222291328960361394887 6141333436993440542092331)
            ·
              refine ⟨9212000155490160813138497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6141333436993440542092331 9212000155490160813138497)
              ·
                refine ⟨6909000116617620609853873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9212000155490160813138497 6909000116617620609853873)
                ·
                  refine ⟨5181750087463215457390405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6909000116617620609853873 5181750087463215457390405)
                  ·
                    refine ⟨971578141399352898260701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5181750087463215457390405 971578141399352898260701)
                    ·
                      rfl

theorem cell23_5676425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 2, 4].length) (baseStart_5676425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676425 prefixEnd_5676425 := by exact prefixLift 5676425
  have htrace : WordTrace (prefixWord ++ tailWord_5676425) baseStart_5676425 baseEnd_5676425 := by
    simpa [prefixWord, tailWord_5676425, baseEnd_5676425] using wordTrace_append hprefix tailTrace_5676425
  have hstable : (prefixWord ++ tailWord_5676425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676425).length < 2 ^ (prefixWord ++ tailWord_5676425).sum := by decide
  have hdescent : baseEnd_5676425 < baseStart_5676425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676461 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_5676461 : Nat := 118140960795 + 5676461 * 2 ^ 59
def prefixEnd_5676461 : Nat := 4983230072969 + 3 ^ 40 * 5676461 * 2
def baseEnd_5676461 : Nat := 2914752909501620553931937

theorem tailTrace_5676461 : CollatzResearch.WordTrace tailWord_5676461 prefixEnd_5676461 2914752909501620553931937 := by
  unfold tailWord_5676461
  simp only [CollatzResearch.WordTrace]
  refine ⟨207037541488158734201069237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138025027658772489467379491 207037541488158734201069237)
  ·
    refine ⟨19409769514514881331350241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207037541488158734201069237 19409769514514881331350241)
    ·
      refine ⟨14557327135886160998512681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19409769514514881331350241 14557327135886160998512681)
      ·
        refine ⟨10917995351914620748884511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14557327135886160998512681 10917995351914620748884511)
        ·
          refine ⟨16376993027871931123326767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10917995351914620748884511 16376993027871931123326767)
          ·
            refine ⟨24565489541807896684990151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16376993027871931123326767 24565489541807896684990151)
            ·
              refine ⟨36848234312711845027485227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24565489541807896684990151 36848234312711845027485227)
              ·
                refine ⟨55272351469067767541227841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36848234312711845027485227 55272351469067767541227841)
                ·
                  refine ⟨41454263601800825655920881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55272351469067767541227841 41454263601800825655920881)
                  ·
                    refine ⟨31090697701350619241940661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41454263601800825655920881 31090697701350619241940661)
                    ·
                      refine ⟨2914752909501620553931937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31090697701350619241940661 2914752909501620553931937)
                      ·
                        rfl

theorem cell23_5676461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_5676461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676461 prefixEnd_5676461 := by exact prefixLift 5676461
  have htrace : WordTrace (prefixWord ++ tailWord_5676461) baseStart_5676461 baseEnd_5676461 := by
    simpa [prefixWord, tailWord_5676461, baseEnd_5676461] using wordTrace_append hprefix tailTrace_5676461
  have hstable : (prefixWord ++ tailWord_5676461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676461).length < 2 ^ (prefixWord ++ tailWord_5676461).sum := by decide
  have hdescent : baseEnd_5676461 < baseStart_5676461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676471 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 3, 4, 2]
def baseStart_5676471 : Nat := 118140960795 + 5676471 * 2 ^ 59
def prefixEnd_5676471 : Nat := 4983230072969 + 3 ^ 40 * 5676471 * 2
def baseEnd_5676471 : Nat := 2914758044308165514806891

theorem tailTrace_5676471 : CollatzResearch.WordTrace tailWord_5676471 prefixEnd_5676471 2914758044308165514806891 := by
  unfold tailWord_5676471
  simp only [CollatzResearch.WordTrace]
  refine ⟨207037906218122505908933267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138025270812081670605955511 207037906218122505908933267)
  ·
    refine ⟨310556859327183758863399901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207037906218122505908933267 310556859327183758863399901)
    ·
      refine ⟨116458822247693909573774963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310556859327183758863399901 116458822247693909573774963)
      ·
        refine ⟨174688233371540864360662445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116458822247693909573774963 174688233371540864360662445)
        ·
          refine ⟨65508087514327824135248417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174688233371540864360662445 65508087514327824135248417)
          ·
            refine ⟨49131065635745868101436313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65508087514327824135248417 49131065635745868101436313)
            ·
              refine ⟨36848299226809401076077235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49131065635745868101436313 36848299226809401076077235)
              ·
                refine ⟨55272448840214101614115853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36848299226809401076077235 55272448840214101614115853)
                ·
                  refine ⟨20727168315080288105293445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55272448840214101614115853 20727168315080288105293445)
                  ·
                    refine ⟨3886344059077554019742521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20727168315080288105293445 3886344059077554019742521)
                    ·
                      refine ⟨2914758044308165514806891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3886344059077554019742521 2914758044308165514806891)
                      ·
                        rfl

theorem cell23_5676471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 4, 2].length) (baseStart_5676471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676471 prefixEnd_5676471 := by exact prefixLift 5676471
  have htrace : WordTrace (prefixWord ++ tailWord_5676471) baseStart_5676471 baseEnd_5676471 := by
    simpa [prefixWord, tailWord_5676471, baseEnd_5676471] using wordTrace_append hprefix tailTrace_5676471
  have hstable : (prefixWord ++ tailWord_5676471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676471).length < 2 ^ (prefixWord ++ tailWord_5676471).sum := by decide
  have hdescent : baseEnd_5676471 < baseStart_5676471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676474 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3]
def baseStart_5676474 : Nat := 118140960795 + 5676474 * 2 ^ 59
def prefixEnd_5676474 : Nat := 4983230072969 + 3 ^ 40 * 5676474 * 2
def baseEnd_5676474 : Nat := 2914759584750129003069377

theorem tailTrace_5676474 : CollatzResearch.WordTrace tailWord_5676474 prefixEnd_5676474 2914759584750129003069377 := by
  unfold tailWord_5676474
  simp only [CollatzResearch.WordTrace]
  refine ⟨51759503909277909355323119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138025343758074424947528317 51759503909277909355323119)
  ·
    refine ⟨77639255863916864032984679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51759503909277909355323119 77639255863916864032984679)
    ·
      refine ⟨116458883795875296049477019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77639255863916864032984679 116458883795875296049477019)
      ·
        refine ⟨174688325693812944074215529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116458883795875296049477019 174688325693812944074215529)
        ·
          refine ⟨131016244270359708055661647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174688325693812944074215529 131016244270359708055661647)
          ·
            refine ⟨196524366405539562083492471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131016244270359708055661647 196524366405539562083492471)
            ·
              refine ⟨294786549608309343125238707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196524366405539562083492471 294786549608309343125238707)
              ·
                refine ⟨442179824412464014687858061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294786549608309343125238707 442179824412464014687858061)
                ·
                  refine ⟨165817434154674005507946773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 442179824412464014687858061 165817434154674005507946773)
                  ·
                    refine ⟨7772692226000344008185005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 165817434154674005507946773 7772692226000344008185005)
                    ·
                      refine ⟨2914759584750129003069377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7772692226000344008185005 2914759584750129003069377)
                      ·
                        rfl

theorem cell23_5676474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_5676474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676474 prefixEnd_5676474 := by exact prefixLift 5676474
  have htrace : WordTrace (prefixWord ++ tailWord_5676474) baseStart_5676474 baseEnd_5676474 := by
    simpa [prefixWord, tailWord_5676474, baseEnd_5676474] using wordTrace_append hprefix tailTrace_5676474
  have hstable : (prefixWord ++ tailWord_5676474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676474).length < 2 ^ (prefixWord ++ tailWord_5676474).sum := by decide
  have hdescent : baseEnd_5676474 < baseStart_5676474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676488 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 4, 2, 2]
def baseStart_5676488 : Nat := 118140960795 + 5676488 * 2 ^ 59
def prefixEnd_5676488 : Nat := 4983230072969 + 3 ^ 40 * 5676488 * 2
def baseEnd_5676488 : Nat := 2914766773479291948294313

theorem tailTrace_5676488 : CollatzResearch.WordTrace tailWord_5676488 prefixEnd_5676488 2914766773479291948294313 := by
  unfold tailWord_5676488
  simp only [CollatzResearch.WordTrace]
  refine ⟨103519263129530458906151059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138025684172707278541534745 103519263129530458906151059)
  ·
    refine ⟨155278894694295688359226589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103519263129530458906151059 155278894694295688359226589)
    ·
      refine ⟨58229585510360883134709971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155278894694295688359226589 58229585510360883134709971)
      ·
        refine ⟨87344378265541324702064957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58229585510360883134709971 87344378265541324702064957)
        ·
          refine ⟨32754141849577996763274359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87344378265541324702064957 32754141849577996763274359)
          ·
            refine ⟨49131212774366995144911539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32754141849577996763274359 49131212774366995144911539)
            ·
              refine ⟨73696819161550492717367309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49131212774366995144911539 73696819161550492717367309)
              ·
                refine ⟨27636307185581434769012741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73696819161550492717367309 27636307185581434769012741)
                ·
                  refine ⟨5181807597296519019189889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27636307185581434769012741 5181807597296519019189889)
                  ·
                    refine ⟨3886355697972389264392417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5181807597296519019189889 3886355697972389264392417)
                    ·
                      refine ⟨2914766773479291948294313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3886355697972389264392417 2914766773479291948294313)
                      ·
                        rfl

theorem cell23_5676488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_5676488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676488 prefixEnd_5676488 := by exact prefixLift 5676488
  have htrace : WordTrace (prefixWord ++ tailWord_5676488) baseStart_5676488 baseEnd_5676488 := by
    simpa [prefixWord, tailWord_5676488, baseEnd_5676488] using wordTrace_append hprefix tailTrace_5676488
  have hstable : (prefixWord ++ tailWord_5676488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676488).length < 2 ^ (prefixWord ++ tailWord_5676488).sum := by decide
  have hdescent : baseEnd_5676488 < baseStart_5676488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676505 : List Nat := [1, 2, 1, 2, 4, 3, 1, 3, 2, 2, 2]
def baseStart_5676505 : Nat := 118140960795 + 5676505 * 2 ^ 59
def prefixEnd_5676505 : Nat := 4983230072969 + 3 ^ 40 * 5676505 * 2
def baseEnd_5676505 : Nat := 2914775502650418381781735

theorem tailTrace_5676505 : CollatzResearch.WordTrace tailWord_5676505 prefixEnd_5676505 2914775502650418381781735 := by
  unfold tailWord_5676505
  simp only [CollatzResearch.WordTrace]
  refine ⟨207039146299999329715670969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138026097533332886477113979 207039146299999329715670969)
  ·
    refine ⟨155279359724999497286753227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207039146299999329715670969 155279359724999497286753227)
    ·
      refine ⟨232919039587499245930129841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155279359724999497286753227 232919039587499245930129841)
      ·
        refine ⟨174689279690624434447597381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232919039587499245930129841 174689279690624434447597381)
        ·
          refine ⟨32754239941992081458924509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174689279690624434447597381 32754239941992081458924509)
          ·
            refine ⟨12282839978247030547096691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32754239941992081458924509 12282839978247030547096691)
            ·
              refine ⟨18424259967370545820645037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12282839978247030547096691 18424259967370545820645037)
              ·
                refine ⟨6909097487763954682741889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18424259967370545820645037 6909097487763954682741889)
                ·
                  refine ⟨5181823115822966012056417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6909097487763954682741889 5181823115822966012056417)
                  ·
                    refine ⟨3886367336867224509042313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5181823115822966012056417 3886367336867224509042313)
                    ·
                      refine ⟨2914775502650418381781735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3886367336867224509042313 2914775502650418381781735)
                      ·
                        rfl

theorem cell23_5676505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 2, 2].length) (baseStart_5676505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676505 prefixEnd_5676505 := by exact prefixLift 5676505
  have htrace : WordTrace (prefixWord ++ tailWord_5676505) baseStart_5676505 baseEnd_5676505 := by
    simpa [prefixWord, tailWord_5676505, baseEnd_5676505] using wordTrace_append hprefix tailTrace_5676505
  have hstable : (prefixWord ++ tailWord_5676505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676505).length < 2 ^ (prefixWord ++ tailWord_5676505).sum := by decide
  have hdescent : baseEnd_5676505 < baseStart_5676505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676541 : List Nat := [1, 4, 1, 1, 1, 4, 2, 2, 2, 5]
def baseStart_5676541 : Nat := 118140960795 + 5676541 * 2 ^ 59
def prefixEnd_5676541 : Nat := 4983230072969 + 3 ^ 40 * 5676541 * 2
def baseEnd_5676541 : Nat := 971597995984660080310523

theorem tailTrace_5676541 : CollatzResearch.WordTrace tailWord_5676541 prefixEnd_5676541 971597995984660080310523 := by
  unfold tailWord_5676541
  simp only [CollatzResearch.WordTrace]
  refine ⟨207040459327868907863981477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138026972885245938575987651 207040459327868907863981477)
  ·
    refine ⟨38820086123975420224496527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207040459327868907863981477 38820086123975420224496527)
    ·
      refine ⟨58230129185963130336744791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38820086123975420224496527 58230129185963130336744791)
      ·
        refine ⟨87345193778944695505117187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58230129185963130336744791 87345193778944695505117187)
        ·
          refine ⟨131017790668417043257675781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87345193778944695505117187 131017790668417043257675781)
          ·
            refine ⟨24565835750328195610814209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131017790668417043257675781 24565835750328195610814209)
            ·
              refine ⟨18424376812746146708110657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24565835750328195610814209 18424376812746146708110657)
              ·
                refine ⟨13818282609559610031082993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18424376812746146708110657 13818282609559610031082993)
                ·
                  refine ⟨10363711957169707523312245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13818282609559610031082993 10363711957169707523312245)
                  ·
                    refine ⟨971597995984660080310523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10363711957169707523312245 971597995984660080310523)
                    ·
                      rfl

theorem cell23_5676541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_5676541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676541 prefixEnd_5676541 := by exact prefixLift 5676541
  have htrace : WordTrace (prefixWord ++ tailWord_5676541) baseStart_5676541 baseEnd_5676541 := by
    simpa [prefixWord, tailWord_5676541, baseEnd_5676541] using wordTrace_append hprefix tailTrace_5676541
  have hstable : (prefixWord ++ tailWord_5676541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676541).length < 2 ^ (prefixWord ++ tailWord_5676541).sum := by decide
  have hdescent : baseEnd_5676541 < baseStart_5676541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676551 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_5676551 : Nat := 118140960795 + 5676551 * 2 ^ 59
def prefixEnd_5676551 : Nat := 4983230072969 + 3 ^ 40 * 5676551 * 2
def baseEnd_5676551 : Nat := 2914799122760525201806523

theorem tailTrace_5676551 : CollatzResearch.WordTrace tailWord_5676551 prefixEnd_5676551 2914799122760525201806523 := by
  unfold tailWord_5676551
  simp only [CollatzResearch.WordTrace]
  refine ⟨207040824057832679571845507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138027216038555119714563671 207040824057832679571845507)
  ·
    refine ⟨310561236086749019357768261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207040824057832679571845507 310561236086749019357768261)
    ·
      refine ⟨58230231766265441129581549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310561236086749019357768261 58230231766265441129581549)
      ·
        refine ⟨21836336912349540423593081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58230231766265441129581549 21836336912349540423593081)
        ·
          refine ⟨16377252684262155317694811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21836336912349540423593081 16377252684262155317694811)
          ·
            refine ⟨24565879026393232976542217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16377252684262155317694811 24565879026393232976542217)
            ·
              refine ⟨18424409269794924732406663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24565879026393232976542217 18424409269794924732406663)
              ·
                refine ⟨27636613904692387098609995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18424409269794924732406663 27636613904692387098609995)
                ·
                  refine ⟨41454920857038580647914993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27636613904692387098609995 41454920857038580647914993)
                  ·
                    refine ⟨31091190642778935485936245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41454920857038580647914993 31091190642778935485936245)
                    ·
                      refine ⟨2914799122760525201806523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31091190642778935485936245 2914799122760525201806523)
                      ·
                        rfl

theorem cell23_5676551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_5676551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676551 prefixEnd_5676551 := by exact prefixLift 5676551
  have htrace : WordTrace (prefixWord ++ tailWord_5676551) baseStart_5676551 baseEnd_5676551 := by
    simpa [prefixWord, tailWord_5676551, baseEnd_5676551] using wordTrace_append hprefix tailTrace_5676551
  have hstable : (prefixWord ++ tailWord_5676551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676551).length < 2 ^ (prefixWord ++ tailWord_5676551).sum := by decide
  have hdescent : baseEnd_5676551 < baseStart_5676551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676578 : List Nat := [3, 3, 1, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_5676578 : Nat := 118140960795 + 5676578 * 2 ^ 59
def prefixEnd_5676578 : Nat := 4983230072969 + 3 ^ 40 * 5676578 * 2
def baseEnd_5676578 : Nat := 2914812986738196596168899

theorem tailTrace_5676578 : CollatzResearch.WordTrace tailWord_5676578 prefixEnd_5676578 2914812986738196596168899 := by
  unfold tailWord_5676578
  simp only [CollatzResearch.WordTrace]
  refine ⟨51760452207183715795769597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138027872552489908788718925 51760452207183715795769597)
  ·
    refine ⟨19410169577693893423413599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51760452207183715795769597 19410169577693893423413599)
    ·
      refine ⟨29115254366540840135120399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19410169577693893423413599 29115254366540840135120399)
      ·
        refine ⟨43672881549811260202680599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29115254366540840135120399 43672881549811260202680599)
        ·
          refine ⟨65509322324716890304020899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43672881549811260202680599 65509322324716890304020899)
          ·
            refine ⟨98263983487075335456031349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65509322324716890304020899 98263983487075335456031349)
            ·
              refine ⟨9212248451913312699002939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98263983487075335456031349 9212248451913312699002939)
              ·
                refine ⟨13818372677869969048504409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9212248451913312699002939 13818372677869969048504409)
                ·
                  refine ⟨10363779508402476786378307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13818372677869969048504409 10363779508402476786378307)
                  ·
                    refine ⟨15545669262603715179567461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10363779508402476786378307 15545669262603715179567461)
                    ·
                      refine ⟨2914812986738196596168899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15545669262603715179567461 2914812986738196596168899)
                      ·
                        rfl

theorem cell23_5676578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_5676578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676578 prefixEnd_5676578 := by exact prefixLift 5676578
  have htrace : WordTrace (prefixWord ++ tailWord_5676578) baseStart_5676578 baseEnd_5676578 := by
    simpa [prefixWord, tailWord_5676578, baseEnd_5676578] using wordTrace_append hprefix tailTrace_5676578
  have hstable : (prefixWord ++ tailWord_5676578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676578).length < 2 ^ (prefixWord ++ tailWord_5676578).sum := by decide
  have hdescent : baseEnd_5676578 < baseStart_5676578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676601 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 8]
def baseStart_5676601 : Nat := 118140960795 + 5676601 * 2 ^ 59
def prefixEnd_5676601 : Nat := 4983230072969 + 3 ^ 40 * 5676601 * 2
def baseEnd_5676601 : Nat := 323869421865916667353477

theorem tailTrace_5676601 : CollatzResearch.WordTrace tailWord_5676601 prefixEnd_5676601 323869421865916667353477 := by
  unfold tailWord_5676601
  simp only [CollatzResearch.WordTrace]
  refine ⟨207042647707651538111165657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138028431805101025407443771 207042647707651538111165657)
  ·
    refine ⟨155281985780738653583374243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207042647707651538111165657 155281985780738653583374243)
    ·
      refine ⟨232922978671107980375061365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155281985780738653583374243 232922978671107980375061365)
      ·
        refine ⟨21836529250416373160162003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 232922978671107980375061365 21836529250416373160162003)
        ·
          refine ⟨32754793875624559740243005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21836529250416373160162003 32754793875624559740243005)
          ·
            refine ⟨12283047703359209902591127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32754793875624559740243005 12283047703359209902591127)
            ·
              refine ⟨18424571555038814853886691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12283047703359209902591127 18424571555038814853886691)
              ·
                refine ⟨27636857332558222280830037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18424571555038814853886691 27636857332558222280830037)
                ·
                  refine ⟨323869421865916667353477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27636857332558222280830037 323869421865916667353477)
                  ·
                    rfl

theorem cell23_5676601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 8].length) (baseStart_5676601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676601 prefixEnd_5676601 := by exact prefixLift 5676601
  have htrace : WordTrace (prefixWord ++ tailWord_5676601) baseStart_5676601 baseEnd_5676601 := by
    simpa [prefixWord, tailWord_5676601, baseEnd_5676601] using wordTrace_append hprefix tailTrace_5676601
  have hstable : (prefixWord ++ tailWord_5676601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676601).length < 2 ^ (prefixWord ++ tailWord_5676601).sum := by decide
  have hdescent : baseEnd_5676601 < baseStart_5676601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676605 : List Nat := [1, 4, 1, 3, 3, 1, 2, 1, 3, 4]
def baseStart_5676605 : Nat := 118140960795 + 5676605 * 2 ^ 59
def prefixEnd_5676605 : Nat := 4983230072969 + 3 ^ 40 * 5676605 * 2
def baseEnd_5676605 : Nat := 971608950238622663510425

theorem tailTrace_5676605 : CollatzResearch.WordTrace tailWord_5676605 prefixEnd_5676605 971608950238622663510425 := by
  unfold tailWord_5676605
  simp only [CollatzResearch.WordTrace]
  refine ⟨207042793599637046794311269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138028529066424697862874179 207042793599637046794311269)
  ·
    refine ⟨38820523799931946273933363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207042793599637046794311269 38820523799931946273933363)
    ·
      refine ⟨58230785699897919410900045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38820523799931946273933363 58230785699897919410900045)
      ·
        refine ⟨21836544637461719779087517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58230785699897919410900045 21836544637461719779087517)
        ·
          refine ⟨8188704239048144917157819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21836544637461719779087517 8188704239048144917157819)
          ·
            refine ⟨12283056358572217375736729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8188704239048144917157819 12283056358572217375736729)
            ·
              refine ⟨9212292268929163031802547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12283056358572217375736729 9212292268929163031802547)
              ·
                refine ⟨13818438403393744547703821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9212292268929163031802547 13818438403393744547703821)
                ·
                  refine ⟨5181914401272654205388933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13818438403393744547703821 5181914401272654205388933)
                  ·
                    refine ⟨971608950238622663510425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5181914401272654205388933 971608950238622663510425)
                    ·
                      rfl

theorem cell23_5676605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_5676605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676605 prefixEnd_5676605 := by exact prefixLift 5676605
  have htrace : WordTrace (prefixWord ++ tailWord_5676605) baseStart_5676605 baseEnd_5676605 := by
    simpa [prefixWord, tailWord_5676605, baseEnd_5676605] using wordTrace_append hprefix tailTrace_5676605
  have hstable : (prefixWord ++ tailWord_5676605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676605).length < 2 ^ (prefixWord ++ tailWord_5676605).sum := by decide
  have hdescent : baseEnd_5676605 < baseStart_5676605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676618 : List Nat := [3, 1, 2, 1, 1, 3, 5, 1, 6]
def baseStart_5676618 : Nat := 118140960795 + 5676618 * 2 ^ 59
def prefixEnd_5676618 : Nat := 4983230072969 + 3 ^ 40 * 5676618 * 2
def baseEnd_5676618 : Nat := 323870391773819604407635

theorem tailTrace_5676618 : CollatzResearch.WordTrace tailWord_5676618 prefixEnd_5676618 323870391773819604407635 := by
  unfold tailWord_5676618
  simp only [CollatzResearch.WordTrace]
  refine ⟨51760816937147487503633627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138028845165726633343023005 51760816937147487503633627)
  ·
    refine ⟨77641225405721231255450441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51760816937147487503633627 77641225405721231255450441)
    ·
      refine ⟨58230919054290923441587831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77641225405721231255450441 58230919054290923441587831)
      ·
        refine ⟨87346378581436385162381747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58230919054290923441587831 87346378581436385162381747)
        ·
          refine ⟨131019567872154577743572621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87346378581436385162381747 131019567872154577743572621)
          ·
            refine ⟨49132337952057966653839733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131019567872154577743572621 49132337952057966653839733)
            ·
              refine ⟨4606156683005434373797475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49132337952057966653839733 4606156683005434373797475)
              ·
                refine ⟨6909235024508151560696213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4606156683005434373797475 6909235024508151560696213)
                ·
                  refine ⟨323870391773819604407635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6909235024508151560696213 323870391773819604407635)
                  ·
                    rfl

theorem cell23_5676618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 6].length) (baseStart_5676618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676618 prefixEnd_5676618 := by exact prefixLift 5676618
  have htrace : WordTrace (prefixWord ++ tailWord_5676618) baseStart_5676618 baseEnd_5676618 := by
    simpa [prefixWord, tailWord_5676618, baseEnd_5676618] using wordTrace_append hprefix tailTrace_5676618
  have hstable : (prefixWord ++ tailWord_5676618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676618).length < 2 ^ (prefixWord ++ tailWord_5676618).sum := by decide
  have hdescent : baseEnd_5676618 < baseStart_5676618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676662 : List Nat := [5, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_5676662 : Nat := 118140960795 + 5676662 * 2 ^ 59
def prefixEnd_5676662 : Nat := 4983230072969 + 3 ^ 40 * 5676662 * 2
def baseEnd_5676662 : Nat := 2914856119113174267518513

theorem tailTrace_5676662 : CollatzResearch.WordTrace tailWord_5676662 prefixEnd_5676662 2914856119113174267518513 := by
  unfold tailWord_5676662
  simp only [CollatzResearch.WordTrace]
  refine ⟨12940304535026909095571015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138029915040287030352757493 12940304535026909095571015)
  ·
    refine ⟨19410456802540363643356523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12940304535026909095571015 19410456802540363643356523)
    ·
      refine ⟨29115685203810545465034785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19410456802540363643356523 29115685203810545465034785)
      ·
        refine ⟨21836763902857909098776089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29115685203810545465034785 21836763902857909098776089)
        ·
          refine ⟨16377572927143431824082067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21836763902857909098776089 16377572927143431824082067)
          ·
            refine ⟨24566359390715147736123101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16377572927143431824082067 24566359390715147736123101)
            ·
              refine ⟨9212384771518180401046163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24566359390715147736123101 9212384771518180401046163)
              ·
                refine ⟨13818577157277270601569245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9212384771518180401046163 13818577157277270601569245)
                ·
                  refine ⟨5181966433978976475588467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13818577157277270601569245 5181966433978976475588467)
                  ·
                    refine ⟨7772949650968464713382701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5181966433978976475588467 7772949650968464713382701)
                    ·
                      refine ⟨2914856119113174267518513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7772949650968464713382701 2914856119113174267518513)
                      ·
                        rfl

theorem cell23_5676662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_5676662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676662 prefixEnd_5676662 := by exact prefixLift 5676662
  have htrace : WordTrace (prefixWord ++ tailWord_5676662) baseStart_5676662 baseEnd_5676662 := by
    simpa [prefixWord, tailWord_5676662, baseEnd_5676662] using wordTrace_append hprefix tailTrace_5676662
  have hstable : (prefixWord ++ tailWord_5676662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676662).length < 2 ^ (prefixWord ++ tailWord_5676662).sum := by decide
  have hdescent : baseEnd_5676662 < baseStart_5676662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676681 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 1, 1, 6]
def baseStart_5676681 : Nat := 118140960795 + 5676681 * 2 ^ 59
def prefixEnd_5676681 : Nat := 4983230072969 + 3 ^ 40 * 5676681 * 2
def baseEnd_5676681 : Nat := 2914865875245609693180925

theorem tailTrace_5676681 : CollatzResearch.WordTrace tailWord_5676681 prefixEnd_5676681 2914865875245609693180925 := by
  unfold tailWord_5676681
  simp only [CollatzResearch.WordTrace]
  refine ⟨207045565547361711774077897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138030377031574474516051931 207045565547361711774077897)
  ·
    refine ⟨155284174160521283830558423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207045565547361711774077897 155284174160521283830558423)
    ·
      refine ⟨232926261240781925745837635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155284174160521283830558423 232926261240781925745837635)
      ·
        refine ⟨349389391861172888618756453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232926261240781925745837635 349389391861172888618756453)
        ·
          refine ⟨65510510973969916616016835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 349389391861172888618756453 65510510973969916616016835)
          ·
            refine ⟨98265766460954874924025253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65510510973969916616016835 98265766460954874924025253)
            ·
              refine ⟨18424831211429039048254735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98265766460954874924025253 18424831211429039048254735)
              ·
                refine ⟨27637246817143558572382103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18424831211429039048254735 27637246817143558572382103)
                ·
                  refine ⟨41455870225715337858573155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27637246817143558572382103 41455870225715337858573155)
                  ·
                    refine ⟨62183805338573006787859733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41455870225715337858573155 62183805338573006787859733)
                    ·
                      refine ⟨2914865875245609693180925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62183805338573006787859733 2914865875245609693180925)
                      ·
                        rfl

theorem cell23_5676681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_5676681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676681 prefixEnd_5676681 := by exact prefixLift 5676681
  have htrace : WordTrace (prefixWord ++ tailWord_5676681) baseStart_5676681 baseEnd_5676681 := by
    simpa [prefixWord, tailWord_5676681, baseEnd_5676681] using wordTrace_append hprefix tailTrace_5676681
  have hstable : (prefixWord ++ tailWord_5676681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676681).length < 2 ^ (prefixWord ++ tailWord_5676681).sum := by decide
  have hdescent : baseEnd_5676681 < baseStart_5676681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676705 : List Nat := [1, 2, 3, 3, 2, 3, 1, 1, 1, 1, 5]
def baseStart_5676705 : Nat := 118140960795 + 5676705 * 2 ^ 59
def prefixEnd_5676705 : Nat := 4983230072969 + 3 ^ 40 * 5676705 * 2
def baseEnd_5676705 : Nat := 2914878198781317599280815

theorem tailTrace_5676705 : CollatzResearch.WordTrace tailWord_5676705 prefixEnd_5676705 2914878198781317599280815 := by
  unfold tailWord_5676705
  simp only [CollatzResearch.WordTrace]
  refine ⟨207046440899274763872951569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138030960599516509248634379 207046440899274763872951569)
  ·
    refine ⟨155284830674456072904713677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207046440899274763872951569 155284830674456072904713677)
    ·
      refine ⟨58231811502921027339267629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155284830674456072904713677 58231811502921027339267629)
      ·
        refine ⟨21836929313595385252225361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58231811502921027339267629 21836929313595385252225361)
        ·
          refine ⟨16377696985196538939169021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21836929313595385252225361 16377696985196538939169021)
          ·
            refine ⟨6141636369448702102188383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16377696985196538939169021 6141636369448702102188383)
            ·
              refine ⟨9212454554173053153282575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6141636369448702102188383 9212454554173053153282575)
              ·
                refine ⟨13818681831259579729923863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9212454554173053153282575 13818681831259579729923863)
                ·
                  refine ⟨20728022746889369594885795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13818681831259579729923863 20728022746889369594885795)
                  ·
                    refine ⟨31092034120334054392328693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20728022746889369594885795 31092034120334054392328693)
                    ·
                      refine ⟨2914878198781317599280815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31092034120334054392328693 2914878198781317599280815)
                      ·
                        rfl

theorem cell23_5676705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_5676705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676705 prefixEnd_5676705 := by exact prefixLift 5676705
  have htrace : WordTrace (prefixWord ++ tailWord_5676705) baseStart_5676705 baseEnd_5676705 := by
    simpa [prefixWord, tailWord_5676705, baseEnd_5676705] using wordTrace_append hprefix tailTrace_5676705
  have hstable : (prefixWord ++ tailWord_5676705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676705).length < 2 ^ (prefixWord ++ tailWord_5676705).sum := by decide
  have hdescent : baseEnd_5676705 < baseStart_5676705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676725 : List Nat := [1, 3, 3, 3, 2, 2, 1, 8]
def baseStart_5676725 : Nat := 118140960795 + 5676725 * 2 ^ 59
def prefixEnd_5676725 : Nat := 4983230072969 + 3 ^ 40 * 5676725 * 2
def baseEnd_5676725 : Nat := 107958832162755834112249

theorem tailTrace_5676725 : CollatzResearch.WordTrace tailWord_5676725 prefixEnd_5676725 107958832162755834112249 := by
  unfold tailWord_5676725
  simp only [CollatzResearch.WordTrace]
  refine ⟨207047170359202307288679629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138031446906134871525786419 207047170359202307288679629)
  ·
    refine ⟨77642688884700865233254861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207047170359202307288679629 77642688884700865233254861)
    ·
      refine ⟨29116008331762824462470573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77642688884700865233254861 29116008331762824462470573)
      ·
        refine ⟨10918503124411059173426465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29116008331762824462470573 10918503124411059173426465)
        ·
          refine ⟨8188877343308294380069849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10918503124411059173426465 8188877343308294380069849)
          ·
            refine ⟨6141658007481220785052387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8188877343308294380069849 6141658007481220785052387)
            ·
              refine ⟨9212487011221831177578581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6141658007481220785052387 9212487011221831177578581)
              ·
                refine ⟨107958832162755834112249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9212487011221831177578581 107958832162755834112249)
                ·
                  rfl

theorem cell23_5676725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 8].length) (baseStart_5676725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676725 prefixEnd_5676725 := by exact prefixLift 5676725
  have htrace : WordTrace (prefixWord ++ tailWord_5676725) baseStart_5676725 baseEnd_5676725 := by
    simpa [prefixWord, tailWord_5676725, baseEnd_5676725] using wordTrace_append hprefix tailTrace_5676725
  have hstable : (prefixWord ++ tailWord_5676725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676725).length < 2 ^ (prefixWord ++ tailWord_5676725).sum := by decide
  have hdescent : baseEnd_5676725 < baseStart_5676725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676735 : List Nat := [1, 1, 2, 2, 2, 3, 1, 5, 2, 1, 3]
def baseStart_5676735 : Nat := 118140960795 + 5676735 * 2 ^ 59
def prefixEnd_5676735 : Nat := 4983230072969 + 3 ^ 40 * 5676735 * 2
def baseEnd_5676735 : Nat := 2914893603200952481905677

theorem tailTrace_5676735 : CollatzResearch.WordTrace tailWord_5676735 prefixEnd_5676735 2914893603200952481905677 := by
  unfold tailWord_5676735
  simp only [CollatzResearch.WordTrace]
  refine ⟨207047535089166078996543659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138031690059444052664362439 207047535089166078996543659)
  ·
    refine ⟨310571302633749118494815489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207047535089166078996543659 310571302633749118494815489)
    ·
      refine ⟨232928476975311838871111617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310571302633749118494815489 232928476975311838871111617)
      ·
        refine ⟨174696357731483879153333713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232928476975311838871111617 174696357731483879153333713)
        ·
          refine ⟨131022268298612909365000285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174696357731483879153333713 131022268298612909365000285)
          ·
            refine ⟨49133350611979841011875107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131022268298612909365000285 49133350611979841011875107)
            ·
              refine ⟨73700025917969761517812661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49133350611979841011875107 73700025917969761517812661)
              ·
                refine ⟨6909377429809665142294937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73700025917969761517812661 6909377429809665142294937)
                ·
                  refine ⟨5182033072357248856721203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6909377429809665142294937 5182033072357248856721203)
                  ·
                    refine ⟨7773049608535873285081805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5182033072357248856721203 7773049608535873285081805)
                    ·
                      refine ⟨2914893603200952481905677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7773049608535873285081805 2914893603200952481905677)
                      ·
                        rfl

theorem cell23_5676735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 1, 3].length) (baseStart_5676735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676735 prefixEnd_5676735 := by exact prefixLift 5676735
  have htrace : WordTrace (prefixWord ++ tailWord_5676735) baseStart_5676735 baseEnd_5676735 := by
    simpa [prefixWord, tailWord_5676735, baseEnd_5676735] using wordTrace_append hprefix tailTrace_5676735
  have hstable : (prefixWord ++ tailWord_5676735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676735).length < 2 ^ (prefixWord ++ tailWord_5676735).sum := by decide
  have hdescent : baseEnd_5676735 < baseStart_5676735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676762 : List Nat := [3, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2]
def baseStart_5676762 : Nat := 118140960795 + 5676762 * 2 ^ 59
def prefixEnd_5676762 : Nat := 4983230072969 + 3 ^ 40 * 5676762 * 2
def baseEnd_5676762 : Nat := 2914907467178623876268053

theorem tailTrace_5676762 : CollatzResearch.WordTrace tailWord_5676762 prefixEnd_5676762 2914907467178623876268053 := by
  unfold tailWord_5676762
  simp only [CollatzResearch.WordTrace]
  refine ⟨51762129965017065651944135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138032346573378841738517693 51762129965017065651944135)
  ·
    refine ⟨77643194947525598477916203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51762129965017065651944135 77643194947525598477916203)
    ·
      refine ⟨116464792421288397716874305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77643194947525598477916203 116464792421288397716874305)
      ·
        refine ⟨87348594315966298287655729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116464792421288397716874305 87348594315966298287655729)
        ·
          refine ⟨65511445736974723715741797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87348594315966298287655729 65511445736974723715741797)
          ·
            refine ⟨12283396075682760696701587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65511445736974723715741797 12283396075682760696701587)
            ·
              refine ⟨18425094113524141045052381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12283396075682760696701587 18425094113524141045052381)
              ·
                refine ⟨6909410292571552891894643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18425094113524141045052381 6909410292571552891894643)
                ·
                  refine ⟨10364115438857329337841965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6909410292571552891894643 10364115438857329337841965)
                  ·
                    refine ⟨3886543289571498501690737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10364115438857329337841965 3886543289571498501690737)
                    ·
                      refine ⟨2914907467178623876268053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3886543289571498501690737 2914907467178623876268053)
                      ·
                        rfl

theorem cell23_5676762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_5676762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676762 prefixEnd_5676762 := by exact prefixLift 5676762
  have htrace : WordTrace (prefixWord ++ tailWord_5676762) baseStart_5676762 baseEnd_5676762 := by
    simpa [prefixWord, tailWord_5676762, baseEnd_5676762] using wordTrace_append hprefix tailTrace_5676762
  have hstable : (prefixWord ++ tailWord_5676762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676762).length < 2 ^ (prefixWord ++ tailWord_5676762).sum := by decide
  have hdescent : baseEnd_5676762 < baseStart_5676762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676769 : List Nat := [1, 2, 3, 1, 5, 2, 1, 2, 2, 1, 3]
def baseStart_5676769 : Nat := 118140960795 + 5676769 * 2 ^ 59
def prefixEnd_5676769 : Nat := 4983230072969 + 3 ^ 40 * 5676769 * 2
def baseEnd_5676769 : Nat := 2914911061543205348880521

theorem tailTrace_5676769 : CollatzResearch.WordTrace tailWord_5676769 prefixEnd_5676769 2914911061543205348880521 := by
  unfold tailWord_5676769
  simp only [CollatzResearch.WordTrace]
  refine ⟨207048775171042902803281361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138032516780695268535520907 207048775171042902803281361)
  ·
    refine ⟨155286581378282177102461021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207048775171042902803281361 155286581378282177102461021)
    ·
      refine ⟨58232468016855816413422883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155286581378282177102461021 58232468016855816413422883)
      ·
        refine ⟨87348702025283724620134325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58232468016855816413422883 87348702025283724620134325)
        ·
          refine ⟨8188940814870349183137593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87348702025283724620134325 8188940814870349183137593)
          ·
            refine ⟨6141705611152761887353195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8188940814870349183137593 6141705611152761887353195)
            ·
              refine ⟨9212558416729142831029793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6141705611152761887353195 9212558416729142831029793)
              ·
                refine ⟨6909418812546857123272345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9212558416729142831029793 6909418812546857123272345)
                ·
                  refine ⟨5182064109410142842454259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6909418812546857123272345 5182064109410142842454259)
                  ·
                    refine ⟨7773096164115214263681389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5182064109410142842454259 7773096164115214263681389)
                    ·
                      refine ⟨2914911061543205348880521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7773096164115214263681389 2914911061543205348880521)
                      ·
                        rfl

theorem cell23_5676769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_5676769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676769 prefixEnd_5676769 := by exact prefixLift 5676769
  have htrace : WordTrace (prefixWord ++ tailWord_5676769) baseStart_5676769 baseEnd_5676769 := by
    simpa [prefixWord, tailWord_5676769, baseEnd_5676769] using wordTrace_append hprefix tailTrace_5676769
  have hstable : (prefixWord ++ tailWord_5676769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676769).length < 2 ^ (prefixWord ++ tailWord_5676769).sum := by decide
  have hdescent : baseEnd_5676769 < baseStart_5676769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676778 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_5676778 : Nat := 118140960795 + 5676778 * 2 ^ 59
def prefixEnd_5676778 : Nat := 4983230072969 + 3 ^ 40 * 5676778 * 2
def baseEnd_5676778 : Nat := 2914915682869095813667979

theorem tailTrace_5676778 : CollatzResearch.WordTrace tailWord_5676778 prefixEnd_5676778 2914915682869095813667979 := by
  unfold tailWord_5676778
  simp only [CollatzResearch.WordTrace]
  refine ⟨51762275857002574335089747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138032735618673531560239325 51762275857002574335089747)
  ·
    refine ⟨77643413785503861502634621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51762275857002574335089747 77643413785503861502634621)
    ·
      refine ⟨29116280169563948063487983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77643413785503861502634621 29116280169563948063487983)
      ·
        refine ⟨43674420254345922095231975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29116280169563948063487983 43674420254345922095231975)
        ·
          refine ⟨65511630381518883142847963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43674420254345922095231975 65511630381518883142847963)
          ·
            refine ⟨98267445572278324714271945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65511630381518883142847963 98267445572278324714271945)
            ·
              refine ⟨73700584179208743535703959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98267445572278324714271945 73700584179208743535703959)
              ·
                refine ⟨110550876268813115303555939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73700584179208743535703959 110550876268813115303555939)
                ·
                  refine ⟨165826314403219672955333909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110550876268813115303555939 165826314403219672955333909)
                  ·
                    refine ⟨7773108487650922169781277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 165826314403219672955333909 7773108487650922169781277)
                    ·
                      refine ⟨2914915682869095813667979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7773108487650922169781277 2914915682869095813667979)
                      ·
                        rfl

theorem cell23_5676778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_5676778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676778 prefixEnd_5676778 := by exact prefixLift 5676778
  have htrace : WordTrace (prefixWord ++ tailWord_5676778) baseStart_5676778 baseEnd_5676778 := by
    simpa [prefixWord, tailWord_5676778, baseEnd_5676778] using wordTrace_append hprefix tailTrace_5676778
  have hstable : (prefixWord ++ tailWord_5676778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676778).length < 2 ^ (prefixWord ++ tailWord_5676778).sum := by decide
  have hdescent : baseEnd_5676778 < baseStart_5676778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676832 : List Nat := [2, 1, 1, 5, 1, 1, 5, 2, 5]
def baseStart_5676832 : Nat := 118140960795 + 5676832 * 2 ^ 59
def prefixEnd_5676832 : Nat := 4983230072969 + 3 ^ 40 * 5676832 * 2
def baseEnd_5676832 : Nat := 323882601202715400265859

theorem tailTrace_5676832 : CollatzResearch.WordTrace tailWord_5676832 prefixEnd_5676832 323882601202715400265859 := by
  unfold tailWord_5676832
  simp only [CollatzResearch.WordTrace]
  refine ⟨103525536484907332281412375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138034048646543109708549833 103525536484907332281412375)
  ·
    refine ⟨155288304727360998422118563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103525536484907332281412375 155288304727360998422118563)
    ·
      refine ⟨232932457091041497633177845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155288304727360998422118563 232932457091041497633177845)
      ·
        refine ⟨21837417852285140403110423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 232932457091041497633177845 21837417852285140403110423)
        ·
          refine ⟨32756126778427710604665635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21837417852285140403110423 32756126778427710604665635)
          ·
            refine ⟨49134190167641565906998453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32756126778427710604665635 49134190167641565906998453)
            ·
              refine ⟨4606330328216396803781105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49134190167641565906998453 4606330328216396803781105)
              ·
                refine ⟨3454747746162297602835829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4606330328216396803781105 3454747746162297602835829)
                ·
                  refine ⟨323882601202715400265859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3454747746162297602835829 323882601202715400265859)
                  ·
                    rfl

theorem cell23_5676832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 5].length) (baseStart_5676832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676832 prefixEnd_5676832 := by exact prefixLift 5676832
  have htrace : WordTrace (prefixWord ++ tailWord_5676832) baseStart_5676832 baseEnd_5676832 := by
    simpa [prefixWord, tailWord_5676832, baseEnd_5676832] using wordTrace_append hprefix tailTrace_5676832
  have hstable : (prefixWord ++ tailWord_5676832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676832).length < 2 ^ (prefixWord ++ tailWord_5676832).sum := by decide
  have hdescent : baseEnd_5676832 < baseStart_5676832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676862 : List Nat := [4, 2, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_5676862 : Nat := 118140960795 + 5676862 * 2 ^ 59
def prefixEnd_5676862 : Nat := 4983230072969 + 3 ^ 40 * 5676862 * 2
def baseEnd_5676862 : Nat := 971652938414691161672531

theorem tailTrace_5676862 : CollatzResearch.WordTrace tailWord_5676862 prefixEnd_5676862 971652938414691161672531 := by
  unfold tailWord_5676862
  simp only [CollatzResearch.WordTrace]
  refine ⟨25881520894963247460802105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138034778106470653124277893 25881520894963247460802105)
  ·
    refine ⟨19411140671222435595601579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25881520894963247460802105 19411140671222435595601579)
    ·
      refine ⟨29116711006833653393402369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19411140671222435595601579 29116711006833653393402369)
      ·
        refine ⟨21837533255125240045051777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29116711006833653393402369 21837533255125240045051777)
        ·
          refine ⟨16378149941343930033788833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21837533255125240045051777 16378149941343930033788833)
          ·
            refine ⟨12283612456007947525341625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16378149941343930033788833 12283612456007947525341625)
            ·
              refine ⟨9212709342005960644006219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12283612456007947525341625 9212709342005960644006219)
              ·
                refine ⟨13819064013008940966009329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9212709342005960644006219 13819064013008940966009329)
                ·
                  refine ⟨10364298009756705724506997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13819064013008940966009329 10364298009756705724506997)
                  ·
                    refine ⟨971652938414691161672531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10364298009756705724506997 971652938414691161672531)
                    ·
                      rfl

theorem cell23_5676862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_5676862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676862 prefixEnd_5676862 := by exact prefixLift 5676862
  have htrace : WordTrace (prefixWord ++ tailWord_5676862) baseStart_5676862 baseEnd_5676862 := by
    simpa [prefixWord, tailWord_5676862, baseEnd_5676862] using wordTrace_append hprefix tailTrace_5676862
  have hstable : (prefixWord ++ tailWord_5676862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676862).length < 2 ^ (prefixWord ++ tailWord_5676862).sum := by decide
  have hdescent : baseEnd_5676862 < baseStart_5676862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676926 : List Nat := [4, 2, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_5676926 : Nat := 118140960795 + 5676926 * 2 ^ 59
def prefixEnd_5676926 : Nat := 4983230072969 + 3 ^ 40 * 5676926 * 2
def baseEnd_5676926 : Nat := 971663892668653744872433

theorem tailTrace_5676926 : CollatzResearch.WordTrace tailWord_5676926 prefixEnd_5676926 971663892668653744872433 := by
  unfold tailWord_5676926
  simp only [CollatzResearch.WordTrace]
  refine ⟨25881812678934264827093329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138036334287649412411164421 25881812678934264827093329)
  ·
    refine ⟨19411359509200698620319997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25881812678934264827093329 19411359509200698620319997)
    ·
      refine ⟨7279259815950261982619999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19411359509200698620319997 7279259815950261982619999)
      ·
        refine ⟨10918889723925392973929999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7279259815950261982619999 10918889723925392973929999)
        ·
          refine ⟨16378334585888089460894999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10918889723925392973929999 16378334585888089460894999)
          ·
            refine ⟨24567501878832134191342499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16378334585888089460894999 24567501878832134191342499)
            ·
              refine ⟨36851252818248201287013749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24567501878832134191342499 36851252818248201287013749)
              ·
                refine ⟨3454804951710768870657539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36851252818248201287013749 3454804951710768870657539)
                ·
                  refine ⟨5182207427566153305986309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3454804951710768870657539 5182207427566153305986309)
                  ·
                    refine ⟨971663892668653744872433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5182207427566153305986309 971663892668653744872433)
                    ·
                      rfl

theorem cell23_5676926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_5676926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676926 prefixEnd_5676926 := by exact prefixLift 5676926
  have htrace : WordTrace (prefixWord ++ tailWord_5676926) baseStart_5676926 baseEnd_5676926 := by
    simpa [prefixWord, tailWord_5676926, baseEnd_5676926] using wordTrace_append hprefix tailTrace_5676926
  have hstable : (prefixWord ++ tailWord_5676926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676926).length < 2 ^ (prefixWord ++ tailWord_5676926).sum := by decide
  have hdescent : baseEnd_5676926 < baseStart_5676926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676949 : List Nat := [1, 3, 2, 1, 1, 3, 1, 6, 1, 1, 3]
def baseStart_5676949 : Nat := 118140960795 + 5676949 * 2 ^ 59
def prefixEnd_5676949 : Nat := 4983230072969 + 3 ^ 40 * 5676949 * 2
def baseEnd_5676949 : Nat := 2915003488061014644629693

theorem tailTrace_5676949 : CollatzResearch.WordTrace tailWord_5676949 prefixEnd_5676949 2915003488061014644629693 := by
  unfold tailWord_5676949
  simp only [CollatzResearch.WordTrace]
  refine ⟨207055340310390793544833901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138036893540260529029889267 207055340310390793544833901)
  ·
    refine ⟨77645752616396547579312713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207055340310390793544833901 77645752616396547579312713)
    ·
      refine ⟨58234314462297410684484535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77645752616396547579312713 58234314462297410684484535)
      ·
        refine ⟨87351471693446116026726803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58234314462297410684484535 87351471693446116026726803)
        ·
          refine ⟨131027207540169174040090205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87351471693446116026726803 131027207540169174040090205)
          ·
            refine ⟨49135202827563440265033827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131027207540169174040090205 49135202827563440265033827)
            ·
              refine ⟨73702804241345160397550741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49135202827563440265033827 73702804241345160397550741)
              ·
                refine ⟨3454818948813054393635191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73702804241345160397550741 3454818948813054393635191)
                ·
                  refine ⟨5182228423219581590452787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3454818948813054393635191 5182228423219581590452787)
                  ·
                    refine ⟨7773342634829372385679181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5182228423219581590452787 7773342634829372385679181)
                    ·
                      refine ⟨2915003488061014644629693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7773342634829372385679181 2915003488061014644629693)
                      ·
                        rfl

theorem cell23_5676949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_5676949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676949 prefixEnd_5676949 := by exact prefixLift 5676949
  have htrace : WordTrace (prefixWord ++ tailWord_5676949) baseStart_5676949 baseEnd_5676949 := by
    simpa [prefixWord, tailWord_5676949, baseEnd_5676949] using wordTrace_append hprefix tailTrace_5676949
  have hstable : (prefixWord ++ tailWord_5676949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676949).length < 2 ^ (prefixWord ++ tailWord_5676949).sum := by decide
  have hdescent : baseEnd_5676949 < baseStart_5676949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676985 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 3, 2, 4]
def baseStart_5676985 : Nat := 118140960795 + 5676985 * 2 ^ 59
def prefixEnd_5676985 : Nat := 4983230072969 + 3 ^ 40 * 5676985 * 2
def baseEnd_5676985 : Nat := 2915021973364576503779527

theorem tailTrace_5676985 : CollatzResearch.WordTrace tailWord_5676985 prefixEnd_5676985 2915021973364576503779527 := by
  unfold tailWord_5676985
  simp only [CollatzResearch.WordTrace]
  refine ⟨207056653338260371693144409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138037768892173581128762939 207056653338260371693144409)
  ·
    refine ⟨155292490003695278769858307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207056653338260371693144409 155292490003695278769858307)
    ·
      refine ⟨232938735005542918154787461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155292490003695278769858307 232938735005542918154787461)
      ·
        refine ⟨43676012813539297154022649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232938735005542918154787461 43676012813539297154022649)
        ·
          refine ⟨32757009610154472865516987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43676012813539297154022649 32757009610154472865516987)
          ·
            refine ⟨49135514415231709298275481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32757009610154472865516987 49135514415231709298275481)
            ·
              refine ⟨36851635811423781973706611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49135514415231709298275481 36851635811423781973706611)
              ·
                refine ⟨55277453717135672960559917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36851635811423781973706611 55277453717135672960559917)
                ·
                  refine ⟨20729045143925877360209969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55277453717135672960559917 20729045143925877360209969)
                  ·
                    refine ⟨15546783857944408020157477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20729045143925877360209969 15546783857944408020157477)
                    ·
                      refine ⟨2915021973364576503779527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15546783857944408020157477 2915021973364576503779527)
                      ·
                        rfl

theorem cell23_5676985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_5676985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676985 prefixEnd_5676985 := by exact prefixLift 5676985
  have htrace : WordTrace (prefixWord ++ tailWord_5676985) baseStart_5676985 baseEnd_5676985 := by
    simpa [prefixWord, tailWord_5676985, baseEnd_5676985] using wordTrace_append hprefix tailTrace_5676985
  have hstable : (prefixWord ++ tailWord_5676985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676985).length < 2 ^ (prefixWord ++ tailWord_5676985).sum := by decide
  have hdescent : baseEnd_5676985 < baseStart_5676985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5676992 : List Nat := [2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 3]
def baseStart_5676992 : Nat := 118140960795 + 5676992 * 2 ^ 59
def prefixEnd_5676992 : Nat := 4983230072969 + 3 ^ 40 * 5676992 * 2
def baseEnd_5676992 : Nat := 2915025567729157976391995

theorem tailTrace_5676992 : CollatzResearch.WordTrace tailWord_5676992 prefixEnd_5676992 2915025567729157976391995 := by
  unfold tailWord_5676992
  simp only [CollatzResearch.WordTrace]
  refine ⟨103528454324617505944324615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138037939099490007925766153 103528454324617505944324615)
  ·
    refine ⟨155292681486926258916486923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103528454324617505944324615 155292681486926258916486923)
    ·
      refine ⟨232939022230389388374730385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155292681486926258916486923 232939022230389388374730385)
      ·
        refine ⟨174704266672792041281047789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232939022230389388374730385 174704266672792041281047789)
        ·
          refine ⟨65514100002297015480392921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174704266672792041281047789 65514100002297015480392921)
          ·
            refine ⟨49135575001722761610294691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65514100002297015480392921 49135575001722761610294691)
            ·
              refine ⟨73703362502584142415442037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49135575001722761610294691 73703362502584142415442037)
              ·
                refine ⟨6909690234617263351447691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73703362502584142415442037 6909690234617263351447691)
                ·
                  refine ⟨10364535351925895027171537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6909690234617263351447691 10364535351925895027171537)
                  ·
                    refine ⟨7773401513944421270378653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10364535351925895027171537 7773401513944421270378653)
                    ·
                      refine ⟨2915025567729157976391995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7773401513944421270378653 2915025567729157976391995)
                      ·
                        rfl

theorem cell23_5676992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 3].length) (baseStart_5676992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5676992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5676992 prefixEnd_5676992 := by exact prefixLift 5676992
  have htrace : WordTrace (prefixWord ++ tailWord_5676992) baseStart_5676992 baseEnd_5676992 := by
    simpa [prefixWord, tailWord_5676992, baseEnd_5676992] using wordTrace_append hprefix tailTrace_5676992
  have hstable : (prefixWord ++ tailWord_5676992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5676992).length < 2 ^ (prefixWord ++ tailWord_5676992).sum := by decide
  have hdescent : baseEnd_5676992 < baseStart_5676992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5676992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677020 : List Nat := [2, 2, 6, 1, 2, 1, 1, 2, 1, 5]
def baseStart_5677020 : Nat := 118140960795 + 5677020 * 2 ^ 59
def prefixEnd_5677020 : Nat := 4983230072969 + 3 ^ 40 * 5677020 * 2
def baseEnd_5677020 : Nat := 971679981729161288947289

theorem tailTrace_5677020 : CollatzResearch.WordTrace tailWord_5677020 prefixEnd_5677020 971679981729161288947289 := by
  unfold tailWord_5677020
  simp only [CollatzResearch.WordTrace]
  refine ⟨103528964946566786335334257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138038619928755715113779009 103528964946566786335334257)
  ·
    refine ⟨77646723709925089751500693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103528964946566786335334257 77646723709925089751500693)
    ·
      refine ⟨3639690173902738582101595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77646723709925089751500693 3639690173902738582101595)
      ·
        refine ⟨5459535260854107873152393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3639690173902738582101595 5459535260854107873152393)
        ·
          refine ⟨4094651445640580904864295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5459535260854107873152393 4094651445640580904864295)
          ·
            refine ⟨6141977168460871357296443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4094651445640580904864295 6141977168460871357296443)
            ·
              refine ⟨9212965752691307035944665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6141977168460871357296443 9212965752691307035944665)
              ·
                refine ⟨6909724314518480276958499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9212965752691307035944665 6909724314518480276958499)
                ·
                  refine ⟨10364586471777720415437749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6909724314518480276958499 10364586471777720415437749)
                  ·
                    refine ⟨971679981729161288947289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10364586471777720415437749 971679981729161288947289)
                    ·
                      rfl

theorem cell23_5677020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_5677020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677020 prefixEnd_5677020 := by exact prefixLift 5677020
  have htrace : WordTrace (prefixWord ++ tailWord_5677020) baseStart_5677020 baseEnd_5677020 := by
    simpa [prefixWord, tailWord_5677020, baseEnd_5677020] using wordTrace_append hprefix tailTrace_5677020
  have hstable : (prefixWord ++ tailWord_5677020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677020).length < 2 ^ (prefixWord ++ tailWord_5677020).sum := by decide
  have hdescent : baseEnd_5677020 < baseStart_5677020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677026 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_5677026 : Nat := 118140960795 + 5677026 * 2 ^ 59
def prefixEnd_5677026 : Nat := 4983230072969 + 3 ^ 40 * 5677026 * 2
def baseEnd_5677026 : Nat := 2915043026071410843366839

theorem tailTrace_5677026 : CollatzResearch.WordTrace tailWord_5677026 prefixEnd_5677026 2915043026071410843366839 := by
  unfold tailWord_5677026
  simp only [CollatzResearch.WordTrace]
  refine ⟨51764537182777958923846733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138038765820741223796924621 51764537182777958923846733)
  ·
    refine ⟨19411701443541734596442525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51764537182777958923846733 19411701443541734596442525)
    ·
      refine ⟨7279388041328150473665947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19411701443541734596442525 7279388041328150473665947)
      ·
        refine ⟨10919082061992225710498921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7279388041328150473665947 10919082061992225710498921)
        ·
          refine ⟨8189311546494169282874191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10919082061992225710498921 8189311546494169282874191)
          ·
            refine ⟨12283967319741253924311287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8189311546494169282874191 12283967319741253924311287)
            ·
              refine ⟨18425950979611880886466931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12283967319741253924311287 18425950979611880886466931)
              ·
                refine ⟨27638926469417821329700397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18425950979611880886466931 27638926469417821329700397)
                ·
                  refine ⟨10364597426031682998637649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27638926469417821329700397 10364597426031682998637649)
                  ·
                    refine ⟨7773448069523762248978237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10364597426031682998637649 7773448069523762248978237)
                    ·
                      refine ⟨2915043026071410843366839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7773448069523762248978237 2915043026071410843366839)
                      ·
                        rfl

theorem cell23_5677026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_5677026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677026 prefixEnd_5677026 := by exact prefixLift 5677026
  have htrace : WordTrace (prefixWord ++ tailWord_5677026) baseStart_5677026 baseEnd_5677026 := by
    simpa [prefixWord, tailWord_5677026, baseEnd_5677026] using wordTrace_append hprefix tailTrace_5677026
  have hstable : (prefixWord ++ tailWord_5677026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677026).length < 2 ^ (prefixWord ++ tailWord_5677026).sum := by decide
  have hdescent : baseEnd_5677026 < baseStart_5677026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677075 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 4]
def baseStart_5677075 : Nat := 118140960795 + 5677075 * 2 ^ 59
def prefixEnd_5677075 : Nat := 4983230072969 + 3 ^ 40 * 5677075 * 2
def baseEnd_5677075 : Nat := 2915068186623481151654113

theorem tailTrace_5677075 : CollatzResearch.WordTrace tailWord_5677075 prefixEnd_5677075 2915068186623481151654113 := by
  unfold tailWord_5677075
  simp only [CollatzResearch.WordTrace]
  refine ⟨207059935907934317063920679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138039957271956211375947119 207059935907934317063920679)
  ·
    refine ⟨310589903861901475595881019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207059935907934317063920679 310589903861901475595881019)
    ·
      refine ⟨465884855792852213393821529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310589903861901475595881019 465884855792852213393821529)
      ·
        refine ⟨349413641844639160045366147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 465884855792852213393821529 349413641844639160045366147)
        ·
          refine ⟨524120462766958740068049221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349413641844639160045366147 524120462766958740068049221)
          ·
            refine ⟨98272586768804763762759229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 524120462766958740068049221 98272586768804763762759229)
            ·
              refine ⟨36852220038301786411034711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98272586768804763762759229 36852220038301786411034711)
              ·
                refine ⟨55278330057452679616552067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36852220038301786411034711 55278330057452679616552067)
                ·
                  refine ⟨82917495086179019424828101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55278330057452679616552067 82917495086179019424828101)
                  ·
                    refine ⟨15547030328658566142155269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82917495086179019424828101 15547030328658566142155269)
                    ·
                      refine ⟨2915068186623481151654113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15547030328658566142155269 2915068186623481151654113)
                      ·
                        rfl

theorem cell23_5677075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_5677075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677075 prefixEnd_5677075 := by exact prefixLift 5677075
  have htrace : WordTrace (prefixWord ++ tailWord_5677075) baseStart_5677075 baseEnd_5677075 := by
    simpa [prefixWord, tailWord_5677075, baseEnd_5677075] using wordTrace_append hprefix tailTrace_5677075
  have hstable : (prefixWord ++ tailWord_5677075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677075).length < 2 ^ (prefixWord ++ tailWord_5677075).sum := by decide
  have hdescent : baseEnd_5677075 < baseStart_5677075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677125 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 7]
def baseStart_5677125 : Nat := 118140960795 + 5677125 * 2 ^ 59
def prefixEnd_5677125 : Nat := 4983230072969 + 3 ^ 40 * 5677125 * 2
def baseEnd_5677125 : Nat := 2915093860656205956028883

theorem tailTrace_5677125 : CollatzResearch.WordTrace tailWord_5677125 prefixEnd_5677125 2915093860656205956028883 := by
  unfold tailWord_5677125
  simp only [CollatzResearch.WordTrace]
  refine ⟨207061759557753175603240829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138041173038502117068827219 207061759557753175603240829)
  ·
    refine ⟨77648159834157440851215311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207061759557753175603240829 77648159834157440851215311)
    ·
      refine ⟨116472239751236161276822967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77648159834157440851215311 116472239751236161276822967)
      ·
        refine ⟨174708359626854241915234451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116472239751236161276822967 174708359626854241915234451)
        ·
          refine ⟨262062539440281362872851677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174708359626854241915234451 262062539440281362872851677)
          ·
            refine ⟨98273452290105511077319379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 262062539440281362872851677 98273452290105511077319379)
            ·
              refine ⟨147410178435158266615979069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98273452290105511077319379 147410178435158266615979069)
              ·
                refine ⟨55278816913184349980992151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147410178435158266615979069 55278816913184349980992151)
                ·
                  refine ⟨82918225369776524971488227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55278816913184349980992151 82918225369776524971488227)
                  ·
                    refine ⟨124377338054664787457232341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82918225369776524971488227 124377338054664787457232341)
                    ·
                      refine ⟨2915093860656205956028883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124377338054664787457232341 2915093860656205956028883)
                      ·
                        rfl

theorem cell23_5677125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_5677125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677125 prefixEnd_5677125 := by exact prefixLift 5677125
  have htrace : WordTrace (prefixWord ++ tailWord_5677125) baseStart_5677125 baseEnd_5677125 := by
    simpa [prefixWord, tailWord_5677125, baseEnd_5677125] using wordTrace_append hprefix tailTrace_5677125
  have hstable : (prefixWord ++ tailWord_5677125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677125).length < 2 ^ (prefixWord ++ tailWord_5677125).sum := by decide
  have hdescent : baseEnd_5677125 < baseStart_5677125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677145 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 2, 8]
def baseStart_5677145 : Nat := 118140960795 + 5677145 * 2 ^ 59
def prefixEnd_5677145 : Nat := 4983230072969 + 3 ^ 40 * 5677145 * 2
def baseEnd_5677145 : Nat := 971701376756431959259597

theorem tailTrace_5677145 : CollatzResearch.WordTrace tailWord_5677145 prefixEnd_5677145 971701376756431959259597 := by
  unfold tailWord_5677145
  simp only [CollatzResearch.WordTrace]
  refine ⟨207062489017680719018968889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138041659345120479345979259 207062489017680719018968889)
  ·
    refine ⟨155296866763260539264226667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207062489017680719018968889 155296866763260539264226667)
    ·
      refine ⟨232945300144890808896340001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155296866763260539264226667 232945300144890808896340001)
      ·
        refine ⟨174708975108668106672255001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232945300144890808896340001 174708975108668106672255001)
        ·
          refine ⟨131031731331501080004191251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174708975108668106672255001 131031731331501080004191251)
          ·
            refine ⟨196547596997251620006286877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131031731331501080004191251 196547596997251620006286877)
            ·
              refine ⟨73705348873969357502357579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196547596997251620006286877 73705348873969357502357579)
              ·
                refine ⟨110558023310954036253536369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73705348873969357502357579 110558023310954036253536369)
                ·
                  refine ⟨82918517483215527190152277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110558023310954036253536369 82918517483215527190152277)
                  ·
                    refine ⟨971701376756431959259597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82918517483215527190152277 971701376756431959259597)
                    ·
                      rfl

theorem cell23_5677145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 8].length) (baseStart_5677145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677145 prefixEnd_5677145 := by exact prefixLift 5677145
  have htrace : WordTrace (prefixWord ++ tailWord_5677145) baseStart_5677145 baseEnd_5677145 := by
    simpa [prefixWord, tailWord_5677145, baseEnd_5677145] using wordTrace_append hprefix tailTrace_5677145
  have hstable : (prefixWord ++ tailWord_5677145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677145).length < 2 ^ (prefixWord ++ tailWord_5677145).sum := by decide
  have hdescent : baseEnd_5677145 < baseStart_5677145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677149 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 1, 7]
def baseStart_5677149 : Nat := 118140960795 + 5677149 * 2 ^ 59
def prefixEnd_5677149 : Nat := 4983230072969 + 3 ^ 40 * 5677149 * 2
def baseEnd_5677149 : Nat := 971702061397304620709591

theorem tailTrace_5677149 : CollatzResearch.WordTrace tailWord_5677149 prefixEnd_5677149 971702061397304620709591 := by
  unfold tailWord_5677149
  simp only [CollatzResearch.WordTrace]
  refine ⟨207062634909666227702114501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138041756606444151801409667 207062634909666227702114501)
  ·
    refine ⟨38824244045562417694146469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207062634909666227702114501 38824244045562417694146469)
    ·
      refine ⟨7279545758542953317652463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38824244045562417694146469 7279545758542953317652463)
      ·
        refine ⟨10919318637814429976478695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7279545758542953317652463 10919318637814429976478695)
        ·
          refine ⟨16378977956721644964718043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10919318637814429976478695 16378977956721644964718043)
          ·
            refine ⟨24568466935082467447077065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16378977956721644964718043 24568466935082467447077065)
            ·
              refine ⟨18426350201311850585307799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24568466935082467447077065 18426350201311850585307799)
              ·
                refine ⟨27639525301967775877961699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18426350201311850585307799 27639525301967775877961699)
                ·
                  refine ⟨41459287952951663816942549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27639525301967775877961699 41459287952951663816942549)
                  ·
                    refine ⟨971702061397304620709591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41459287952951663816942549 971702061397304620709591)
                    ·
                      rfl

theorem cell23_5677149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_5677149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677149 prefixEnd_5677149 := by exact prefixLift 5677149
  have htrace : WordTrace (prefixWord ++ tailWord_5677149) baseStart_5677149 baseEnd_5677149 := by
    simpa [prefixWord, tailWord_5677149, baseEnd_5677149] using wordTrace_append hprefix tailTrace_5677149
  have hstable : (prefixWord ++ tailWord_5677149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677149).length < 2 ^ (prefixWord ++ tailWord_5677149).sum := by decide
  have hdescent : baseEnd_5677149 < baseStart_5677149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677152 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 4]
def baseStart_5677152 : Nat := 118140960795 + 5677152 * 2 ^ 59
def prefixEnd_5677152 : Nat := 4983230072969 + 3 ^ 40 * 5677152 * 2
def baseEnd_5677152 : Nat := 2915107724633877350391259

theorem tailTrace_5677152 : CollatzResearch.WordTrace tailWord_5677152 prefixEnd_5677152 2915107724633877350391259 := by
  unfold tailWord_5677152
  simp only [CollatzResearch.WordTrace]
  refine ⟨103531372164327679607236855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138041829552436906142982473 103531372164327679607236855)
  ·
    refine ⟨155297058246491519410855283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103531372164327679607236855 155297058246491519410855283)
    ·
      refine ⟨232945587369737279116282925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155297058246491519410855283 232945587369737279116282925)
      ·
        refine ⟨87354595263651479668606097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232945587369737279116282925 87354595263651479668606097)
        ·
          refine ⟨65515946447738609751454573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87354595263651479668606097 65515946447738609751454573)
          ·
            refine ⟨24568479917901978656795465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65515946447738609751454573 24568479917901978656795465)
            ·
              refine ⟨18426359938426483992596599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24568479917901978656795465 18426359938426483992596599)
              ·
                refine ⟨27639539907639725988894899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18426359938426483992596599 27639539907639725988894899)
                ·
                  refine ⟨41459309861459588983342349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27639539907639725988894899 41459309861459588983342349)
                  ·
                    refine ⟨15547241198047345868753381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41459309861459588983342349 15547241198047345868753381)
                    ·
                      refine ⟨2915107724633877350391259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15547241198047345868753381 2915107724633877350391259)
                      ·
                        rfl

theorem cell23_5677152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_5677152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677152 prefixEnd_5677152 := by exact prefixLift 5677152
  have htrace : WordTrace (prefixWord ++ tailWord_5677152) baseStart_5677152 baseEnd_5677152 := by
    simpa [prefixWord, tailWord_5677152, baseEnd_5677152] using wordTrace_append hprefix tailTrace_5677152
  have hstable : (prefixWord ++ tailWord_5677152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677152).length < 2 ^ (prefixWord ++ tailWord_5677152).sum := by decide
  have hdescent : baseEnd_5677152 < baseStart_5677152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677259 : List Nat := [1, 1, 1, 1, 3, 2, 4, 4, 1, 1, 4]
def baseStart_5677259 : Nat := 118140960795 + 5677259 * 2 ^ 59
def prefixEnd_5677259 : Nat := 4983230072969 + 3 ^ 40 * 5677259 * 2
def baseEnd_5677259 : Nat := 2915162667063908431753267

theorem tailTrace_5677259 : CollatzResearch.WordTrace tailWord_5677259 prefixEnd_5677259 2915162667063908431753267 := by
  unfold tailWord_5677259
  simp only [CollatzResearch.WordTrace]
  refine ⟨207066646939267716488618831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138044431292845144325745887 207066646939267716488618831)
  ·
    refine ⟨310599970408901574732928247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207066646939267716488618831 310599970408901574732928247)
    ·
      refine ⟨465899955613352362099392371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310599970408901574732928247 465899955613352362099392371)
      ·
        refine ⟨698849933420028543149088557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465899955613352362099392371 698849933420028543149088557)
        ·
          refine ⟨262068725032510703680908209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 698849933420028543149088557 262068725032510703680908209)
          ·
            refine ⟨196551543774383027760681157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262068725032510703680908209 196551543774383027760681157)
            ·
              refine ⟨36853414457696817705127717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196551543774383027760681157 36853414457696817705127717)
              ·
                refine ⟨6910015210818153319711447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36853414457696817705127717 6910015210818153319711447)
                ·
                  refine ⟨10365022816227229979567171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6910015210818153319711447 10365022816227229979567171)
                  ·
                    refine ⟨15547534224340844969350757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10365022816227229979567171 15547534224340844969350757)
                    ·
                      refine ⟨2915162667063908431753267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15547534224340844969350757 2915162667063908431753267)
                      ·
                        rfl

theorem cell23_5677259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 1, 4].length) (baseStart_5677259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677259 prefixEnd_5677259 := by exact prefixLift 5677259
  have htrace : WordTrace (prefixWord ++ tailWord_5677259) baseStart_5677259 baseEnd_5677259 := by
    simpa [prefixWord, tailWord_5677259, baseEnd_5677259] using wordTrace_append hprefix tailTrace_5677259
  have hstable : (prefixWord ++ tailWord_5677259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677259).length < 2 ^ (prefixWord ++ tailWord_5677259).sum := by decide
  have hdescent : baseEnd_5677259 < baseStart_5677259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677306 : List Nat := [3, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4]
def baseStart_5677306 : Nat := 118140960795 + 5677306 * 2 ^ 59
def prefixEnd_5677306 : Nat := 4983230072969 + 3 ^ 40 * 5677306 * 2
def baseEnd_5677306 : Nat := 2915186800654669747865551

theorem tailTrace_5677306 : CollatzResearch.WordTrace tailWord_5677306 prefixEnd_5677306 2915186800654669747865551 := by
  unfold tailWord_5677306
  simp only [CollatzResearch.WordTrace]
  refine ⟨51767090292524360878894943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138045574113398295677053181 51767090292524360878894943)
  ·
    refine ⟨77650635438786541318342415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51767090292524360878894943 77650635438786541318342415)
    ·
      refine ⟨116475953158179811977513623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77650635438786541318342415 116475953158179811977513623)
      ·
        refine ⟨174713929737269717966270435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116475953158179811977513623 174713929737269717966270435)
        ·
          refine ⟨262070894605904576949405653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174713929737269717966270435 262070894605904576949405653)
          ·
            refine ⟨6142286592325888522251695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 262070894605904576949405653 6142286592325888522251695)
            ·
              refine ⟨9213429888488832783377543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6142286592325888522251695 9213429888488832783377543)
              ·
                refine ⟨13820144832733249175066315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9213429888488832783377543 13820144832733249175066315)
                ·
                  refine ⟨20730217249099873762599473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13820144832733249175066315 20730217249099873762599473)
                  ·
                    refine ⟨15547662936824905321949605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20730217249099873762599473 15547662936824905321949605)
                    ·
                      refine ⟨2915186800654669747865551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15547662936824905321949605 2915186800654669747865551)
                      ·
                        rfl

theorem cell23_5677306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4].length) (baseStart_5677306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677306 prefixEnd_5677306 := by exact prefixLift 5677306
  have htrace : WordTrace (prefixWord ++ tailWord_5677306) baseStart_5677306 baseEnd_5677306 := by
    simpa [prefixWord, tailWord_5677306, baseEnd_5677306] using wordTrace_append hprefix tailTrace_5677306
  have hstable : (prefixWord ++ tailWord_5677306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677306).length < 2 ^ (prefixWord ++ tailWord_5677306).sum := by decide
  have hdescent : baseEnd_5677306 < baseStart_5677306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677312 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 2, 7]
def baseStart_5677312 : Nat := 118140960795 + 5677312 * 2 ^ 59
def prefixEnd_5677312 : Nat := 4983230072969 + 3 ^ 40 * 5677312 * 2
def baseEnd_5677312 : Nat := 971729960512865574796841

theorem tailTrace_5677312 : CollatzResearch.WordTrace tailWord_5677312 prefixEnd_5677312 971729960512865574796841 := by
  unfold tailWord_5677312
  simp only [CollatzResearch.WordTrace]
  refine ⟨103534290004037853270149095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138045720005383804360198793 103534290004037853270149095)
  ·
    refine ⟨155301435006056779905223643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103534290004037853270149095 155301435006056779905223643)
    ·
      refine ⟨232952152509085169857835465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155301435006056779905223643 232952152509085169857835465)
      ·
        refine ⟨174714114381813877393376599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232952152509085169857835465 174714114381813877393376599)
        ·
          refine ⟨262071171572720816090064899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174714114381813877393376599 262071171572720816090064899)
          ·
            refine ⟨393106757359081224135097349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262071171572720816090064899 393106757359081224135097349)
            ·
              refine ⟨73707517004827729525330753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 393106757359081224135097349 73707517004827729525330753)
              ·
                refine ⟨55280637753620797143998065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73707517004827729525330753 55280637753620797143998065)
                ·
                  refine ⟨41460478315215597857998549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55280637753620797143998065 41460478315215597857998549)
                  ·
                    refine ⟨971729960512865574796841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41460478315215597857998549 971729960512865574796841)
                    ·
                      rfl

theorem cell23_5677312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 7].length) (baseStart_5677312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677312 prefixEnd_5677312 := by exact prefixLift 5677312
  have htrace : WordTrace (prefixWord ++ tailWord_5677312) baseStart_5677312 baseEnd_5677312 := by
    simpa [prefixWord, tailWord_5677312, baseEnd_5677312] using wordTrace_append hprefix tailTrace_5677312
  have hstable : (prefixWord ++ tailWord_5677312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677312).length < 2 ^ (prefixWord ++ tailWord_5677312).sum := by decide
  have hdescent : baseEnd_5677312 < baseStart_5677312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677326 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3]
def baseStart_5677326 : Nat := 118140960795 + 5677326 * 2 ^ 59
def prefixEnd_5677326 : Nat := 4983230072969 + 3 ^ 40 * 5677326 * 2
def baseEnd_5677326 : Nat := 2915197070267759669615459

theorem tailTrace_5677326 : CollatzResearch.WordTrace tailWord_5677326 prefixEnd_5677326 2915197070267759669615459 := by
  unfold tailWord_5677326
  simp only [CollatzResearch.WordTrace]
  refine ⟨25883636328753123366413479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138046060420016657954205221 25883636328753123366413479)
  ·
    refine ⟨38825454493129685049620219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25883636328753123366413479 38825454493129685049620219)
    ·
      refine ⟨58238181739694527574430329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38825454493129685049620219 58238181739694527574430329)
      ·
        refine ⟨43678636304770895680822747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58238181739694527574430329 43678636304770895680822747)
        ·
          refine ⟨65517954457156343521234121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43678636304770895680822747 65517954457156343521234121)
          ·
            refine ⟨49138465842867257640925591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65517954457156343521234121 49138465842867257640925591)
            ·
              refine ⟨73707698764300886461388387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49138465842867257640925591 73707698764300886461388387)
              ·
                refine ⟨110561548146451329692082581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73707698764300886461388387 110561548146451329692082581)
                ·
                  refine ⟨5182572569364906079316371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110561548146451329692082581 5182572569364906079316371)
                  ·
                    refine ⟨7773858854047359118974557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5182572569364906079316371 7773858854047359118974557)
                    ·
                      refine ⟨2915197070267759669615459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7773858854047359118974557 2915197070267759669615459)
                      ·
                        rfl

theorem cell23_5677326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_5677326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677326 prefixEnd_5677326 := by exact prefixLift 5677326
  have htrace : WordTrace (prefixWord ++ tailWord_5677326) baseStart_5677326 baseEnd_5677326 := by
    simpa [prefixWord, tailWord_5677326, baseEnd_5677326] using wordTrace_append hprefix tailTrace_5677326
  have hstable : (prefixWord ++ tailWord_5677326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677326).length < 2 ^ (prefixWord ++ tailWord_5677326).sum := by decide
  have hdescent : baseEnd_5677326 < baseStart_5677326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677370 : List Nat := [3, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2]
def baseStart_5677370 : Nat := 118140960795 + 5677370 * 2 ^ 59
def prefixEnd_5677370 : Nat := 4983230072969 + 3 ^ 40 * 5677370 * 2
def baseEnd_5677370 : Nat := 2915219663416557497465257

theorem tailTrace_5677370 : CollatzResearch.WordTrace tailWord_5677370 prefixEnd_5677370 2915219663416557497465257 := by
  unfold tailWord_5677370
  simp only [CollatzResearch.WordTrace]
  refine ⟨51767673860466395611477391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138047130294577054963939709 51767673860466395611477391)
  ·
    refine ⟨77651510790699593417216087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51767673860466395611477391 77651510790699593417216087)
    ·
      refine ⟨116477266186049390125824131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77651510790699593417216087 116477266186049390125824131)
      ·
        refine ⟨174715899279074085188736197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116477266186049390125824131 174715899279074085188736197)
        ·
          refine ⟨32759231114826390972888037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174715899279074085188736197 32759231114826390972888037)
          ·
            refine ⟨6142355834029948307416507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32759231114826390972888037 6142355834029948307416507)
            ·
              refine ⟨9213533751044922461124761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6142355834029948307416507 9213533751044922461124761)
              ·
                refine ⟨6910150313283691845843571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9213533751044922461124761 6910150313283691845843571)
                ·
                  refine ⟨10365225469925537768765357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6910150313283691845843571 10365225469925537768765357)
                  ·
                    refine ⟨3886959551222076663287009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10365225469925537768765357 3886959551222076663287009)
                    ·
                      refine ⟨2915219663416557497465257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3886959551222076663287009 2915219663416557497465257)
                      ·
                        rfl

theorem cell23_5677370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2].length) (baseStart_5677370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677370 prefixEnd_5677370 := by exact prefixLift 5677370
  have htrace : WordTrace (prefixWord ++ tailWord_5677370) baseStart_5677370 baseEnd_5677370 := by
    simpa [prefixWord, tailWord_5677370, baseEnd_5677370] using wordTrace_append hprefix tailTrace_5677370
  have hstable : (prefixWord ++ tailWord_5677370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677370).length < 2 ^ (prefixWord ++ tailWord_5677370).sum := by decide
  have hdescent : baseEnd_5677370 < baseStart_5677370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677416 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_5677416 : Nat := 118140960795 + 5677416 * 2 ^ 59
def prefixEnd_5677416 : Nat := 4983230072969 + 3 ^ 40 * 5677416 * 2
def baseEnd_5677416 : Nat := 2915243283526664317490045

theorem tailTrace_5677416 : CollatzResearch.WordTrace tailWord_5677416 prefixEnd_5677416 2915243283526664317490045 := by
  unfold tailWord_5677416
  simp only [CollatzResearch.WordTrace]
  refine ⟨103536186599849466151042051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138048248799799288201389401 103536186599849466151042051)
  ·
    refine ⟨155304279899774199226563077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103536186599849466151042051 155304279899774199226563077)
    ·
      refine ⟨29119552481207662354980577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155304279899774199226563077 29119552481207662354980577)
      ·
        refine ⟨21839664360905746766235433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29119552481207662354980577 21839664360905746766235433)
        ·
          refine ⟨16379748270679310074676575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21839664360905746766235433 16379748270679310074676575)
          ·
            refine ⟨24569622406018965112014863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16379748270679310074676575 24569622406018965112014863)
            ·
              refine ⟨36854433609028447668022295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24569622406018965112014863 36854433609028447668022295)
              ·
                refine ⟨55281650413542671502033443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36854433609028447668022295 55281650413542671502033443)
                ·
                  refine ⟨82922475620314007253050165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55281650413542671502033443 82922475620314007253050165)
                  ·
                    refine ⟨7773982089404438179973453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82922475620314007253050165 7773982089404438179973453)
                    ·
                      refine ⟨2915243283526664317490045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7773982089404438179973453 2915243283526664317490045)
                      ·
                        rfl

theorem cell23_5677416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_5677416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677416 prefixEnd_5677416 := by exact prefixLift 5677416
  have htrace : WordTrace (prefixWord ++ tailWord_5677416) baseStart_5677416 baseEnd_5677416 := by
    simpa [prefixWord, tailWord_5677416, baseEnd_5677416] using wordTrace_append hprefix tailTrace_5677416
  have hstable : (prefixWord ++ tailWord_5677416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677416).length < 2 ^ (prefixWord ++ tailWord_5677416).sum := by decide
  have hdescent : baseEnd_5677416 < baseStart_5677416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677439 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 4]
def baseStart_5677439 : Nat := 118140960795 + 5677439 * 2 ^ 59
def prefixEnd_5677439 : Nat := 4983230072969 + 3 ^ 40 * 5677439 * 2
def baseEnd_5677439 : Nat := 2915255093581717727502439

theorem tailTrace_5677439 : CollatzResearch.WordTrace tailWord_5677439 prefixEnd_5677439 2915255093581717727502439 := by
  unfold tailWord_5677439
  simp only [CollatzResearch.WordTrace]
  refine ⟨207073212078615607230171371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138048808052410404820114247 207073212078615607230171371)
  ·
    refine ⟨310609818117923410845257057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207073212078615607230171371 310609818117923410845257057)
    ·
      refine ⟨232957363588442558133942793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310609818117923410845257057 232957363588442558133942793)
      ·
        refine ⟨174718022691331918600457095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232957363588442558133942793 174718022691331918600457095)
        ·
          refine ⟨262077034036997877900685643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174718022691331918600457095 262077034036997877900685643)
          ·
            refine ⟨393115551055496816851028465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262077034036997877900685643 393115551055496816851028465)
            ·
              refine ⟨294836663291622612638271349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393115551055496816851028465 294836663291622612638271349)
              ·
                refine ⟨27640937183589619934837939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 294836663291622612638271349 27640937183589619934837939)
                ·
                  refine ⟨41461405775384429902256909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27640937183589619934837939 41461405775384429902256909)
                  ·
                    refine ⟨15548027165769161213346341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41461405775384429902256909 15548027165769161213346341)
                    ·
                      refine ⟨2915255093581717727502439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15548027165769161213346341 2915255093581717727502439)
                      ·
                        rfl

theorem cell23_5677439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_5677439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677439 prefixEnd_5677439 := by exact prefixLift 5677439
  have htrace : WordTrace (prefixWord ++ tailWord_5677439) baseStart_5677439 baseEnd_5677439 := by
    simpa [prefixWord, tailWord_5677439, baseEnd_5677439] using wordTrace_append hprefix tailTrace_5677439
  have hstable : (prefixWord ++ tailWord_5677439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677439).length < 2 ^ (prefixWord ++ tailWord_5677439).sum := by decide
  have hdescent : baseEnd_5677439 < baseStart_5677439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677476 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 1, 4, 3]
def baseStart_5677476 : Nat := 118140960795 + 5677476 * 2 ^ 59
def prefixEnd_5677476 : Nat := 4983230072969 + 3 ^ 40 * 5677476 * 2
def baseEnd_5677476 : Nat := 2915274092365934082739769

theorem tailTrace_5677476 : CollatzResearch.WordTrace tailWord_5677476 prefixEnd_5677476 2915274092365934082739769 := by
  unfold tailWord_5677476
  simp only [CollatzResearch.WordTrace]
  refine ⟨103537280789740781274634141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138049707719654375032845521 103537280789740781274634141)
  ·
    refine ⟨38826480296152792977987803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103537280789740781274634141 38826480296152792977987803)
    ·
      refine ⟨58239720444229189466981705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38826480296152792977987803 58239720444229189466981705)
      ·
        refine ⟨43679790333171892100236279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58239720444229189466981705 43679790333171892100236279)
        ·
          refine ⟨65519685499757838150354419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43679790333171892100236279 65519685499757838150354419)
          ·
            refine ⟨98279528249636757225531629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65519685499757838150354419 98279528249636757225531629)
            ·
              refine ⟨36854823093613783959574361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98279528249636757225531629 36854823093613783959574361)
              ·
                refine ⟨27641117320210337969680771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36854823093613783959574361 27641117320210337969680771)
                ·
                  refine ⟨41461675980315506954521157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27641117320210337969680771 41461675980315506954521157)
                  ·
                    refine ⟨7774064246309157553972717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41461675980315506954521157 7774064246309157553972717)
                    ·
                      refine ⟨2915274092365934082739769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7774064246309157553972717 2915274092365934082739769)
                      ·
                        rfl

theorem cell23_5677476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_5677476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677476 prefixEnd_5677476 := by exact prefixLift 5677476
  have htrace : WordTrace (prefixWord ++ tailWord_5677476) baseStart_5677476 baseEnd_5677476 := by
    simpa [prefixWord, tailWord_5677476, baseEnd_5677476] using wordTrace_append hprefix tailTrace_5677476
  have hstable : (prefixWord ++ tailWord_5677476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677476).length < 2 ^ (prefixWord ++ tailWord_5677476).sum := by decide
  have hdescent : baseEnd_5677476 < baseStart_5677476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677519 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 7]
def baseStart_5677519 : Nat := 118140960795 + 5677519 * 2 ^ 59
def prefixEnd_5677519 : Nat := 4983230072969 + 3 ^ 40 * 5677519 * 2
def baseEnd_5677519 : Nat := 2915296172034077414502071

theorem tailTrace_5677519 : CollatzResearch.WordTrace tailWord_5677519 prefixEnd_5677519 2915296172034077414502071 := by
  unfold tailWord_5677519
  simp only [CollatzResearch.WordTrace]
  refine ⟨207076129918325780893083611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138050753278883853928722407 207076129918325780893083611)
  ·
    refine ⟨310614194877488671339625417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207076129918325780893083611 310614194877488671339625417)
    ·
      refine ⟨232960646158116503504719063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310614194877488671339625417 232960646158116503504719063)
      ·
        refine ⟨349440969237174755257078595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232960646158116503504719063 349440969237174755257078595)
        ·
          refine ⟨524161453855762132885617893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349440969237174755257078595 524161453855762132885617893)
          ·
            refine ⟨98280272597955399916053355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 524161453855762132885617893 98280272597955399916053355)
            ·
              refine ⟨147420408896933099874080033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98280272597955399916053355 147420408896933099874080033)
              ·
                refine ⟨110565306672699824905560025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147420408896933099874080033 110565306672699824905560025)
                ·
                  refine ⟨82923980004524868679170019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110565306672699824905560025 82923980004524868679170019)
                  ·
                    refine ⟨124385970006787303018755029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82923980004524868679170019 124385970006787303018755029)
                    ·
                      refine ⟨2915296172034077414502071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124385970006787303018755029 2915296172034077414502071)
                      ·
                        rfl

theorem cell23_5677519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_5677519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677519 prefixEnd_5677519 := by exact prefixLift 5677519
  have htrace : WordTrace (prefixWord ++ tailWord_5677519) baseStart_5677519 baseEnd_5677519 := by
    simpa [prefixWord, tailWord_5677519, baseEnd_5677519] using wordTrace_append hprefix tailTrace_5677519
  have hstable : (prefixWord ++ tailWord_5677519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677519).length < 2 ^ (prefixWord ++ tailWord_5677519).sum := by decide
  have hdescent : baseEnd_5677519 < baseStart_5677519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677550 : List Nat := [4, 1, 2, 1, 2, 2, 1, 3, 2, 3, 2]
def baseStart_5677550 : Nat := 118140960795 + 5677550 * 2 ^ 59
def prefixEnd_5677550 : Nat := 4983230072969 + 3 ^ 40 * 5677550 * 2
def baseEnd_5677550 : Nat := 2915312089934366793214429

theorem tailTrace_5677550 : CollatzResearch.WordTrace tailWord_5677550 prefixEnd_5677550 2915312089934366793214429 := by
  unfold tailWord_5677550
  simp only [CollatzResearch.WordTrace]
  refine ⟨25884657572651684148432763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138051507054142315458308069 25884657572651684148432763)
  ·
    refine ⟨38826986358977526222649145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25884657572651684148432763 38826986358977526222649145)
    ·
      refine ⟨29120239769233144666986859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38826986358977526222649145 29120239769233144666986859)
      ·
        refine ⟨43680359653849717000480289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29120239769233144666986859 43680359653849717000480289)
        ·
          refine ⟨32760269740387287750360217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43680359653849717000480289 32760269740387287750360217)
          ·
            refine ⟨24570202305290465812770163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32760269740387287750360217 24570202305290465812770163)
            ·
              refine ⟨36855303457935698719155245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24570202305290465812770163 36855303457935698719155245)
              ·
                refine ⟨13820738796725887019683217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36855303457935698719155245 13820738796725887019683217)
                ·
                  refine ⟨10365554097544415264762413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13820738796725887019683217 10365554097544415264762413)
                  ·
                    refine ⟨3887082786579155724285905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10365554097544415264762413 3887082786579155724285905)
                    ·
                      refine ⟨2915312089934366793214429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3887082786579155724285905 2915312089934366793214429)
                      ·
                        rfl

theorem cell23_5677550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_5677550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677550 prefixEnd_5677550 := by exact prefixLift 5677550
  have htrace : WordTrace (prefixWord ++ tailWord_5677550) baseStart_5677550 baseEnd_5677550 := by
    simpa [prefixWord, tailWord_5677550, baseEnd_5677550] using wordTrace_append hprefix tailTrace_5677550
  have hstable : (prefixWord ++ tailWord_5677550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677550).length < 2 ^ (prefixWord ++ tailWord_5677550).sum := by decide
  have hdescent : baseEnd_5677550 < baseStart_5677550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677573 : List Nat := [1, 3, 1, 1, 2, 2, 3, 4, 2, 4]
def baseStart_5677573 : Nat := 118140960795 + 5677573 * 2 ^ 59
def prefixEnd_5677573 : Nat := 4983230072969 + 3 ^ 40 * 5677573 * 2
def baseEnd_5677573 : Nat := 971774633329806734408941

theorem tailTrace_5677573 : CollatzResearch.WordTrace tailWord_5677573 prefixEnd_5677573 971774633329806734408941 := by
  unfold tailWord_5677573
  simp only [CollatzResearch.WordTrace]
  refine ⟨207078099460130148115549373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138052066306753432077032915 207078099460130148115549373)
  ·
    refine ⟨77654287297548805543331015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207078099460130148115549373 77654287297548805543331015)
    ·
      refine ⟨116481430946323208314996523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77654287297548805543331015 116481430946323208314996523)
      ·
        refine ⟨174722146419484812472494785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116481430946323208314996523 174722146419484812472494785)
        ·
          refine ⟨131041609814613609354371089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174722146419484812472494785 131041609814613609354371089)
          ·
            refine ⟨98281207360960207015778317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131041609814613609354371089 98281207360960207015778317)
            ·
              refine ⟨36855452760360077630916869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98281207360960207015778317 36855452760360077630916869)
              ·
                refine ⟨6910397392567514555796913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36855452760360077630916869 6910397392567514555796913)
                ·
                  refine ⟨5182798044425635916847685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6910397392567514555796913 5182798044425635916847685)
                  ·
                    refine ⟨971774633329806734408941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5182798044425635916847685 971774633329806734408941)
                    ·
                      rfl

theorem cell23_5677573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_5677573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677573 prefixEnd_5677573 := by exact prefixLift 5677573
  have htrace : WordTrace (prefixWord ++ tailWord_5677573) baseStart_5677573 baseEnd_5677573 := by
    simpa [prefixWord, tailWord_5677573, baseEnd_5677573] using wordTrace_append hprefix tailTrace_5677573
  have hstable : (prefixWord ++ tailWord_5677573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677573).length < 2 ^ (prefixWord ++ tailWord_5677573).sum := by decide
  have hdescent : baseEnd_5677573 < baseStart_5677573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677576 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_5677576 : Nat := 118140960795 + 5677576 * 2 ^ 59
def prefixEnd_5677576 : Nat := 4983230072969 + 3 ^ 40 * 5677576 * 2
def baseEnd_5677576 : Nat := 2915325440431383691489309

theorem tailTrace_5677576 : CollatzResearch.WordTrace tailWord_5677576 prefixEnd_5677576 2915325440431383691489309 := by
  unfold tailWord_5677576
  simp only [CollatzResearch.WordTrace]
  refine ⟨103539104439559639813954291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138052139252746186418605721 103539104439559639813954291)
  ·
    refine ⟨155308656659339459720931437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103539104439559639813954291 155308656659339459720931437)
    ·
      refine ⟨58240746247252297395349289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155308656659339459720931437 58240746247252297395349289)
      ·
        refine ⟨43680559685439223046511967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58240746247252297395349289 43680559685439223046511967)
        ·
          refine ⟨65520839528158834569767951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43680559685439223046511967 65520839528158834569767951)
          ·
            refine ⟨98281259292238251854651927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65520839528158834569767951 98281259292238251854651927)
            ·
              refine ⟨147421888938357377781977891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98281259292238251854651927 147421888938357377781977891)
              ·
                refine ⟨221132833407536066672966837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147421888938357377781977891 221132833407536066672966837)
                ·
                  refine ⟨20731203131956506250590641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 221132833407536066672966837 20731203131956506250590641)
                  ·
                    refine ⟨15548402348967379687942981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20731203131956506250590641 15548402348967379687942981)
                    ·
                      refine ⟨2915325440431383691489309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15548402348967379687942981 2915325440431383691489309)
                      ·
                        rfl

theorem cell23_5677576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_5677576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677576 prefixEnd_5677576 := by exact prefixLift 5677576
  have htrace : WordTrace (prefixWord ++ tailWord_5677576) baseStart_5677576 baseEnd_5677576 := by
    simpa [prefixWord, tailWord_5677576, baseEnd_5677576] using wordTrace_append hprefix tailTrace_5677576
  have hstable : (prefixWord ++ tailWord_5677576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677576).length < 2 ^ (prefixWord ++ tailWord_5677576).sum := by decide
  have hdescent : baseEnd_5677576 < baseStart_5677576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677597 : List Nat := [1, 4, 2, 2, 1, 3, 1, 2, 3, 2, 2]
def baseStart_5677597 : Nat := 118140960795 + 5677597 * 2 ^ 59
def prefixEnd_5677597 : Nat := 4983230072969 + 3 ^ 40 * 5677597 * 2
def baseEnd_5677597 : Nat := 2915336223525128109326713

theorem tailTrace_5677597 : CollatzResearch.WordTrace tailWord_5677597 prefixEnd_5677597 2915336223525128109326713 := by
  unfold tailWord_5677597
  simp only [CollatzResearch.WordTrace]
  refine ⟨207078974812043200214423045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138052649874695466809615363 207078974812043200214423045)
  ·
    refine ⟨38827307777258100040204321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207078974812043200214423045 38827307777258100040204321)
    ·
      refine ⟨29120480832943575030153241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38827307777258100040204321 29120480832943575030153241)
      ·
        refine ⟨21840360624707681272614931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29120480832943575030153241 21840360624707681272614931)
        ·
          refine ⟨32760540937061521908922397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21840360624707681272614931 32760540937061521908922397)
          ·
            refine ⟨12285202851398070715845899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32760540937061521908922397 12285202851398070715845899)
            ·
              refine ⟨18427804277097106073768849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12285202851398070715845899 18427804277097106073768849)
              ·
                refine ⟨13820853207822829555326637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18427804277097106073768849 13820853207822829555326637)
                ·
                  refine ⟨5182819952933561083247489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13820853207822829555326637 5182819952933561083247489)
                  ·
                    refine ⟨3887114964700170812435617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5182819952933561083247489 3887114964700170812435617)
                    ·
                      refine ⟨2915336223525128109326713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3887114964700170812435617 2915336223525128109326713)
                      ·
                        rfl

theorem cell23_5677597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_5677597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677597 prefixEnd_5677597 := by exact prefixLift 5677597
  have htrace : WordTrace (prefixWord ++ tailWord_5677597) baseStart_5677597 baseEnd_5677597 := by
    simpa [prefixWord, tailWord_5677597, baseEnd_5677597] using wordTrace_append hprefix tailTrace_5677597
  have hstable : (prefixWord ++ tailWord_5677597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677597).length < 2 ^ (prefixWord ++ tailWord_5677597).sum := by decide
  have hdescent : baseEnd_5677597 < baseStart_5677597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677603 : List Nat := [1, 1, 1, 4, 4, 2, 3, 7]
def baseStart_5677603 : Nat := 118140960795 + 5677603 * 2 ^ 59
def prefixEnd_5677603 : Nat := 4983230072969 + 3 ^ 40 * 5677603 * 2
def baseEnd_5677603 : Nat := 107975529792927966142655

theorem tailTrace_5677603 : CollatzResearch.WordTrace tailWord_5677603 prefixEnd_5677603 107975529792927966142655 := by
  unfold tailWord_5677603
  simp only [CollatzResearch.WordTrace]
  refine ⟨207079193650021463239141463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138052795766680975492760975 207079193650021463239141463)
  ·
    refine ⟨310618790475032194858712195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207079193650021463239141463 310618790475032194858712195)
    ·
      refine ⟨465928185712548292288068293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310618790475032194858712195 465928185712548292288068293)
      ·
        refine ⟨87361534821102804804012805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 465928185712548292288068293 87361534821102804804012805)
        ·
          refine ⟨16380287778956775900752401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87361534821102804804012805 16380287778956775900752401)
          ·
            refine ⟨12285215834217581925564301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16380287778956775900752401 12285215834217581925564301)
            ·
              refine ⟨4606955937831593222086613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12285215834217581925564301 4606955937831593222086613)
              ·
                refine ⟨107975529792927966142655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4606955937831593222086613 107975529792927966142655)
                ·
                  rfl

theorem cell23_5677603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 7].length) (baseStart_5677603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677603 prefixEnd_5677603 := by exact prefixLift 5677603
  have htrace : WordTrace (prefixWord ++ tailWord_5677603) baseStart_5677603 baseEnd_5677603 := by
    simpa [prefixWord, tailWord_5677603, baseEnd_5677603] using wordTrace_append hprefix tailTrace_5677603
  have hstable : (prefixWord ++ tailWord_5677603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677603).length < 2 ^ (prefixWord ++ tailWord_5677603).sum := by decide
  have hdescent : baseEnd_5677603 < baseStart_5677603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677614 : List Nat := [4, 1, 3, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_5677614 : Nat := 118140960795 + 5677614 * 2 ^ 59
def prefixEnd_5677614 : Nat := 4983230072969 + 3 ^ 40 * 5677614 * 2
def baseEnd_5677614 : Nat := 2915344952696254542814135

theorem tailTrace_5677614 : CollatzResearch.WordTrace tailWord_5677614 prefixEnd_5677614 2915344952696254542814135 := by
  unfold tailWord_5677614
  simp only [CollatzResearch.WordTrace]
  refine ⟨25884949356622701514723987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138053063235321074745194597 25884949356622701514723987)
  ·
    refine ⟨38827424034934052272085981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25884949356622701514723987 38827424034934052272085981)
    ·
      refine ⟨14560284013100269602032243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38827424034934052272085981 14560284013100269602032243)
      ·
        refine ⟨21840426019650404403048365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14560284013100269602032243 21840426019650404403048365)
        ·
          refine ⟨8190159757368901651143137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21840426019650404403048365 8190159757368901651143137)
          ·
            refine ⟨6142619818026676238357353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8190159757368901651143137 6142619818026676238357353)
            ·
              refine ⟨4606964863520007178768015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6142619818026676238357353 4606964863520007178768015)
              ·
                refine ⟨6910447295280010768152023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4606964863520007178768015 6910447295280010768152023)
                ·
                  refine ⟨10365670942920016152228035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6910447295280010768152023 10365670942920016152228035)
                  ·
                    refine ⟨15548506414380024228342053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10365670942920016152228035 15548506414380024228342053)
                    ·
                      refine ⟨2915344952696254542814135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15548506414380024228342053 2915344952696254542814135)
                      ·
                        rfl

theorem cell23_5677614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_5677614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677614 prefixEnd_5677614 := by exact prefixLift 5677614
  have htrace : WordTrace (prefixWord ++ tailWord_5677614) baseStart_5677614 baseEnd_5677614 := by
    simpa [prefixWord, tailWord_5677614, baseEnd_5677614] using wordTrace_append hprefix tailTrace_5677614
  have hstable : (prefixWord ++ tailWord_5677614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677614).length < 2 ^ (prefixWord ++ tailWord_5677614).sum := by decide
  have hdescent : baseEnd_5677614 < baseStart_5677614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677620 : List Nat := [2, 5, 1, 3, 1, 1, 10]
def baseStart_5677620 : Nat := 118140960795 + 5677620 * 2 ^ 59
def prefixEnd_5677620 : Nat := 4983230072969 + 3 ^ 40 * 5677620 * 2
def baseEnd_5677620 : Nat := 35991951031854092831347

theorem tailTrace_5677620 : CollatzResearch.WordTrace tailWord_5677620 prefixEnd_5677620 35991951031854092831347 := by
  unfold tailWord_5677620
  simp only [CollatzResearch.WordTrace]
  refine ⟨103539906845479937571255157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138053209127306583428340209 103539906845479937571255157)
  ·
    refine ⟨9706866266763744147305171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103539906845479937571255157 9706866266763744147305171)
    ·
      refine ⟨14560299400145616220957757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9706866266763744147305171 14560299400145616220957757)
      ·
        refine ⟨5460112275054606082859159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14560299400145616220957757 5460112275054606082859159)
        ·
          refine ⟨8190168412581909124288739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5460112275054606082859159 8190168412581909124288739)
          ·
            refine ⟨12285252618872863686433109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8190168412581909124288739 12285252618872863686433109)
            ·
              refine ⟨35991951031854092831347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12285252618872863686433109 35991951031854092831347)
              ·
                rfl

theorem cell23_5677620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 10].length) (baseStart_5677620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677620 prefixEnd_5677620 := by exact prefixLift 5677620
  have htrace : WordTrace (prefixWord ++ tailWord_5677620) baseStart_5677620 baseEnd_5677620 := by
    simpa [prefixWord, tailWord_5677620, baseEnd_5677620] using wordTrace_append hprefix tailTrace_5677620
  have hstable : (prefixWord ++ tailWord_5677620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677620).length < 2 ^ (prefixWord ++ tailWord_5677620).sum := by decide
  have hdescent : baseEnd_5677620 < baseStart_5677620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677676 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 9]
def baseStart_5677676 : Nat := 118140960795 + 5677676 * 2 ^ 59
def prefixEnd_5677676 : Nat := 4983230072969 + 3 ^ 40 * 5677676 * 2
def baseEnd_5677676 : Nat := 323930754277425922248761

theorem tailTrace_5677676 : CollatzResearch.WordTrace tailWord_5677676 prefixEnd_5677676 323930754277425922248761 := by
  unfold tailWord_5677676
  simp only [CollatzResearch.WordTrace]
  refine ⟨103540928089378498353274441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138054570785837997804365921 103540928089378498353274441)
  ·
    refine ⟨77655696067033873764955831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103540928089378498353274441 77655696067033873764955831)
    ·
      refine ⟨116483544100550810647433747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77655696067033873764955831 116483544100550810647433747)
      ·
        refine ⟨174725316150826215971150621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116483544100550810647433747 174725316150826215971150621)
        ·
          refine ⟨65521993556559830989181483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174725316150826215971150621 65521993556559830989181483)
          ·
            refine ⟨98282990334839746483772225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65521993556559830989181483 98282990334839746483772225)
            ·
              refine ⟨73712242751129809862829169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98282990334839746483772225 73712242751129809862829169)
              ·
                refine ⟨55284182063347357397121877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73712242751129809862829169 55284182063347357397121877)
                ·
                  refine ⟨323930754277425922248761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55284182063347357397121877 323930754277425922248761)
                  ·
                    rfl

theorem cell23_5677676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 9].length) (baseStart_5677676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677676 prefixEnd_5677676 := by exact prefixLift 5677676
  have htrace : WordTrace (prefixWord ++ tailWord_5677676) baseStart_5677676 baseEnd_5677676 := by
    simpa [prefixWord, tailWord_5677676, baseEnd_5677676] using wordTrace_append hprefix tailTrace_5677676
  have hstable : (prefixWord ++ tailWord_5677676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677676).length < 2 ^ (prefixWord ++ tailWord_5677676).sum := by decide
  have hdescent : baseEnd_5677676 < baseStart_5677676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677698 : List Nat := [3, 4, 3, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_5677698 : Nat := 118140960795 + 5677698 * 2 ^ 59
def prefixEnd_5677698 : Nat := 4983230072969 + 3 ^ 40 * 5677698 * 2
def baseEnd_5677698 : Nat := 2915388085071232214163749

theorem tailTrace_5677698 : CollatzResearch.WordTrace tailWord_5677698 prefixEnd_5677698 2915388085071232214163749 := by
  unfold tailWord_5677698
  simp only [CollatzResearch.WordTrace]
  refine ⟨51770664646169323615962437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138055105723118196309233165 51770664646169323615962437)
  ·
    refine ⟨9706999621156748177992957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51770664646169323615962437 9706999621156748177992957)
    ·
      refine ⟨3640124857933780566747359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9706999621156748177992957 3640124857933780566747359)
      ·
        refine ⟨5460187286900670850121039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3640124857933780566747359 5460187286900670850121039)
        ·
          refine ⟨8190280930351006275181559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5460187286900670850121039 8190280930351006275181559)
          ·
            refine ⟨12285421395526509412772339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8190280930351006275181559 12285421395526509412772339)
            ·
              refine ⟨18428132093289764119158509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12285421395526509412772339 18428132093289764119158509)
              ·
                refine ⟨6910549534983661544684441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18428132093289764119158509 6910549534983661544684441)
                ·
                  refine ⟨5182912151237746158513331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6910549534983661544684441 5182912151237746158513331)
                  ·
                    refine ⟨7774368226856619237769997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5182912151237746158513331 7774368226856619237769997)
                    ·
                      refine ⟨2915388085071232214163749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7774368226856619237769997 2915388085071232214163749)
                      ·
                        rfl

theorem cell23_5677698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_5677698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677698 prefixEnd_5677698 := by exact prefixLift 5677698
  have htrace : WordTrace (prefixWord ++ tailWord_5677698) baseStart_5677698 baseEnd_5677698 := by
    simpa [prefixWord, tailWord_5677698, baseEnd_5677698] using wordTrace_append hprefix tailTrace_5677698
  have hstable : (prefixWord ++ tailWord_5677698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677698).length < 2 ^ (prefixWord ++ tailWord_5677698).sum := by decide
  have hdescent : baseEnd_5677698 < baseStart_5677698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677703 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 3]
def baseStart_5677703 : Nat := 118140960795 + 5677703 * 2 ^ 59
def prefixEnd_5677703 : Nat := 4983230072969 + 3 ^ 40 * 5677703 * 2
def baseEnd_5677703 : Nat := 2915390652474504694601225

theorem tailTrace_5677703 : CollatzResearch.WordTrace tailWord_5677703 prefixEnd_5677703 2915390652474504694601225 := by
  unfold tailWord_5677703
  simp only [CollatzResearch.WordTrace]
  refine ⟨207082840949659180317781763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138055227299772786878521175 207082840949659180317781763)
  ·
    refine ⟨310624261424488770476672645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207082840949659180317781763 310624261424488770476672645)
    ·
      refine ⟨58242049017091644464376121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310624261424488770476672645 58242049017091644464376121)
      ·
        refine ⟨43681536762818733348282091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58242049017091644464376121 43681536762818733348282091)
        ·
          refine ⟨65522305144228100022423137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43681536762818733348282091 65522305144228100022423137)
          ·
            refine ⟨49141728858171075016817353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65522305144228100022423137 49141728858171075016817353)
            ·
              refine ⟨36856296643628306262613015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49141728858171075016817353 36856296643628306262613015)
              ·
                refine ⟨55284444965442459393919523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36856296643628306262613015 55284444965442459393919523)
                ·
                  refine ⟨82926667448163689090879285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55284444965442459393919523 82926667448163689090879285)
                  ·
                    refine ⟨7774375073265345852269933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82926667448163689090879285 7774375073265345852269933)
                    ·
                      refine ⟨2915390652474504694601225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7774375073265345852269933 2915390652474504694601225)
                      ·
                        rfl

theorem cell23_5677703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_5677703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677703 prefixEnd_5677703 := by exact prefixLift 5677703
  have htrace : WordTrace (prefixWord ++ tailWord_5677703) baseStart_5677703 baseEnd_5677703 := by
    simpa [prefixWord, tailWord_5677703, baseEnd_5677703] using wordTrace_append hprefix tailTrace_5677703
  have hstable : (prefixWord ++ tailWord_5677703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677703).length < 2 ^ (prefixWord ++ tailWord_5677703).sum := by decide
  have hdescent : baseEnd_5677703 < baseStart_5677703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677738 : List Nat := [3, 1, 5, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_5677738 : Nat := 118140960795 + 5677738 * 2 ^ 59
def prefixEnd_5677738 : Nat := 4983230072969 + 3 ^ 40 * 5677738 * 2
def baseEnd_5677738 : Nat := 2915408624297412057663565

theorem tailTrace_5677738 : CollatzResearch.WordTrace tailWord_5677738 prefixEnd_5677738 2915408624297412057663565 := by
  unfold tailWord_5677738
  simp only [CollatzResearch.WordTrace]
  refine ⟨51771029376133095323826467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138056078336354920863537245 51771029376133095323826467)
  ·
    refine ⟨77656544064199642985739701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51771029376133095323826467 77656544064199642985739701)
    ·
      refine ⟨7280301006018716529913097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77656544064199642985739701 7280301006018716529913097)
      ·
        refine ⟨5460225754514037397434823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7280301006018716529913097 5460225754514037397434823)
        ·
          refine ⟨8190338631771056096152235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5460225754514037397434823 8190338631771056096152235)
          ·
            refine ⟨12285507947656584144228353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8190338631771056096152235 12285507947656584144228353)
            ·
              refine ⟨9214130960742438108171265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12285507947656584144228353 9214130960742438108171265)
              ·
                refine ⟨6910598220556828581128449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9214130960742438108171265 6910598220556828581128449)
                ·
                  refine ⟨5182948665417621435846337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6910598220556828581128449 5182948665417621435846337)
                  ·
                    refine ⟨3887211499063216076884753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5182948665417621435846337 3887211499063216076884753)
                    ·
                      refine ⟨2915408624297412057663565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3887211499063216076884753 2915408624297412057663565)
                      ·
                        rfl

theorem cell23_5677738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_5677738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677738 prefixEnd_5677738 := by exact prefixLift 5677738
  have htrace : WordTrace (prefixWord ++ tailWord_5677738) baseStart_5677738 baseEnd_5677738 := by
    simpa [prefixWord, tailWord_5677738, baseEnd_5677738] using wordTrace_append hprefix tailTrace_5677738
  have hstable : (prefixWord ++ tailWord_5677738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677738).length < 2 ^ (prefixWord ++ tailWord_5677738).sum := by decide
  have hdescent : baseEnd_5677738 < baseStart_5677738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677760 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 1, 6, 2]
def baseStart_5677760 : Nat := 118140960795 + 5677760 * 2 ^ 59
def prefixEnd_5677760 : Nat := 4983230072969 + 3 ^ 40 * 5677760 * 2
def baseEnd_5677760 : Nat := 2915419920871810971588463

theorem tailTrace_5677760 : CollatzResearch.WordTrace tailWord_5677760 prefixEnd_5677760 2915419920871810971588463 := by
  unfold tailWord_5677760
  simp only [CollatzResearch.WordTrace]
  refine ⟨103542459955226339526303367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138056613273635119368404489 103542459955226339526303367)
  ·
    refine ⟨155313689932839509289455051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103542459955226339526303367 155313689932839509289455051)
    ·
      refine ⟨232970534899259263934182577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155313689932839509289455051 232970534899259263934182577)
      ·
        refine ⟨174727901174444447950636933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232970534899259263934182577 174727901174444447950636933)
        ·
          refine ⟨32761481470208333990744425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174727901174444447950636933 32761481470208333990744425)
          ·
            refine ⟨24571111102656250493058319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32761481470208333990744425 24571111102656250493058319)
            ·
              refine ⟨36856666653984375739587479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24571111102656250493058319 36856666653984375739587479)
              ·
                refine ⟨55284999980976563609381219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36856666653984375739587479 55284999980976563609381219)
                ·
                  refine ⟨82927499971464845414071829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55284999980976563609381219 82927499971464845414071829)
                  ·
                    refine ⟨3887226561162414628784617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82927499971464845414071829 3887226561162414628784617)
                    ·
                      refine ⟨2915419920871810971588463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3887226561162414628784617 2915419920871810971588463)
                      ·
                        rfl

theorem cell23_5677760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 1, 6, 2].length) (baseStart_5677760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677760 prefixEnd_5677760 := by exact prefixLift 5677760
  have htrace : WordTrace (prefixWord ++ tailWord_5677760) baseStart_5677760 baseEnd_5677760 := by
    simpa [prefixWord, tailWord_5677760, baseEnd_5677760] using wordTrace_append hprefix tailTrace_5677760
  have hstable : (prefixWord ++ tailWord_5677760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677760).length < 2 ^ (prefixWord ++ tailWord_5677760).sum := by decide
  have hdescent : baseEnd_5677760 < baseStart_5677760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677770 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 5, 4]
def baseStart_5677770 : Nat := 118140960795 + 5677770 * 2 ^ 59
def prefixEnd_5677770 : Nat := 4983230072969 + 3 ^ 40 * 5677770 * 2
def baseEnd_5677770 : Nat := 971808351892785310821139

theorem tailTrace_5677770 : CollatzResearch.WordTrace tailWord_5677770 prefixEnd_5677770 971808351892785310821139 := by
  unfold tailWord_5677770
  simp only [CollatzResearch.WordTrace]
  refine ⟨51771321160104112690117691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138056856426944300506980509 51771321160104112690117691)
  ·
    refine ⟨77656981740156169035176537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51771321160104112690117691 77656981740156169035176537)
    ·
      refine ⟨58242736305117126776382403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77656981740156169035176537 58242736305117126776382403)
      ·
        refine ⟨87364104457675690164573605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58242736305117126776382403 87364104457675690164573605)
        ·
          refine ⟨16380769585814191905857551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87364104457675690164573605 16380769585814191905857551)
          ·
            refine ⟨24571154378721287858786327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16380769585814191905857551 24571154378721287858786327)
            ·
              refine ⟨36856731568081931788179491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24571154378721287858786327 36856731568081931788179491)
              ·
                refine ⟨55285097352122897682269237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36856731568081931788179491 55285097352122897682269237)
                ·
                  refine ⟨5182977876761521657712741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55285097352122897682269237 5182977876761521657712741)
                  ·
                    refine ⟨971808351892785310821139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5182977876761521657712741 971808351892785310821139)
                    ·
                      rfl

theorem cell23_5677770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_5677770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677770 prefixEnd_5677770 := by exact prefixLift 5677770
  have htrace : WordTrace (prefixWord ++ tailWord_5677770) baseStart_5677770 baseEnd_5677770 := by
    simpa [prefixWord, tailWord_5677770, baseEnd_5677770] using wordTrace_append hprefix tailTrace_5677770
  have hstable : (prefixWord ++ tailWord_5677770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677770).length < 2 ^ (prefixWord ++ tailWord_5677770).sum := by decide
  have hdescent : baseEnd_5677770 < baseStart_5677770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677800 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 8]
def baseStart_5677800 : Nat := 118140960795 + 5677800 * 2 ^ 59
def prefixEnd_5677800 : Nat := 4983230072969 + 3 ^ 40 * 5677800 * 2
def baseEnd_5677800 : Nat := 323937828899776757232031

theorem tailTrace_5677800 : CollatzResearch.WordTrace tailWord_5677800 prefixEnd_5677800 323937828899776757232031 := by
  unfold tailWord_5677800
  simp only [CollatzResearch.WordTrace]
  refine ⟨103543189415153882942031427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138057585886871843922708569 103543189415153882942031427)
  ·
    refine ⟨155314784122730824413047141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103543189415153882942031427 155314784122730824413047141)
    ·
      refine ⟨29121522023012029577446339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155314784122730824413047141 29121522023012029577446339)
      ·
        refine ⟨43682283034518044366169509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29121522023012029577446339 43682283034518044366169509)
        ·
          refine ⟨8190428068972133318656783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43682283034518044366169509 8190428068972133318656783)
          ·
            refine ⟨12285642103458199977985175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8190428068972133318656783 12285642103458199977985175)
            ·
              refine ⟨18428463155187299966977763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12285642103458199977985175 18428463155187299966977763)
              ·
                refine ⟨27642694732780949950466645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18428463155187299966977763 27642694732780949950466645)
                ·
                  refine ⟨323937828899776757232031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27642694732780949950466645 323937828899776757232031)
                  ·
                    rfl

theorem cell23_5677800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 8].length) (baseStart_5677800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677800 prefixEnd_5677800 := by exact prefixLift 5677800
  have htrace : WordTrace (prefixWord ++ tailWord_5677800) baseStart_5677800 baseEnd_5677800 := by
    simpa [prefixWord, tailWord_5677800, baseEnd_5677800] using wordTrace_append hprefix tailTrace_5677800
  have hstable : (prefixWord ++ tailWord_5677800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677800).length < 2 ^ (prefixWord ++ tailWord_5677800).sum := by decide
  have hdescent : baseEnd_5677800 < baseStart_5677800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677843 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 3, 6]
def baseStart_5677843 : Nat := 118140960795 + 5677843 * 2 ^ 59
def prefixEnd_5677843 : Nat := 4983230072969 + 3 ^ 40 * 5677843 * 2
def baseEnd_5677843 : Nat := 971820846588711382283527

theorem tailTrace_5677843 : CollatzResearch.WordTrace tailWord_5677843 prefixEnd_5677843 971820846588711382283527 := by
  unfold tailWord_5677843
  simp only [CollatzResearch.WordTrace]
  refine ⟨207087947169151984227878183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138058631446101322818585455 207087947169151984227878183)
  ·
    refine ⟨310631920753727976341817275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207087947169151984227878183 310631920753727976341817275)
    ·
      refine ⟨465947881130591964512725913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310631920753727976341817275 465947881130591964512725913)
      ·
        refine ⟨349460910847943973384544435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 465947881130591964512725913 349460910847943973384544435)
        ·
          refine ⟨524191366271915960076816653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349460910847943973384544435 524191366271915960076816653)
          ·
            refine ⟨196571762351968485028806245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 524191366271915960076816653 196571762351968485028806245)
            ·
              refine ⟨36857205440994090942901171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196571762351968485028806245 36857205440994090942901171)
              ·
                refine ⟨55285808161491136414351757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36857205440994090942901171 55285808161491136414351757)
                ·
                  refine ⟨20732178060559176155381909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55285808161491136414351757 20732178060559176155381909)
                  ·
                    refine ⟨971820846588711382283527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20732178060559176155381909 971820846588711382283527)
                    ·
                      rfl

theorem cell23_5677843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 6].length) (baseStart_5677843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677843 prefixEnd_5677843 := by exact prefixLift 5677843
  have htrace : WordTrace (prefixWord ++ tailWord_5677843) baseStart_5677843 baseEnd_5677843 := by
    simpa [prefixWord, tailWord_5677843, baseEnd_5677843] using wordTrace_append hprefix tailTrace_5677843
  have hstable : (prefixWord ++ tailWord_5677843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677843).length < 2 ^ (prefixWord ++ tailWord_5677843).sum := by decide
  have hdescent : baseEnd_5677843 < baseStart_5677843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677861 : List Nat := [1, 3, 1, 2, 3, 1, 5, 2, 1, 1, 3]
def baseStart_5677861 : Nat := 118140960795 + 5677861 * 2 ^ 59
def prefixEnd_5677861 : Nat := 4983230072969 + 3 ^ 40 * 5677861 * 2
def baseEnd_5677861 : Nat := 2915471782417915076425499

theorem tailTrace_5677861 : CollatzResearch.WordTrace tailWord_5677861 prefixEnd_5677861 2915471782417915076425499 := by
  unfold tailWord_5677861
  simp only [CollatzResearch.WordTrace]
  refine ⟨207088603683086773302033437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138059069122057848868022291 207088603683086773302033437)
  ·
    refine ⟨77658226381157539988262539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207088603683086773302033437 77658226381157539988262539)
    ·
      refine ⟨116487339571736309982393809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77658226381157539988262539 116487339571736309982393809)
      ·
        refine ⟨87365504678802232486795357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116487339571736309982393809 87365504678802232486795357)
        ·
          refine ⟨32762064254550837182548259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87365504678802232486795357 32762064254550837182548259)
          ·
            refine ⟨49143096381826255773822389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32762064254550837182548259 49143096381826255773822389)
            ·
              refine ⟨4607165285796211478795849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49143096381826255773822389 4607165285796211478795849)
              ·
                refine ⟨3455373964347158609096887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4607165285796211478795849 3455373964347158609096887)
                ·
                  refine ⟨5183060946520737913645331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3455373964347158609096887 5183060946520737913645331)
                  ·
                    refine ⟨7774591419781106870467997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5183060946520737913645331 7774591419781106870467997)
                    ·
                      refine ⟨2915471782417915076425499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7774591419781106870467997 2915471782417915076425499)
                      ·
                        rfl

theorem cell23_5677861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_5677861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677861 prefixEnd_5677861 := by exact prefixLift 5677861
  have htrace : WordTrace (prefixWord ++ tailWord_5677861) baseStart_5677861 baseEnd_5677861 := by
    simpa [prefixWord, tailWord_5677861, baseEnd_5677861] using wordTrace_append hprefix tailTrace_5677861
  have hstable : (prefixWord ++ tailWord_5677861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677861).length < 2 ^ (prefixWord ++ tailWord_5677861).sum := by decide
  have hdescent : baseEnd_5677861 < baseStart_5677861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677880 : List Nat := [2, 1, 2, 1, 3, 2, 2, 3, 1, 2, 4]
def baseStart_5677880 : Nat := 118140960795 + 5677880 * 2 ^ 59
def prefixEnd_5677880 : Nat := 4983230072969 + 3 ^ 40 * 5677880 * 2
def baseEnd_5677880 : Nat := 2915481538550350502087911

theorem tailTrace_5677880 : CollatzResearch.WordTrace tailWord_5677880 prefixEnd_5677880 2915481538550350502087911 := by
  unfold tailWord_5677880
  simp only [CollatzResearch.WordTrace]
  refine ⟨103544648335008969773487547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138059531113345293031316729 103544648335008969773487547)
  ·
    refine ⟨155316972502513454660231321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103544648335008969773487547 155316972502513454660231321)
    ·
      refine ⟨116487729376885090995173491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155316972502513454660231321 116487729376885090995173491)
      ·
        refine ⟨174731594065327636492760237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116487729376885090995173491 174731594065327636492760237)
        ·
          refine ⟨65524347774497863684785089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174731594065327636492760237 65524347774497863684785089)
          ·
            refine ⟨49143260830873397763588817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65524347774497863684785089 49143260830873397763588817)
            ·
              refine ⟨36857445623155048322691613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49143260830873397763588817 36857445623155048322691613)
              ·
                refine ⟨13821542108683143121009355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36857445623155048322691613 13821542108683143121009355)
                ·
                  refine ⟨20732313163024714681514033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13821542108683143121009355 20732313163024714681514033)
                  ·
                    refine ⟨15549234872268536011135525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20732313163024714681514033 15549234872268536011135525)
                    ·
                      refine ⟨2915481538550350502087911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15549234872268536011135525 2915481538550350502087911)
                      ·
                        rfl

theorem cell23_5677880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_5677880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677880 prefixEnd_5677880 := by exact prefixLift 5677880
  have htrace : WordTrace (prefixWord ++ tailWord_5677880) baseStart_5677880 baseEnd_5677880 := by
    simpa [prefixWord, tailWord_5677880, baseEnd_5677880] using wordTrace_append hprefix tailTrace_5677880
  have hstable : (prefixWord ++ tailWord_5677880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677880).length < 2 ^ (prefixWord ++ tailWord_5677880).sum := by decide
  have hdescent : baseEnd_5677880 < baseStart_5677880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677887 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 3]
def baseStart_5677887 : Nat := 118140960795 + 5677887 * 2 ^ 59
def prefixEnd_5677887 : Nat := 4983230072969 + 3 ^ 40 * 5677887 * 2
def baseEnd_5677887 : Nat := 2915485132914931974700379

theorem tailTrace_5677887 : CollatzResearch.WordTrace tailWord_5677887 prefixEnd_5677887 2915485132914931974700379 := by
  unfold tailWord_5677887
  simp only [CollatzResearch.WordTrace]
  refine ⟨207089551980992579742479915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138059701320661719828319943 207089551980992579742479915)
  ·
    refine ⟨310634327971488869613719873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207089551980992579742479915 310634327971488869613719873)
    ·
      refine ⟨232975745978616652210289905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310634327971488869613719873 232975745978616652210289905)
      ·
        refine ⟨174731809483962489157717429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232975745978616652210289905 174731809483962489157717429)
        ·
          refine ⟨16381107139121483358536009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174731809483962489157717429 16381107139121483358536009)
          ·
            refine ⟨12285830354341112518902007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16381107139121483358536009 12285830354341112518902007)
            ·
              refine ⟨18428745531511668778353011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12285830354341112518902007 18428745531511668778353011)
              ·
                refine ⟨27643118297267503167529517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18428745531511668778353011 27643118297267503167529517)
                ·
                  refine ⟨10366169361475313687823569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27643118297267503167529517 10366169361475313687823569)
                  ·
                    refine ⟨7774627021106485265867677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10366169361475313687823569 7774627021106485265867677)
                    ·
                      refine ⟨2915485132914931974700379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7774627021106485265867677 2915485132914931974700379)
                      ·
                        rfl

theorem cell23_5677887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_5677887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677887 prefixEnd_5677887 := by exact prefixLift 5677887
  have htrace : WordTrace (prefixWord ++ tailWord_5677887) baseStart_5677887 baseEnd_5677887 := by
    simpa [prefixWord, tailWord_5677887, baseEnd_5677887] using wordTrace_append hprefix tailTrace_5677887
  have hstable : (prefixWord ++ tailWord_5677887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677887).length < 2 ^ (prefixWord ++ tailWord_5677887).sum := by decide
  have hdescent : baseEnd_5677887 < baseStart_5677887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677903 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 6, 7]
def baseStart_5677903 : Nat := 118140960795 + 5677903 * 2 ^ 59
def prefixEnd_5677903 : Nat := 4983230072969 + 3 ^ 40 * 5677903 * 2
def baseEnd_5677903 : Nat := 971831116201801304033435

theorem tailTrace_5677903 : CollatzResearch.WordTrace tailWord_5677903 prefixEnd_5677903 971831116201801304033435 := by
  unfold tailWord_5677903
  simp only [CollatzResearch.WordTrace]
  refine ⟨207090135548934614475062363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138060090365956409650041575 207090135548934614475062363)
  ·
    refine ⟨310635203323401921712593545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207090135548934614475062363 310635203323401921712593545)
    ·
      refine ⟨232976402492551441284445159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310635203323401921712593545 232976402492551441284445159)
      ·
        refine ⟨349464603738827161926667739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232976402492551441284445159 349464603738827161926667739)
        ·
          refine ⟨524196905608240742890001609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349464603738827161926667739 524196905608240742890001609)
          ·
            refine ⟨393147679206180557167501207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524196905608240742890001609 393147679206180557167501207)
            ·
              refine ⟨589721518809270835751251811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393147679206180557167501207 589721518809270835751251811)
              ·
                refine ⟨884582278213906253626877717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589721518809270835751251811 884582278213906253626877717)
                ·
                  refine ⟨41464794291276855638759893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 884582278213906253626877717 41464794291276855638759893)
                  ·
                    refine ⟨971831116201801304033435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41464794291276855638759893 971831116201801304033435)
                    ·
                      rfl

theorem cell23_5677903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 7].length) (baseStart_5677903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677903 prefixEnd_5677903 := by exact prefixLift 5677903
  have htrace : WordTrace (prefixWord ++ tailWord_5677903) baseStart_5677903 baseEnd_5677903 := by
    simpa [prefixWord, tailWord_5677903, baseEnd_5677903] using wordTrace_append hprefix tailTrace_5677903
  have hstable : (prefixWord ++ tailWord_5677903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677903).length < 2 ^ (prefixWord ++ tailWord_5677903).sum := by decide
  have hdescent : baseEnd_5677903 < baseStart_5677903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5677961 : List Nat := [1, 2, 1, 1, 5, 2, 4, 1, 1, 3, 2]
def baseStart_5677961 : Nat := 118140960795 + 5677961 * 2 ^ 59
def prefixEnd_5677961 : Nat := 4983230072969 + 3 ^ 40 * 5677961 * 2
def baseEnd_5677961 : Nat := 2915523130483364685175039

theorem tailTrace_5677961 : CollatzResearch.WordTrace tailWord_5677961 prefixEnd_5677961 2915523130483364685175039 := by
  unfold tailWord_5677961
  simp only [CollatzResearch.WordTrace]
  refine ⟨207092250982724490380673737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138061500655149660253782491 207092250982724490380673737)
  ·
    refine ⟨155319188237043367785505303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207092250982724490380673737 155319188237043367785505303)
    ·
      refine ⟨232978782355565051678257955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155319188237043367785505303 232978782355565051678257955)
      ·
        refine ⟨349468173533347577517386933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232978782355565051678257955 349468173533347577517386933)
        ·
          refine ⟨32762641268751335392255025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 349468173533347577517386933 32762641268751335392255025)
          ·
            refine ⟨24571980951563501544191269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32762641268751335392255025 24571980951563501544191269)
            ·
              refine ⟨4607246428418156539535863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24571980951563501544191269 4607246428418156539535863)
              ·
                refine ⟨6910869642627234809303795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4607246428418156539535863 6910869642627234809303795)
                ·
                  refine ⟨10366304463940852213955693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6910869642627234809303795 10366304463940852213955693)
                  ·
                    refine ⟨3887364173977819580233385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10366304463940852213955693 3887364173977819580233385)
                    ·
                      refine ⟨2915523130483364685175039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3887364173977819580233385 2915523130483364685175039)
                      ·
                        rfl

theorem cell23_5677961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 1, 3, 2].length) (baseStart_5677961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5677961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5677961 prefixEnd_5677961 := by exact prefixLift 5677961
  have htrace : WordTrace (prefixWord ++ tailWord_5677961) baseStart_5677961 baseEnd_5677961 := by
    simpa [prefixWord, tailWord_5677961, baseEnd_5677961] using wordTrace_append hprefix tailTrace_5677961
  have hstable : (prefixWord ++ tailWord_5677961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5677961).length < 2 ^ (prefixWord ++ tailWord_5677961).sum := by decide
  have hdescent : baseEnd_5677961 < baseStart_5677961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5677961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678010 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 1, 7]
def baseStart_5678010 : Nat := 118140960795 + 5678010 * 2 ^ 59
def prefixEnd_5678010 : Nat := 4983230072969 + 3 ^ 40 * 5678010 * 2
def baseEnd_5678010 : Nat := 971849430345144997820771

theorem tailTrace_5678010 : CollatzResearch.WordTrace tailWord_5678010 prefixEnd_5678010 971849430345144997820771 := by
  unfold tailWord_5678010
  simp only [CollatzResearch.WordTrace]
  refine ⟨51773509539886742937301871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138062692106364647832804989 51773509539886742937301871)
  ·
    refine ⟨77660264309830114405952807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51773509539886742937301871 77660264309830114405952807)
    ·
      refine ⟨116490396464745171608929211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77660264309830114405952807 116490396464745171608929211)
      ·
        refine ⟨174735594697117757413393817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116490396464745171608929211 174735594697117757413393817)
        ·
          refine ⟨131051696022838318060045363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174735594697117757413393817 131051696022838318060045363)
          ·
            refine ⟨196577544034257477090068045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131051696022838318060045363 196577544034257477090068045)
            ·
              refine ⟨73716579012846553908775517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196577544034257477090068045 73716579012846553908775517)
              ·
                refine ⟨27643717129817457715790819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73716579012846553908775517 27643717129817457715790819)
                ·
                  refine ⟨41465575694726186573686229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27643717129817457715790819 41465575694726186573686229)
                  ·
                    refine ⟨971849430345144997820771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41465575694726186573686229 971849430345144997820771)
                    ·
                      rfl

theorem cell23_5678010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_5678010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678010 prefixEnd_5678010 := by exact prefixLift 5678010
  have htrace : WordTrace (prefixWord ++ tailWord_5678010) baseStart_5678010 baseEnd_5678010 := by
    simpa [prefixWord, tailWord_5678010, baseEnd_5678010] using wordTrace_append hprefix tailTrace_5678010
  have hstable : (prefixWord ++ tailWord_5678010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678010).length < 2 ^ (prefixWord ++ tailWord_5678010).sum := by decide
  have hdescent : baseEnd_5678010 < baseStart_5678010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678027 : List Nat := [1, 1, 1, 1, 3, 6, 1, 2, 2, 5]
def baseStart_5678027 : Nat := 118140960795 + 5678027 * 2 ^ 59
def prefixEnd_5678027 : Nat := 4983230072969 + 3 ^ 40 * 5678027 * 2
def baseEnd_5678027 : Nat := 971852340068853808983245

theorem tailTrace_5678027 : CollatzResearch.WordTrace tailWord_5678027 prefixEnd_5678027 971852340068853808983245 := by
  unfold tailWord_5678027
  simp only [CollatzResearch.WordTrace]
  refine ⟨207094658200485383652576335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138063105466990255768384223 207094658200485383652576335)
  ·
    refine ⟨310641987300728075478864503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207094658200485383652576335 310641987300728075478864503)
    ·
      refine ⟨465962980951092113218296755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310641987300728075478864503 465962980951092113218296755)
      ·
        refine ⟨698944471426638169827445133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465962980951092113218296755 698944471426638169827445133)
        ·
          refine ⟨262104176784989313685291925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 698944471426638169827445133 262104176784989313685291925)
          ·
            refine ⟨12286133286796374078998059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 262104176784989313685291925 12286133286796374078998059)
            ·
              refine ⟨18429199930194561118497089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12286133286796374078998059 18429199930194561118497089)
              ·
                refine ⟨13821899947645920838872817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18429199930194561118497089 13821899947645920838872817)
                ·
                  refine ⟨10366424960734440629154613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13821899947645920838872817 10366424960734440629154613)
                  ·
                    refine ⟨971852340068853808983245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10366424960734440629154613 971852340068853808983245)
                    ·
                      rfl

theorem cell23_5678027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 5].length) (baseStart_5678027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678027 prefixEnd_5678027 := by exact prefixLift 5678027
  have htrace : WordTrace (prefixWord ++ tailWord_5678027) baseStart_5678027 baseEnd_5678027 := by
    simpa [prefixWord, tailWord_5678027, baseEnd_5678027] using wordTrace_append hprefix tailTrace_5678027
  have hstable : (prefixWord ++ tailWord_5678027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678027).length < 2 ^ (prefixWord ++ tailWord_5678027).sum := by decide
  have hdescent : baseEnd_5678027 < baseStart_5678027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678060 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 6]
def baseStart_5678060 : Nat := 118140960795 + 5678060 * 2 ^ 59
def prefixEnd_5678060 : Nat := 4983230072969 + 3 ^ 40 * 5678060 * 2
def baseEnd_5678060 : Nat := 2915573965068159797837083

theorem tailTrace_5678060 : CollatzResearch.WordTrace tailWord_5678060 prefixEnd_5678060 2915573965068159797837083 := by
  unfold tailWord_5678060
  simp only [CollatzResearch.WordTrace]
  refine ⟨103547930904682915144263817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138063907872910553525685089 103547930904682915144263817)
  ·
    refine ⟨77660948178512186358197863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103547930904682915144263817 77660948178512186358197863)
    ·
      refine ⟨116491422267768279537296795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77660948178512186358197863 116491422267768279537296795)
      ·
        refine ⟨174737133401652419305945193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116491422267768279537296795 174737133401652419305945193)
        ·
          refine ⟨131052850051239314479458895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174737133401652419305945193 131052850051239314479458895)
          ·
            refine ⟨196579275076858971719188343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131052850051239314479458895 196579275076858971719188343)
            ·
              refine ⟨294868912615288457578782515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196579275076858971719188343 294868912615288457578782515)
              ·
                refine ⟨442303368922932686368173773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294868912615288457578782515 442303368922932686368173773)
                ·
                  refine ⟨165863763346099757388065165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 442303368922932686368173773 165863763346099757388065165)
                  ·
                    refine ⟨62198911254787409020524437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165863763346099757388065165 62198911254787409020524437)
                    ·
                      refine ⟨2915573965068159797837083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62198911254787409020524437 2915573965068159797837083)
                      ·
                        rfl

theorem cell23_5678060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_5678060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678060 prefixEnd_5678060 := by exact prefixLift 5678060
  have htrace : WordTrace (prefixWord ++ tailWord_5678060) baseStart_5678060 baseEnd_5678060 := by
    simpa [prefixWord, tailWord_5678060, baseEnd_5678060] using wordTrace_append hprefix tailTrace_5678060
  have hstable : (prefixWord ++ tailWord_5678060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678060).length < 2 ^ (prefixWord ++ tailWord_5678060).sum := by decide
  have hdescent : baseEnd_5678060 < baseStart_5678060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678082 : List Nat := [3, 4, 1, 3, 2, 1, 2, 2, 5]
def baseStart_5678082 : Nat := 118140960795 + 5678082 * 2 ^ 59
def prefixEnd_5678082 : Nat := 4983230072969 + 3 ^ 40 * 5678082 * 2
def baseEnd_5678082 : Nat := 323953917960284301306887

theorem tailTrace_5678082 : CollatzResearch.WordTrace tailWord_5678082 prefixEnd_5678082 323953917960284301306887 := by
  unfold tailWord_5678082
  simp only [CollatzResearch.WordTrace]
  refine ⟨51774166053821532011457125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138064442810190752030552333 51774166053821532011457125)
  ·
    refine ⟨9707656135091537252148211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51774166053821532011457125 9707656135091537252148211)
    ·
      refine ⟨14561484202637305878222317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9707656135091537252148211 14561484202637305878222317)
      ·
        refine ⟨5460556575988989704333369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14561484202637305878222317 5460556575988989704333369)
        ·
          refine ⟨4095417431991742278250027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5460556575988989704333369 4095417431991742278250027)
          ·
            refine ⟨6143126147987613417375041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4095417431991742278250027 6143126147987613417375041)
            ·
              refine ⟨4607344610990710063031281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6143126147987613417375041 4607344610990710063031281)
              ·
                refine ⟨3455508458243032547273461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4607344610990710063031281 3455508458243032547273461)
                ·
                  refine ⟨323953917960284301306887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3455508458243032547273461 323953917960284301306887)
                  ·
                    rfl

theorem cell23_5678082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_5678082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678082 prefixEnd_5678082 := by exact prefixLift 5678082
  have htrace : WordTrace (prefixWord ++ tailWord_5678082) baseStart_5678082 baseEnd_5678082 := by
    simpa [prefixWord, tailWord_5678082, baseEnd_5678082] using wordTrace_append hprefix tailTrace_5678082
  have hstable : (prefixWord ++ tailWord_5678082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678082).length < 2 ^ (prefixWord ++ tailWord_5678082).sum := by decide
  have hdescent : baseEnd_5678082 < baseStart_5678082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678091 : List Nat := [1, 1, 1, 1, 6, 3, 1, 4, 1, 4]
def baseStart_5678091 : Nat := 118140960795 + 5678091 * 2 ^ 59
def prefixEnd_5678091 : Nat := 4983230072969 + 3 ^ 40 * 5678091 * 2
def baseEnd_5678091 : Nat := 971863294322816392183147

theorem tailTrace_5678091 : CollatzResearch.WordTrace tailWord_5678091 prefixEnd_5678091 971863294322816392183147 := by
  unfold tailWord_5678091
  simp only [CollatzResearch.WordTrace]
  refine ⟨207096992472253522582906127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138064661648169015055270751 207096992472253522582906127)
  ·
    refine ⟨310645488708380283874359191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207096992472253522582906127 310645488708380283874359191)
    ·
      refine ⟨465968233062570425811538787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310645488708380283874359191 465968233062570425811538787)
      ·
        refine ⟨698952349593855638717308181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465968233062570425811538787 698952349593855638717308181)
        ·
          refine ⟨32763391387211983064873821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 698952349593855638717308181 32763391387211983064873821)
          ·
            refine ⟨12286271770204493649327683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32763391387211983064873821 12286271770204493649327683)
            ·
              refine ⟨18429407655306740473991525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12286271770204493649327683 18429407655306740473991525)
              ·
                refine ⟨3455513935370013838873411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18429407655306740473991525 3455513935370013838873411)
                ·
                  refine ⟨5183270903055020758310117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3455513935370013838873411 5183270903055020758310117)
                  ·
                    refine ⟨971863294322816392183147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5183270903055020758310117 971863294322816392183147)
                    ·
                      rfl

theorem cell23_5678091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 1, 4].length) (baseStart_5678091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678091 prefixEnd_5678091 := by exact prefixLift 5678091
  have htrace : WordTrace (prefixWord ++ tailWord_5678091) baseStart_5678091 baseEnd_5678091 := by
    simpa [prefixWord, tailWord_5678091, baseEnd_5678091] using wordTrace_append hprefix tailTrace_5678091
  have hstable : (prefixWord ++ tailWord_5678091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678091).length < 2 ^ (prefixWord ++ tailWord_5678091).sum := by decide
  have hdescent : baseEnd_5678091 < baseStart_5678091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678117 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 3, 5]
def baseStart_5678117 : Nat := 118140960795 + 5678117 * 2 ^ 59
def prefixEnd_5678117 : Nat := 4983230072969 + 3 ^ 40 * 5678117 * 2
def baseEnd_5678117 : Nat := 971867744488488691608107

theorem tailTrace_5678117 : CollatzResearch.WordTrace tailWord_5678117 prefixEnd_5678117 971867744488488691608107 := by
  unfold tailWord_5678117
  simp only [CollatzResearch.WordTrace]
  refine ⟨207097940770159329023352605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138065293846772886015568403 207097940770159329023352605)
  ·
    refine ⟨77661727788809748383757227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207097940770159329023352605 77661727788809748383757227)
    ·
      refine ⟨116492591683214622575635841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77661727788809748383757227 116492591683214622575635841)
      ·
        refine ⟨87369443762410966931726881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116492591683214622575635841 87369443762410966931726881)
        ·
          refine ⟨65527082821808225198795161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87369443762410966931726881 65527082821808225198795161)
          ·
            refine ⟨49145312116356168899096371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65527082821808225198795161 49145312116356168899096371)
            ·
              refine ⟨73717968174534253348644557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49145312116356168899096371 73717968174534253348644557)
              ·
                refine ⟨27644238065450345005741709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73717968174534253348644557 27644238065450345005741709)
                ·
                  refine ⟨10366589274543879377153141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27644238065450345005741709 10366589274543879377153141)
                  ·
                    refine ⟨971867744488488691608107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10366589274543879377153141 971867744488488691608107)
                    ·
                      rfl

theorem cell23_5678117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_5678117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678117 prefixEnd_5678117 := by exact prefixLift 5678117
  have htrace : WordTrace (prefixWord ++ tailWord_5678117) baseStart_5678117 baseEnd_5678117 := by
    simpa [prefixWord, tailWord_5678117, baseEnd_5678117] using wordTrace_append hprefix tailTrace_5678117
  have hstable : (prefixWord ++ tailWord_5678117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678117).length < 2 ^ (prefixWord ++ tailWord_5678117).sum := by decide
  have hdescent : baseEnd_5678117 < baseStart_5678117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678124 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 1, 5, 2]
def baseStart_5678124 : Nat := 118140960795 + 5678124 * 2 ^ 59
def prefixEnd_5678124 : Nat := 4983230072969 + 3 ^ 40 * 5678124 * 2
def baseEnd_5678124 : Nat := 2915606827830047547436789

theorem tailTrace_5678124 : CollatzResearch.WordTrace tailWord_5678124 prefixEnd_5678124 2915606827830047547436789 := by
  unfold tailWord_5678124
  simp only [CollatzResearch.WordTrace]
  refine ⟨103549098040566984609428713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138065464054089312812571617 103549098040566984609428713)
  ·
    refine ⟨77661823530425238457071535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103549098040566984609428713 77661823530425238457071535)
    ·
      refine ⟨116492735295637857685607303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77661823530425238457071535 116492735295637857685607303)
      ·
        refine ⟨174739102943456786528410955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116492735295637857685607303 174739102943456786528410955)
        ·
          refine ⟨262108654415185179792616433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174739102943456786528410955 262108654415185179792616433)
          ·
            refine ⟨196581490811388884844462325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262108654415185179792616433 196581490811388884844462325)
            ·
              refine ⟨18429514763567707954168343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 196581490811388884844462325 18429514763567707954168343)
              ·
                refine ⟨27644272145351561931252515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18429514763567707954168343 27644272145351561931252515)
                ·
                  refine ⟨41466408218027342896878773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27644272145351561931252515 41466408218027342896878773)
                  ·
                    refine ⟨3887475770440063396582385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41466408218027342896878773 3887475770440063396582385)
                    ·
                      refine ⟨2915606827830047547436789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3887475770440063396582385 2915606827830047547436789)
                      ·
                        rfl

theorem cell23_5678124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 5, 2].length) (baseStart_5678124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678124 prefixEnd_5678124 := by exact prefixLift 5678124
  have htrace : WordTrace (prefixWord ++ tailWord_5678124) baseStart_5678124 baseEnd_5678124 := by
    simpa [prefixWord, tailWord_5678124, baseEnd_5678124] using wordTrace_append hprefix tailTrace_5678124
  have hstable : (prefixWord ++ tailWord_5678124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678124).length < 2 ^ (prefixWord ++ tailWord_5678124).sum := by decide
  have hdescent : baseEnd_5678124 < baseStart_5678124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678164 : List Nat := [2, 4, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_5678164 : Nat := 118140960795 + 5678164 * 2 ^ 59
def prefixEnd_5678164 : Nat := 4983230072969 + 3 ^ 40 * 5678164 * 2
def baseEnd_5678164 : Nat := 971875789018742463645535

theorem tailTrace_5678164 : CollatzResearch.WordTrace tailWord_5678164 prefixEnd_5678164 971875789018742463645535 := by
  unfold tailWord_5678164
  simp only [CollatzResearch.WordTrace]
  refine ⟨103549827500494528025156773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138066436667326037366875697 103549827500494528025156773)
  ·
    refine ⟨19415592656342724004716895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103549827500494528025156773 19415592656342724004716895)
    ·
      refine ⟨29123388984514086007075343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19415592656342724004716895 29123388984514086007075343)
      ·
        refine ⟨43685083476771129010613015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29123388984514086007075343 43685083476771129010613015)
        ·
          refine ⟨65527625215156693515919523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43685083476771129010613015 65527625215156693515919523)
          ·
            refine ⟨98291437822735040273879285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65527625215156693515919523 98291437822735040273879285)
            ·
              refine ⟨9214822295881410025676183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98291437822735040273879285 9214822295881410025676183)
              ·
                refine ⟨13822233443822115038514275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9214822295881410025676183 13822233443822115038514275)
                ·
                  refine ⟨20733350165733172557771413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13822233443822115038514275 20733350165733172557771413)
                  ·
                    refine ⟨971875789018742463645535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20733350165733172557771413 971875789018742463645535)
                    ·
                      rfl

theorem cell23_5678164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_5678164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678164 prefixEnd_5678164 := by exact prefixLift 5678164
  have htrace : WordTrace (prefixWord ++ tailWord_5678164) baseStart_5678164 baseEnd_5678164 := by
    simpa [prefixWord, tailWord_5678164, baseEnd_5678164] using wordTrace_append hprefix tailTrace_5678164
  have hstable : (prefixWord ++ tailWord_5678164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678164).length < 2 ^ (prefixWord ++ tailWord_5678164).sum := by decide
  have hdescent : baseEnd_5678164 < baseStart_5678164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678238 : List Nat := [4, 3, 1, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_5678238 : Nat := 118140960795 + 5678238 * 2 ^ 59
def prefixEnd_5678238 : Nat := 4983230072969 + 3 ^ 40 * 5678238 * 2
def baseEnd_5678238 : Nat := 2915665364624660101411265

theorem tailTrace_5678238 : CollatzResearch.WordTrace tailWord_5678238 prefixEnd_5678238 2915665364624660101411265 := by
  unfold tailWord_5678238
  simp only [CollatzResearch.WordTrace]
  refine ⟨25887794250340120836063421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138068236001813977792338245 25887794250340120836063421)
  ·
    refine ⟨9707922843877545313523783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25887794250340120836063421 9707922843877545313523783)
    ·
      refine ⟨14561884265816317970285675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9707922843877545313523783 14561884265816317970285675)
      ·
        refine ⟨21842826398724476955428513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14561884265816317970285675 21842826398724476955428513)
        ·
          refine ⟨16382119799043357716571385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21842826398724476955428513 16382119799043357716571385)
          ·
            refine ⟨12286589849282518287428539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16382119799043357716571385 12286589849282518287428539)
            ·
              refine ⟨18429884773923777431142809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12286589849282518287428539 18429884773923777431142809)
              ·
                refine ⟨13822413580442833073357107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18429884773923777431142809 13822413580442833073357107)
                ·
                  refine ⟨20733620370664249610035661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13822413580442833073357107 20733620370664249610035661)
                  ·
                    refine ⟨7775107638999093603763373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20733620370664249610035661 7775107638999093603763373)
                    ·
                      refine ⟨2915665364624660101411265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7775107638999093603763373 2915665364624660101411265)
                      ·
                        rfl

theorem cell23_5678238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_5678238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678238 prefixEnd_5678238 := by exact prefixLift 5678238
  have htrace : WordTrace (prefixWord ++ tailWord_5678238) baseStart_5678238 baseEnd_5678238 := by
    simpa [prefixWord, tailWord_5678238, baseEnd_5678238] using wordTrace_append hprefix tailTrace_5678238
  have hstable : (prefixWord ++ tailWord_5678238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678238).length < 2 ^ (prefixWord ++ tailWord_5678238).sum := by decide
  have hdescent : baseEnd_5678238 < baseStart_5678238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678364 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_5678364 : Nat := 118140960795 + 5678364 * 2 ^ 59
def prefixEnd_5678364 : Nat := 4983230072969 + 3 ^ 40 * 5678364 * 2
def baseEnd_5678364 : Nat := 2915730063187126608435685

theorem tailTrace_5678364 : CollatzResearch.WordTrace tailWord_5678364 prefixEnd_5678364 2915730063187126608435685 := by
  unfold tailWord_5678364
  simp only [CollatzResearch.WordTrace]
  refine ⟨103553474800132245103797073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138071299733509660138396097 103553474800132245103797073)
  ·
    refine ⟨77665106100099183827847805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103553474800132245103797073 77665106100099183827847805)
    ·
      refine ⟨29124414787537193935442927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77665106100099183827847805 29124414787537193935442927)
      ·
        refine ⟨43686622181305790903164391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29124414787537193935442927 43686622181305790903164391)
        ·
          refine ⟨65529933271958686354746587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43686622181305790903164391 65529933271958686354746587)
          ·
            refine ⟨98294899907938029532119881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65529933271958686354746587 98294899907938029532119881)
            ·
              refine ⟨73721174930953522149089911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98294899907938029532119881 73721174930953522149089911)
              ·
                refine ⟨110581762396430283223634867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73721174930953522149089911 110581762396430283223634867)
                ·
                  refine ⟨165872643594645424835452301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110581762396430283223634867 165872643594645424835452301)
                  ·
                    refine ⟨62202241347992034313294613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165872643594645424835452301 62202241347992034313294613)
                    ·
                      refine ⟨2915730063187126608435685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62202241347992034313294613 2915730063187126608435685)
                      ·
                        rfl

theorem cell23_5678364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_5678364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678364 prefixEnd_5678364 := by exact prefixLift 5678364
  have htrace : WordTrace (prefixWord ++ tailWord_5678364) baseStart_5678364 baseEnd_5678364 := by
    simpa [prefixWord, tailWord_5678364, baseEnd_5678364] using wordTrace_append hprefix tailTrace_5678364
  have hstable : (prefixWord ++ tailWord_5678364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678364).length < 2 ^ (prefixWord ++ tailWord_5678364).sum := by decide
  have hdescent : baseEnd_5678364 < baseStart_5678364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678368 : List Nat := [2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 4]
def baseStart_5678368 : Nat := 118140960795 + 5678368 * 2 ^ 59
def prefixEnd_5678368 : Nat := 4983230072969 + 3 ^ 40 * 5678368 * 2
def baseEnd_5678368 : Nat := 2915732117109744592785667

theorem tailTrace_5678368 : CollatzResearch.WordTrace tailWord_5678368 prefixEnd_5678368 2915732117109744592785667 := by
  unfold tailWord_5678368
  simp only [CollatzResearch.WordTrace]
  refine ⟨103553547746124999445369879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138071396994833332593826505 103553547746124999445369879)
  ·
    refine ⟨155330321619187499168054819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103553547746124999445369879 155330321619187499168054819)
    ·
      refine ⟨232995482428781248752082229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155330321619187499168054819 232995482428781248752082229)
      ·
        refine ⟨21843326477698242070507709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 232995482428781248752082229 21843326477698242070507709)
        ·
          refine ⟨8191247429136840776440391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21843326477698242070507709 8191247429136840776440391)
          ·
            refine ⟨12286871143705261164660587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8191247429136840776440391 12286871143705261164660587)
            ·
              refine ⟨18430306715557891746990881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12286871143705261164660587 18430306715557891746990881)
              ·
                refine ⟨13822730036668418810243161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18430306715557891746990881 13822730036668418810243161)
                ·
                  refine ⟨10367047527501314107682371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13822730036668418810243161 10367047527501314107682371)
                  ·
                    refine ⟨15550571291251971161523557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10367047527501314107682371 15550571291251971161523557)
                    ·
                      refine ⟨2915732117109744592785667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15550571291251971161523557 2915732117109744592785667)
                      ·
                        rfl

theorem cell23_5678368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_5678368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678368 prefixEnd_5678368 := by exact prefixLift 5678368
  have htrace : WordTrace (prefixWord ++ tailWord_5678368) baseStart_5678368 baseEnd_5678368 := by
    simpa [prefixWord, tailWord_5678368, baseEnd_5678368] using wordTrace_append hprefix tailTrace_5678368
  have hstable : (prefixWord ++ tailWord_5678368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678368).length < 2 ^ (prefixWord ++ tailWord_5678368).sum := by decide
  have hdescent : baseEnd_5678368 < baseStart_5678368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678371 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 3]
def baseStart_5678371 : Nat := 118140960795 + 5678371 * 2 ^ 59
def prefixEnd_5678371 : Nat := 4983230072969 + 3 ^ 40 * 5678371 * 2
def baseEnd_5678371 : Nat := 2915733657551708081048153

theorem tailTrace_5678371 : CollatzResearch.WordTrace tailWord_5678371 prefixEnd_5678371 2915733657551708081048153 := by
  unfold tailWord_5678371
  simp only [CollatzResearch.WordTrace]
  refine ⟨207107204911239130403098967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138071469940826086935399311 207107204911239130403098967)
  ·
    refine ⟨310660807366858695604648451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207107204911239130403098967 310660807366858695604648451)
    ·
      refine ⟨465991211050288043406972677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310660807366858695604648451 465991211050288043406972677)
      ·
        refine ⟨87373352071929008138807377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 465991211050288043406972677 87373352071929008138807377)
        ·
          refine ⟨65530014053946756104105533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87373352071929008138807377 65530014053946756104105533)
          ·
            refine ⟨24573755270230033539039575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65530014053946756104105533 24573755270230033539039575)
            ·
              refine ⟨36860632905345050308559363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24573755270230033539039575 36860632905345050308559363)
              ·
                refine ⟨55290949358017575462839045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36860632905345050308559363 55290949358017575462839045)
                ·
                  refine ⟨10367053004628295399282321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55290949358017575462839045 10367053004628295399282321)
                  ·
                    refine ⟨7775289753471221549461741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10367053004628295399282321 7775289753471221549461741)
                    ·
                      refine ⟨2915733657551708081048153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7775289753471221549461741 2915733657551708081048153)
                      ·
                        rfl

theorem cell23_5678371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_5678371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678371 prefixEnd_5678371 := by exact prefixLift 5678371
  have htrace : WordTrace (prefixWord ++ tailWord_5678371) baseStart_5678371 baseEnd_5678371 := by
    simpa [prefixWord, tailWord_5678371, baseEnd_5678371] using wordTrace_append hprefix tailTrace_5678371
  have hstable : (prefixWord ++ tailWord_5678371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678371).length < 2 ^ (prefixWord ++ tailWord_5678371).sum := by decide
  have hdescent : baseEnd_5678371 < baseStart_5678371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678388 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_5678388 : Nat := 118140960795 + 5678388 * 2 ^ 59
def prefixEnd_5678388 : Nat := 4983230072969 + 3 ^ 40 * 5678388 * 2
def baseEnd_5678388 : Nat := 2915742386722834514535575

theorem tailTrace_5678388 : CollatzResearch.WordTrace tailWord_5678388 prefixEnd_5678388 2915742386722834514535575 := by
  unfold tailWord_5678388
  simp only [CollatzResearch.WordTrace]
  refine ⟨103553912476088771153233909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138071883301451694870978545 103553912476088771153233909)
  ·
    refine ⟨9708179294633322295615679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103553912476088771153233909 9708179294633322295615679)
    ·
      refine ⟨14562268941949983443423519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9708179294633322295615679 14562268941949983443423519)
      ·
        refine ⟨21843403412924975165135279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14562268941949983443423519 21843403412924975165135279)
        ·
          refine ⟨32765105119387462747702919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21843403412924975165135279 32765105119387462747702919)
          ·
            refine ⟨49147657679081194121554379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32765105119387462747702919 49147657679081194121554379)
            ·
              refine ⟨73721486518621791182331569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49147657679081194121554379 73721486518621791182331569)
              ·
                refine ⟨55291114888966343386748677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73721486518621791182331569 55291114888966343386748677)
                ·
                  refine ⟨10367084041681189385015377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55291114888966343386748677 10367084041681189385015377)
                  ·
                    refine ⟨7775313031260892038761533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10367084041681189385015377 7775313031260892038761533)
                    ·
                      refine ⟨2915742386722834514535575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7775313031260892038761533 2915742386722834514535575)
                      ·
                        rfl

theorem cell23_5678388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_5678388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678388 prefixEnd_5678388 := by exact prefixLift 5678388
  have htrace : WordTrace (prefixWord ++ tailWord_5678388) baseStart_5678388 baseEnd_5678388 := by
    simpa [prefixWord, tailWord_5678388, baseEnd_5678388] using wordTrace_append hprefix tailTrace_5678388
  have hstable : (prefixWord ++ tailWord_5678388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678388).length < 2 ^ (prefixWord ++ tailWord_5678388).sum := by decide
  have hdescent : baseEnd_5678388 < baseStart_5678388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678411 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 5, 5, 2]
def baseStart_5678411 : Nat := 118140960795 + 5678411 * 2 ^ 59
def prefixEnd_5678411 : Nat := 4983230072969 + 3 ^ 40 * 5678411 * 2
def baseEnd_5678411 : Nat := 2915754196777887924547969

theorem tailTrace_5678411 : CollatzResearch.WordTrace tailWord_5678411 prefixEnd_5678411 2915754196777887924547969 := by
  unfold tailWord_5678411
  simp only [CollatzResearch.WordTrace]
  refine ⟨207108663831094217234555087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138072442554062811489703391 207108663831094217234555087)
  ·
    refine ⟨310662995746641325851832631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207108663831094217234555087 310662995746641325851832631)
    ·
      refine ⟨465994493619961988777748947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310662995746641325851832631 465994493619961988777748947)
      ·
        refine ⟨698991740429942983166623421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465994493619961988777748947 698991740429942983166623421)
        ·
          refine ⟨262121902661228618687483783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 698991740429942983166623421 262121902661228618687483783)
          ·
            refine ⟨393182853991842928031225675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262121902661228618687483783 393182853991842928031225675)
            ·
              refine ⟨589774280987764392046838513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393182853991842928031225675 589774280987764392046838513)
              ·
                refine ⟨442330710740823294035128885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589774280987764392046838513 442330710740823294035128885)
                ·
                  refine ⟨41468504131952183815793333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 442330710740823294035128885 41468504131952183815793333)
                  ·
                    refine ⟨3887672262370517232730625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41468504131952183815793333 3887672262370517232730625)
                    ·
                      refine ⟨2915754196777887924547969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3887672262370517232730625 2915754196777887924547969)
                      ·
                        rfl

theorem cell23_5678411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 5, 2].length) (baseStart_5678411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678411 prefixEnd_5678411 := by exact prefixLift 5678411
  have htrace : WordTrace (prefixWord ++ tailWord_5678411) baseStart_5678411 baseEnd_5678411 := by
    simpa [prefixWord, tailWord_5678411, baseEnd_5678411] using wordTrace_append hprefix tailTrace_5678411
  have hstable : (prefixWord ++ tailWord_5678411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678411).length < 2 ^ (prefixWord ++ tailWord_5678411).sum := by decide
  have hdescent : baseEnd_5678411 < baseStart_5678411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678464 : List Nat := [2, 1, 1, 2, 1, 2, 1, 13]
def baseStart_5678464 : Nat := 118140960795 + 5678464 * 2 ^ 59
def prefixEnd_5678464 : Nat := 4983230072969 + 3 ^ 40 * 5678464 * 2
def baseEnd_5678464 : Nat := 107991904120465785821675

theorem tailTrace_5678464 : CollatzResearch.WordTrace tailWord_5678464 prefixEnd_5678464 107991904120465785821675 := by
  unfold tailWord_5678464
  simp only [CollatzResearch.WordTrace]
  refine ⟨103555298449951103643117223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138073731266601471524156297 103555298449951103643117223)
  ·
    refine ⟨155332947674926655464675835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103555298449951103643117223 155332947674926655464675835)
    ·
      refine ⟨232999421512389983197013753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155332947674926655464675835 232999421512389983197013753)
      ·
        refine ⟨174749566134292487397760315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232999421512389983197013753 174749566134292487397760315)
        ·
          refine ⟨262124349201438731096640473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174749566134292487397760315 262124349201438731096640473)
          ·
            refine ⟨196593261901079048322480355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262124349201438731096640473 196593261901079048322480355)
            ·
              refine ⟨294889892851618572483720533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196593261901079048322480355 294889892851618572483720533)
              ·
                refine ⟨107991904120465785821675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 294889892851618572483720533 107991904120465785821675)
                ·
                  rfl

theorem cell23_5678464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 13].length) (baseStart_5678464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678464 prefixEnd_5678464 := by exact prefixLift 5678464
  have htrace : WordTrace (prefixWord ++ tailWord_5678464) baseStart_5678464 baseEnd_5678464 := by
    simpa [prefixWord, tailWord_5678464, baseEnd_5678464] using wordTrace_append hprefix tailTrace_5678464
  have hstable : (prefixWord ++ tailWord_5678464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678464).length < 2 ^ (prefixWord ++ tailWord_5678464).sum := by decide
  have hdescent : baseEnd_5678464 < baseStart_5678464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678508 : List Nat := [2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 3]
def baseStart_5678508 : Nat := 118140960795 + 5678508 * 2 ^ 59
def prefixEnd_5678508 : Nat := 4983230072969 + 3 ^ 40 * 5678508 * 2
def baseEnd_5678508 : Nat := 2915804004401374045035023

theorem tailTrace_5678508 : CollatzResearch.WordTrace tailWord_5678508 prefixEnd_5678508 2915804004401374045035023 := by
  unfold tailWord_5678508
  simp only [CollatzResearch.WordTrace]
  refine ⟨103556100855871401400418089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138074801141161868533890785 103556100855871401400418089)
  ·
    refine ⟨77667075641903551050313567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103556100855871401400418089 77667075641903551050313567)
    ·
      refine ⟨116500613462855326575470351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77667075641903551050313567 116500613462855326575470351)
      ·
        refine ⟨174750920194282989863205527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116500613462855326575470351 174750920194282989863205527)
        ·
          refine ⟨262126380291424484794808291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174750920194282989863205527 262126380291424484794808291)
          ·
            refine ⟨393189570437136727192212437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262126380291424484794808291 393189570437136727192212437)
            ·
              refine ⟨9215380557120392043567479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 393189570437136727192212437 9215380557120392043567479)
              ·
                refine ⟨13823070835680588065351219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9215380557120392043567479 13823070835680588065351219)
                ·
                  refine ⟨20734606253520882098026829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13823070835680588065351219 20734606253520882098026829)
                  ·
                    refine ⟨7775477345070330786760061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20734606253520882098026829 7775477345070330786760061)
                    ·
                      refine ⟨2915804004401374045035023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7775477345070330786760061 2915804004401374045035023)
                      ·
                        rfl

theorem cell23_5678508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_5678508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678508 prefixEnd_5678508 := by exact prefixLift 5678508
  have htrace : WordTrace (prefixWord ++ tailWord_5678508) baseStart_5678508 baseEnd_5678508 := by
    simpa [prefixWord, tailWord_5678508, baseEnd_5678508] using wordTrace_append hprefix tailTrace_5678508
  have hstable : (prefixWord ++ tailWord_5678508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678508).length < 2 ^ (prefixWord ++ tailWord_5678508).sum := by decide
  have hdescent : baseEnd_5678508 < baseStart_5678508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678535 : List Nat := [1, 1, 4, 1, 1, 3, 1, 5, 1, 3, 2]
def baseStart_5678535 : Nat := 118140960795 + 5678535 * 2 ^ 59
def prefixEnd_5678535 : Nat := 4983230072969 + 3 ^ 40 * 5678535 * 2
def baseEnd_5678535 : Nat := 2915817868379045439397399

theorem tailTrace_5678535 : CollatzResearch.WordTrace tailWord_5678535 prefixEnd_5678535 2915817868379045439397399 := by
  unfold tailWord_5678535
  simp only [CollatzResearch.WordTrace]
  refine ⟨207113186482644986412069059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138075457655096657608046039 207113186482644986412069059)
  ·
    refine ⟨310669779723967479618103589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207113186482644986412069059 310669779723967479618103589)
    ·
      refine ⟨58250583698243902428394423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310669779723967479618103589 58250583698243902428394423)
      ·
        refine ⟨87375875547365853642591635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58250583698243902428394423 87375875547365853642591635)
        ·
          refine ⟨131063813321048780463887453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87375875547365853642591635 131063813321048780463887453)
          ·
            refine ⟨49148929995393292673957795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131063813321048780463887453 49148929995393292673957795)
            ·
              refine ⟨73723394993089939010936693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49148929995393292673957795 73723394993089939010936693)
              ·
                refine ⟨6911568280602181782275315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73723394993089939010936693 6911568280602181782275315)
                ·
                  refine ⟨10367352420903272673412973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6911568280602181782275315 10367352420903272673412973)
                  ·
                    refine ⟨3887757157838727252529865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10367352420903272673412973 3887757157838727252529865)
                    ·
                      refine ⟨2915817868379045439397399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3887757157838727252529865 2915817868379045439397399)
                      ·
                        rfl

theorem cell23_5678535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_5678535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678535 prefixEnd_5678535 := by exact prefixLift 5678535
  have htrace : WordTrace (prefixWord ++ tailWord_5678535) baseStart_5678535 baseEnd_5678535 := by
    simpa [prefixWord, tailWord_5678535, baseEnd_5678535] using wordTrace_append hprefix tailTrace_5678535
  have hstable : (prefixWord ++ tailWord_5678535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678535).length < 2 ^ (prefixWord ++ tailWord_5678535).sum := by decide
  have hdescent : baseEnd_5678535 < baseStart_5678535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
