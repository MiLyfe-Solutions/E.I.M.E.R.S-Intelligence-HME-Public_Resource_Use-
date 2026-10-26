import V185TrunkScan22Chunk050

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_457173 : List Nat := [1, 3, 2, 3, 1, 2, 1, 3, 1, 5]
def baseStart_457173 : Nat := 118140960795 + 457173 * 2 ^ 59
def prefixEnd_457173 : Nat := 4983230072969 + 3 ^ 40 * 457173 * 2
def baseEnd_457173 : Nat := 156499660838696694823337

theorem tailTrace_457173 : CollatzResearch.WordTrace tailWord_457173 prefixEnd_457173 156499660838696694823337 := by
  unfold tailWord_457173
  simp only [CollatzResearch.WordTrace]
  refine ⟨16674469172747774777328173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11116312781831849851552115 16674469172747774777328173)
  ·
    refine ⟨6252925939780415541498065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16674469172747774777328173 6252925939780415541498065)
    ·
      refine ⟨4689694454835311656123549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6252925939780415541498065 4689694454835311656123549)
      ·
        refine ⟨1758635420563241871046331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4689694454835311656123549 1758635420563241871046331)
        ·
          refine ⟨2637953130844862806569497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1758635420563241871046331 2637953130844862806569497)
          ·
            refine ⟨1978464848133647104927123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2637953130844862806569497 1978464848133647104927123)
            ·
              refine ⟨2967697272200470657390685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1978464848133647104927123 2967697272200470657390685)
              ·
                refine ⟨1112886477075176496521507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2967697272200470657390685 1112886477075176496521507)
                ·
                  refine ⟨1669329715612764744782261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1112886477075176496521507 1669329715612764744782261)
                  ·
                    refine ⟨156499660838696694823337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1669329715612764744782261 156499660838696694823337)
                    ·
                      rfl

theorem cell22_457173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_457173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457173 prefixEnd_457173 := by exact prefixLift 457173
  have htrace : WordTrace (prefixWord ++ tailWord_457173) baseStart_457173 baseEnd_457173 := by
    simpa [prefixWord, tailWord_457173, baseEnd_457173] using wordTrace_append hprefix tailTrace_457173
  have hstable : (prefixWord ++ tailWord_457173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457173).length < 2 ^ (prefixWord ++ tailWord_457173).sum := by decide
  have hdescent : baseEnd_457173 < baseStart_457173 := by decide
  rcases family_descends (prefixWord ++ tailWord_457173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457231 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 9]
def baseStart_457231 : Nat := 118140960795 + 457231 * 2 ^ 59
def prefixEnd_457231 : Nat := 4983230072969 + 3 ^ 40 * 457231 * 2
def baseEnd_457231 : Nat := 52173171808001292291053

theorem tailTrace_457231 : CollatzResearch.WordTrace tailWord_457231 prefixEnd_457231 52173171808001292291053 := by
  unfold tailWord_457231
  simp only [CollatzResearch.WordTrace]
  refine ⟨16676584606537650682939547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11117723071025100455293031 16676584606537650682939547)
  ·
    refine ⟨25014876909806476024409321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16676584606537650682939547 25014876909806476024409321)
    ·
      refine ⟨18761157682354857018306991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25014876909806476024409321 18761157682354857018306991)
      ·
        refine ⟨28141736523532285527460487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18761157682354857018306991 28141736523532285527460487)
        ·
          refine ⟨42212604785298428291190731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28141736523532285527460487 42212604785298428291190731)
          ·
            refine ⟨63318907177947642436786097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42212604785298428291190731 63318907177947642436786097)
            ·
              refine ⟨47489180383460731827589573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63318907177947642436786097 47489180383460731827589573)
              ·
                refine ⟨8904221321898887217673045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47489180383460731827589573 8904221321898887217673045)
                ·
                  refine ⟨52173171808001292291053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8904221321898887217673045 52173171808001292291053)
                  ·
                    rfl

theorem cell22_457231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 9].length) (baseStart_457231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457231 prefixEnd_457231 := by exact prefixLift 457231
  have htrace : WordTrace (prefixWord ++ tailWord_457231) baseStart_457231 baseEnd_457231 := by
    simpa [prefixWord, tailWord_457231, baseEnd_457231] using wordTrace_append hprefix tailTrace_457231
  have hstable : (prefixWord ++ tailWord_457231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457231).length < 2 ^ (prefixWord ++ tailWord_457231).sum := by decide
  have hdescent : baseEnd_457231 < baseStart_457231 := by decide
  rcases family_descends (prefixWord ++ tailWord_457231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457269 : List Nat := [1, 3, 3, 1, 1, 2, 5, 2, 1, 3]
def baseStart_457269 : Nat := 118140960795 + 457269 * 2 ^ 59
def prefixEnd_457269 : Nat := 4983230072969 + 3 ^ 40 * 457269 * 2
def baseEnd_457269 : Nat := 156532523600584444423043

theorem tailTrace_457269 : CollatzResearch.WordTrace tailWord_457269 prefixEnd_457269 156532523600584444423043 := by
  unfold tailWord_457269
  simp only [CollatzResearch.WordTrace]
  refine ⟨16677970580399983172822861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11118647053599988781881907 16677970580399983172822861)
  ·
    refine ⟨6254238967649993689808573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16677970580399983172822861 6254238967649993689808573)
    ·
      refine ⟨2345339612868747633678215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6254238967649993689808573 2345339612868747633678215)
      ·
        refine ⟨3518009419303121450517323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2345339612868747633678215 3518009419303121450517323)
        ·
          refine ⟨5277014128954682175775985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3518009419303121450517323 5277014128954682175775985)
          ·
            refine ⟨3957760596716011631831989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5277014128954682175775985 3957760596716011631831989)
            ·
              refine ⟨371040055942126090484249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3957760596716011631831989 371040055942126090484249)
              ·
                refine ⟨278280041956594567863187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371040055942126090484249 278280041956594567863187)
                ·
                  refine ⟨417420062934891851794781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278280041956594567863187 417420062934891851794781)
                  ·
                    refine ⟨156532523600584444423043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 417420062934891851794781 156532523600584444423043)
                    ·
                      rfl

theorem cell22_457269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_457269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457269 prefixEnd_457269 := by exact prefixLift 457269
  have htrace : WordTrace (prefixWord ++ tailWord_457269) baseStart_457269 baseEnd_457269 := by
    simpa [prefixWord, tailWord_457269, baseEnd_457269] using wordTrace_append hprefix tailTrace_457269
  have hstable : (prefixWord ++ tailWord_457269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457269).length < 2 ^ (prefixWord ++ tailWord_457269).sum := by decide
  have hdescent : baseEnd_457269 < baseStart_457269 := by decide
  rcases family_descends (prefixWord ++ tailWord_457269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457295 : List Nat := [1, 1, 2, 1, 1, 2, 7, 2, 1, 4]
def baseStart_457295 : Nat := 118140960795 + 457295 * 2 ^ 59
def prefixEnd_457295 : Nat := 4983230072969 + 3 ^ 40 * 457295 * 2
def baseEnd_457295 : Nat := 156541423931929043272963

theorem tailTrace_457295 : CollatzResearch.WordTrace tailWord_457295 prefixEnd_457295 156541423931929043272963 := by
  unfold tailWord_457295
  simp only [CollatzResearch.WordTrace]
  refine ⟨16678918878305789613269339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11119279252203859742179559 16678918878305789613269339)
  ·
    refine ⟨25018378317458684419904009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16678918878305789613269339 25018378317458684419904009)
    ·
      refine ⟨18763783738094013314928007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25018378317458684419904009 18763783738094013314928007)
      ·
        refine ⟨28145675607141019972392011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18763783738094013314928007 28145675607141019972392011)
        ·
          refine ⟨42218513410711529958588017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28145675607141019972392011 42218513410711529958588017)
          ·
            refine ⟨31663885058033647468941013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42218513410711529958588017 31663885058033647468941013)
            ·
              refine ⟨742122306047663612553305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 31663885058033647468941013 742122306047663612553305)
              ·
                refine ⟨556591729535747709414979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 742122306047663612553305 556591729535747709414979)
                ·
                  refine ⟨834887594303621564122469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556591729535747709414979 834887594303621564122469)
                  ·
                    refine ⟨156541423931929043272963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 834887594303621564122469 156541423931929043272963)
                    ·
                      rfl

theorem cell22_457295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 4].length) (baseStart_457295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457295 prefixEnd_457295 := by exact prefixLift 457295
  have htrace : WordTrace (prefixWord ++ tailWord_457295) baseStart_457295 baseEnd_457295 := by
    simpa [prefixWord, tailWord_457295, baseEnd_457295] using wordTrace_append hprefix tailTrace_457295
  have hstable : (prefixWord ++ tailWord_457295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457295).length < 2 ^ (prefixWord ++ tailWord_457295).sum := by decide
  have hdescent : baseEnd_457295 < baseStart_457295 := by decide
  rcases family_descends (prefixWord ++ tailWord_457295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457323 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 4, 4]
def baseStart_457323 : Nat := 118140960795 + 457323 * 2 ^ 59
def prefixEnd_457323 : Nat := 4983230072969 + 3 ^ 40 * 457323 * 2
def baseEnd_457323 : Nat := 156551008904146303572877

theorem tailTrace_457323 : CollatzResearch.WordTrace tailWord_457323 prefixEnd_457323 156551008904146303572877 := by
  unfold tailWord_457323
  simp only [CollatzResearch.WordTrace]
  refine ⟨16679940122204350395288623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11119960081469566930192415 16679940122204350395288623)
  ·
    refine ⟨25019910183306525592932935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16679940122204350395288623 25019910183306525592932935)
    ·
      refine ⟨37529865274959788389399403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25019910183306525592932935 37529865274959788389399403)
      ·
        refine ⟨56294797912439682584099105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37529865274959788389399403 56294797912439682584099105)
        ·
          refine ⟨42221098434329761938074329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56294797912439682584099105 42221098434329761938074329)
          ·
            refine ⟨31665823825747321453555747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42221098434329761938074329 31665823825747321453555747)
            ·
              refine ⟨47498735738620982180333621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31665823825747321453555747 47498735738620982180333621)
              ·
                refine ⟨4453006475495717079406277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47498735738620982180333621 4453006475495717079406277)
                ·
                  refine ⟨834938714155446952388677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4453006475495717079406277 834938714155446952388677)
                  ·
                    refine ⟨156551008904146303572877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 834938714155446952388677 156551008904146303572877)
                    ·
                      rfl

theorem cell22_457323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 4].length) (baseStart_457323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457323 prefixEnd_457323 := by exact prefixLift 457323
  have htrace : WordTrace (prefixWord ++ tailWord_457323) baseStart_457323 baseEnd_457323 := by
    simpa [prefixWord, tailWord_457323, baseEnd_457323] using wordTrace_append hprefix tailTrace_457323
  have hstable : (prefixWord ++ tailWord_457323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457323).length < 2 ^ (prefixWord ++ tailWord_457323).sum := by decide
  have hdescent : baseEnd_457323 < baseStart_457323 := by decide
  rcases family_descends (prefixWord ++ tailWord_457323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457327 : List Nat := [1, 1, 2, 1, 3, 2, 6, 2, 4]
def baseStart_457327 : Nat := 118140960795 + 457327 * 2 ^ 59
def prefixEnd_457327 : Nat := 4983230072969 + 3 ^ 40 * 457327 * 2
def baseEnd_457327 : Nat := 52184126061963875490955

theorem tailTrace_457327 : CollatzResearch.WordTrace tailWord_457327 prefixEnd_457327 52184126061963875490955 := by
  unfold tailWord_457327
  simp only [CollatzResearch.WordTrace]
  refine ⟨16680086014189859078434235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11120057342793239385622823 16680086014189859078434235)
  ·
    refine ⟨25020129021284788617651353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16680086014189859078434235 25020129021284788617651353)
    ·
      refine ⟨18765096765963591463238515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25020129021284788617651353 18765096765963591463238515)
      ·
        refine ⟨28147645148945387194857773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18765096765963591463238515 28147645148945387194857773)
        ·
          refine ⟨10555366930854520198071665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28147645148945387194857773 10555366930854520198071665)
          ·
            refine ⟨7916525198140890148553749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10555366930854520198071665 7916525198140890148553749)
            ·
              refine ⟨371087118662854225713457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7916525198140890148553749 371087118662854225713457)
              ·
                refine ⟨278315338997140669285093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371087118662854225713457 278315338997140669285093)
                ·
                  refine ⟨52184126061963875490955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 278315338997140669285093 52184126061963875490955)
                  ·
                    rfl

theorem cell22_457327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 4].length) (baseStart_457327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457327 prefixEnd_457327 := by exact prefixLift 457327
  have htrace : WordTrace (prefixWord ++ tailWord_457327) baseStart_457327 baseEnd_457327 := by
    simpa [prefixWord, tailWord_457327, baseEnd_457327] using wordTrace_append hprefix tailTrace_457327
  have hstable : (prefixWord ++ tailWord_457327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457327).length < 2 ^ (prefixWord ++ tailWord_457327).sum := by decide
  have hdescent : baseEnd_457327 < baseStart_457327 := by decide
  rcases family_descends (prefixWord ++ tailWord_457327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457376 : List Nat := [2, 1, 1, 4, 5, 1, 1, 2, 2, 3]
def baseStart_457376 : Nat := 118140960795 + 457376 * 2 ^ 59
def prefixEnd_457376 : Nat := 4983230072969 + 3 ^ 40 * 457376 * 2
def baseEnd_457376 : Nat := 156569151887271831997715

theorem tailTrace_457376 : CollatzResearch.WordTrace tailWord_457376 prefixEnd_457376 156569151887271831997715 := by
  unfold tailWord_457376
  simp only [CollatzResearch.WordTrace]
  refine ⟨8340936595506170223483991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11121248794008226964645321 8340936595506170223483991)
  ·
    refine ⟨12511404893259255335225987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8340936595506170223483991 12511404893259255335225987)
    ·
      refine ⟨18767107339888883002838981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12511404893259255335225987 18767107339888883002838981)
      ·
        refine ⟨3518832626229165563032309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18767107339888883002838981 3518832626229165563032309)
        ·
          refine ⟨329890558708984271534279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3518832626229165563032309 329890558708984271534279)
          ·
            refine ⟨494835838063476407301419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329890558708984271534279 494835838063476407301419)
            ·
              refine ⟨742253757095214610952129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494835838063476407301419 742253757095214610952129)
              ·
                refine ⟨556690317821410958214097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 742253757095214610952129 556690317821410958214097)
                ·
                  refine ⟨417517738366058218660573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556690317821410958214097 417517738366058218660573)
                  ·
                    refine ⟨156569151887271831997715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 417517738366058218660573 156569151887271831997715)
                    ·
                      rfl

theorem cell22_457376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 2, 3].length) (baseStart_457376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457376 prefixEnd_457376 := by exact prefixLift 457376
  have htrace : WordTrace (prefixWord ++ tailWord_457376) baseStart_457376 baseEnd_457376 := by
    simpa [prefixWord, tailWord_457376, baseEnd_457376] using wordTrace_append hprefix tailTrace_457376
  have hstable : (prefixWord ++ tailWord_457376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457376).length < 2 ^ (prefixWord ++ tailWord_457376).sum := by decide
  have hdescent : baseEnd_457376 < baseStart_457376 := by decide
  rcases family_descends (prefixWord ++ tailWord_457376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457552 : List Nat := [2, 1, 1, 1, 1, 4, 5, 2, 5]
def baseStart_457552 : Nat := 118140960795 + 457552 * 2 ^ 59
def prefixEnd_457552 : Nat := 4983230072969 + 3 ^ 40 * 457552 * 2
def baseEnd_457552 : Nat := 52209800094688679865725

theorem tailTrace_457552 : CollatzResearch.WordTrace tailWord_457552 prefixEnd_457552 52209800094688679865725 := by
  unfold tailWord_457552
  simp only [CollatzResearch.WordTrace]
  refine ⟨8344146219187361252687455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11125528292249815003583273 8344146219187361252687455)
  ·
    refine ⟨12516219328781041879031183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8344146219187361252687455 12516219328781041879031183)
    ·
      refine ⟨18774328993171562818546775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12516219328781041879031183 18774328993171562818546775)
      ·
        refine ⟨28161493489757344227820163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18774328993171562818546775 28161493489757344227820163)
        ·
          refine ⟨42242240234636016341730245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28161493489757344227820163 42242240234636016341730245)
          ·
            refine ⟨7920420043994253064074421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42242240234636016341730245 7920420043994253064074421)
            ·
              refine ⟨742539379124461224756977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7920420043994253064074421 742539379124461224756977)
              ·
                refine ⟨556904534343345918567733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 742539379124461224756977 556904534343345918567733)
                ·
                  refine ⟨52209800094688679865725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 556904534343345918567733 52209800094688679865725)
                  ·
                    rfl

theorem cell22_457552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 5].length) (baseStart_457552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457552 prefixEnd_457552 := by exact prefixLift 457552
  have htrace : WordTrace (prefixWord ++ tailWord_457552) baseStart_457552 baseEnd_457552 := by
    simpa [prefixWord, tailWord_457552, baseEnd_457552] using wordTrace_append hprefix tailTrace_457552
  have hstable : (prefixWord ++ tailWord_457552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457552).length < 2 ^ (prefixWord ++ tailWord_457552).sum := by decide
  have hdescent : baseEnd_457552 < baseStart_457552 := by decide
  rcases family_descends (prefixWord ++ tailWord_457552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457556 : List Nat := [2, 4, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_457556 : Nat := 118140960795 + 457556 * 2 ^ 59
def prefixEnd_457556 : Nat := 4983230072969 + 3 ^ 40 * 457556 * 2
def baseEnd_457556 : Nat := 156630769565811362497163

theorem tailTrace_457556 : CollatzResearch.WordTrace tailWord_457556 prefixEnd_457556 156630769565811362497163 := by
  unfold tailWord_457556
  simp only [CollatzResearch.WordTrace]
  refine ⟨8344219165180115594260261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11125625553573487459013681 8344219165180115594260261)
  ·
    refine ⟨1564541093471271673923799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8344219165180115594260261 1564541093471271673923799)
    ·
      refine ⟨2346811640206907510885699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1564541093471271673923799 2346811640206907510885699)
      ·
        refine ⟨3520217460310361266328549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2346811640206907510885699 3520217460310361266328549)
        ·
          refine ⟨660040773808192737436603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3520217460310361266328549 660040773808192737436603)
          ·
            refine ⟨990061160712289106154905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660040773808192737436603 990061160712289106154905)
            ·
              refine ⟨742545870534216829616179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 990061160712289106154905 742545870534216829616179)
              ·
                refine ⟨1113818805801325244424269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742545870534216829616179 1113818805801325244424269)
                ·
                  refine ⟨417682052175496966659101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1113818805801325244424269 417682052175496966659101)
                  ·
                    refine ⟨156630769565811362497163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 417682052175496966659101 156630769565811362497163)
                    ·
                      rfl

theorem cell22_457556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_457556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457556 prefixEnd_457556 := by exact prefixLift 457556
  have htrace : WordTrace (prefixWord ++ tailWord_457556) baseStart_457556 baseEnd_457556 := by
    simpa [prefixWord, tailWord_457556, baseEnd_457556] using wordTrace_append hprefix tailTrace_457556
  have hstable : (prefixWord ++ tailWord_457556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457556).length < 2 ^ (prefixWord ++ tailWord_457556).sum := by decide
  have hdescent : baseEnd_457556 < baseStart_457556 := by decide
  rcases family_descends (prefixWord ++ tailWord_457556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457590 : List Nat := [5, 1, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_457590 : Nat := 118140960795 + 457590 * 2 ^ 59
def prefixEnd_457590 : Nat := 4983230072969 + 3 ^ 40 * 457590 * 2
def baseEnd_457590 : Nat := 156642408460646607147059

theorem tailTrace_457590 : CollatzResearch.WordTrace tailWord_457590 prefixEnd_457590 156642408460646607147059 := by
  unfold tailWord_457590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1043104900764815937203639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11126452274824703330172149 1043104900764815937203639)
  ·
    refine ⟨1564657351147223905805459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1043104900764815937203639 1564657351147223905805459)
    ·
      refine ⟨2346986026720835858708189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1564657351147223905805459 2346986026720835858708189)
      ·
        refine ⟨880119760020313447015571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2346986026720835858708189 880119760020313447015571)
        ·
          refine ⟨1320179640030470170523357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880119760020313447015571 1320179640030470170523357)
          ·
            refine ⟨495067365011426313946259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1320179640030470170523357 495067365011426313946259)
            ·
              refine ⟨742601047517139470919389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495067365011426313946259 742601047517139470919389)
              ·
                refine ⟨278475392818927301594771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 742601047517139470919389 278475392818927301594771)
                ·
                  refine ⟨417713089228390952392157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278475392818927301594771 417713089228390952392157)
                  ·
                    refine ⟨156642408460646607147059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 417713089228390952392157 156642408460646607147059)
                    ·
                      rfl

theorem cell22_457590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_457590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457590 prefixEnd_457590 := by exact prefixLift 457590
  have htrace : WordTrace (prefixWord ++ tailWord_457590) baseStart_457590 baseEnd_457590 := by
    simpa [prefixWord, tailWord_457590, baseEnd_457590] using wordTrace_append hprefix tailTrace_457590
  have hstable : (prefixWord ++ tailWord_457590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457590).length < 2 ^ (prefixWord ++ tailWord_457590).sum := by decide
  have hdescent : baseEnd_457590 < baseStart_457590 := by decide
  rcases family_descends (prefixWord ++ tailWord_457590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457674 : List Nat := [3, 1, 2, 1, 2, 1, 1, 5, 3, 3]
def baseStart_457674 : Nat := 118140960795 + 457674 * 2 ^ 59
def prefixEnd_457674 : Nat := 4983230072969 + 3 ^ 40 * 457674 * 2
def baseEnd_457674 : Nat := 156671163377298388046801

theorem tailTrace_457674 : CollatzResearch.WordTrace tailWord_457674 prefixEnd_457674 156671163377298388046801 := by
  unfold tailWord_457674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4173185535983184335329019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11128494762621824894210717 4173185535983184335329019)
  ·
    refine ⟨6259778303974776502993529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4173185535983184335329019 6259778303974776502993529)
    ·
      refine ⟨4694833727981082377245147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6259778303974776502993529 4694833727981082377245147)
      ·
        refine ⟨7042250591971623565867721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4694833727981082377245147 7042250591971623565867721)
        ·
          refine ⟨5281687943978717674400791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7042250591971623565867721 5281687943978717674400791)
          ·
            refine ⟨7922531915968076511601187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5281687943978717674400791 7922531915968076511601187)
            ·
              refine ⟨11883797873952114767401781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7922531915968076511601187 11883797873952114767401781)
              ·
                refine ⟨1114106050683010759443917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11883797873952114767401781 1114106050683010759443917)
                ·
                  refine ⟨417789769006129034791469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114106050683010759443917 417789769006129034791469)
                  ·
                    refine ⟨156671163377298388046801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 417789769006129034791469 156671163377298388046801)
                    ·
                      rfl

theorem cell22_457674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_457674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457674 prefixEnd_457674 := by exact prefixLift 457674
  have htrace : WordTrace (prefixWord ++ tailWord_457674) baseStart_457674 baseEnd_457674 := by
    simpa [prefixWord, tailWord_457674, baseEnd_457674] using wordTrace_append hprefix tailTrace_457674
  have hstable : (prefixWord ++ tailWord_457674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457674).length < 2 ^ (prefixWord ++ tailWord_457674).sum := by decide
  have hdescent : baseEnd_457674 < baseStart_457674 := by decide
  rcases family_descends (prefixWord ++ tailWord_457674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457749 : List Nat := [1, 3, 2, 1, 4, 1, 2, 2, 6]
def baseStart_457749 : Nat := 118140960795 + 457749 * 2 ^ 59
def prefixEnd_457749 : Nat := 4983230072969 + 3 ^ 40 * 457749 * 2
def baseEnd_457749 : Nat := 52232279136674397473857

theorem tailTrace_457749 : CollatzResearch.WordTrace tailWord_457749 prefixEnd_457749 52232279136674397473857 := by
  unfold tailWord_457749
  simp only [CollatzResearch.WordTrace]
  refine ⟨16695477618661025150296301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11130318412440683433530867 16695477618661025150296301)
  ·
    refine ⟨6260804106997884431361113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16695477618661025150296301 6260804106997884431361113)
    ·
      refine ⟨4695603080248413323520835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6260804106997884431361113 4695603080248413323520835)
      ·
        refine ⟨7043404620372619985281253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4695603080248413323520835 7043404620372619985281253)
        ·
          refine ⟨1320638366319866247240235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7043404620372619985281253 1320638366319866247240235)
          ·
            refine ⟨1980957549479799370860353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320638366319866247240235 1980957549479799370860353)
            ·
              refine ⟨1485718162109849528145265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1980957549479799370860353 1485718162109849528145265)
              ·
                refine ⟨1114288621582387146108949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1485718162109849528145265 1114288621582387146108949)
                ·
                  refine ⟨52232279136674397473857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1114288621582387146108949 52232279136674397473857)
                  ·
                    rfl

theorem cell22_457749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_457749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457749 prefixEnd_457749 := by exact prefixLift 457749
  have htrace : WordTrace (prefixWord ++ tailWord_457749) baseStart_457749 baseEnd_457749 := by
    simpa [prefixWord, tailWord_457749, baseEnd_457749] using wordTrace_append hprefix tailTrace_457749
  have hstable : (prefixWord ++ tailWord_457749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457749).length < 2 ^ (prefixWord ++ tailWord_457749).sum := by decide
  have hdescent : baseEnd_457749 < baseStart_457749 := by decide
  rcases family_descends (prefixWord ++ tailWord_457749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457751 : List Nat := [1, 1, 3, 5, 1, 1, 1, 4, 1, 4]
def baseStart_457751 : Nat := 118140960795 + 457751 * 2 ^ 59
def prefixEnd_457751 : Nat := 4983230072969 + 3 ^ 40 * 457751 * 2
def baseEnd_457751 : Nat := 156697522050895853871565

theorem tailTrace_457751 : CollatzResearch.WordTrace tailWord_457751 prefixEnd_457751 156697522050895853871565 := by
  unfold tailWord_457751
  simp only [CollatzResearch.WordTrace]
  refine ⟨16695550564653779491869107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11130367043102519661246071 16695550564653779491869107)
  ·
    refine ⟨25043325846980669237803661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16695550564653779491869107 25043325846980669237803661)
    ·
      refine ⟨9391247192617750964176373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25043325846980669237803661 9391247192617750964176373)
      ·
        refine ⟨880429424307914152891535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9391247192617750964176373 880429424307914152891535)
        ·
          refine ⟨1320644136461871229337303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880429424307914152891535 1320644136461871229337303)
          ·
            refine ⟨1980966204692806844005955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320644136461871229337303 1980966204692806844005955)
            ·
              refine ⟨2971449307039210266008933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980966204692806844005955 2971449307039210266008933)
              ·
                refine ⟨557146745069851924876675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2971449307039210266008933 557146745069851924876675)
                ·
                  refine ⟨835720117604777887315013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 557146745069851924876675 835720117604777887315013)
                  ·
                    refine ⟨156697522050895853871565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 835720117604777887315013 156697522050895853871565)
                    ·
                      rfl

theorem cell22_457751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_457751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457751 prefixEnd_457751 := by exact prefixLift 457751
  have htrace : WordTrace (prefixWord ++ tailWord_457751) baseStart_457751 baseEnd_457751 := by
    simpa [prefixWord, tailWord_457751, baseEnd_457751] using wordTrace_append hprefix tailTrace_457751
  have hstable : (prefixWord ++ tailWord_457751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457751).length < 2 ^ (prefixWord ++ tailWord_457751).sum := by decide
  have hdescent : baseEnd_457751 < baseStart_457751 := by decide
  rcases family_descends (prefixWord ++ tailWord_457751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457781 : List Nat := [1, 3, 3, 1, 1, 1, 1, 6, 2, 3]
def baseStart_457781 : Nat := 118140960795 + 457781 * 2 ^ 59
def prefixEnd_457781 : Nat := 4983230072969 + 3 ^ 40 * 457781 * 2
def baseEnd_457781 : Nat := 156707791663985775621473

theorem tailTrace_457781 : CollatzResearch.WordTrace tailWord_457781 prefixEnd_457781 156707791663985775621473 := by
  unfold tailWord_457781
  simp only [CollatzResearch.WordTrace]
  refine ⟨16696644754545094615461197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11131096503030063076974131 16696644754545094615461197)
  ·
    refine ⟨6261241782954410480797949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16696644754545094615461197 6261241782954410480797949)
    ·
      refine ⟨2347965668607903930299231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6261241782954410480797949 2347965668607903930299231)
      ·
        refine ⟨3521948502911855895448847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2347965668607903930299231 3521948502911855895448847)
        ·
          refine ⟨5282922754367783843173271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3521948502911855895448847 5282922754367783843173271)
          ·
            refine ⟨7924384131551675764759907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5282922754367783843173271 7924384131551675764759907)
            ·
              refine ⟨11886576197327513647139861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7924384131551675764759907 11886576197327513647139861)
              ·
                refine ⟨557183259249727202209681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11886576197327513647139861 557183259249727202209681)
                ·
                  refine ⟨417887444437295401657261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557183259249727202209681 417887444437295401657261)
                  ·
                    refine ⟨156707791663985775621473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 417887444437295401657261 156707791663985775621473)
                    ·
                      rfl

theorem cell22_457781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_457781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457781 prefixEnd_457781 := by exact prefixLift 457781
  have htrace : WordTrace (prefixWord ++ tailWord_457781) baseStart_457781 baseEnd_457781 := by
    simpa [prefixWord, tailWord_457781, baseEnd_457781] using wordTrace_append hprefix tailTrace_457781
  have hstable : (prefixWord ++ tailWord_457781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457781).length < 2 ^ (prefixWord ++ tailWord_457781).sum := by decide
  have hdescent : baseEnd_457781 < baseStart_457781 := by decide
  rcases family_descends (prefixWord ++ tailWord_457781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457845 : List Nat := [1, 3, 4, 3, 2, 1, 1, 7]
def baseStart_457845 : Nat := 118140960795 + 457845 * 2 ^ 59
def prefixEnd_457845 : Nat := 4983230072969 + 3 ^ 40 * 457845 * 2
def baseEnd_457845 : Nat := 17414411130212326891253

theorem tailTrace_457845 : CollatzResearch.WordTrace tailWord_457845 prefixEnd_457845 17414411130212326891253 := by
  unfold tailWord_457845
  simp only [CollatzResearch.WordTrace]
  refine ⟨16698979026313233545790989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11132652684208822363860659 16698979026313233545790989)
  ·
    refine ⟨6262117134867462579671621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16698979026313233545790989 6262117134867462579671621)
    ·
      refine ⟨1174146962787649233688429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6262117134867462579671621 1174146962787649233688429)
      ·
        refine ⟨440305111045368462633161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1174146962787649233688429 440305111045368462633161)
        ·
          refine ⟨330228833284026346974871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440305111045368462633161 330228833284026346974871)
          ·
            refine ⟨495343249926039520462307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330228833284026346974871 495343249926039520462307)
            ·
              refine ⟨743014874889059280693461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495343249926039520462307 743014874889059280693461)
              ·
                refine ⟨17414411130212326891253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 743014874889059280693461 17414411130212326891253)
                ·
                  rfl

theorem cell22_457845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 7].length) (baseStart_457845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457845 prefixEnd_457845 := by exact prefixLift 457845
  have htrace : WordTrace (prefixWord ++ tailWord_457845) baseStart_457845 baseEnd_457845 := by
    simpa [prefixWord, tailWord_457845, baseEnd_457845] using wordTrace_append hprefix tailTrace_457845
  have hstable : (prefixWord ++ tailWord_457845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457845).length < 2 ^ (prefixWord ++ tailWord_457845).sum := by decide
  have hdescent : baseEnd_457845 < baseStart_457845 := by decide
  rcases family_descends (prefixWord ++ tailWord_457845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457890 : List Nat := [3, 3, 1, 3, 2, 2, 1, 2, 5]
def baseStart_457890 : Nat := 118140960795 + 457890 * 2 ^ 59
def prefixEnd_457890 : Nat := 4983230072969 + 3 ^ 40 * 457890 * 2
def baseEnd_457890 : Nat := 52248368197181941548713

theorem tailTrace_457890 : CollatzResearch.WordTrace tailWord_457890 prefixEnd_457890 52248368197181941548713 := by
  unfold tailWord_457890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4175155077787551557794781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11133746874100137487452749 4175155077787551557794781)
  ·
    refine ⟨1565683154170331834173043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4175155077787551557794781 1565683154170331834173043)
    ·
      refine ⟨2348524731255497751259565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1565683154170331834173043 2348524731255497751259565)
      ·
        refine ⟨880696774220811656722337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2348524731255497751259565 880696774220811656722337)
        ·
          refine ⟨660522580665608742541753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 880696774220811656722337 660522580665608742541753)
          ·
            refine ⟨495391935499206556906315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 660522580665608742541753 495391935499206556906315)
            ·
              refine ⟨743087903248809835359473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495391935499206556906315 743087903248809835359473)
              ·
                refine ⟨557315927436607376519605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 743087903248809835359473 557315927436607376519605)
                ·
                  refine ⟨52248368197181941548713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 557315927436607376519605 52248368197181941548713)
                  ·
                    rfl

theorem cell22_457890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_457890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457890 prefixEnd_457890 := by exact prefixLift 457890
  have htrace : WordTrace (prefixWord ++ tailWord_457890) baseStart_457890 baseEnd_457890 := by
    simpa [prefixWord, tailWord_457890, baseEnd_457890] using wordTrace_append hprefix tailTrace_457890
  have hstable : (prefixWord ++ tailWord_457890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457890).length < 2 ^ (prefixWord ++ tailWord_457890).sum := by decide
  have hdescent : baseEnd_457890 < baseStart_457890 := by decide
  rcases family_descends (prefixWord ++ tailWord_457890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457967 : List Nat := [1, 1, 2, 1, 7, 2, 2, 1, 2, 3]
def baseStart_457967 : Nat := 118140960795 + 457967 * 2 ^ 59
def prefixEnd_457967 : Nat := 4983230072969 + 3 ^ 40 * 457967 * 2
def baseEnd_457967 : Nat := 156771463265143290470903

theorem tailTrace_457967 : CollatzResearch.WordTrace tailWord_457967 prefixEnd_457967 156771463265143290470903 := by
  unfold tailWord_457967
  simp only [CollatzResearch.WordTrace]
  refine ⟨16703428731871248381732155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11135619154580832254488103 16703428731871248381732155)
  ·
    refine ⟨25055143097806872572598233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16703428731871248381732155 25055143097806872572598233)
    ·
      refine ⟨18791357323355154429448675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25055143097806872572598233 18791357323355154429448675)
      ·
        refine ⟨28187035985032731644173013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18791357323355154429448675 28187035985032731644173013)
        ·
          refine ⟨660633655899204647910305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 28187035985032731644173013 660633655899204647910305)
          ·
            refine ⟨495475241924403485932729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 660633655899204647910305 495475241924403485932729)
            ·
              refine ⟨371606431443302614449547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495475241924403485932729 371606431443302614449547)
              ·
                refine ⟨557409647164953921674321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371606431443302614449547 557409647164953921674321)
                ·
                  refine ⟨418057235373715441255741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557409647164953921674321 418057235373715441255741)
                  ·
                    refine ⟨156771463265143290470903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 418057235373715441255741 156771463265143290470903)
                    ·
                      rfl

theorem cell22_457967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 2, 3].length) (baseStart_457967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_457967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_457967 prefixEnd_457967 := by exact prefixLift 457967
  have htrace : WordTrace (prefixWord ++ tailWord_457967) baseStart_457967 baseEnd_457967 := by
    simpa [prefixWord, tailWord_457967, baseEnd_457967] using wordTrace_append hprefix tailTrace_457967
  have hstable : (prefixWord ++ tailWord_457967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457967).length < 2 ^ (prefixWord ++ tailWord_457967).sum := by decide
  have hdescent : baseEnd_457967 < baseStart_457967 := by decide
  rcases family_descends (prefixWord ++ tailWord_457967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458008 : List Nat := [2, 1, 2, 3, 1, 4, 2, 2, 5]
def baseStart_458008 : Nat := 118140960795 + 458008 * 2 ^ 59
def prefixEnd_458008 : Nat := 4983230072969 + 3 ^ 40 * 458008 * 2
def baseEnd_458008 : Nat := 52261832801010950065259

theorem tailTrace_458008 : CollatzResearch.WordTrace tailWord_458008 prefixEnd_458008 52261832801010950065259 := by
  unfold tailWord_458008
  simp only [CollatzResearch.WordTrace]
  refine ⟨8352462062361356191987339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11136616083148474922649785 8352462062361356191987339)
  ·
    refine ⟨12528693093542034287981009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8352462062361356191987339 12528693093542034287981009)
    ·
      refine ⟨9396519820156525715985757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12528693093542034287981009 9396519820156525715985757)
      ·
        refine ⟨3523694932558697143494659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9396519820156525715985757 3523694932558697143494659)
        ·
          refine ⟨5285542398838045715241989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3523694932558697143494659 5285542398838045715241989)
          ·
            refine ⟨991039199782133571607873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5285542398838045715241989 991039199782133571607873)
            ·
              refine ⟨743279399836600178705905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 991039199782133571607873 743279399836600178705905)
              ·
                refine ⟨557459549877450134029429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 743279399836600178705905 557459549877450134029429)
                ·
                  refine ⟨52261832801010950065259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 557459549877450134029429 52261832801010950065259)
                  ·
                    rfl

theorem cell22_458008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 5].length) (baseStart_458008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458008 prefixEnd_458008 := by exact prefixLift 458008
  have htrace : WordTrace (prefixWord ++ tailWord_458008) baseStart_458008 baseEnd_458008 := by
    simpa [prefixWord, tailWord_458008, baseEnd_458008] using wordTrace_append hprefix tailTrace_458008
  have hstable : (prefixWord ++ tailWord_458008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458008).length < 2 ^ (prefixWord ++ tailWord_458008).sum := by decide
  have hdescent : baseEnd_458008 < baseStart_458008 := by decide
  rcases family_descends (prefixWord ++ tailWord_458008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458012 : List Nat := [2, 2, 3, 1, 1, 1, 6, 2, 1, 3]
def baseStart_458012 : Nat := 118140960795 + 458012 * 2 ^ 59
def prefixEnd_458012 : Nat := 4983230072969 + 3 ^ 40 * 458012 * 2
def baseEnd_458012 : Nat := 156786867684778173095765

theorem tailTrace_458012 : CollatzResearch.WordTrace tailWord_458012 prefixEnd_458012 156786867684778173095765 := by
  unfold tailWord_458012
  simp only [CollatzResearch.WordTrace]
  refine ⟨8352535008354110533560145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11136713344472147378080193 8352535008354110533560145)
  ·
    refine ⟨6264401256265582900170109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8352535008354110533560145 6264401256265582900170109)
    ·
      refine ⟨2349150471099593587563791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6264401256265582900170109 2349150471099593587563791)
      ·
        refine ⟨3523725706649390381345687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2349150471099593587563791 3523725706649390381345687)
        ·
          refine ⟨5285588559974085572018531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3523725706649390381345687 5285588559974085572018531)
          ·
            refine ⟨7928382839961128358027797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5285588559974085572018531 7928382839961128358027797)
            ·
              refine ⟨371642945623177891782553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7928382839961128358027797 371642945623177891782553)
              ·
                refine ⟨278732209217383418836915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371642945623177891782553 278732209217383418836915)
                ·
                  refine ⟨418098313826075128255373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278732209217383418836915 418098313826075128255373)
                  ·
                    refine ⟨156786867684778173095765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 418098313826075128255373 156786867684778173095765)
                    ·
                      rfl

theorem cell22_458012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_458012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458012 prefixEnd_458012 := by exact prefixLift 458012
  have htrace : WordTrace (prefixWord ++ tailWord_458012) baseStart_458012 baseEnd_458012 := by
    simpa [prefixWord, tailWord_458012, baseEnd_458012] using wordTrace_append hprefix tailTrace_458012
  have hstable : (prefixWord ++ tailWord_458012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458012).length < 2 ^ (prefixWord ++ tailWord_458012).sum := by decide
  have hdescent : baseEnd_458012 < baseStart_458012 := by decide
  rcases family_descends (prefixWord ++ tailWord_458012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458055 : List Nat := [1, 1, 4, 1, 2, 3, 4, 1, 1, 4]
def baseStart_458055 : Nat := 118140960795 + 458055 * 2 ^ 59
def prefixEnd_458055 : Nat := 4983230072969 + 3 ^ 40 * 458055 * 2
def baseEnd_458055 : Nat := 156801587463540394270633

theorem tailTrace_458055 : CollatzResearch.WordTrace tailWord_458055 prefixEnd_458055 156801587463540394270633 := by
  unfold tailWord_458055
  simp only [CollatzResearch.WordTrace]
  refine ⟨16706638355552439410935619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11137758903701626273957079 16706638355552439410935619)
  ·
    refine ⟨25059957533328659116403429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16706638355552439410935619 25059957533328659116403429)
    ·
      refine ⟨4698742037499123584325643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25059957533328659116403429 4698742037499123584325643)
      ·
        refine ⟨7048113056248685376488465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4698742037499123584325643 7048113056248685376488465)
        ·
          refine ⟨5286084792186514032366349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7048113056248685376488465 5286084792186514032366349)
          ·
            refine ⟨1982281797069942762137381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5286084792186514032366349 1982281797069942762137381)
            ·
              refine ⟨371677836950614267900759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1982281797069942762137381 371677836950614267900759)
              ·
                refine ⟨557516755425921401851139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371677836950614267900759 557516755425921401851139)
                ·
                  refine ⟨836275133138882102776709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 557516755425921401851139 836275133138882102776709)
                  ·
                    refine ⟨156801587463540394270633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 836275133138882102776709 156801587463540394270633)
                    ·
                      rfl

theorem cell22_458055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_458055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458055 prefixEnd_458055 := by exact prefixLift 458055
  have htrace : WordTrace (prefixWord ++ tailWord_458055) baseStart_458055 baseEnd_458055 := by
    simpa [prefixWord, tailWord_458055, baseEnd_458055] using wordTrace_append hprefix tailTrace_458055
  have hstable : (prefixWord ++ tailWord_458055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458055).length < 2 ^ (prefixWord ++ tailWord_458055).sum := by decide
  have hdescent : baseEnd_458055 < baseStart_458055 := by decide
  rcases family_descends (prefixWord ++ tailWord_458055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458096 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 2, 7]
def baseStart_458096 : Nat := 118140960795 + 458096 * 2 ^ 59
def prefixEnd_458096 : Nat := 4983230072969 + 3 ^ 40 * 458096 * 2
def baseEnd_458096 : Nat := 156815622601429953995507

theorem tailTrace_458096 : CollatzResearch.WordTrace tailWord_458096 prefixEnd_458096 156815622601429953995507 := by
  unfold tailWord_458096
  simp only [CollatzResearch.WordTrace]
  refine ⟨8354066874201951706589071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11138755832269268942118761 8354066874201951706589071)
  ·
    refine ⟨12531100311302927559883607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8354066874201951706589071 12531100311302927559883607)
    ·
      refine ⟨18796650466954391339825411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12531100311302927559883607 18796650466954391339825411)
      ·
        refine ⟨28194975700431587009738117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18796650466954391339825411 28194975700431587009738117)
        ·
          refine ⟨5286557943830922564325897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28194975700431587009738117 5286557943830922564325897)
          ·
            refine ⟨3964918457873191923244423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5286557943830922564325897 3964918457873191923244423)
            ·
              refine ⟨5947377686809787884866635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964918457873191923244423 5947377686809787884866635)
              ·
                refine ⟨8921066530214681827299953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5947377686809787884866635 8921066530214681827299953)
                ·
                  refine ⟨6690799897661011370474965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8921066530214681827299953 6690799897661011370474965)
                  ·
                    refine ⟨156815622601429953995507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6690799897661011370474965 156815622601429953995507)
                    ·
                      rfl

theorem cell22_458096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_458096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458096 prefixEnd_458096 := by exact prefixLift 458096
  have htrace : WordTrace (prefixWord ++ tailWord_458096) baseStart_458096 baseEnd_458096 := by
    simpa [prefixWord, tailWord_458096, baseEnd_458096] using wordTrace_append hprefix tailTrace_458096
  have hstable : (prefixWord ++ tailWord_458096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458096).length < 2 ^ (prefixWord ++ tailWord_458096).sum := by decide
  have hdescent : baseEnd_458096 < baseStart_458096 := by decide
  rcases family_descends (prefixWord ++ tailWord_458096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458136 : List Nat := [2, 1, 2, 5, 3, 1, 2, 1, 2, 3]
def baseStart_458136 : Nat := 118140960795 + 458136 * 2 ^ 59
def prefixEnd_458136 : Nat := 4983230072969 + 3 ^ 40 * 458136 * 2
def baseEnd_458136 : Nat := 156829315418883182995385

theorem tailTrace_458136 : CollatzResearch.WordTrace tailWord_458136 prefixEnd_458136 156829315418883182995385 := by
  unfold tailWord_458136
  simp only [CollatzResearch.WordTrace]
  refine ⟨8354796334129495122317131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11139728445505993496422841 8354796334129495122317131)
  ·
    refine ⟨12532194501194242683475697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8354796334129495122317131 12532194501194242683475697)
    ·
      refine ⟨9399145875895682012606773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12532194501194242683475697 9399145875895682012606773)
      ·
        refine ⟨881169925865220188681885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9399145875895682012606773 881169925865220188681885)
        ·
          refine ⟨330438722199457570755707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 881169925865220188681885 330438722199457570755707)
          ·
            refine ⟨495658083299186356133561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330438722199457570755707 495658083299186356133561)
            ·
              refine ⟨371743562474389767100171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495658083299186356133561 371743562474389767100171)
              ·
                refine ⟨557615343711584650650257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371743562474389767100171 557615343711584650650257)
                ·
                  refine ⟨418211507783688487987693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557615343711584650650257 418211507783688487987693)
                  ·
                    refine ⟨156829315418883182995385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 418211507783688487987693 156829315418883182995385)
                    ·
                      rfl

theorem cell22_458136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 2, 3].length) (baseStart_458136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458136 prefixEnd_458136 := by exact prefixLift 458136
  have htrace : WordTrace (prefixWord ++ tailWord_458136) baseStart_458136 baseEnd_458136 := by
    simpa [prefixWord, tailWord_458136, baseEnd_458136] using wordTrace_append hprefix tailTrace_458136
  have hstable : (prefixWord ++ tailWord_458136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458136).length < 2 ^ (prefixWord ++ tailWord_458136).sum := by decide
  have hdescent : baseEnd_458136 < baseStart_458136 := by decide
  rcases family_descends (prefixWord ++ tailWord_458136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458205 : List Nat := [1, 4, 3, 1, 1, 3, 1, 2, 6]
def baseStart_458205 : Nat := 118140960795 + 458205 * 2 ^ 59
def prefixEnd_458205 : Nat := 4983230072969 + 3 ^ 40 * 458205 * 2
def baseEnd_458205 : Nat := 52284311842996667673391

theorem tailTrace_458205 : CollatzResearch.WordTrace tailWord_458205 prefixEnd_458205 52284311842996667673391 := by
  unfold tailWord_458205
  simp only [CollatzResearch.WordTrace]
  refine ⟨16712109305009015028896069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11141406203339343352597379 16712109305009015028896069)
  ·
    refine ⟨3133520494689190317918013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16712109305009015028896069 3133520494689190317918013)
    ·
      refine ⟨1175070185508446369219255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3133520494689190317918013 1175070185508446369219255)
      ·
        refine ⟨1762605278262669553828883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1175070185508446369219255 1762605278262669553828883)
        ·
          refine ⟨2643907917394004330743325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1762605278262669553828883 2643907917394004330743325)
          ·
            refine ⟨991465469022751624028747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2643907917394004330743325 991465469022751624028747)
            ·
              refine ⟨1487198203534127436043121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 991465469022751624028747 1487198203534127436043121)
              ·
                refine ⟨1115398652650595577032341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1487198203534127436043121 1115398652650595577032341)
                ·
                  refine ⟨52284311842996667673391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1115398652650595577032341 52284311842996667673391)
                  ·
                    rfl

theorem cell22_458205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_458205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458205 prefixEnd_458205 := by exact prefixLift 458205
  have htrace : WordTrace (prefixWord ++ tailWord_458205) baseStart_458205 baseEnd_458205 := by
    simpa [prefixWord, tailWord_458205, baseEnd_458205] using wordTrace_append hprefix tailTrace_458205
  have hstable : (prefixWord ++ tailWord_458205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458205).length < 2 ^ (prefixWord ++ tailWord_458205).sum := by decide
  have hdescent : baseEnd_458205 < baseStart_458205 := by decide
  rcases family_descends (prefixWord ++ tailWord_458205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458222 : List Nat := [4, 1, 2, 1, 2, 1, 4, 3, 4]
def baseStart_458222 : Nat := 118140960795 + 458222 * 2 ^ 59
def prefixEnd_458222 : Nat := 4983230072969 + 3 ^ 40 * 458222 * 2
def baseEnd_458222 : Nat := 52286251658802541781707

theorem tailTrace_458222 : CollatzResearch.WordTrace tailWord_458222 prefixEnd_458222 52286251658802541781707 := by
  unfold tailWord_458222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2089091168243428366533115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11141819563964951288176613 2089091168243428366533115)
  ·
    refine ⟨3133636752365142549799673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2089091168243428366533115 3133636752365142549799673)
    ·
      refine ⟨2350227564273856912349755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3133636752365142549799673 2350227564273856912349755)
      ·
        refine ⟨3525341346410785368524633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2350227564273856912349755 3525341346410785368524633)
        ·
          refine ⟨2644006009808089026393475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3525341346410785368524633 2644006009808089026393475)
          ·
            refine ⟨3966009014712133539590213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2644006009808089026393475 3966009014712133539590213)
            ·
              refine ⟨743626690258525038673165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3966009014712133539590213 743626690258525038673165)
              ·
                refine ⟨278860008846946889502437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 743626690258525038673165 278860008846946889502437)
                ·
                  refine ⟨52286251658802541781707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 278860008846946889502437 52286251658802541781707)
                  ·
                    rfl

theorem cell22_458222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_458222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458222 prefixEnd_458222 := by exact prefixLift 458222
  have htrace : WordTrace (prefixWord ++ tailWord_458222) baseStart_458222 baseEnd_458222 := by
    simpa [prefixWord, tailWord_458222, baseEnd_458222] using wordTrace_append hprefix tailTrace_458222
  have hstable : (prefixWord ++ tailWord_458222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458222).length < 2 ^ (prefixWord ++ tailWord_458222).sum := by decide
  have hdescent : baseEnd_458222 < baseStart_458222 := by decide
  rcases family_descends (prefixWord ++ tailWord_458222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458237 : List Nat := [1, 4, 1, 1, 1, 4, 3, 2, 2, 3]
def baseStart_458237 : Nat := 118140960795 + 458237 * 2 ^ 59
def prefixEnd_458237 : Nat := 4983230072969 + 3 ^ 40 * 458237 * 2
def baseEnd_458237 : Nat := 156863889782952586220075

theorem tailTrace_458237 : CollatzResearch.WordTrace tailWord_458237 prefixEnd_458237 156863889782952586220075 := by
  unfold tailWord_458237
  simp only [CollatzResearch.WordTrace]
  refine ⟨16713276440893084494060965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11142184293928722996040643 16713276440893084494060965)
  ·
    refine ⟨3133739332667453342636431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16713276440893084494060965 3133739332667453342636431)
    ·
      refine ⟨4700608999001180013954647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3133739332667453342636431 4700608999001180013954647)
      ·
        refine ⟨7050913498501770020931971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4700608999001180013954647 7050913498501770020931971)
        ·
          refine ⟨10576370247752655031397957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7050913498501770020931971 10576370247752655031397957)
          ·
            refine ⟨1983069421453622818387117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10576370247752655031397957 1983069421453622818387117)
            ·
              refine ⟨743651033045108556895169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1983069421453622818387117 743651033045108556895169)
              ·
                refine ⟨557738274783831417671377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 743651033045108556895169 557738274783831417671377)
                ·
                  refine ⟨418303706087873563253533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 557738274783831417671377 418303706087873563253533)
                  ·
                    refine ⟨156863889782952586220075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 418303706087873563253533 156863889782952586220075)
                    ·
                      rfl

theorem cell22_458237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_458237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458237 prefixEnd_458237 := by exact prefixLift 458237
  have htrace : WordTrace (prefixWord ++ tailWord_458237) baseStart_458237 baseEnd_458237 := by
    simpa [prefixWord, tailWord_458237, baseEnd_458237] using wordTrace_append hprefix tailTrace_458237
  have hstable : (prefixWord ++ tailWord_458237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458237).length < 2 ^ (prefixWord ++ tailWord_458237).sum := by decide
  have hdescent : baseEnd_458237 < baseStart_458237 := by decide
  rcases family_descends (prefixWord ++ tailWord_458237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458254 : List Nat := [4, 1, 1, 2, 5, 1, 1, 1, 1, 5]
def baseStart_458254 : Nat := 118140960795 + 458254 * 2 ^ 59
def prefixEnd_458254 : Nat := 4983230072969 + 3 ^ 40 * 458254 * 2
def baseEnd_458254 : Nat := 156869709230370208545023

theorem tailTrace_458254 : CollatzResearch.WordTrace tailWord_458254 prefixEnd_458254 156869709230370208545023 := by
  unfold tailWord_458254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2089237060228937049678727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11142597654554330931619877 2089237060228937049678727)
  ·
    refine ⟨3133855590343405574518091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2089237060228937049678727 3133855590343405574518091)
    ·
      refine ⟨4700783385515108361777137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3133855590343405574518091 4700783385515108361777137)
      ·
        refine ⟨3525587539136331271332853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4700783385515108361777137 3525587539136331271332853)
        ·
          refine ⟨330523831794031056687455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3525587539136331271332853 330523831794031056687455)
          ·
            refine ⟨495785747691046585031183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330523831794031056687455 495785747691046585031183)
            ·
              refine ⟨743678621536569877546775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495785747691046585031183 743678621536569877546775)
              ·
                refine ⟨1115517932304854816320163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 743678621536569877546775 1115517932304854816320163)
                ·
                  refine ⟨1673276898457282224480245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115517932304854816320163 1673276898457282224480245)
                  ·
                    refine ⟨156869709230370208545023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1673276898457282224480245 156869709230370208545023)
                    ·
                      rfl

theorem cell22_458254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_458254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458254 prefixEnd_458254 := by exact prefixLift 458254
  have htrace : WordTrace (prefixWord ++ tailWord_458254) baseStart_458254 baseEnd_458254 := by
    simpa [prefixWord, tailWord_458254, baseEnd_458254] using wordTrace_append hprefix tailTrace_458254
  have hstable : (prefixWord ++ tailWord_458254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458254).length < 2 ^ (prefixWord ++ tailWord_458254).sum := by decide
  have hdescent : baseEnd_458254 < baseStart_458254 := by decide
  rcases family_descends (prefixWord ++ tailWord_458254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458350 : List Nat := [4, 1, 2, 2, 4, 1, 2, 2, 1, 3]
def baseStart_458350 : Nat := 118140960795 + 458350 * 2 ^ 59
def prefixEnd_458350 : Nat := 4983230072969 + 3 ^ 40 * 458350 * 2
def baseEnd_458350 : Nat := 156902571992257958144729

theorem tailTrace_458350 : CollatzResearch.WordTrace tailWord_458350 prefixEnd_458350 156902571992257958144729 := by
  unfold tailWord_458350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2089674736185463099115563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11144931926322469861949669 2089674736185463099115563)
  ·
    refine ⟨3134512104278194648673345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2089674736185463099115563 3134512104278194648673345)
    ·
      refine ⟨2350884078208645986505009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3134512104278194648673345 2350884078208645986505009)
      ·
        refine ⟨1763163058656484489878757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2350884078208645986505009 1763163058656484489878757)
        ·
          refine ⟨330593073498090841852267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1763163058656484489878757 330593073498090841852267)
          ·
            refine ⟨495889610247136262778401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330593073498090841852267 495889610247136262778401)
            ·
              refine ⟨371917207685352197083801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495889610247136262778401 371917207685352197083801)
              ·
                refine ⟨278937905764014147812851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371917207685352197083801 278937905764014147812851)
                ·
                  refine ⟨418406858646021221719277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278937905764014147812851 418406858646021221719277)
                  ·
                    refine ⟨156902571992257958144729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 418406858646021221719277 156902571992257958144729)
                    ·
                      rfl

theorem cell22_458350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_458350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458350 prefixEnd_458350 := by exact prefixLift 458350
  have htrace : WordTrace (prefixWord ++ tailWord_458350) baseStart_458350 baseEnd_458350 := by
    simpa [prefixWord, tailWord_458350, baseEnd_458350] using wordTrace_append hprefix tailTrace_458350
  have hstable : (prefixWord ++ tailWord_458350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458350).length < 2 ^ (prefixWord ++ tailWord_458350).sum := by decide
  have hdescent : baseEnd_458350 < baseStart_458350 := by decide
  rcases family_descends (prefixWord ++ tailWord_458350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458355 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 8, 3]
def baseStart_458355 : Nat := 118140960795 + 458355 * 2 ^ 59
def prefixEnd_458355 : Nat := 4983230072969 + 3 ^ 40 * 458355 * 2
def baseEnd_458355 : Nat := 156904283594439611769713

theorem tailTrace_458355 : CollatzResearch.WordTrace tailWord_458355 prefixEnd_458355 156904283594439611769713 := by
  unfold tailWord_458355
  simp only [CollatzResearch.WordTrace]
  refine ⟨16717580254465590646856519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11145053502977060431237679 16717580254465590646856519)
  ·
    refine ⟨25076370381698385970284779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16717580254465590646856519 25076370381698385970284779)
    ·
      refine ⟨37614555572547578955427169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25076370381698385970284779 37614555572547578955427169)
      ·
        refine ⟨28210916679410684216570377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37614555572547578955427169 28210916679410684216570377)
        ·
          refine ⟨21158187509558013162427783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28210916679410684216570377 21158187509558013162427783)
          ·
            refine ⟨31737281264337019743641675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21158187509558013162427783 31737281264337019743641675)
            ·
              refine ⟨47605921896505529615462513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31737281264337019743641675 47605921896505529615462513)
              ·
                refine ⟨35704441422379147211596885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47605921896505529615462513 35704441422379147211596885)
                ·
                  refine ⟨418411422918505631385901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35704441422379147211596885 418411422918505631385901)
                  ·
                    refine ⟨156904283594439611769713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 418411422918505631385901 156904283594439611769713)
                    ·
                      rfl

theorem cell22_458355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 3].length) (baseStart_458355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458355 prefixEnd_458355 := by exact prefixLift 458355
  have htrace : WordTrace (prefixWord ++ tailWord_458355) baseStart_458355 baseEnd_458355 := by
    simpa [prefixWord, tailWord_458355, baseEnd_458355] using wordTrace_append hprefix tailTrace_458355
  have hstable : (prefixWord ++ tailWord_458355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458355).length < 2 ^ (prefixWord ++ tailWord_458355).sum := by decide
  have hdescent : baseEnd_458355 < baseStart_458355 := by decide
  rcases family_descends (prefixWord ++ tailWord_458355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458507 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 6, 3]
def baseStart_458507 : Nat := 118140960795 + 458507 * 2 ^ 59
def prefixEnd_458507 : Nat := 4983230072969 + 3 ^ 40 * 458507 * 2
def baseEnd_458507 : Nat := 156956316300761881969247

theorem tailTrace_458507 : CollatzResearch.WordTrace tailWord_458507 prefixEnd_458507 156956316300761881969247 := by
  unfold tailWord_458507
  simp only [CollatzResearch.WordTrace]
  refine ⟨16723124149914920606389775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11148749433276613737593183 16723124149914920606389775)
  ·
    refine ⟨25084686224872380909584663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16723124149914920606389775 25084686224872380909584663)
    ·
      refine ⟨37627029337308571364376995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25084686224872380909584663 37627029337308571364376995)
      ·
        refine ⟨56440544005962857046565493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37627029337308571364376995 56440544005962857046565493)
        ·
          refine ⟨5291301000559017848115515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56440544005962857046565493 5291301000559017848115515)
          ·
            refine ⟨7936951500838526772173273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5291301000559017848115515 7936951500838526772173273)
            ·
              refine ⟨5952713625628895079129955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7936951500838526772173273 5952713625628895079129955)
              ·
                refine ⟨8929070438443342618694933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5952713625628895079129955 8929070438443342618694933)
                ·
                  refine ⟨418550176802031685251325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8929070438443342618694933 418550176802031685251325)
                  ·
                    refine ⟨156956316300761881969247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 418550176802031685251325 156956316300761881969247)
                    ·
                      rfl

theorem cell22_458507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 3].length) (baseStart_458507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458507 prefixEnd_458507 := by exact prefixLift 458507
  have htrace : WordTrace (prefixWord ++ tailWord_458507) baseStart_458507 baseEnd_458507 := by
    simpa [prefixWord, tailWord_458507, baseEnd_458507] using wordTrace_append hprefix tailTrace_458507
  have hstable : (prefixWord ++ tailWord_458507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458507).length < 2 ^ (prefixWord ++ tailWord_458507).sum := by decide
  have hdescent : baseEnd_458507 < baseStart_458507 := by decide
  rcases family_descends (prefixWord ++ tailWord_458507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458554 : List Nat := [3, 1, 1, 1, 5, 2, 3, 6]
def baseStart_458554 : Nat := 118140960795 + 458554 * 2 ^ 59
def prefixEnd_458554 : Nat := 4983230072969 + 3 ^ 40 * 458554 * 2
def baseEnd_458554 : Nat := 17441378373474380671567

theorem tailTrace_458554 : CollatzResearch.WordTrace tailWord_458554 prefixEnd_458554 17441378373474380671567 := by
  unfold tailWord_458554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4181209595186161908337679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11149892253829765088900477 4181209595186161908337679)
  ·
    refine ⟨6271814392779242862506519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4181209595186161908337679 6271814392779242862506519)
    ·
      refine ⟨9407721589168864293759779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6271814392779242862506519 9407721589168864293759779)
      ·
        refine ⟨14111582383753296440639669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9407721589168864293759779 14111582383753296440639669)
        ·
          refine ⟨1322960848476871541309969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14111582383753296440639669 1322960848476871541309969)
          ·
            refine ⟨992220636357653655982477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1322960848476871541309969 992220636357653655982477)
            ·
              refine ⟨372082738634120120993429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 992220636357653655982477 372082738634120120993429)
              ·
                refine ⟨17441378373474380671567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 372082738634120120993429 17441378373474380671567)
                ·
                  rfl

theorem cell22_458554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 6].length) (baseStart_458554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458554 prefixEnd_458554 := by exact prefixLift 458554
  have htrace : WordTrace (prefixWord ++ tailWord_458554) baseStart_458554 baseEnd_458554 := by
    simpa [prefixWord, tailWord_458554, baseEnd_458554] using wordTrace_append hprefix tailTrace_458554
  have hstable : (prefixWord ++ tailWord_458554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458554).length < 2 ^ (prefixWord ++ tailWord_458554).sum := by decide
  have hdescent : baseEnd_458554 < baseStart_458554 := by decide
  rcases family_descends (prefixWord ++ tailWord_458554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458586 : List Nat := [3, 1, 1, 2, 1, 3, 1, 6, 1, 3]
def baseStart_458586 : Nat := 118140960795 + 458586 * 2 ^ 59
def prefixEnd_458586 : Nat := 4983230072969 + 3 ^ 40 * 458586 * 2
def baseEnd_458586 : Nat := 156983359615232009244005

theorem tailTrace_458586 : CollatzResearch.WordTrace tailWord_458586 prefixEnd_458586 156983359615232009244005 := by
  unfold tailWord_458586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4181501379157179274628903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11150670344419144732343741 4181501379157179274628903)
  ·
    refine ⟨6272252068735768911943355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4181501379157179274628903 6272252068735768911943355)
    ·
      refine ⟨9408378103103653367915033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6272252068735768911943355 9408378103103653367915033)
      ·
        refine ⟨7056283577327740025936275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9408378103103653367915033 7056283577327740025936275)
        ·
          refine ⟨10584425365991610038904413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7056283577327740025936275 10584425365991610038904413)
          ·
            refine ⟨3969159512246853764589155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10584425365991610038904413 3969159512246853764589155)
            ·
              refine ⟨5953739268370280646883733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3969159512246853764589155 5953739268370280646883733)
              ·
                refine ⟨279081528204856905322675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5953739268370280646883733 279081528204856905322675)
                ·
                  refine ⟨418622292307285357984013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279081528204856905322675 418622292307285357984013)
                  ·
                    refine ⟨156983359615232009244005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 418622292307285357984013 156983359615232009244005)
                    ·
                      rfl

theorem cell22_458586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 1, 3].length) (baseStart_458586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458586 prefixEnd_458586 := by exact prefixLift 458586
  have htrace : WordTrace (prefixWord ++ tailWord_458586) baseStart_458586 baseEnd_458586 := by
    simpa [prefixWord, tailWord_458586, baseEnd_458586] using wordTrace_append hprefix tailTrace_458586
  have hstable : (prefixWord ++ tailWord_458586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458586).length < 2 ^ (prefixWord ++ tailWord_458586).sum := by decide
  have hdescent : baseEnd_458586 < baseStart_458586 := by decide
  rcases family_descends (prefixWord ++ tailWord_458586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458629 : List Nat := [1, 3, 1, 1, 3, 2, 1, 5, 1, 4]
def baseStart_458629 : Nat := 118140960795 + 458629 * 2 ^ 59
def prefixEnd_458629 : Nat := 4983230072969 + 3 ^ 40 * 458629 * 2
def baseEnd_458629 : Nat := 156998079393994230418873

theorem tailTrace_458629 : CollatzResearch.WordTrace tailWord_458629 prefixEnd_458629 156998079393994230418873 := by
  unfold tailWord_458629
  simp only [CollatzResearch.WordTrace]
  refine ⟨16727573855472935442330941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11151715903648623628220627 16727573855472935442330941)
  ·
    refine ⟨6272840195802350790874103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16727573855472935442330941 6272840195802350790874103)
    ·
      refine ⟨9409260293703526186311155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6272840195802350790874103 9409260293703526186311155)
      ·
        refine ⟨14113890440555289279466733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9409260293703526186311155 14113890440555289279466733)
        ·
          refine ⟨5292708915208233479800025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14113890440555289279466733 5292708915208233479800025)
          ·
            refine ⟨3969531686406175109850019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5292708915208233479800025 3969531686406175109850019)
            ·
              refine ⟨5954297529609262664775029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3969531686406175109850019 5954297529609262664775029)
              ·
                refine ⟨558215393400868374822659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5954297529609262664775029 558215393400868374822659)
                ·
                  refine ⟨837323090101302562233989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 558215393400868374822659 837323090101302562233989)
                  ·
                    refine ⟨156998079393994230418873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 837323090101302562233989 156998079393994230418873)
                    ·
                      rfl

theorem cell22_458629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_458629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458629 prefixEnd_458629 := by exact prefixLift 458629
  have htrace : WordTrace (prefixWord ++ tailWord_458629) baseStart_458629 baseEnd_458629 := by
    simpa [prefixWord, tailWord_458629, baseEnd_458629] using wordTrace_append hprefix tailTrace_458629
  have hstable : (prefixWord ++ tailWord_458629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458629).length < 2 ^ (prefixWord ++ tailWord_458629).sum := by decide
  have hdescent : baseEnd_458629 < baseStart_458629 := by decide
  rcases family_descends (prefixWord ++ tailWord_458629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458663 : List Nat := [1, 1, 6, 1, 2, 3, 1, 2, 1, 4]
def baseStart_458663 : Nat := 118140960795 + 458663 * 2 ^ 59
def prefixEnd_458663 : Nat := 4983230072969 + 3 ^ 40 * 458663 * 2
def baseEnd_458663 : Nat := 157009718288829475068769

theorem tailTrace_458663 : CollatzResearch.WordTrace tailWord_458663 prefixEnd_458663 157009718288829475068769 := by
  unfold tailWord_458663
  simp only [CollatzResearch.WordTrace]
  refine ⟨16728813937349759249068643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11152542624899839499379095 16728813937349759249068643)
  ·
    refine ⟨25093220906024638873602965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16728813937349759249068643 25093220906024638873602965)
    ·
      refine ⟨1176244729969904947200139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25093220906024638873602965 1176244729969904947200139)
      ·
        refine ⟨1764367094954857420800209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176244729969904947200139 1764367094954857420800209)
        ·
          refine ⟨1323275321216143065600157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1764367094954857420800209 1323275321216143065600157)
          ·
            refine ⟨496228245456053649600059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1323275321216143065600157 496228245456053649600059)
            ·
              refine ⟨744342368184080474400089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496228245456053649600059 744342368184080474400089)
              ·
                refine ⟨558256776138060355800067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 744342368184080474400089 558256776138060355800067)
                ·
                  refine ⟨837385164207090533700101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 558256776138060355800067 837385164207090533700101)
                  ·
                    refine ⟨157009718288829475068769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 837385164207090533700101 157009718288829475068769)
                    ·
                      rfl

theorem cell22_458663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_458663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458663 prefixEnd_458663 := by exact prefixLift 458663
  have htrace : WordTrace (prefixWord ++ tailWord_458663) baseStart_458663 baseEnd_458663 := by
    simpa [prefixWord, tailWord_458663, baseEnd_458663] using wordTrace_append hprefix tailTrace_458663
  have hstable : (prefixWord ++ tailWord_458663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458663).length < 2 ^ (prefixWord ++ tailWord_458663).sum := by decide
  have hdescent : baseEnd_458663 < baseStart_458663 := by decide
  rcases family_descends (prefixWord ++ tailWord_458663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458749 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_458749 : Nat := 118140960795 + 458749 * 2 ^ 59
def prefixEnd_458749 : Nat := 4983230072969 + 3 ^ 40 * 458749 * 2
def baseEnd_458749 : Nat := 157039157846353917418505

theorem tailTrace_458749 : CollatzResearch.WordTrace tailWord_458749 prefixEnd_458749 157039157846353917418505 := by
  unfold tailWord_458749
  simp only [CollatzResearch.WordTrace]
  refine ⟨16731950615038195936699301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11154633743358797291132867 16731950615038195936699301)
  ·
    refine ⟨3137240740319661738131119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16731950615038195936699301 3137240740319661738131119)
    ·
      refine ⟨4705861110479492607196679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3137240740319661738131119 4705861110479492607196679)
      ·
        refine ⟨7058791665719238910795019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4705861110479492607196679 7058791665719238910795019)
        ·
          refine ⟨10588187498578858366192529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7058791665719238910795019 10588187498578858366192529)
          ·
            refine ⟨7941140623934143774644397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10588187498578858366192529 7941140623934143774644397)
            ·
              refine ⟨2977927733975303915491649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7941140623934143774644397 2977927733975303915491649)
              ·
                refine ⟨2233445800481477936618737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2977927733975303915491649 2233445800481477936618737)
                ·
                  refine ⟨1675084350361108452464053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2233445800481477936618737 1675084350361108452464053)
                  ·
                    refine ⟨157039157846353917418505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1675084350361108452464053 157039157846353917418505)
                    ·
                      rfl

theorem cell22_458749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_458749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458749 prefixEnd_458749 := by exact prefixLift 458749
  have htrace : WordTrace (prefixWord ++ tailWord_458749) baseStart_458749 baseEnd_458749 := by
    simpa [prefixWord, tailWord_458749, baseEnd_458749] using wordTrace_append hprefix tailTrace_458749
  have hstable : (prefixWord ++ tailWord_458749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458749).length < 2 ^ (prefixWord ++ tailWord_458749).sum := by decide
  have hdescent : baseEnd_458749 < baseStart_458749 := by decide
  rcases family_descends (prefixWord ++ tailWord_458749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458796 : List Nat := [2, 2, 1, 1, 1, 2, 2, 7, 4]
def baseStart_458796 : Nat := 118140960795 + 458796 * 2 ^ 59
def prefixEnd_458796 : Nat := 4983230072969 + 3 ^ 40 * 458796 * 2
def baseEnd_458796 : Nat := 52351748968953820497787

theorem tailTrace_458796 : CollatzResearch.WordTrace tailWord_458796 prefixEnd_458796 52351748968953820497787 := by
  unfold tailWord_458796
  simp only [CollatzResearch.WordTrace]
  refine ⟨8366832422933961481830121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11155776563911948642440161 8366832422933961481830121)
  ·
    refine ⟨6275124317200471111372591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8366832422933961481830121 6275124317200471111372591)
    ·
      refine ⟨9412686475800706667058887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6275124317200471111372591 9412686475800706667058887)
      ·
        refine ⟨14119029713701060000588331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9412686475800706667058887 14119029713701060000588331)
        ·
          refine ⟨21178544570551590000882497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14119029713701060000588331 21178544570551590000882497)
          ·
            refine ⟨15883908427913692500661873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21178544570551590000882497 15883908427913692500661873)
            ·
              refine ⟨11912931320935269375496405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15883908427913692500661873 11912931320935269375496405)
              ·
                refine ⟨279209327834420375988197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11912931320935269375496405 279209327834420375988197)
                ·
                  refine ⟨52351748968953820497787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 279209327834420375988197 52351748968953820497787)
                  ·
                    rfl

theorem cell22_458796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_458796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458796 prefixEnd_458796 := by exact prefixLift 458796
  have htrace : WordTrace (prefixWord ++ tailWord_458796) baseStart_458796 baseEnd_458796 := by
    simpa [prefixWord, tailWord_458796, baseEnd_458796] using wordTrace_append hprefix tailTrace_458796
  have hstable : (prefixWord ++ tailWord_458796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458796).length < 2 ^ (prefixWord ++ tailWord_458796).sum := by decide
  have hdescent : baseEnd_458796 < baseStart_458796 := by decide
  rcases family_descends (prefixWord ++ tailWord_458796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458798 : List Nat := [4, 1, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_458798 : Nat := 118140960795 + 458798 * 2 ^ 59
def prefixEnd_458798 : Nat := 4983230072969 + 3 ^ 40 * 458798 * 2
def baseEnd_458798 : Nat := 157055931547734122943355

theorem tailTrace_458798 : CollatzResearch.WordTrace tailWord_458798 prefixEnd_458798 157055931547734122943355 := by
  unfold tailWord_458798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2091717223982584663154131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11155825194573784870155365 2091717223982584663154131)
  ·
    refine ⟨3137575835973876994731197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2091717223982584663154131 3137575835973876994731197)
    ·
      refine ⟨1176590938490203873024199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3137575835973876994731197 1176590938490203873024199)
      ·
        refine ⟨1764886407735305809536299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176590938490203873024199 1764886407735305809536299)
        ·
          refine ⟨2647329611602958714304449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1764886407735305809536299 2647329611602958714304449)
          ·
            refine ⟨1985497208702219035728337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2647329611602958714304449 1985497208702219035728337)
            ·
              refine ⟨1489122906526664276796253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1985497208702219035728337 1489122906526664276796253)
              ·
                refine ⟨558421089947499103798595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1489122906526664276796253 558421089947499103798595)
                ·
                  refine ⟨837631634921248655697893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 558421089947499103798595 837631634921248655697893)
                  ·
                    refine ⟨157055931547734122943355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 837631634921248655697893 157055931547734122943355)
                    ·
                      rfl

theorem cell22_458798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_458798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458798 prefixEnd_458798 := by exact prefixLift 458798
  have htrace : WordTrace (prefixWord ++ tailWord_458798) baseStart_458798 baseEnd_458798 := by
    simpa [prefixWord, tailWord_458798, baseEnd_458798] using wordTrace_append hprefix tailTrace_458798
  have hstable : (prefixWord ++ tailWord_458798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458798).length < 2 ^ (prefixWord ++ tailWord_458798).sum := by decide
  have hdescent : baseEnd_458798 < baseStart_458798 := by decide
  rcases family_descends (prefixWord ++ tailWord_458798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458839 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 2, 7]
def baseStart_458839 : Nat := 118140960795 + 458839 * 2 ^ 59
def prefixEnd_458839 : Nat := 4983230072969 + 3 ^ 40 * 458839 * 2
def baseEnd_458839 : Nat := 157069966685623682668229

theorem tailTrace_458839 : CollatzResearch.WordTrace tailWord_458839 prefixEnd_458839 157069966685623682668229 := by
  unfold tailWord_458839
  simp only [CollatzResearch.WordTrace]
  refine ⟨16735233184712141307475571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11156822123141427538317047 16735233184712141307475571)
  ·
    refine ⟨25102849777068211961213357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16735233184712141307475571 25102849777068211961213357)
    ·
      refine ⟨9413568666400579485455009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25102849777068211961213357 9413568666400579485455009)
      ·
        refine ⟨7060176499800434614091257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9413568666400579485455009 7060176499800434614091257)
        ·
          refine ⟨5295132374850325960568443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7060176499800434614091257 5295132374850325960568443)
          ·
            refine ⟨7942698562275488940852665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5295132374850325960568443 7942698562275488940852665)
            ·
              refine ⟨5957023921706616705639499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7942698562275488940852665 5957023921706616705639499)
              ·
                refine ⟨8935535882559925058459249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5957023921706616705639499 8935535882559925058459249)
                ·
                  refine ⟨6701651911919943793844437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8935535882559925058459249 6701651911919943793844437)
                  ·
                    refine ⟨157069966685623682668229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6701651911919943793844437 157069966685623682668229)
                    ·
                      rfl

theorem cell22_458839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_458839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458839 prefixEnd_458839 := by exact prefixLift 458839
  have htrace : WordTrace (prefixWord ++ tailWord_458839) baseStart_458839 baseEnd_458839 := by
    simpa [prefixWord, tailWord_458839, baseEnd_458839] using wordTrace_append hprefix tailTrace_458839
  have hstable : (prefixWord ++ tailWord_458839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458839).length < 2 ^ (prefixWord ++ tailWord_458839).sum := by decide
  have hdescent : baseEnd_458839 < baseStart_458839 := by decide
  rcases family_descends (prefixWord ++ tailWord_458839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458948 : List Nat := [2, 3, 3, 1, 2, 1, 2, 2, 6]
def baseStart_458948 : Nat := 118140960795 + 458948 * 2 ^ 59
def prefixEnd_458948 : Nat := 4983230072969 + 3 ^ 40 * 458948 * 2
def baseEnd_458948 : Nat := 52369093204394577230965

theorem tailTrace_458948 : CollatzResearch.WordTrace tailWord_458948 prefixEnd_458948 52369093204394577230965 := by
  unfold tailWord_458948
  simp only [CollatzResearch.WordTrace]
  refine ⟨8369604370658626461596749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11159472494211501948795665 8369604370658626461596749)
  ·
    refine ⟨3138601638996984923098781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8369604370658626461596749 3138601638996984923098781)
    ·
      refine ⟨1176975614623869346162043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3138601638996984923098781 1176975614623869346162043)
      ·
        refine ⟨1765463421935804019243065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176975614623869346162043 1765463421935804019243065)
        ·
          refine ⟨1324097566451853014432299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1765463421935804019243065 1324097566451853014432299)
          ·
            refine ⟨1986146349677779521648449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324097566451853014432299 1986146349677779521648449)
            ·
              refine ⟨1489609762258334641236337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1986146349677779521648449 1489609762258334641236337)
              ·
                refine ⟨1117207321693750980927253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1489609762258334641236337 1117207321693750980927253)
                ·
                  refine ⟨52369093204394577230965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1117207321693750980927253 52369093204394577230965)
                  ·
                    rfl

theorem cell22_458948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_458948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458948 prefixEnd_458948 := by exact prefixLift 458948
  have htrace : WordTrace (prefixWord ++ tailWord_458948) baseStart_458948 baseEnd_458948 := by
    simpa [prefixWord, tailWord_458948, baseEnd_458948] using wordTrace_append hprefix tailTrace_458948
  have hstable : (prefixWord ++ tailWord_458948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458948).length < 2 ^ (prefixWord ++ tailWord_458948).sum := by decide
  have hdescent : baseEnd_458948 < baseStart_458948 := by decide
  rcases family_descends (prefixWord ++ tailWord_458948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458961 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 1, 6]
def baseStart_458961 : Nat := 118140960795 + 458961 * 2 ^ 59
def prefixEnd_458961 : Nat := 4983230072969 + 3 ^ 40 * 458961 * 2
def baseEnd_458961 : Nat := 157111729778856031117855

theorem tailTrace_458961 : CollatzResearch.WordTrace tailWord_458961 prefixEnd_458961 157111729778856031117855 := by
  unfold tailWord_458961
  simp only [CollatzResearch.WordTrace]
  refine ⟨16739682890270156143416737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11159788593513437428944491 16739682890270156143416737)
  ·
    refine ⟨12554762167702617107562553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16739682890270156143416737 12554762167702617107562553)
    ·
      refine ⟨9416071625776962830671915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12554762167702617107562553 9416071625776962830671915)
      ·
        refine ⟨14124107438665444246007873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9416071625776962830671915 14124107438665444246007873)
        ·
          refine ⟨10593080578999083184505905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14124107438665444246007873 10593080578999083184505905)
          ·
            refine ⟨7944810434249312388379429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10593080578999083184505905 7944810434249312388379429)
            ·
              refine ⟨1489651956421746072821143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7944810434249312388379429 1489651956421746072821143)
              ·
                refine ⟨2234477934632619109231715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1489651956421746072821143 2234477934632619109231715)
                ·
                  refine ⟨3351716901948928663847573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234477934632619109231715 3351716901948928663847573)
                  ·
                    refine ⟨157111729778856031117855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3351716901948928663847573 157111729778856031117855)
                    ·
                      rfl

theorem cell22_458961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_458961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_458961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_458961 prefixEnd_458961 := by exact prefixLift 458961
  have htrace : WordTrace (prefixWord ++ tailWord_458961) baseStart_458961 baseEnd_458961 := by
    simpa [prefixWord, tailWord_458961, baseEnd_458961] using wordTrace_append hprefix tailTrace_458961
  have hstable : (prefixWord ++ tailWord_458961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458961).length < 2 ^ (prefixWord ++ tailWord_458961).sum := by decide
  have hdescent : baseEnd_458961 < baseStart_458961 := by decide
  rcases family_descends (prefixWord ++ tailWord_458961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459008 : List Nat := [2, 1, 1, 2, 1, 1, 4, 4, 3, 3]
def baseStart_459008 : Nat := 118140960795 + 459008 * 2 ^ 59
def prefixEnd_459008 : Nat := 4983230072969 + 3 ^ 40 * 459008 * 2
def baseEnd_459008 : Nat := 157127818839363575192711

theorem tailTrace_459008 : CollatzResearch.WordTrace tailWord_459008 prefixEnd_459008 157127818839363575192711 := by
  unfold tailWord_459008
  simp only [CollatzResearch.WordTrace]
  refine ⟨8370698560549941585188839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11160931414066588780251785 8370698560549941585188839)
  ·
    refine ⟨12556047840824912377783259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8370698560549941585188839 12556047840824912377783259)
    ·
      refine ⟨18834071761237368566674889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12556047840824912377783259 18834071761237368566674889)
      ·
        refine ⟨14125553820928026425006167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18834071761237368566674889 14125553820928026425006167)
        ·
          refine ⟨21188330731392039637509251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14125553820928026425006167 21188330731392039637509251)
          ·
            refine ⟨31782496097088059456263877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21188330731392039637509251 31782496097088059456263877)
            ·
              refine ⟨5959218018204011148049477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31782496097088059456263877 5959218018204011148049477)
              ·
                refine ⟨1117353378413252090259277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5959218018204011148049477 1117353378413252090259277)
                ·
                  refine ⟨419007516904969533847229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1117353378413252090259277 419007516904969533847229)
                  ·
                    refine ⟨157127818839363575192711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 419007516904969533847229 157127818839363575192711)
                    ·
                      rfl

theorem cell22_459008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 3, 3].length) (baseStart_459008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459008 prefixEnd_459008 := by exact prefixLift 459008
  have htrace : WordTrace (prefixWord ++ tailWord_459008) baseStart_459008 baseEnd_459008 := by
    simpa [prefixWord, tailWord_459008, baseEnd_459008] using wordTrace_append hprefix tailTrace_459008
  have hstable : (prefixWord ++ tailWord_459008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459008).length < 2 ^ (prefixWord ++ tailWord_459008).sum := by decide
  have hdescent : baseEnd_459008 < baseStart_459008 := by decide
  rcases family_descends (prefixWord ++ tailWord_459008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459068 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 3, 4]
def baseStart_459068 : Nat := 118140960795 + 459068 * 2 ^ 59
def prefixEnd_459068 : Nat := 4983230072969 + 3 ^ 40 * 459068 * 2
def baseEnd_459068 : Nat := 157148358065543418692527

theorem tailTrace_459068 : CollatzResearch.WordTrace tailWord_459068 prefixEnd_459068 157148358065543418692527 := by
  unfold tailWord_459068
  simp only [CollatzResearch.WordTrace]
  refine ⟨8371792750441256708780929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11162390333921675611707905 8371792750441256708780929)
  ·
    refine ⟨6278844562830942531585697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8371792750441256708780929 6278844562830942531585697)
    ·
      refine ⟨4709133422123206898689273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6278844562830942531585697 4709133422123206898689273)
      ·
        refine ⟨3531850066592405174016955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4709133422123206898689273 3531850066592405174016955)
        ·
          refine ⟨5297775099888607761025433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531850066592405174016955 5297775099888607761025433)
          ·
            refine ⟨3973331324916455820769075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5297775099888607761025433 3973331324916455820769075)
            ·
              refine ⟨5959996987374683731153613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3973331324916455820769075 5959996987374683731153613)
              ·
                refine ⟨2234998870265506399182605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5959996987374683731153613 2234998870265506399182605)
                ·
                  refine ⟨838124576349564899693477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2234998870265506399182605 838124576349564899693477)
                  ·
                    refine ⟨157148358065543418692527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 838124576349564899693477 157148358065543418692527)
                    ·
                      rfl

theorem cell22_459068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_459068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459068 prefixEnd_459068 := by exact prefixLift 459068
  have htrace : WordTrace (prefixWord ++ tailWord_459068) baseStart_459068 baseEnd_459068 := by
    simpa [prefixWord, tailWord_459068, baseEnd_459068] using wordTrace_append hprefix tailTrace_459068
  have hstable : (prefixWord ++ tailWord_459068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459068).length < 2 ^ (prefixWord ++ tailWord_459068).sum := by decide
  have hdescent : baseEnd_459068 < baseStart_459068 := by decide
  rcases family_descends (prefixWord ++ tailWord_459068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459076 : List Nat := [2, 3, 4, 1, 2, 1, 2, 3, 1, 3]
def baseStart_459076 : Nat := 118140960795 + 459076 * 2 ^ 59
def prefixEnd_459076 : Nat := 4983230072969 + 3 ^ 40 * 459076 * 2
def baseEnd_459076 : Nat := 157151096629034064492503

theorem tailTrace_459076 : CollatzResearch.WordTrace tailWord_459076 prefixEnd_459076 157151096629034064492503 := by
  unfold tailWord_459076
  simp only [CollatzResearch.WordTrace]
  refine ⟨8371938642426765391926541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11162584856569020522568721 8371938642426765391926541)
  ·
    refine ⟨3139476990910037021972453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8371938642426765391926541 3139476990910037021972453)
    ·
      refine ⟨588651935795631941619835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3139476990910037021972453 588651935795631941619835)
      ·
        refine ⟨882977903693447912429753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588651935795631941619835 882977903693447912429753)
        ·
          refine ⟨662233427770085934322315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 882977903693447912429753 662233427770085934322315)
          ·
            refine ⟨993350141655128901483473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662233427770085934322315 993350141655128901483473)
            ·
              refine ⟨745012606241346676112605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 993350141655128901483473 745012606241346676112605)
              ·
                refine ⟨279379727340505003542227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 745012606241346676112605 279379727340505003542227)
                ·
                  refine ⟨419069591010757505313341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279379727340505003542227 419069591010757505313341)
                  ·
                    refine ⟨157151096629034064492503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 419069591010757505313341 157151096629034064492503)
                    ·
                      rfl

theorem cell22_459076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_459076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459076 prefixEnd_459076 := by exact prefixLift 459076
  have htrace : WordTrace (prefixWord ++ tailWord_459076) baseStart_459076 baseEnd_459076 := by
    simpa [prefixWord, tailWord_459076, baseEnd_459076] using wordTrace_append hprefix tailTrace_459076
  have hstable : (prefixWord ++ tailWord_459076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459076).length < 2 ^ (prefixWord ++ tailWord_459076).sum := by decide
  have hdescent : baseEnd_459076 < baseStart_459076 := by decide
  rcases family_descends (prefixWord ++ tailWord_459076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459166 : List Nat := [4, 3, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_459166 : Nat := 118140960795 + 459166 * 2 ^ 59
def prefixEnd_459166 : Nat := 4983230072969 + 3 ^ 40 * 459166 * 2
def baseEnd_459166 : Nat := 157181905468303829742227

theorem tailTrace_459166 : CollatzResearch.WordTrace tailWord_459166 prefixEnd_459166 157181905468303829742227 := by
  unfold tailWord_459166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2093394981815934519328669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11164773236351650769752901 2093394981815934519328669)
  ·
    refine ⟨785023118180975444748251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2093394981815934519328669 785023118180975444748251)
    ·
      refine ⟨1177534677271463167122377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 785023118180975444748251 1177534677271463167122377)
      ·
        refine ⟨883151007953597375341783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1177534677271463167122377 883151007953597375341783)
        ·
          refine ⟨1324726511930396063012675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883151007953597375341783 1324726511930396063012675)
          ·
            refine ⟨1987089767895594094519013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324726511930396063012675 1987089767895594094519013)
            ·
              refine ⟨372579331480423892722315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1987089767895594094519013 372579331480423892722315)
              ·
                refine ⟨558868997220635839083473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372579331480423892722315 558868997220635839083473)
                ·
                  refine ⟨419151747915476879312605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558868997220635839083473 419151747915476879312605)
                  ·
                    refine ⟨157181905468303829742227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 419151747915476879312605 157181905468303829742227)
                    ·
                      rfl

theorem cell22_459166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_459166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459166 prefixEnd_459166 := by exact prefixLift 459166
  have htrace : WordTrace (prefixWord ++ tailWord_459166) baseStart_459166 baseEnd_459166 := by
    simpa [prefixWord, tailWord_459166, baseEnd_459166] using wordTrace_append hprefix tailTrace_459166
  have hstable : (prefixWord ++ tailWord_459166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459166).length < 2 ^ (prefixWord ++ tailWord_459166).sum := by decide
  have hdescent : baseEnd_459166 < baseStart_459166 := by decide
  rcases family_descends (prefixWord ++ tailWord_459166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459222 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_459222 : Nat := 118140960795 + 459222 * 2 ^ 59
def prefixEnd_459222 : Nat := 4983230072969 + 3 ^ 40 * 459222 * 2
def baseEnd_459222 : Nat := 157201075412738350342055

theorem tailTrace_459222 : CollatzResearch.WordTrace tailWord_459222 prefixEnd_459222 157201075412738350342055 := by
  unfold tailWord_459222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1046825146395287357416745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11166134894883065145778613 1046825146395287357416745)
  ·
    refine ⟨785118859796465518062559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1046825146395287357416745 785118859796465518062559)
    ·
      refine ⟨1177678289694698277093839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 785118859796465518062559 1177678289694698277093839)
      ·
        refine ⟨1766517434542047415640759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177678289694698277093839 1766517434542047415640759)
        ·
          refine ⟨2649776151813071123461139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766517434542047415640759 2649776151813071123461139)
          ·
            refine ⟨3974664227719606685191709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2649776151813071123461139 3974664227719606685191709)
            ·
              refine ⟨1490499085394852506946891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3974664227719606685191709 1490499085394852506946891)
              ·
                refine ⟨2235748628092278760420337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1490499085394852506946891 2235748628092278760420337)
                ·
                  refine ⟨1676811471069209070315253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2235748628092278760420337 1676811471069209070315253)
                  ·
                    refine ⟨157201075412738350342055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1676811471069209070315253 157201075412738350342055)
                    ·
                      rfl

theorem cell22_459222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_459222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459222 prefixEnd_459222 := by exact prefixLift 459222
  have htrace : WordTrace (prefixWord ++ tailWord_459222) baseStart_459222 baseEnd_459222 := by
    simpa [prefixWord, tailWord_459222, baseEnd_459222] using wordTrace_append hprefix tailTrace_459222
  have hstable : (prefixWord ++ tailWord_459222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459222).length < 2 ^ (prefixWord ++ tailWord_459222).sum := by decide
  have hdescent : baseEnd_459222 < baseStart_459222 := by decide
  rcases family_descends (prefixWord ++ tailWord_459222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459263 : List Nat := [1, 1, 2, 2, 1, 2, 13]
def baseStart_459263 : Nat := 118140960795 + 459263 * 2 ^ 59
def prefixEnd_459263 : Nat := 4983230072969 + 3 ^ 40 * 459263 * 2
def baseEnd_459263 : Nat := 5822781872245478150627

theorem tailTrace_459263 : CollatzResearch.WordTrace tailWord_459263 prefixEnd_459263 5822781872245478150627 := by
  unfold tailWord_459263
  simp only [CollatzResearch.WordTrace]
  refine ⟨16750697735176061720910443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11167131823450707813940295 16750697735176061720910443)
  ·
    refine ⟨25126046602764092581365665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16750697735176061720910443 25126046602764092581365665)
    ·
      refine ⟨18844534952073069436024249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25126046602764092581365665 18844534952073069436024249)
      ·
        refine ⟨14133401214054802077018187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18844534952073069436024249 14133401214054802077018187)
        ·
          refine ⟨21200101821082203115527281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14133401214054802077018187 21200101821082203115527281)
          ·
            refine ⟨15900076365811652336645461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21200101821082203115527281 15900076365811652336645461)
            ·
              refine ⟨5822781872245478150627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 15900076365811652336645461 5822781872245478150627)
              ·
                rfl

theorem cell22_459263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 13].length) (baseStart_459263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459263 prefixEnd_459263 := by exact prefixLift 459263
  have htrace : WordTrace (prefixWord ++ tailWord_459263) baseStart_459263 baseEnd_459263 := by
    simpa [prefixWord, tailWord_459263, baseEnd_459263] using wordTrace_append hprefix tailTrace_459263
  have hstable : (prefixWord ++ tailWord_459263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459263).length < 2 ^ (prefixWord ++ tailWord_459263).sum := by decide
  have hdescent : baseEnd_459263 < baseStart_459263 := by decide
  rcases family_descends (prefixWord ++ tailWord_459263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459284 : List Nat := [2, 4, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_459284 : Nat := 118140960795 + 459284 * 2 ^ 59
def prefixEnd_459284 : Nat := 4983230072969 + 3 ^ 40 * 459284 * 2
def baseEnd_459284 : Nat := 157222299279790855291865

theorem tailTrace_459284 : CollatzResearch.WordTrace tailWord_459284 prefixEnd_459284 157222299279790855291865 := by
  unfold tailWord_459284
  simp only [CollatzResearch.WordTrace]
  refine ⟨8375731834049991153712453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11167642445399988204949937 8375731834049991153712453)
  ·
    refine ⟨1570449718884373341321085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8375731834049991153712453 1570449718884373341321085)
    ·
      refine ⟨588918644581640002995407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1570449718884373341321085 588918644581640002995407)
      ·
        refine ⟨883377966872460004493111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588918644581640002995407 883377966872460004493111)
        ·
          refine ⟨1325066950308690006739667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883377966872460004493111 1325066950308690006739667)
          ·
            refine ⟨1987600425463035010109501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325066950308690006739667 1987600425463035010109501)
            ·
              refine ⟨745350159548638128791063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1987600425463035010109501 745350159548638128791063)
              ·
                refine ⟨1118025239322957193186595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745350159548638128791063 1118025239322957193186595)
                ·
                  refine ⟨1677037858984435789779893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1118025239322957193186595 1677037858984435789779893)
                  ·
                    refine ⟨157222299279790855291865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1677037858984435789779893 157222299279790855291865)
                    ·
                      rfl

theorem cell22_459284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_459284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459284 prefixEnd_459284 := by exact prefixLift 459284
  have htrace : WordTrace (prefixWord ++ tailWord_459284) baseStart_459284 baseEnd_459284 := by
    simpa [prefixWord, tailWord_459284, baseEnd_459284] using wordTrace_append hprefix tailTrace_459284
  have hstable : (prefixWord ++ tailWord_459284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459284).length < 2 ^ (prefixWord ++ tailWord_459284).sum := by decide
  have hdescent : baseEnd_459284 < baseStart_459284 := by decide
  rcases family_descends (prefixWord ++ tailWord_459284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459303 : List Nat := [1, 1, 7, 2, 1, 2, 1, 3, 4]
def baseStart_459303 : Nat := 118140960795 + 459303 * 2 ^ 59
def prefixEnd_459303 : Nat := 4983230072969 + 3 ^ 40 * 459303 * 2
def baseEnd_459303 : Nat := 52409601122693713022269

theorem tailTrace_459303 : CollatzResearch.WordTrace tailWord_459303 prefixEnd_459303 52409601122693713022269 := by
  unfold tailWord_459303
  simp only [CollatzResearch.WordTrace]
  refine ⟨16752156655031148552366563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11168104436687432368244375 16752156655031148552366563)
  ·
    refine ⟨25128234982546722828549845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16752156655031148552366563 25128234982546722828549845)
    ·
      refine ⟨588943007403438816294137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 25128234982546722828549845 588943007403438816294137)
      ·
        refine ⟨441707255552579112220603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 588943007403438816294137 441707255552579112220603)
        ·
          refine ⟨662560883328868668330905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441707255552579112220603 662560883328868668330905)
          ·
            refine ⟨496920662496651501248179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 662560883328868668330905 496920662496651501248179)
            ·
              refine ⟨745380993744977251872269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496920662496651501248179 745380993744977251872269)
              ·
                refine ⟨279517872654366469452101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 745380993744977251872269 279517872654366469452101)
                ·
                  refine ⟨52409601122693713022269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 279517872654366469452101 52409601122693713022269)
                  ·
                    rfl

theorem cell22_459303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 4].length) (baseStart_459303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459303 prefixEnd_459303 := by exact prefixLift 459303
  have htrace : WordTrace (prefixWord ++ tailWord_459303) baseStart_459303 baseEnd_459303 := by
    simpa [prefixWord, tailWord_459303, baseEnd_459303] using wordTrace_append hprefix tailTrace_459303
  have hstable : (prefixWord ++ tailWord_459303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459303).length < 2 ^ (prefixWord ++ tailWord_459303).sum := by decide
  have hdescent : baseEnd_459303 < baseStart_459303 := by decide
  rcases family_descends (prefixWord ++ tailWord_459303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459316 : List Nat := [2, 5, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_459316 : Nat := 118140960795 + 459316 * 2 ^ 59
def prefixEnd_459316 : Nat := 4983230072969 + 3 ^ 40 * 459316 * 2
def baseEnd_459316 : Nat := 157233253533753438491767

theorem tailTrace_459316 : CollatzResearch.WordTrace tailWord_459316 prefixEnd_459316 157233253533753438491767 := by
  unfold tailWord_459316
  simp only [CollatzResearch.WordTrace]
  refine ⟨8376315401992025886294901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11168420535989367848393201 8376315401992025886294901)
  ·
    refine ⟨785279568936752426840147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8376315401992025886294901 785279568936752426840147)
    ·
      refine ⟨1177919353405128640260221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 785279568936752426840147 1177919353405128640260221)
      ·
        refine ⟨441719757526923240097583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1177919353405128640260221 441719757526923240097583)
        ·
          refine ⟨662579636290384860146375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441719757526923240097583 662579636290384860146375)
          ·
            refine ⟨993869454435577290219563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662579636290384860146375 993869454435577290219563)
            ·
              refine ⟨1490804181653365935329345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993869454435577290219563 1490804181653365935329345)
              ·
                refine ⟨1118103136240024451497009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1490804181653365935329345 1118103136240024451497009)
                ·
                  refine ⟨838577352180018338622757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1118103136240024451497009 838577352180018338622757)
                  ·
                    refine ⟨157233253533753438491767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 838577352180018338622757 157233253533753438491767)
                    ·
                      rfl

theorem cell22_459316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_459316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459316 prefixEnd_459316 := by exact prefixLift 459316
  have htrace : WordTrace (prefixWord ++ tailWord_459316) baseStart_459316 baseEnd_459316 := by
    simpa [prefixWord, tailWord_459316, baseEnd_459316] using wordTrace_append hprefix tailTrace_459316
  have hstable : (prefixWord ++ tailWord_459316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459316).length < 2 ^ (prefixWord ++ tailWord_459316).sum := by decide
  have hdescent : baseEnd_459316 < baseStart_459316 := by decide
  rcases family_descends (prefixWord ++ tailWord_459316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459329 : List Nat := [1, 2, 5, 1, 1, 2, 3, 1, 3, 3]
def baseStart_459329 : Nat := 118140960795 + 459329 * 2 ^ 59
def prefixEnd_459329 : Nat := 4983230072969 + 3 ^ 40 * 459329 * 2
def baseEnd_459329 : Nat := 157237703699425737916727

theorem tailTrace_459329 : CollatzResearch.WordTrace tailWord_459329 prefixEnd_459329 157237703699425737916727 := by
  unfold tailWord_459329
  simp only [CollatzResearch.WordTrace]
  refine ⟨16753104952936954992813041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11168736635291303328542027 16753104952936954992813041)
  ·
    refine ⟨12564828714702716244609781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16753104952936954992813041 12564828714702716244609781)
    ·
      refine ⟨1177952692003379647932167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12564828714702716244609781 1177952692003379647932167)
      ·
        refine ⟨1766929038005069471898251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177952692003379647932167 1766929038005069471898251)
        ·
          refine ⟨2650393557007604207847377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766929038005069471898251 2650393557007604207847377)
          ·
            refine ⟨1987795167755703155885533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2650393557007604207847377 1987795167755703155885533)
            ·
              refine ⟨745423187908388683457075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1987795167755703155885533 745423187908388683457075)
              ·
                refine ⟨1118134781862583025185613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745423187908388683457075 1118134781862583025185613)
                ·
                  refine ⟨419300543198468634444605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1118134781862583025185613 419300543198468634444605)
                  ·
                    refine ⟨157237703699425737916727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 419300543198468634444605 157237703699425737916727)
                    ·
                      rfl

theorem cell22_459329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_459329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459329 prefixEnd_459329 := by exact prefixLift 459329
  have htrace : WordTrace (prefixWord ++ tailWord_459329) baseStart_459329 baseEnd_459329 := by
    simpa [prefixWord, tailWord_459329, baseEnd_459329] using wordTrace_append hprefix tailTrace_459329
  have hstable : (prefixWord ++ tailWord_459329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459329).length < 2 ^ (prefixWord ++ tailWord_459329).sum := by decide
  have hdescent : baseEnd_459329 < baseStart_459329 := by decide
  rcases family_descends (prefixWord ++ tailWord_459329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459340 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 1, 7]
def baseStart_459340 : Nat := 118140960795 + 459340 * 2 ^ 59
def prefixEnd_459340 : Nat := 4983230072969 + 3 ^ 40 * 459340 * 2
def baseEnd_459340 : Nat := 157241469224225375891693

theorem tailTrace_459340 : CollatzResearch.WordTrace tailWord_459340 prefixEnd_459340 157241469224225375891693 := by
  unfold tailWord_459340
  simp only [CollatzResearch.WordTrace]
  refine ⟨8376753077948551935731737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11169004103931402580975649 8376753077948551935731737)
  ·
    refine ⟨6282564808461413951798803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8376753077948551935731737 6282564808461413951798803)
    ·
      refine ⟨9423847212692120927698205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6282564808461413951798803 9423847212692120927698205)
      ·
        refine ⟨3533942704759545347886827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9423847212692120927698205 3533942704759545347886827)
        ·
          refine ⟨5300914057139318021830241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3533942704759545347886827 5300914057139318021830241)
          ·
            refine ⟨3975685542854488516372681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5300914057139318021830241 3975685542854488516372681)
            ·
              refine ⟨2981764157140866387279511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3975685542854488516372681 2981764157140866387279511)
              ·
                refine ⟨4472646235711299580919267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2981764157140866387279511 4472646235711299580919267)
                ·
                  refine ⟨6708969353566949371378901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472646235711299580919267 6708969353566949371378901)
                  ·
                    refine ⟨157241469224225375891693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6708969353566949371378901 157241469224225375891693)
                    ·
                      rfl

theorem cell22_459340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_459340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459340 prefixEnd_459340 := by exact prefixLift 459340
  have htrace : WordTrace (prefixWord ++ tailWord_459340) baseStart_459340 baseEnd_459340 := by
    simpa [prefixWord, tailWord_459340, baseEnd_459340] using wordTrace_append hprefix tailTrace_459340
  have hstable : (prefixWord ++ tailWord_459340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459340).length < 2 ^ (prefixWord ++ tailWord_459340).sum := by decide
  have hdescent : baseEnd_459340 < baseStart_459340 := by decide
  rcases family_descends (prefixWord ++ tailWord_459340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459372 : List Nat := [2, 2, 1, 1, 3, 1, 2, 5, 1, 4]
def baseStart_459372 : Nat := 118140960795 + 459372 * 2 ^ 59
def prefixEnd_459372 : Nat := 4983230072969 + 3 ^ 40 * 459372 * 2
def baseEnd_459372 : Nat := 157252423478187959091595

theorem tailTrace_459372 : CollatzResearch.WordTrace tailWord_459372 prefixEnd_459372 157252423478187959091595 := by
  unfold tailWord_459372
  simp only [CollatzResearch.WordTrace]
  refine ⟨8377336645890586668314185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11169782194520782224418913 8377336645890586668314185)
  ·
    refine ⟨6283002484417940001235639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8377336645890586668314185 6283002484417940001235639)
    ·
      refine ⟨9424503726626910001853459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6283002484417940001235639 9424503726626910001853459)
      ·
        refine ⟨14136755589940365002780189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9424503726626910001853459 14136755589940365002780189)
        ·
          refine ⟨5301283346227636876042571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14136755589940365002780189 5301283346227636876042571)
          ·
            refine ⟨7951925019341455314063857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5301283346227636876042571 7951925019341455314063857)
            ·
              refine ⟨5963943764506091485547893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7951925019341455314063857 5963943764506091485547893)
              ·
                refine ⟨559119727922446076770115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5963943764506091485547893 559119727922446076770115)
                ·
                  refine ⟨838679591883669115155173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 559119727922446076770115 838679591883669115155173)
                  ·
                    refine ⟨157252423478187959091595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 838679591883669115155173 157252423478187959091595)
                    ·
                      rfl

theorem cell22_459372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_459372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459372 prefixEnd_459372 := by exact prefixLift 459372
  have htrace : WordTrace (prefixWord ++ tailWord_459372) baseStart_459372 baseEnd_459372 := by
    simpa [prefixWord, tailWord_459372, baseEnd_459372] using wordTrace_append hprefix tailTrace_459372
  have hstable : (prefixWord ++ tailWord_459372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459372).length < 2 ^ (prefixWord ++ tailWord_459372).sum := by decide
  have hdescent : baseEnd_459372 < baseStart_459372 := by decide
  rcases family_descends (prefixWord ++ tailWord_459372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459464 : List Nat := [2, 1, 3, 1, 2, 3, 2, 2, 3, 3]
def baseStart_459464 : Nat := 118140960795 + 459464 * 2 ^ 59
def prefixEnd_459464 : Nat := 4983230072969 + 3 ^ 40 * 459464 * 2
def baseEnd_459464 : Nat := 157283916958330385791313

theorem tailTrace_459464 : CollatzResearch.WordTrace tailWord_459464 prefixEnd_459464 157283916958330385791313 := by
  unfold tailWord_459464
  simp only [CollatzResearch.WordTrace]
  refine ⟨8379014403723936524488723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11172019204965248699318297 8379014403723936524488723)
  ·
    refine ⟨12568521605585904786733085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8379014403723936524488723 12568521605585904786733085)
    ·
      refine ⟨4713195602094714295024907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12568521605585904786733085 4713195602094714295024907)
      ·
        refine ⟨7069793403142071442537361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4713195602094714295024907 7069793403142071442537361)
        ·
          refine ⟨5302345052356553581903021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7069793403142071442537361 5302345052356553581903021)
          ·
            refine ⟨1988379394633707593213633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5302345052356553581903021 1988379394633707593213633)
            ·
              refine ⟨1491284545975280694910225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1988379394633707593213633 1491284545975280694910225)
              ·
                refine ⟨1118463409481460521182669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1491284545975280694910225 1118463409481460521182669)
                ·
                  refine ⟨419423778555547695443501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1118463409481460521182669 419423778555547695443501)
                  ·
                    refine ⟨157283916958330385791313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 419423778555547695443501 157283916958330385791313)
                    ·
                      rfl

theorem cell22_459464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_459464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459464 prefixEnd_459464 := by exact prefixLift 459464
  have htrace : WordTrace (prefixWord ++ tailWord_459464) baseStart_459464 baseEnd_459464 := by
    simpa [prefixWord, tailWord_459464, baseEnd_459464] using wordTrace_append hprefix tailTrace_459464
  have hstable : (prefixWord ++ tailWord_459464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459464).length < 2 ^ (prefixWord ++ tailWord_459464).sum := by decide
  have hdescent : baseEnd_459464 < baseStart_459464 := by decide
  rcases family_descends (prefixWord ++ tailWord_459464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459507 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 3, 4]
def baseStart_459507 : Nat := 118140960795 + 459507 * 2 ^ 59
def prefixEnd_459507 : Nat := 4983230072969 + 3 ^ 40 * 459507 * 2
def baseEnd_459507 : Nat := 157298636737092606966181

theorem tailTrace_459507 : CollatzResearch.WordTrace tailWord_459507 prefixEnd_459507 157298636737092606966181 := by
  unfold tailWord_459507
  simp only [CollatzResearch.WordTrace]
  refine ⟨16759597146292091392792775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11173064764194727595195183 16759597146292091392792775)
  ·
    refine ⟨25139395719438137089189163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16759597146292091392792775 25139395719438137089189163)
    ·
      refine ⟨37709093579157205633783745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25139395719438137089189163 37709093579157205633783745)
      ·
        refine ⟨28281820184367904225337809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37709093579157205633783745 28281820184367904225337809)
        ·
          refine ⟨21211365138275928169003357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28281820184367904225337809 21211365138275928169003357)
          ·
            refine ⟨7954261926853473063376259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21211365138275928169003357 7954261926853473063376259)
            ·
              refine ⟨11931392890280209595064389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7954261926853473063376259 11931392890280209595064389)
              ·
                refine ⟨2237136166927539299074573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11931392890280209595064389 2237136166927539299074573)
                ·
                  refine ⟨838926062597827237152965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2237136166927539299074573 838926062597827237152965)
                  ·
                    refine ⟨157298636737092606966181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 838926062597827237152965 157298636737092606966181)
                    ·
                      rfl

theorem cell22_459507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 4].length) (baseStart_459507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459507 prefixEnd_459507 := by exact prefixLift 459507
  have htrace : WordTrace (prefixWord ++ tailWord_459507) baseStart_459507 baseEnd_459507 := by
    simpa [prefixWord, tailWord_459507, baseEnd_459507] using wordTrace_append hprefix tailTrace_459507
  have hstable : (prefixWord ++ tailWord_459507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459507).length < 2 ^ (prefixWord ++ tailWord_459507).sum := by decide
  have hdescent : baseEnd_459507 < baseStart_459507 := by decide
  rcases family_descends (prefixWord ++ tailWord_459507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459524 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_459524 : Nat := 118140960795 + 459524 * 2 ^ 59
def prefixEnd_459524 : Nat := 4983230072969 + 3 ^ 40 * 459524 * 2
def baseEnd_459524 : Nat := 157304456184510229291129

theorem tailTrace_459524 : CollatzResearch.WordTrace tailWord_459524 prefixEnd_459524 157304456184510229291129 := by
  unfold tailWord_459524
  simp only [CollatzResearch.WordTrace]
  refine ⟨8380108593615251648080813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11173478124820335530774417 8380108593615251648080813)
  ·
    refine ⟨3142540722605719368030305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8380108593615251648080813 3142540722605719368030305)
    ·
      refine ⟨2356905541954289526022729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3142540722605719368030305 2356905541954289526022729)
      ·
        refine ⟨1767679156465717144517047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2356905541954289526022729 1767679156465717144517047)
        ·
          refine ⟨2651518734698575716775571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1767679156465717144517047 2651518734698575716775571)
          ·
            refine ⟨3977278102047863575163357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651518734698575716775571 3977278102047863575163357)
            ·
              refine ⟨1491479288267948840686259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3977278102047863575163357 1491479288267948840686259)
              ·
                refine ⟨2237218932401923261029389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491479288267948840686259 2237218932401923261029389)
                ·
                  refine ⟨838957099650721222886021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2237218932401923261029389 838957099650721222886021)
                  ·
                    refine ⟨157304456184510229291129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 838957099650721222886021 157304456184510229291129)
                    ·
                      rfl

theorem cell22_459524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_459524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459524 prefixEnd_459524 := by exact prefixLift 459524
  have htrace : WordTrace (prefixWord ++ tailWord_459524) baseStart_459524 baseEnd_459524 := by
    simpa [prefixWord, tailWord_459524, baseEnd_459524] using wordTrace_append hprefix tailTrace_459524
  have hstable : (prefixWord ++ tailWord_459524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459524).length < 2 ^ (prefixWord ++ tailWord_459524).sum := by decide
  have hdescent : baseEnd_459524 < baseStart_459524 := by decide
  rcases family_descends (prefixWord ++ tailWord_459524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459537 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 3, 5]
def baseStart_459537 : Nat := 118140960795 + 459537 * 2 ^ 59
def prefixEnd_459537 : Nat := 4983230072969 + 3 ^ 40 * 459537 * 2
def baseEnd_459537 : Nat := 157308906350182528716089

theorem tailTrace_459537 : CollatzResearch.WordTrace tailWord_459537 prefixEnd_459537 157308906350182528716089 := by
  unfold tailWord_459537
  simp only [CollatzResearch.WordTrace]
  refine ⟨16760691336183406516384865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11173794224122271010923243 16760691336183406516384865)
  ·
    refine ⟨12570518502137554887288649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16760691336183406516384865 12570518502137554887288649)
    ·
      refine ⟨9427888876603166165466487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12570518502137554887288649 9427888876603166165466487)
      ·
        refine ⟨14141833314904749248199731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9427888876603166165466487 14141833314904749248199731)
        ·
          refine ⟨21212749972357123872299597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14141833314904749248199731 21212749972357123872299597)
          ·
            refine ⟨7954781239633921452112349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21212749972357123872299597 7954781239633921452112349)
            ·
              refine ⟨2983042964862720544542131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7954781239633921452112349 2983042964862720544542131)
              ·
                refine ⟨4474564447294080816813197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2983042964862720544542131 4474564447294080816813197)
                ·
                  refine ⟨1677961667735280306304949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4474564447294080816813197 1677961667735280306304949)
                  ·
                    refine ⟨157308906350182528716089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1677961667735280306304949 157308906350182528716089)
                    ·
                      rfl

theorem cell22_459537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_459537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459537 prefixEnd_459537 := by exact prefixLift 459537
  have htrace : WordTrace (prefixWord ++ tailWord_459537) baseStart_459537 baseEnd_459537 := by
    simpa [prefixWord, tailWord_459537, baseEnd_459537] using wordTrace_append hprefix tailTrace_459537
  have hstable : (prefixWord ++ tailWord_459537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459537).length < 2 ^ (prefixWord ++ tailWord_459537).sum := by decide
  have hdescent : baseEnd_459537 < baseStart_459537 := by decide
  rcases family_descends (prefixWord ++ tailWord_459537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459539 : List Nat := [1, 1, 1, 2, 1, 3, 4, 5, 4]
def baseStart_459539 : Nat := 118140960795 + 459539 * 2 ^ 59
def prefixEnd_459539 : Nat := 4983230072969 + 3 ^ 40 * 459539 * 2
def baseEnd_459539 : Nat := 52436530330351730055361

theorem tailTrace_459539 : CollatzResearch.WordTrace tailWord_459539 prefixEnd_459539 52436530330351730055361 := by
  unfold tailWord_459539
  simp only [CollatzResearch.WordTrace]
  refine ⟨16760764282176160857957671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11173842854784107238638447 16760764282176160857957671)
  ·
    refine ⟨25141146423264241286936507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16760764282176160857957671 25141146423264241286936507)
    ·
      refine ⟨37711719634896361930404761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25141146423264241286936507 37711719634896361930404761)
      ·
        refine ⟨28283789726172271447803571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37711719634896361930404761 28283789726172271447803571)
        ·
          refine ⟨42425684589258407171705357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28283789726172271447803571 42425684589258407171705357)
          ·
            refine ⟨15909631720971902689389509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42425684589258407171705357 15909631720971902689389509)
            ·
              refine ⟨2983055947682231754260533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15909631720971902689389509 2983055947682231754260533)
              ·
                refine ⟨279661495095209226961925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2983055947682231754260533 279661495095209226961925)
                ·
                  refine ⟨52436530330351730055361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 279661495095209226961925 52436530330351730055361)
                  ·
                    rfl

theorem cell22_459539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 4].length) (baseStart_459539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459539 prefixEnd_459539 := by exact prefixLift 459539
  have htrace : WordTrace (prefixWord ++ tailWord_459539) baseStart_459539 baseEnd_459539 := by
    simpa [prefixWord, tailWord_459539, baseEnd_459539] using wordTrace_append hprefix tailTrace_459539
  have hstable : (prefixWord ++ tailWord_459539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459539).length < 2 ^ (prefixWord ++ tailWord_459539).sum := by decide
  have hdescent : baseEnd_459539 < baseStart_459539 := by decide
  rcases family_descends (prefixWord ++ tailWord_459539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459541 : List Nat := [1, 3, 2, 1, 2, 2, 5, 1, 1, 4]
def baseStart_459541 : Nat := 118140960795 + 459541 * 2 ^ 59
def prefixEnd_459541 : Nat := 4983230072969 + 3 ^ 40 * 459541 * 2
def baseEnd_459541 : Nat := 157310275631927851616077

theorem tailTrace_459541 : CollatzResearch.WordTrace tailWord_459541 prefixEnd_459541 157310275631927851616077 := by
  unfold tailWord_459541
  simp only [CollatzResearch.WordTrace]
  refine ⟨16760837228168915199530477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11173891485445943466353651 16760837228168915199530477)
  ·
    refine ⟨6285313960563343199823929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16760837228168915199530477 6285313960563343199823929)
    ·
      refine ⟨4713985470422507399867947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6285313960563343199823929 4713985470422507399867947)
      ·
        refine ⟨7070978205633761099801921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4713985470422507399867947 7070978205633761099801921)
        ·
          refine ⟨5303233654225320824851441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7070978205633761099801921 5303233654225320824851441)
          ·
            refine ⟨3977425240668990618638581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5303233654225320824851441 3977425240668990618638581)
            ·
              refine ⟨372883616312717870497367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3977425240668990618638581 372883616312717870497367)
              ·
                refine ⟨559325424469076805746051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372883616312717870497367 559325424469076805746051)
                ·
                  refine ⟨838988136703615208619077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 559325424469076805746051 838988136703615208619077)
                  ·
                    refine ⟨157310275631927851616077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 838988136703615208619077 157310275631927851616077)
                    ·
                      rfl

theorem cell22_459541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_459541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459541 prefixEnd_459541 := by exact prefixLift 459541
  have htrace : WordTrace (prefixWord ++ tailWord_459541) baseStart_459541 baseEnd_459541 := by
    simpa [prefixWord, tailWord_459541, baseEnd_459541] using wordTrace_append hprefix tailTrace_459541
  have hstable : (prefixWord ++ tailWord_459541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459541).length < 2 ^ (prefixWord ++ tailWord_459541).sum := by decide
  have hdescent : baseEnd_459541 < baseStart_459541 := by decide
  rcases family_descends (prefixWord ++ tailWord_459541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459549 : List Nat := [1, 4, 2, 4, 2, 1, 2, 2, 1, 3]
def baseStart_459549 : Nat := 118140960795 + 459549 * 2 ^ 59
def prefixEnd_459549 : Nat := 4983230072969 + 3 ^ 40 * 459549 * 2
def baseEnd_459549 : Nat := 157313014195418497416053

theorem tailTrace_459549 : CollatzResearch.WordTrace tailWord_459549 prefixEnd_459549 157313014195418497416053 := by
  unfold tailWord_459549
  simp only [CollatzResearch.WordTrace]
  refine ⟨16761129012139932565821701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11174086008093288377214467 16761129012139932565821701)
  ·
    refine ⟨3142711689776237356091569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16761129012139932565821701 3142711689776237356091569)
    ·
      refine ⟨2357033767332178017068677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3142711689776237356091569 2357033767332178017068677)
      ·
        refine ⟨441943831374783378200377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2357033767332178017068677 441943831374783378200377)
        ·
          refine ⟨331457873531087533650283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441943831374783378200377 331457873531087533650283)
          ·
            refine ⟨497186810296631300475425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331457873531087533650283 497186810296631300475425)
            ·
              refine ⟨372890107722473475356569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497186810296631300475425 372890107722473475356569)
              ·
                refine ⟨279667580791855106517427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372890107722473475356569 279667580791855106517427)
                ·
                  refine ⟨419501371187782659776141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279667580791855106517427 419501371187782659776141)
                  ·
                    refine ⟨157313014195418497416053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 419501371187782659776141 157313014195418497416053)
                    ·
                      rfl

theorem cell22_459549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_459549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459549 prefixEnd_459549 := by exact prefixLift 459549
  have htrace : WordTrace (prefixWord ++ tailWord_459549) baseStart_459549 baseEnd_459549 := by
    simpa [prefixWord, tailWord_459549, baseEnd_459549] using wordTrace_append hprefix tailTrace_459549
  have hstable : (prefixWord ++ tailWord_459549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459549).length < 2 ^ (prefixWord ++ tailWord_459549).sum := by decide
  have hdescent : baseEnd_459549 < baseStart_459549 := by decide
  rcases family_descends (prefixWord ++ tailWord_459549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459571 : List Nat := [1, 1, 1, 2, 6, 1, 2, 3, 2, 3]
def baseStart_459571 : Nat := 118140960795 + 459571 * 2 ^ 59
def prefixEnd_459571 : Nat := 4983230072969 + 3 ^ 40 * 459571 * 2
def baseEnd_459571 : Nat := 157320545245017773365985

theorem tailTrace_459571 : CollatzResearch.WordTrace tailWord_459571 prefixEnd_459571 157320545245017773365985 := by
  unfold tailWord_459571
  simp only [CollatzResearch.WordTrace]
  refine ⟨16761931418060230323122567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11174620945373486882081711 16761931418060230323122567)
  ·
    refine ⟨25142897127090345484683851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16761931418060230323122567 25142897127090345484683851)
    ·
      refine ⟨37714345690635518227025777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25142897127090345484683851 37714345690635518227025777)
      ·
        refine ⟨28285759267976638670269333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37714345690635518227025777 28285759267976638670269333)
        ·
          refine ⟨1325894965686404937668875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28285759267976638670269333 1325894965686404937668875)
          ·
            refine ⟨1988842448529607406503313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325894965686404937668875 1988842448529607406503313)
            ·
              refine ⟨1491631836397205554877485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1988842448529607406503313 1491631836397205554877485)
              ·
                refine ⟨559361938648952083079057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1491631836397205554877485 559361938648952083079057)
                ·
                  refine ⟨419521453986714062309293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559361938648952083079057 419521453986714062309293)
                  ·
                    refine ⟨157320545245017773365985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 419521453986714062309293 157320545245017773365985)
                    ·
                      rfl

theorem cell22_459571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 3].length) (baseStart_459571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459571 prefixEnd_459571 := by exact prefixLift 459571
  have htrace : WordTrace (prefixWord ++ tailWord_459571) baseStart_459571 baseEnd_459571 := by
    simpa [prefixWord, tailWord_459571, baseEnd_459571] using wordTrace_append hprefix tailTrace_459571
  have hstable : (prefixWord ++ tailWord_459571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459571).length < 2 ^ (prefixWord ++ tailWord_459571).sum := by decide
  have hdescent : baseEnd_459571 < baseStart_459571 := by decide
  rcases family_descends (prefixWord ++ tailWord_459571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459616 : List Nat := [2, 1, 1, 3, 3, 1, 4, 1, 3, 3]
def baseStart_459616 : Nat := 118140960795 + 459616 * 2 ^ 59
def prefixEnd_459616 : Nat := 4983230072969 + 3 ^ 40 * 459616 * 2
def baseEnd_459616 : Nat := 157335949664652655990847

theorem tailTrace_459616 : CollatzResearch.WordTrace tailWord_459616 prefixEnd_459616 157335949664652655990847 := by
  unfold tailWord_459616
  simp only [CollatzResearch.WordTrace]
  refine ⟨8381786351448601504255351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11175715135264802005673801 8381786351448601504255351)
  ·
    refine ⟨12572679527172902256383027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8381786351448601504255351 12572679527172902256383027)
    ·
      refine ⟨18859019290759353384574541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12572679527172902256383027 18859019290759353384574541)
      ·
        refine ⟨7072132234034757519215453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18859019290759353384574541 7072132234034757519215453)
        ·
          refine ⟨2652049587763034069705795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7072132234034757519215453 2652049587763034069705795)
          ·
            refine ⟨3978074381644551104558693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2652049587763034069705795 3978074381644551104558693)
            ·
              refine ⟨745888946558353332104755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3978074381644551104558693 745888946558353332104755)
              ·
                refine ⟨1118833419837529998157133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745888946558353332104755 1118833419837529998157133)
                ·
                  refine ⟨419562532439073749308925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1118833419837529998157133 419562532439073749308925)
                  ·
                    refine ⟨157335949664652655990847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 419562532439073749308925 157335949664652655990847)
                    ·
                      rfl

theorem cell22_459616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 3, 3].length) (baseStart_459616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459616 prefixEnd_459616 := by exact prefixLift 459616
  have htrace : WordTrace (prefixWord ++ tailWord_459616) baseStart_459616 baseEnd_459616 := by
    simpa [prefixWord, tailWord_459616, baseEnd_459616] using wordTrace_append hprefix tailTrace_459616
  have hstable : (prefixWord ++ tailWord_459616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459616).length < 2 ^ (prefixWord ++ tailWord_459616).sum := by decide
  have hdescent : baseEnd_459616 < baseStart_459616 := by decide
  rcases family_descends (prefixWord ++ tailWord_459616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459689 : List Nat := [1, 2, 1, 1, 1, 1, 6, 3, 1, 5]
def baseStart_459689 : Nat := 118140960795 + 459689 * 2 ^ 59
def prefixEnd_459689 : Nat := 4983230072969 + 3 ^ 40 * 459689 * 2
def baseEnd_459689 : Nat := 157360939056504798915623

theorem tailTrace_459689 : CollatzResearch.WordTrace tailWord_459689 prefixEnd_459689 157360939056504798915623 := by
  unfold tailWord_459689
  simp only [CollatzResearch.WordTrace]
  refine ⟨16766235231632736475918121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11177490154421824317278747 16766235231632736475918121)
  ·
    refine ⟨12574676423724552356938591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16766235231632736475918121 12574676423724552356938591)
    ·
      refine ⟨18862014635586828535407887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12574676423724552356938591 18862014635586828535407887)
      ·
        refine ⟨28293021953380242803111831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18862014635586828535407887 28293021953380242803111831)
        ·
          refine ⟨42439532930070364204667747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28293021953380242803111831 42439532930070364204667747)
          ·
            refine ⟨63659299395105546307001621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42439532930070364204667747 63659299395105546307001621)
            ·
              refine ⟨2984029659145572483140701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63659299395105546307001621 2984029659145572483140701)
              ·
                refine ⟨1119011122179589681177763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2984029659145572483140701 1119011122179589681177763)
                ·
                  refine ⟨1678516683269384521766645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1119011122179589681177763 1678516683269384521766645)
                  ·
                    refine ⟨157360939056504798915623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1678516683269384521766645 157360939056504798915623)
                    ·
                      rfl

theorem cell22_459689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_459689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459689 prefixEnd_459689 := by exact prefixLift 459689
  have htrace : WordTrace (prefixWord ++ tailWord_459689) baseStart_459689 baseEnd_459689 := by
    simpa [prefixWord, tailWord_459689, baseEnd_459689] using wordTrace_append hprefix tailTrace_459689
  have hstable : (prefixWord ++ tailWord_459689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459689).length < 2 ^ (prefixWord ++ tailWord_459689).sum := by decide
  have hdescent : baseEnd_459689 < baseStart_459689 := by decide
  rcases family_descends (prefixWord ++ tailWord_459689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459723 : List Nat := [1, 1, 1, 1, 3, 6, 2, 2, 2, 3]
def baseStart_459723 : Nat := 118140960795 + 459723 * 2 ^ 59
def prefixEnd_459723 : Nat := 4983230072969 + 3 ^ 40 * 459723 * 2
def baseEnd_459723 : Nat := 157372577951340043565519

theorem tailTrace_459723 : CollatzResearch.WordTrace tailWord_459723 prefixEnd_459723 157372577951340043565519 := by
  unfold tailWord_459723
  simp only [CollatzResearch.WordTrace]
  refine ⟨16767475313509560282655823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11178316875673040188437215 16767475313509560282655823)
  ·
    refine ⟨25151212970264340423983735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16767475313509560282655823 25151212970264340423983735)
    ·
      refine ⟨37726819455396510635975603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25151212970264340423983735 37726819455396510635975603)
      ·
        refine ⟨56590229183094765953963405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37726819455396510635975603 56590229183094765953963405)
        ·
          refine ⟨21221335943660537232736277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56590229183094765953963405 21221335943660537232736277)
          ·
            refine ⟨994750122359087682784513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21221335943660537232736277 994750122359087682784513)
            ·
              refine ⟨746062591769315762088385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 994750122359087682784513 746062591769315762088385)
              ·
                refine ⟨559546943826986821566289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746062591769315762088385 559546943826986821566289)
                ·
                  refine ⟨419660207870240116174717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559546943826986821566289 419660207870240116174717)
                  ·
                    refine ⟨157372577951340043565519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 419660207870240116174717 157372577951340043565519)
                    ·
                      rfl

theorem cell22_459723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 3].length) (baseStart_459723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459723 prefixEnd_459723 := by exact prefixLift 459723
  have htrace : WordTrace (prefixWord ++ tailWord_459723) baseStart_459723 baseEnd_459723 := by
    simpa [prefixWord, tailWord_459723, baseEnd_459723] using wordTrace_append hprefix tailTrace_459723
  have hstable : (prefixWord ++ tailWord_459723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459723).length < 2 ^ (prefixWord ++ tailWord_459723).sum := by decide
  have hdescent : baseEnd_459723 < baseStart_459723 := by decide
  rcases family_descends (prefixWord ++ tailWord_459723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459736 : List Nat := [2, 1, 2, 2, 2, 5, 1, 7]
def baseStart_459736 : Nat := 118140960795 + 459736 * 2 ^ 59
def prefixEnd_459736 : Nat := 4983230072969 + 3 ^ 40 * 459736 * 2
def baseEnd_459736 : Nat := 17486336457445815887831

theorem tailTrace_459736 : CollatzResearch.WordTrace tailWord_459736 prefixEnd_459736 17486336457445815887831 := by
  unfold tailWord_459736
  simp only [CollatzResearch.WordTrace]
  refine ⟨8383974731231231751439531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11178632974974975668586041 8383974731231231751439531)
  ·
    refine ⟨12575962096846847627159297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8383974731231231751439531 12575962096846847627159297)
    ·
      refine ⟨9431971572635135720369473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12575962096846847627159297 9431971572635135720369473)
      ·
        refine ⟨7073978679476351790277105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9431971572635135720369473 7073978679476351790277105)
        ·
          refine ⟨5305484009607263842707829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7073978679476351790277105 5305484009607263842707829)
          ·
            refine ⟨497389125900680985253859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5305484009607263842707829 497389125900680985253859)
            ·
              refine ⟨746083688851021477880789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497389125900680985253859 746083688851021477880789)
              ·
                refine ⟨17486336457445815887831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 746083688851021477880789 17486336457445815887831)
                ·
                  rfl

theorem cell22_459736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 7].length) (baseStart_459736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459736 prefixEnd_459736 := by exact prefixLift 459736
  have htrace : WordTrace (prefixWord ++ tailWord_459736) baseStart_459736 baseEnd_459736 := by
    simpa [prefixWord, tailWord_459736, baseEnd_459736] using wordTrace_append hprefix tailTrace_459736
  have hstable : (prefixWord ++ tailWord_459736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459736).length < 2 ^ (prefixWord ++ tailWord_459736).sum := by decide
  have hdescent : baseEnd_459736 < baseStart_459736 := by decide
  rcases family_descends (prefixWord ++ tailWord_459736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459774 : List Nat := [4, 2, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_459774 : Nat := 118140960795 + 459774 * 2 ^ 59
def prefixEnd_459774 : Nat := 4983230072969 + 3 ^ 40 * 459774 * 2
def baseEnd_459774 : Nat := 157390036293592910540363

theorem tailTrace_459774 : CollatzResearch.WordTrace tailWord_459774 prefixEnd_459774 157390036293592910540363 := by
  unfold tailWord_459774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2096166929540599499095297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11179556957549863995174917 2096166929540599499095297)
  ·
    refine ⟨1572125197155449624321473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2096166929540599499095297 1572125197155449624321473)
    ·
      refine ⟨1179093897866587218241105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1572125197155449624321473 1179093897866587218241105)
      ·
        refine ⟨884320423399940413680829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1179093897866587218241105 884320423399940413680829)
        ·
          refine ⟨331620158774977655130311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 884320423399940413680829 331620158774977655130311)
          ·
            refine ⟨497430238162466482695467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331620158774977655130311 497430238162466482695467)
            ·
              refine ⟨746145357243699724043201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497430238162466482695467 746145357243699724043201)
              ·
                refine ⟨559609017932774793032401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746145357243699724043201 559609017932774793032401)
                ·
                  refine ⟨419706763449581094774301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 559609017932774793032401 419706763449581094774301)
                  ·
                    refine ⟨157390036293592910540363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 419706763449581094774301 157390036293592910540363)
                    ·
                      rfl

theorem cell22_459774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_459774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459774 prefixEnd_459774 := by exact prefixLift 459774
  have htrace : WordTrace (prefixWord ++ tailWord_459774) baseStart_459774 baseEnd_459774 := by
    simpa [prefixWord, tailWord_459774, baseEnd_459774] using wordTrace_append hprefix tailTrace_459774
  have hstable : (prefixWord ++ tailWord_459774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459774).length < 2 ^ (prefixWord ++ tailWord_459774).sum := by decide
  have hdescent : baseEnd_459774 < baseStart_459774 := by decide
  rcases family_descends (prefixWord ++ tailWord_459774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459862 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_459862 : Nat := 118140960795 + 459862 * 2 ^ 59
def prefixEnd_459862 : Nat := 4983230072969 + 3 ^ 40 * 459862 * 2
def baseEnd_459862 : Nat := 157420160491990014340093

theorem tailTrace_459862 : CollatzResearch.WordTrace tailWord_459862 prefixEnd_459862 157420160491990014340093 := by
  unfold tailWord_459862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1048284066250374188872865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11181696706670658014643893 1048284066250374188872865)
  ·
    refine ⟨786213049687780641654649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1048284066250374188872865 786213049687780641654649)
    ·
      refine ⟨589659787265835481240987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 786213049687780641654649 589659787265835481240987)
      ·
        refine ⟨884489680898753221861481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589659787265835481240987 884489680898753221861481)
        ·
          refine ⟨663367260674064916396111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 884489680898753221861481 663367260674064916396111)
          ·
            refine ⟨995050891011097374594167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663367260674064916396111 995050891011097374594167)
            ·
              refine ⟨1492576336516646061891251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 995050891011097374594167 1492576336516646061891251)
              ·
                refine ⟨2238864504774969092836877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1492576336516646061891251 2238864504774969092836877)
                ·
                  refine ⟨839574189290613409813829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2238864504774969092836877 839574189290613409813829)
                  ·
                    refine ⟨157420160491990014340093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 839574189290613409813829 157420160491990014340093)
                    ·
                      rfl

theorem cell22_459862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_459862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459862 prefixEnd_459862 := by exact prefixLift 459862
  have htrace : WordTrace (prefixWord ++ tailWord_459862) baseStart_459862 baseEnd_459862 := by
    simpa [prefixWord, tailWord_459862, baseEnd_459862] using wordTrace_append hprefix tailTrace_459862
  have hstable : (prefixWord ++ tailWord_459862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459862).length < 2 ^ (prefixWord ++ tailWord_459862).sum := by decide
  have hdescent : baseEnd_459862 < baseStart_459862 := by decide
  rcases family_descends (prefixWord ++ tailWord_459862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459901 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_459901 : Nat := 118140960795 + 459901 * 2 ^ 59
def prefixEnd_459901 : Nat := 4983230072969 + 3 ^ 40 * 459901 * 2
def baseEnd_459901 : Nat := 157433510989006912614973

theorem tailTrace_459901 : CollatzResearch.WordTrace tailWord_459901 prefixEnd_459901 157433510989006912614973 := by
  unfold tailWord_459901
  simp only [CollatzResearch.WordTrace]
  refine ⟨16773967506864696682635557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11182645004576464455090371 16773967506864696682635557)
  ·
    refine ⟨3145118907537130627994167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16773967506864696682635557 3145118907537130627994167)
    ·
      refine ⟨4717678361305695941991251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3145118907537130627994167 4717678361305695941991251)
      ·
        refine ⟨7076517541958543912986877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4717678361305695941991251 7076517541958543912986877)
        ·
          refine ⟨2653694078234453967370079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7076517541958543912986877 2653694078234453967370079)
          ·
            refine ⟨3980541117351680951055119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2653694078234453967370079 3980541117351680951055119)
            ·
              refine ⟨5970811676027521426582679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3980541117351680951055119 5970811676027521426582679)
              ·
                refine ⟨8956217514041282139874019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5970811676027521426582679 8956217514041282139874019)
                ·
                  refine ⟨13434326271061923209811029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8956217514041282139874019 13434326271061923209811029)
                  ·
                    refine ⟨157433510989006912614973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13434326271061923209811029 157433510989006912614973)
                    ·
                      rfl

theorem cell22_459901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_459901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459901 prefixEnd_459901 := by exact prefixLift 459901
  have htrace : WordTrace (prefixWord ++ tailWord_459901) baseStart_459901 baseEnd_459901 := by
    simpa [prefixWord, tailWord_459901, baseEnd_459901] using wordTrace_append hprefix tailTrace_459901
  have hstable : (prefixWord ++ tailWord_459901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459901).length < 2 ^ (prefixWord ++ tailWord_459901).sum := by decide
  have hdescent : baseEnd_459901 < baseStart_459901 := by decide
  rcases family_descends (prefixWord ++ tailWord_459901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459937 : List Nat := [1, 2, 3, 3, 1, 1, 4, 3, 1, 3]
def baseStart_459937 : Nat := 118140960795 + 459937 * 2 ^ 59
def prefixEnd_459937 : Nat := 4983230072969 + 3 ^ 40 * 459937 * 2
def baseEnd_459937 : Nat := 157445834524714818714863

theorem tailTrace_459937 : CollatzResearch.WordTrace tailWord_459937 prefixEnd_459937 157445834524714818714863 := by
  unfold tailWord_459937
  simp only [CollatzResearch.WordTrace]
  refine ⟨16775280534734274830946065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11183520356489516553964043 16775280534734274830946065)
  ·
    refine ⟨12581460401050706123209549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16775280534734274830946065 12581460401050706123209549)
    ·
      refine ⟨4718047650394014796203581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12581460401050706123209549 4718047650394014796203581)
      ·
        refine ⟨1769267868897755548576343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4718047650394014796203581 1769267868897755548576343)
        ·
          refine ⟨2653901803346633322864515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1769267868897755548576343 2653901803346633322864515)
          ·
            refine ⟨3980852705019949984296773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2653901803346633322864515 3980852705019949984296773)
            ·
              refine ⟨746409882191240622055645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3980852705019949984296773 746409882191240622055645)
              ·
                refine ⟨279903705821715233270867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 746409882191240622055645 279903705821715233270867)
                ·
                  refine ⟨419855558732572849906301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279903705821715233270867 419855558732572849906301)
                  ·
                    refine ⟨157445834524714818714863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 419855558732572849906301 157445834524714818714863)
                    ·
                      rfl

theorem cell22_459937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_459937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459937 prefixEnd_459937 := by exact prefixLift 459937
  have htrace : WordTrace (prefixWord ++ tailWord_459937) baseStart_459937 baseEnd_459937 := by
    simpa [prefixWord, tailWord_459937, baseEnd_459937] using wordTrace_append hprefix tailTrace_459937
  have hstable : (prefixWord ++ tailWord_459937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459937).length < 2 ^ (prefixWord ++ tailWord_459937).sum := by decide
  have hdescent : baseEnd_459937 < baseStart_459937 := by decide
  rcases family_descends (prefixWord ++ tailWord_459937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459978 : List Nat := [3, 1, 2, 1, 3, 2, 2, 2, 6]
def baseStart_459978 : Nat := 118140960795 + 459978 * 2 ^ 59
def prefixEnd_459978 : Nat := 4983230072969 + 3 ^ 40 * 459978 * 2
def baseEnd_459978 : Nat := 52486623220868126146579

theorem tailTrace_459978 : CollatzResearch.WordTrace tailWord_459978 prefixEnd_459978 52486623220868126146579 := by
  unfold tailWord_459978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4194193981896434708297147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11184517285057159222125725 4194193981896434708297147)
  ·
    refine ⟨6291290972844652062445721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4194193981896434708297147 6291290972844652062445721)
    ·
      refine ⟨4718468229633489046834291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6291290972844652062445721 4718468229633489046834291)
      ·
        refine ⟨7077702344450233570251437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4718468229633489046834291 7077702344450233570251437)
        ·
          refine ⟨2654138379168837588844289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7077702344450233570251437 2654138379168837588844289)
          ·
            refine ⟨1990603784376628191633217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2654138379168837588844289 1990603784376628191633217)
            ·
              refine ⟨1492952838282471143724913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1990603784376628191633217 1492952838282471143724913)
              ·
                refine ⟨1119714628711853357793685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1492952838282471143724913 1119714628711853357793685)
                ·
                  refine ⟨52486623220868126146579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1119714628711853357793685 52486623220868126146579)
                  ·
                    rfl

theorem cell22_459978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_459978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459978 prefixEnd_459978 := by exact prefixLift 459978
  have htrace : WordTrace (prefixWord ++ tailWord_459978) baseStart_459978 baseEnd_459978 := by
    simpa [prefixWord, tailWord_459978, baseEnd_459978] using wordTrace_append hprefix tailTrace_459978
  have hstable : (prefixWord ++ tailWord_459978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459978).length < 2 ^ (prefixWord ++ tailWord_459978).sum := by decide
  have hdescent : baseEnd_459978 < baseStart_459978 := by decide
  rcases family_descends (prefixWord ++ tailWord_459978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459988 : List Nat := [2, 4, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_459988 : Nat := 118140960795 + 459988 * 2 ^ 59
def prefixEnd_459988 : Nat := 4983230072969 + 3 ^ 40 * 459988 * 2
def baseEnd_459988 : Nat := 157463292866967685689707

theorem tailTrace_459988 : CollatzResearch.WordTrace tailWord_459988 prefixEnd_459988 157463292866967685689707 := by
  unfold tailWord_459988
  simp only [CollatzResearch.WordTrace]
  refine ⟨8388570328774755270526309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11184760438366340360701745 8388570328774755270526309)
  ·
    refine ⟨1572856936645266613223683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8388570328774755270526309 1572856936645266613223683)
    ·
      refine ⟨2359285404967899919835525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1572856936645266613223683 2359285404967899919835525)
      ·
        refine ⟨442366013431481234969161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2359285404967899919835525 442366013431481234969161)
        ·
          refine ⟨331774510073610926226871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442366013431481234969161 331774510073610926226871)
          ·
            refine ⟨497661765110416389340307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331774510073610926226871 497661765110416389340307)
            ·
              refine ⟨746492647665624584010461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497661765110416389340307 746492647665624584010461)
              ·
                refine ⟨279934742874609219003923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 746492647665624584010461 279934742874609219003923)
                ·
                  refine ⟨419902114311913828505885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279934742874609219003923 419902114311913828505885)
                  ·
                    refine ⟨157463292866967685689707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 419902114311913828505885 157463292866967685689707)
                    ·
                      rfl

theorem cell22_459988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_459988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_459988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_459988 prefixEnd_459988 := by exact prefixLift 459988
  have htrace : WordTrace (prefixWord ++ tailWord_459988) baseStart_459988 baseEnd_459988 := by
    simpa [prefixWord, tailWord_459988, baseEnd_459988] using wordTrace_append hprefix tailTrace_459988
  have hstable : (prefixWord ++ tailWord_459988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459988).length < 2 ^ (prefixWord ++ tailWord_459988).sum := by decide
  have hdescent : baseEnd_459988 < baseStart_459988 := by decide
  rcases family_descends (prefixWord ++ tailWord_459988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460010 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 4, 3]
def baseStart_460010 : Nat := 118140960795 + 460010 * 2 ^ 59
def prefixEnd_460010 : Nat := 4983230072969 + 3 ^ 40 * 460010 * 2
def baseEnd_460010 : Nat := 157470823916566961639639

theorem tailTrace_460010 : CollatzResearch.WordTrace tailWord_460010 prefixEnd_460010 157470823916566961639639 := by
  unfold tailWord_460010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4194485765867452074588371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11185295375646538865568989 4194485765867452074588371)
  ·
    refine ⟨6291728648801178111882557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4194485765867452074588371 6291728648801178111882557)
    ·
      refine ⟨2359398243300441791955959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6291728648801178111882557 2359398243300441791955959)
      ·
        refine ⟨3539097364950662687933939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2359398243300441791955959 3539097364950662687933939)
        ·
          refine ⟨5308646047425994031900909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3539097364950662687933939 5308646047425994031900909)
          ·
            refine ⟨1990742267784747761962841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5308646047425994031900909 1990742267784747761962841)
            ·
              refine ⟨1493056700838560821472131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1990742267784747761962841 1493056700838560821472131)
              ·
                refine ⟨2239585051257841232208197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493056700838560821472131 2239585051257841232208197)
                ·
                  refine ⟨419922197110845231039037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2239585051257841232208197 419922197110845231039037)
                  ·
                    refine ⟨157470823916566961639639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 419922197110845231039037 157470823916566961639639)
                    ·
                      rfl

theorem cell22_460010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_460010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460010 prefixEnd_460010 := by exact prefixLift 460010
  have htrace : WordTrace (prefixWord ++ tailWord_460010) baseStart_460010 baseEnd_460010 := by
    simpa [prefixWord, tailWord_460010, baseEnd_460010] using wordTrace_append hprefix tailTrace_460010
  have hstable : (prefixWord ++ tailWord_460010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460010).length < 2 ^ (prefixWord ++ tailWord_460010).sum := by decide
  have hdescent : baseEnd_460010 < baseStart_460010 := by decide
  rcases family_descends (prefixWord ++ tailWord_460010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460012 : List Nat := [2, 2, 1, 1, 2, 5, 3, 2, 4]
def baseStart_460012 : Nat := 118140960795 + 460012 * 2 ^ 59
def prefixEnd_460012 : Nat := 4983230072969 + 3 ^ 40 * 460012 * 2
def baseEnd_460012 : Nat := 52490502852479874363211

theorem tailTrace_460012 : CollatzResearch.WordTrace tailWord_460012 prefixEnd_460012 52490502852479874363211 := by
  unfold tailWord_460012
  simp only [CollatzResearch.WordTrace]
  refine ⟨8389008004731281319963145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11185344006308375093284193 8389008004731281319963145)
  ·
    refine ⟨6291756003548460989972359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8389008004731281319963145 6291756003548460989972359)
    ·
      refine ⟨9437634005322691484958539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6291756003548460989972359 9437634005322691484958539)
      ·
        refine ⟨14156451007984037227437809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9437634005322691484958539 14156451007984037227437809)
        ·
          refine ⟨10617338255988027920578357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14156451007984037227437809 10617338255988027920578357)
          ·
            refine ⟨995375461498877617554221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10617338255988027920578357 995375461498877617554221)
            ·
              refine ⟨373265798062079106582833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 995375461498877617554221 373265798062079106582833)
              ·
                refine ⟨279949348546559329937125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373265798062079106582833 279949348546559329937125)
                ·
                  refine ⟨52490502852479874363211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 279949348546559329937125 52490502852479874363211)
                  ·
                    rfl

theorem cell22_460012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_460012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460012 prefixEnd_460012 := by exact prefixLift 460012
  have htrace : WordTrace (prefixWord ++ tailWord_460012) baseStart_460012 baseEnd_460012 := by
    simpa [prefixWord, tailWord_460012, baseEnd_460012] using wordTrace_append hprefix tailTrace_460012
  have hstable : (prefixWord ++ tailWord_460012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460012).length < 2 ^ (prefixWord ++ tailWord_460012).sum := by decide
  have hdescent : baseEnd_460012 < baseStart_460012 := by decide
  rcases family_descends (prefixWord ++ tailWord_460012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460083 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 1, 7]
def baseStart_460083 : Nat := 118140960795 + 460083 * 2 ^ 59
def prefixEnd_460083 : Nat := 4983230072969 + 3 ^ 40 * 460083 * 2
def baseEnd_460083 : Nat := 157495813308419104564415

theorem tailTrace_460083 : CollatzResearch.WordTrace tailWord_460083 prefixEnd_460083 157495813308419104564415 := by
  unfold tailWord_460083
  simp only [CollatzResearch.WordTrace]
  refine ⟨16780605592205341765760903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11187070394803561177173935 16780605592205341765760903)
  ·
    refine ⟨25170908388308012648641355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16780605592205341765760903 25170908388308012648641355)
    ·
      refine ⟨37756362582462018972962033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25170908388308012648641355 37756362582462018972962033)
      ·
        refine ⟨28317271936846514229721525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37756362582462018972962033 28317271936846514229721525)
        ·
          refine ⟨2654744244079360709036393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28317271936846514229721525 2654744244079360709036393)
          ·
            refine ⟨1991058183059520531777295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2654744244079360709036393 1991058183059520531777295)
            ·
              refine ⟨2986587274589280797665943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991058183059520531777295 2986587274589280797665943)
              ·
                refine ⟨4479880911883921196498915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2986587274589280797665943 4479880911883921196498915)
                ·
                  refine ⟨6719821367825881794748373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4479880911883921196498915 6719821367825881794748373)
                  ·
                    refine ⟨157495813308419104564415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6719821367825881794748373 157495813308419104564415)
                    ·
                      rfl

theorem cell22_460083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 7].length) (baseStart_460083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460083 prefixEnd_460083 := by exact prefixLift 460083
  have htrace : WordTrace (prefixWord ++ tailWord_460083) baseStart_460083 baseEnd_460083 := by
    simpa [prefixWord, tailWord_460083, baseEnd_460083] using wordTrace_append hprefix tailTrace_460083
  have hstable : (prefixWord ++ tailWord_460083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460083).length < 2 ^ (prefixWord ++ tailWord_460083).sum := by decide
  have hdescent : baseEnd_460083 < baseStart_460083 := by decide
  rcases family_descends (prefixWord ++ tailWord_460083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460085 : List Nat := [1, 3, 3, 1, 2, 2, 2, 3, 5]
def baseStart_460085 : Nat := 118140960795 + 460085 * 2 ^ 59
def prefixEnd_460085 : Nat := 4983230072969 + 3 ^ 40 * 460085 * 2
def baseEnd_460085 : Nat := 52498832649763922004803

theorem tailTrace_460085 : CollatzResearch.WordTrace tailWord_460085 prefixEnd_460085 52498832649763922004803 := by
  unfold tailWord_460085
  simp only [CollatzResearch.WordTrace]
  refine ⟨16780678538198096107333709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11187119025465397404889139 16780678538198096107333709)
  ·
    refine ⟨6292754451824286040250141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16780678538198096107333709 6292754451824286040250141)
    ·
      refine ⟨2359782919434107265093803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6292754451824286040250141 2359782919434107265093803)
      ·
        refine ⟨3539674379151160897640705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2359782919434107265093803 3539674379151160897640705)
        ·
          refine ⟨2654755784363370673230529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3539674379151160897640705 2654755784363370673230529)
          ·
            refine ⟨1991066838272528004922897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2654755784363370673230529 1991066838272528004922897)
            ·
              refine ⟨1493300128704396003692173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1991066838272528004922897 1493300128704396003692173)
              ·
                refine ⟨559987548264148501384565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1493300128704396003692173 559987548264148501384565)
                ·
                  refine ⟨52498832649763922004803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 559987548264148501384565 52498832649763922004803)
                  ·
                    rfl

theorem cell22_460085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_460085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460085 prefixEnd_460085 := by exact prefixLift 460085
  have htrace : WordTrace (prefixWord ++ tailWord_460085) baseStart_460085 baseEnd_460085 := by
    simpa [prefixWord, tailWord_460085, baseEnd_460085] using wordTrace_append hprefix tailTrace_460085
  have hstable : (prefixWord ++ tailWord_460085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460085).length < 2 ^ (prefixWord ++ tailWord_460085).sum := by decide
  have hdescent : baseEnd_460085 < baseStart_460085 := by decide
  rcases family_descends (prefixWord ++ tailWord_460085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460113 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 8]
def baseStart_460113 : Nat := 118140960795 + 460113 * 2 ^ 59
def prefixEnd_460113 : Nat := 4983230072969 + 3 ^ 40 * 460113 * 2
def baseEnd_460113 : Nat := 52502027640503008771441

theorem tailTrace_460113 : CollatzResearch.WordTrace tailWord_460113 prefixEnd_460113 52502027640503008771441 := by
  unfold tailWord_460113
  simp only [CollatzResearch.WordTrace]
  refine ⟨16781699782096656889352993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11187799854731104592901995 16781699782096656889352993)
  ·
    refine ⟨12586274836572492667014745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16781699782096656889352993 12586274836572492667014745)
    ·
      refine ⟨9439706127429369500261059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12586274836572492667014745 9439706127429369500261059)
      ·
        refine ⟨14159559191144054250391589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9439706127429369500261059 14159559191144054250391589)
        ·
          refine ⟨2654917348339510171948423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14159559191144054250391589 2654917348339510171948423)
          ·
            refine ⟨3982376022509265257922635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654917348339510171948423 3982376022509265257922635)
            ·
              refine ⟨5973564033763897886883953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3982376022509265257922635 5973564033763897886883953)
              ·
                refine ⟨4480173025322923415162965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5973564033763897886883953 4480173025322923415162965)
                ·
                  refine ⟨52502027640503008771441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4480173025322923415162965 52502027640503008771441)
                  ·
                    rfl

theorem cell22_460113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 8].length) (baseStart_460113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460113 prefixEnd_460113 := by exact prefixLift 460113
  have htrace : WordTrace (prefixWord ++ tailWord_460113) baseStart_460113 baseEnd_460113 := by
    simpa [prefixWord, tailWord_460113, baseEnd_460113] using wordTrace_append hprefix tailTrace_460113
  have hstable : (prefixWord ++ tailWord_460113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460113).length < 2 ^ (prefixWord ++ tailWord_460113).sum := by decide
  have hdescent : baseEnd_460113 < baseStart_460113 := by decide
  rcases family_descends (prefixWord ++ tailWord_460113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460115 : List Nat := [1, 1, 1, 2, 1, 1, 7, 3, 1, 4]
def baseStart_460115 : Nat := 118140960795 + 460115 * 2 ^ 59
def prefixEnd_460115 : Nat := 4983230072969 + 3 ^ 40 * 460115 * 2
def baseEnd_460115 : Nat := 157506767562381687764317

theorem tailTrace_460115 : CollatzResearch.WordTrace tailWord_460115 prefixEnd_460115 157506767562381687764317 := by
  unfold tailWord_460115
  simp only [CollatzResearch.WordTrace]
  refine ⟨16781772728089411230925799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11187848485392940820617199 16781772728089411230925799)
  ·
    refine ⟨25172659092134116846388699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16781772728089411230925799 25172659092134116846388699)
    ·
      refine ⟨37758988638201175269583049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25172659092134116846388699 37758988638201175269583049)
      ·
        refine ⟨28319241478650881452187287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37758988638201175269583049 28319241478650881452187287)
        ·
          refine ⟨42478862217976322178280931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28319241478650881452187287 42478862217976322178280931)
          ·
            refine ⟨63718293326964483267421397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42478862217976322178280931 63718293326964483267421397)
            ·
              refine ⟨1493397499850730076580189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 63718293326964483267421397 1493397499850730076580189)
              ·
                refine ⟨560024062444023778717571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1493397499850730076580189 560024062444023778717571)
                ·
                  refine ⟨840036093666035668076357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560024062444023778717571 840036093666035668076357)
                  ·
                    refine ⟨157506767562381687764317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 840036093666035668076357 157506767562381687764317)
                    ·
                      rfl

theorem cell22_460115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 4].length) (baseStart_460115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460115 prefixEnd_460115 := by exact prefixLift 460115
  have htrace : WordTrace (prefixWord ++ tailWord_460115) baseStart_460115 baseEnd_460115 := by
    simpa [prefixWord, tailWord_460115, baseEnd_460115] using wordTrace_append hprefix tailTrace_460115
  have hstable : (prefixWord ++ tailWord_460115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460115).length < 2 ^ (prefixWord ++ tailWord_460115).sum := by decide
  have hdescent : baseEnd_460115 < baseStart_460115 := by decide
  rcases family_descends (prefixWord ++ tailWord_460115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460143 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 3, 6]
def baseStart_460143 : Nat := 118140960795 + 460143 * 2 ^ 59
def prefixEnd_460143 : Nat := 4983230072969 + 3 ^ 40 * 460143 * 2
def baseEnd_460143 : Nat := 157516352534598948064231

theorem tailTrace_460143 : CollatzResearch.WordTrace tailWord_460143 prefixEnd_460143 157516352534598948064231 := by
  unfold tailWord_460143
  simp only [CollatzResearch.WordTrace]
  refine ⟨16782793971987972012945083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11188529314658648008630055 16782793971987972012945083)
  ·
    refine ⟨25174190957981958019417625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16782793971987972012945083 25174190957981958019417625)
    ·
      refine ⟨18880643218486468514563219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25174190957981958019417625 18880643218486468514563219)
      ·
        refine ⟨28320964827729702771844829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18880643218486468514563219 28320964827729702771844829)
        ·
          refine ⟨10620361810398638539441811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28320964827729702771844829 10620361810398638539441811)
          ·
            refine ⟨15930542715597957809162717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10620361810398638539441811 15930542715597957809162717)
            ·
              refine ⟨5973953518349234178436019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15930542715597957809162717 5973953518349234178436019)
              ·
                refine ⟨8960930277523851267654029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5973953518349234178436019 8960930277523851267654029)
                ·
                  refine ⟨3360348854071444225370261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8960930277523851267654029 3360348854071444225370261)
                  ·
                    refine ⟨157516352534598948064231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3360348854071444225370261 157516352534598948064231)
                    ·
                      rfl

theorem cell22_460143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_460143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460143 prefixEnd_460143 := by exact prefixLift 460143
  have htrace : WordTrace (prefixWord ++ tailWord_460143) baseStart_460143 baseEnd_460143 := by
    simpa [prefixWord, tailWord_460143, baseEnd_460143] using wordTrace_append hprefix tailTrace_460143
  have hstable : (prefixWord ++ tailWord_460143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460143).length < 2 ^ (prefixWord ++ tailWord_460143).sum := by decide
  have hdescent : baseEnd_460143 < baseStart_460143 := by decide
  rcases family_descends (prefixWord ++ tailWord_460143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460145 : List Nat := [1, 2, 2, 2, 1, 2, 5, 1, 1, 5]
def baseStart_460145 : Nat := 118140960795 + 460145 * 2 ^ 59
def prefixEnd_460145 : Nat := 4983230072969 + 3 ^ 40 * 460145 * 2
def baseEnd_460145 : Nat := 157517037175471609514225

theorem tailTrace_460145 : CollatzResearch.WordTrace tailWord_460145 prefixEnd_460145 157517037175471609514225 := by
  unfold tailWord_460145
  simp only [CollatzResearch.WordTrace]
  refine ⟨16782866917980726354517889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11188577945320484236345259 16782866917980726354517889)
  ·
    refine ⟨12587150188485544765888417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16782866917980726354517889 12587150188485544765888417)
    ·
      refine ⟨9440362641364158574416313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12587150188485544765888417 9440362641364158574416313)
      ·
        refine ⟨7080271981023118930812235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9440362641364158574416313 7080271981023118930812235)
        ·
          refine ⟨10620407971534678396218353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7080271981023118930812235 10620407971534678396218353)
          ·
            refine ⟨7965305978651008797163765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10620407971534678396218353 7965305978651008797163765)
            ·
              refine ⟨746747435498532074734103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7965305978651008797163765 746747435498532074734103)
              ·
                refine ⟨1120121153247798112101155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746747435498532074734103 1120121153247798112101155)
                ·
                  refine ⟨1680181729871697168151733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120121153247798112101155 1680181729871697168151733)
                  ·
                    refine ⟨157517037175471609514225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1680181729871697168151733 157517037175471609514225)
                    ·
                      rfl

theorem cell22_460145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_460145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460145 prefixEnd_460145 := by exact prefixLift 460145
  have htrace : WordTrace (prefixWord ++ tailWord_460145) baseStart_460145 baseEnd_460145 := by
    simpa [prefixWord, tailWord_460145, baseEnd_460145] using wordTrace_append hprefix tailTrace_460145
  have hstable : (prefixWord ++ tailWord_460145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460145).length < 2 ^ (prefixWord ++ tailWord_460145).sum := by decide
  have hdescent : baseEnd_460145 < baseStart_460145 := by decide
  rcases family_descends (prefixWord ++ tailWord_460145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460149 : List Nat := [1, 3, 4, 1, 3, 1, 2, 2, 1, 4]
def baseStart_460149 : Nat := 118140960795 + 460149 * 2 ^ 59
def prefixEnd_460149 : Nat := 4983230072969 + 3 ^ 40 * 460149 * 2
def baseEnd_460149 : Nat := 157518406457216932414213

theorem tailTrace_460149 : CollatzResearch.WordTrace tailWord_460149 prefixEnd_460149 157518406457216932414213 := by
  unfold tailWord_460149
  simp only [CollatzResearch.WordTrace]
  refine ⟨16783012809966235037663501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11188675206644156691775667 16783012809966235037663501)
  ·
    refine ⟨6293629803737338139123813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16783012809966235037663501 6293629803737338139123813)
    ·
      refine ⟨1180055588200750901085715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6293629803737338139123813 1180055588200750901085715)
      ·
        refine ⟨1770083382301126351628573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180055588200750901085715 1770083382301126351628573)
        ·
          refine ⟨663781268362922381860715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1770083382301126351628573 663781268362922381860715)
          ·
            refine ⟨995671902544383572791073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663781268362922381860715 995671902544383572791073)
            ·
              refine ⟨746753926908287679593305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 995671902544383572791073 746753926908287679593305)
              ·
                refine ⟨560065445181215759694979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746753926908287679593305 560065445181215759694979)
                ·
                  refine ⟨840098167771823639542469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560065445181215759694979 840098167771823639542469)
                  ·
                    refine ⟨157518406457216932414213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 840098167771823639542469 157518406457216932414213)
                    ·
                      rfl

theorem cell22_460149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_460149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460149 prefixEnd_460149 := by exact prefixLift 460149
  have htrace : WordTrace (prefixWord ++ tailWord_460149) baseStart_460149 baseEnd_460149 := by
    simpa [prefixWord, tailWord_460149, baseEnd_460149] using wordTrace_append hprefix tailTrace_460149
  have hstable : (prefixWord ++ tailWord_460149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460149).length < 2 ^ (prefixWord ++ tailWord_460149).sum := by decide
  have hdescent : baseEnd_460149 < baseStart_460149 := by decide
  rcases family_descends (prefixWord ++ tailWord_460149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460164 : List Nat := [2, 3, 2, 1, 1, 5, 1, 3, 4]
def baseStart_460164 : Nat := 118140960795 + 460164 * 2 ^ 59
def prefixEnd_460164 : Nat := 4983230072969 + 3 ^ 40 * 460164 * 2
def baseEnd_460164 : Nat := 52507847087920631096389

theorem tailTrace_460164 : CollatzResearch.WordTrace tailWord_460164 prefixEnd_460164 52507847087920631096389 := by
  unfold tailWord_460164
  simp only [CollatzResearch.WordTrace]
  refine ⟨8391779952455946299729773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11189039936607928399639697 8391779952455946299729773)
  ·
    refine ⟨3146917482170979862398665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8391779952455946299729773 3146917482170979862398665)
    ·
      refine ⟨2360188111628234896798999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3146917482170979862398665 2360188111628234896798999)
      ·
        refine ⟨3540282167442352345198499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2360188111628234896798999 3540282167442352345198499)
        ·
          refine ⟨5310423251163528517797749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3540282167442352345198499 5310423251163528517797749)
          ·
            refine ⟨497852179796580798543539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5310423251163528517797749 497852179796580798543539)
            ·
              refine ⟨746778269694871197815309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497852179796580798543539 746778269694871197815309)
              ·
                refine ⟨280041851135576699180741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 746778269694871197815309 280041851135576699180741)
                ·
                  refine ⟨52507847087920631096389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280041851135576699180741 52507847087920631096389)
                  ·
                    rfl

theorem cell22_460164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_460164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460164 prefixEnd_460164 := by exact prefixLift 460164
  have htrace : WordTrace (prefixWord ++ tailWord_460164) baseStart_460164 baseEnd_460164 := by
    simpa [prefixWord, tailWord_460164, baseEnd_460164] using wordTrace_append hprefix tailTrace_460164
  have hstable : (prefixWord ++ tailWord_460164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460164).length < 2 ^ (prefixWord ++ tailWord_460164).sum := by decide
  have hdescent : baseEnd_460164 < baseStart_460164 := by decide
  rcases family_descends (prefixWord ++ tailWord_460164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460226 : List Nat := [3, 5, 2, 1, 1, 10]
def baseStart_460226 : Nat := 118140960795 + 460226 * 2 ^ 59
def prefixEnd_460226 : Nat := 4983230072969 + 3 ^ 40 * 460226 * 2
def baseEnd_460226 : Nat := 1944997100380424669617

theorem tailTrace_460226 : CollatzResearch.WordTrace tailWord_460226 prefixEnd_460226 1944997100380424669617 := by
  unfold tailWord_460226
  simp only [CollatzResearch.WordTrace]
  refine ⟨4196455307671819297054133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11190547487124851458811021 4196455307671819297054133)
  ·
    refine ⟨393417685094233059098825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4196455307671819297054133 393417685094233059098825)
    ·
      refine ⟨295063263820674794324119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393417685094233059098825 295063263820674794324119)
      ·
        refine ⟨442594895731012191486179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295063263820674794324119 442594895731012191486179)
        ·
          refine ⟨663892343596518287229269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442594895731012191486179 663892343596518287229269)
          ·
            refine ⟨1944997100380424669617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 663892343596518287229269 1944997100380424669617)
            ·
              rfl

theorem cell22_460226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 10].length) (baseStart_460226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460226 prefixEnd_460226 := by exact prefixLift 460226
  have htrace : WordTrace (prefixWord ++ tailWord_460226) baseStart_460226 baseEnd_460226 := by
    simpa [prefixWord, tailWord_460226, baseEnd_460226] using wordTrace_append hprefix tailTrace_460226
  have hstable : (prefixWord ++ tailWord_460226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460226).length < 2 ^ (prefixWord ++ tailWord_460226).sum := by decide
  have hdescent : baseEnd_460226 < baseStart_460226 := by decide
  rcases family_descends (prefixWord ++ tailWord_460226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460284 : List Nat := [2, 2, 2, 1, 2, 1, 6, 1, 1, 4]
def baseStart_460284 : Nat := 118140960795 + 460284 * 2 ^ 59
def prefixEnd_460284 : Nat := 4983230072969 + 3 ^ 40 * 460284 * 2
def baseEnd_460284 : Nat := 157564619716121580288799

theorem tailTrace_460284 : CollatzResearch.WordTrace tailWord_460284 prefixEnd_460284 157564619716121580288799 := by
  unfold tailWord_460284
  simp only [CollatzResearch.WordTrace]
  refine ⟨8393968332238576546913953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11191957776318102062551937 8393968332238576546913953)
  ·
    refine ⟨6295476249178932410185465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8393968332238576546913953 6295476249178932410185465)
    ·
      refine ⟨4721607186884199307639099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6295476249178932410185465 4721607186884199307639099)
      ·
        refine ⟨7082410780326298961458649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4721607186884199307639099 7082410780326298961458649)
        ·
          refine ⟨5311808085244724221093987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7082410780326298961458649 5311808085244724221093987)
          ·
            refine ⟨7967712127867086331640981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5311808085244724221093987 7967712127867086331640981)
            ·
              refine ⟨373486505993769671795671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7967712127867086331640981 373486505993769671795671)
              ·
                refine ⟨560229758990654507693507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373486505993769671795671 560229758990654507693507)
                ·
                  refine ⟨840344638485981761540261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560229758990654507693507 840344638485981761540261)
                  ·
                    refine ⟨157564619716121580288799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 840344638485981761540261 157564619716121580288799)
                    ·
                      rfl

theorem cell22_460284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_460284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460284 prefixEnd_460284 := by exact prefixLift 460284
  have htrace : WordTrace (prefixWord ++ tailWord_460284) baseStart_460284 baseEnd_460284 := by
    simpa [prefixWord, tailWord_460284, baseEnd_460284] using wordTrace_append hprefix tailTrace_460284
  have hstable : (prefixWord ++ tailWord_460284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460284).length < 2 ^ (prefixWord ++ tailWord_460284).sum := by decide
  have hdescent : baseEnd_460284 < baseStart_460284 := by decide
  rcases family_descends (prefixWord ++ tailWord_460284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460297 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 4, 3]
def baseStart_460297 : Nat := 118140960795 + 460297 * 2 ^ 59
def prefixEnd_460297 : Nat := 4983230072969 + 3 ^ 40 * 460297 * 2
def baseEnd_460297 : Nat := 157569069881793879713759

theorem tailTrace_460297 : CollatzResearch.WordTrace tailWord_460297 prefixEnd_460297 157569069881793879713759 := by
  unfold tailWord_460297
  simp only [CollatzResearch.WordTrace]
  refine ⟨16788410813430056314051145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11192273875620037542700763 16788410813430056314051145)
  ·
    refine ⟨12591308110072542235538359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16788410813430056314051145 12591308110072542235538359)
    ·
      refine ⟨18886962165108813353307539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12591308110072542235538359 18886962165108813353307539)
      ·
        refine ⟨28330443247663220029961309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18886962165108813353307539 28330443247663220029961309)
        ·
          refine ⟨10623916217873707511235491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28330443247663220029961309 10623916217873707511235491)
          ·
            refine ⟨15935874326810561266853237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10623916217873707511235491 15935874326810561266853237)
            ·
              refine ⟨1493988218138490118767491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15935874326810561266853237 1493988218138490118767491)
              ·
                refine ⟨2240982327207735178151237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493988218138490118767491 2240982327207735178151237)
                ·
                  refine ⟨420184186351450345903357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2240982327207735178151237 420184186351450345903357)
                  ·
                    refine ⟨157569069881793879713759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 420184186351450345903357 157569069881793879713759)
                    ·
                      rfl

theorem cell22_460297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 3].length) (baseStart_460297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460297 prefixEnd_460297 := by exact prefixLift 460297
  have htrace : WordTrace (prefixWord ++ tailWord_460297) baseStart_460297 baseEnd_460297 := by
    simpa [prefixWord, tailWord_460297, baseEnd_460297] using wordTrace_append hprefix tailTrace_460297
  have hstable : (prefixWord ++ tailWord_460297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460297).length < 2 ^ (prefixWord ++ tailWord_460297).sum := by decide
  have hdescent : baseEnd_460297 < baseStart_460297 := by decide
  rcases family_descends (prefixWord ++ tailWord_460297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460325 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 1, 9]
def baseStart_460325 : Nat := 118140960795 + 460325 * 2 ^ 59
def prefixEnd_460325 : Nat := 4983230072969 + 3 ^ 40 * 460325 * 2
def baseEnd_460325 : Nat := 157578654854011140013673

theorem tailTrace_460325 : CollatzResearch.WordTrace tailWord_460325 prefixEnd_460325 157578654854011140013673 := by
  unfold tailWord_460325
  simp only [CollatzResearch.WordTrace]
  refine ⟨16789432057328617096070429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11192954704885744730713619 16789432057328617096070429)
  ·
    refine ⟨6296037021498231411026411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16789432057328617096070429 6296037021498231411026411)
    ·
      refine ⟨9444055532247347116539617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6296037021498231411026411 9444055532247347116539617)
      ·
        refine ⟨7083041649185510337404713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9444055532247347116539617 7083041649185510337404713)
        ·
          refine ⟨5312281236889132753053535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7083041649185510337404713 5312281236889132753053535)
          ·
            refine ⟨7968421855333699129580303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5312281236889132753053535 7968421855333699129580303)
            ·
              refine ⟨11952632783000548694370455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7968421855333699129580303 11952632783000548694370455)
              ·
                refine ⟨17928949174500823041555683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11952632783000548694370455 17928949174500823041555683)
                ·
                  refine ⟨26893423761751234562333525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17928949174500823041555683 26893423761751234562333525)
                  ·
                    refine ⟨157578654854011140013673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 26893423761751234562333525 157578654854011140013673)
                    ·
                      rfl

theorem cell22_460325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_460325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460325 prefixEnd_460325 := by exact prefixLift 460325
  have htrace : WordTrace (prefixWord ++ tailWord_460325) baseStart_460325 baseEnd_460325 := by
    simpa [prefixWord, tailWord_460325, baseEnd_460325] using wordTrace_append hprefix tailTrace_460325
  have hstable : (prefixWord ++ tailWord_460325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460325).length < 2 ^ (prefixWord ++ tailWord_460325).sum := by decide
  have hdescent : baseEnd_460325 < baseStart_460325 := by decide
  rcases family_descends (prefixWord ++ tailWord_460325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460365 : List Nat := [1, 6, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_460365 : Nat := 118140960795 + 460365 * 2 ^ 59
def prefixEnd_460365 : Nat := 4983230072969 + 3 ^ 40 * 460365 * 2
def baseEnd_460365 : Nat := 157592347671464369013551

theorem tailTrace_460365 : CollatzResearch.WordTrace tailWord_460365 prefixEnd_460365 157592347671464369013551 := by
  unfold tailWord_460365
  simp only [CollatzResearch.WordTrace]
  refine ⟨16790890977183703927526549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11193927318122469285017699 16790890977183703927526549)
  ·
    refine ⟨787073014555486121602807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16790890977183703927526549 787073014555486121602807)
    ·
      refine ⟨1180609521833229182404211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 787073014555486121602807 1180609521833229182404211)
      ·
        refine ⟨1770914282749843773606317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180609521833229182404211 1770914282749843773606317)
        ·
          refine ⟨664092856031191415102369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1770914282749843773606317 664092856031191415102369)
          ·
            refine ⟨498069642023393561326777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 664092856031191415102369 498069642023393561326777)
            ·
              refine ⟨373552231517545170995083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498069642023393561326777 373552231517545170995083)
              ·
                refine ⟨560328347276317756492625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373552231517545170995083 560328347276317756492625)
                ·
                  refine ⟨420246260457238317369469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560328347276317756492625 420246260457238317369469)
                  ·
                    refine ⟨157592347671464369013551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 420246260457238317369469 157592347671464369013551)
                    ·
                      rfl

theorem cell22_460365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_460365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460365 prefixEnd_460365 := by exact prefixLift 460365
  have htrace : WordTrace (prefixWord ++ tailWord_460365) baseStart_460365 baseEnd_460365 := by
    simpa [prefixWord, tailWord_460365, baseEnd_460365] using wordTrace_append hprefix tailTrace_460365
  have hstable : (prefixWord ++ tailWord_460365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460365).length < 2 ^ (prefixWord ++ tailWord_460365).sum := by decide
  have hdescent : baseEnd_460365 < baseStart_460365 := by decide
  rcases family_descends (prefixWord ++ tailWord_460365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460406 : List Nat := [5, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_460406 : Nat := 118140960795 + 460406 * 2 ^ 59
def prefixEnd_460406 : Nat := 4983230072969 + 3 ^ 40 * 460406 * 2
def baseEnd_460406 : Nat := 52535460936451309579475

theorem tailTrace_460406 : CollatzResearch.WordTrace tailWord_460406 prefixEnd_460406 52535460936451309579475 := by
  unfold tailWord_460406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1049524148127197995610567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11194924246690111953179381 1049524148127197995610567)
  ·
    refine ⟨1574286222190796993415851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1049524148127197995610567 1574286222190796993415851)
    ·
      refine ⟨2361429333286195490123777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1574286222190796993415851 2361429333286195490123777)
      ·
        refine ⟨1771071999964646617592833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2361429333286195490123777 1771071999964646617592833)
        ·
          refine ⟨1328303999973484963194625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1771071999964646617592833 1328303999973484963194625)
          ·
            refine ⟨996227999980113722395969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1328303999973484963194625 996227999980113722395969)
            ·
              refine ⟨747170999985085291796977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 996227999980113722395969 747170999985085291796977)
              ·
                refine ⟨560378249988813968847733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 747170999985085291796977 560378249988813968847733)
                ·
                  refine ⟨52535460936451309579475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 560378249988813968847733 52535460936451309579475)
                  ·
                    rfl

theorem cell22_460406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_460406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460406 prefixEnd_460406 := by exact prefixLift 460406
  have htrace : WordTrace (prefixWord ++ tailWord_460406) baseStart_460406 baseEnd_460406 := by
    simpa [prefixWord, tailWord_460406, baseEnd_460406] using wordTrace_append hprefix tailTrace_460406
  have hstable : (prefixWord ++ tailWord_460406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460406).length < 2 ^ (prefixWord ++ tailWord_460406).sum := by decide
  have hdescent : baseEnd_460406 < baseStart_460406 := by decide
  rcases family_descends (prefixWord ++ tailWord_460406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460449 : List Nat := [1, 2, 3, 3, 2, 1, 2, 2, 1, 5]
def baseStart_460449 : Nat := 118140960795 + 460449 * 2 ^ 59
def prefixEnd_460449 : Nat := 4983230072969 + 3 ^ 40 * 460449 * 2
def baseEnd_460449 : Nat := 157621102588116149913293

theorem tailTrace_460449 : CollatzResearch.WordTrace tailWord_460449 prefixEnd_460449 157621102588116149913293 := by
  unfold tailWord_460449
  simp only [CollatzResearch.WordTrace]
  refine ⟨16793954708879386273584401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11195969805919590849056267 16793954708879386273584401)
  ·
    refine ⟨12595466031659539705188301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16793954708879386273584401 12595466031659539705188301)
    ·
      refine ⟨4723299761872327389445613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12595466031659539705188301 4723299761872327389445613)
      ·
        refine ⟨1771237410702122771042105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4723299761872327389445613 1771237410702122771042105)
        ·
          refine ⟨1328428058026592078281579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1771237410702122771042105 1328428058026592078281579)
          ·
            refine ⟨1992642087039888117422369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328428058026592078281579 1992642087039888117422369)
            ·
              refine ⟨1494481565279916088066777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1992642087039888117422369 1494481565279916088066777)
              ·
                refine ⟨1120861173959937066050083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1494481565279916088066777 1120861173959937066050083)
                ·
                  refine ⟨1681291760939905599075125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120861173959937066050083 1681291760939905599075125)
                  ·
                    refine ⟨157621102588116149913293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1681291760939905599075125 157621102588116149913293)
                    ·
                      rfl

theorem cell22_460449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_460449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460449 prefixEnd_460449 := by exact prefixLift 460449
  have htrace : WordTrace (prefixWord ++ tailWord_460449) baseStart_460449 baseEnd_460449 := by
    simpa [prefixWord, tailWord_460449, baseEnd_460449] using wordTrace_append hprefix tailTrace_460449
  have hstable : (prefixWord ++ tailWord_460449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460449).length < 2 ^ (prefixWord ++ tailWord_460449).sum := by decide
  have hdescent : baseEnd_460449 < baseStart_460449 := by decide
  rcases family_descends (prefixWord ++ tailWord_460449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460466 : List Nat := [3, 2, 1, 1, 1, 2, 5, 2, 2, 3]
def baseStart_460466 : Nat := 118140960795 + 460466 * 2 ^ 59
def prefixEnd_460466 : Nat := 4983230072969 + 3 ^ 40 * 460466 * 2
def baseEnd_460466 : Nat := 157626922035533772238241

theorem tailTrace_460466 : CollatzResearch.WordTrace tailWord_460466 prefixEnd_460466 157626922035533772238241 := by
  unfold tailWord_460466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4198643687454449544238313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11196383166545198784635501 4198643687454449544238313)
  ·
    refine ⟨3148982765590837158178735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4198643687454449544238313 3148982765590837158178735)
    ·
      refine ⟨4723474148386255737268103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3148982765590837158178735 4723474148386255737268103)
      ·
        refine ⟨7085211222579383605902155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4723474148386255737268103 7085211222579383605902155)
        ·
          refine ⟨10627816833869075408853233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7085211222579383605902155 10627816833869075408853233)
          ·
            refine ⟨7970862625401806556639925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10627816833869075408853233 7970862625401806556639925)
            ·
              refine ⟨747268371131419364684993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7970862625401806556639925 747268371131419364684993)
              ·
                refine ⟨560451278348564523513745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 747268371131419364684993 560451278348564523513745)
                ·
                  refine ⟨420338458761423392635309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560451278348564523513745 420338458761423392635309)
                  ·
                    refine ⟨157626922035533772238241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 420338458761423392635309 157626922035533772238241)
                    ·
                      rfl

theorem cell22_460466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_460466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460466 prefixEnd_460466 := by exact prefixLift 460466
  have htrace : WordTrace (prefixWord ++ tailWord_460466) baseStart_460466 baseEnd_460466 := by
    simpa [prefixWord, tailWord_460466, baseEnd_460466] using wordTrace_append hprefix tailTrace_460466
  have hstable : (prefixWord ++ tailWord_460466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460466).length < 2 ^ (prefixWord ++ tailWord_460466).sum := by decide
  have hdescent : baseEnd_460466 < baseStart_460466 := by decide
  rcases family_descends (prefixWord ++ tailWord_460466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460502 : List Nat := [5, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_460502 : Nat := 118140960795 + 460502 * 2 ^ 59
def prefixEnd_460502 : Nat := 4983230072969 + 3 ^ 40 * 460502 * 2
def baseEnd_460502 : Nat := 52546415190413892779377

theorem tailTrace_460502 : CollatzResearch.WordTrace tailWord_460502 prefixEnd_460502 52546415190413892779377 := by
  unfold tailWord_460502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1049742986105461020328985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11197258518458250883509173 1049742986105461020328985)
  ·
    refine ⟨787307239579095765246739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1049742986105461020328985 787307239579095765246739)
    ·
      refine ⟨1180960859368643647870109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 787307239579095765246739 1180960859368643647870109)
      ·
        refine ⟨442860322263241367951291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1180960859368643647870109 442860322263241367951291)
        ·
          refine ⟨664290483394862051926937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442860322263241367951291 664290483394862051926937)
          ·
            refine ⟨498217862546146538945203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 664290483394862051926937 498217862546146538945203)
            ·
              refine ⟨747326793819219808417805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498217862546146538945203 747326793819219808417805)
              ·
                refine ⟨280247547682207428156677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 747326793819219808417805 280247547682207428156677)
                ·
                  refine ⟨52546415190413892779377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280247547682207428156677 52546415190413892779377)
                  ·
                    rfl

theorem cell22_460502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_460502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460502 prefixEnd_460502 := by exact prefixLift 460502
  have htrace : WordTrace (prefixWord ++ tailWord_460502) baseStart_460502 baseEnd_460502 := by
    simpa [prefixWord, tailWord_460502, baseEnd_460502] using wordTrace_append hprefix tailTrace_460502
  have hstable : (prefixWord ++ tailWord_460502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460502).length < 2 ^ (prefixWord ++ tailWord_460502).sum := by decide
  have hdescent : baseEnd_460502 < baseStart_460502 := by decide
  rcases family_descends (prefixWord ++ tailWord_460502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460537 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 1, 10]
def baseStart_460537 : Nat := 118140960795 + 460537 * 2 ^ 59
def prefixEnd_460537 : Nat := 4983230072969 + 3 ^ 40 * 460537 * 2
def baseEnd_460537 : Nat := 157651226786513253713023

theorem tailTrace_460537 : CollatzResearch.WordTrace tailWord_460537 prefixEnd_460537 157651226786513253713023 := by
  unfold tailWord_460537
  simp only [CollatzResearch.WordTrace]
  refine ⟨16797164332560577302787865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11198109555040384868525243 16797164332560577302787865)
  ·
    refine ⟨12597873249420432977090899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16797164332560577302787865 12597873249420432977090899)
    ·
      refine ⟨18896809874130649465636349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12597873249420432977090899 18896809874130649465636349)
      ·
        refine ⟨7086303702798993549613631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18896809874130649465636349 7086303702798993549613631)
        ·
          refine ⟨10629455554198490324420447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7086303702798993549613631 10629455554198490324420447)
          ·
            refine ⟨15944183331297735486630671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10629455554198490324420447 15944183331297735486630671)
            ·
              refine ⟨23916274996946603229946007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15944183331297735486630671 23916274996946603229946007)
              ·
                refine ⟨35874412495419904844919011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23916274996946603229946007 35874412495419904844919011)
                ·
                  refine ⟨53811618743129857267378517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35874412495419904844919011 53811618743129857267378517)
                  ·
                    refine ⟨157651226786513253713023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 53811618743129857267378517 157651226786513253713023)
                    ·
                      rfl

theorem cell22_460537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_460537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460537 prefixEnd_460537 := by exact prefixLift 460537
  have htrace : WordTrace (prefixWord ++ tailWord_460537) baseStart_460537 baseEnd_460537 := by
    simpa [prefixWord, tailWord_460537, baseEnd_460537] using wordTrace_append hprefix tailTrace_460537
  have hstable : (prefixWord ++ tailWord_460537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460537).length < 2 ^ (prefixWord ++ tailWord_460537).sum := by decide
  have hdescent : baseEnd_460537 < baseStart_460537 := by decide
  rcases family_descends (prefixWord ++ tailWord_460537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460616 : List Nat := [2, 1, 3, 1, 1, 4, 3, 1, 2, 4]
def baseStart_460616 : Nat := 118140960795 + 460616 * 2 ^ 59
def prefixEnd_460616 : Nat := 4983230072969 + 3 ^ 40 * 460616 * 2
def baseEnd_460616 : Nat := 157678270100983380987781

theorem tailTrace_460616 : CollatzResearch.WordTrace tailWord_460616 prefixEnd_460616 157678270100983380987781 := by
  unfold tailWord_460616
  simp only [CollatzResearch.WordTrace]
  refine ⟨8400022849637186897456851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11200030466182915863275801 8400022849637186897456851)
  ·
    refine ⟨12600034274455780346185277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8400022849637186897456851 12600034274455780346185277)
    ·
      refine ⟨4725012852920917629819479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12600034274455780346185277 4725012852920917629819479)
      ·
        refine ⟨7087519279381376444729219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4725012852920917629819479 7087519279381376444729219)
        ·
          refine ⟨10631278919072064667093829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7087519279381376444729219 10631278919072064667093829)
          ·
            refine ⟨1993364797326012125080093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10631278919072064667093829 1993364797326012125080093)
            ·
              refine ⟨747511798997254546905035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1993364797326012125080093 747511798997254546905035)
              ·
                refine ⟨1121267698495881820357553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747511798997254546905035 1121267698495881820357553)
                ·
                  refine ⟨840950773871911365268165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1121267698495881820357553 840950773871911365268165)
                  ·
                    refine ⟨157678270100983380987781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 840950773871911365268165 157678270100983380987781)
                    ·
                      rfl

theorem cell22_460616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_460616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460616 prefixEnd_460616 := by exact prefixLift 460616
  have htrace : WordTrace (prefixWord ++ tailWord_460616) baseStart_460616 baseEnd_460616 := by
    simpa [prefixWord, tailWord_460616, baseEnd_460616] using wordTrace_append hprefix tailTrace_460616
  have hstable : (prefixWord ++ tailWord_460616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460616).length < 2 ^ (prefixWord ++ tailWord_460616).sum := by decide
  have hdescent : baseEnd_460616 < baseStart_460616 := by decide
  rcases family_descends (prefixWord ++ tailWord_460616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460736 : List Nat := [2, 1, 1, 2, 3, 2, 3, 2, 1, 5]
def baseStart_460736 : Nat := 118140960795 + 460736 * 2 ^ 59
def prefixEnd_460736 : Nat := 4983230072969 + 3 ^ 40 * 460736 * 2
def baseEnd_460736 : Nat := 157719348553343067987413

theorem tailTrace_460736 : CollatzResearch.WordTrace tailWord_460736 prefixEnd_460736 157719348553343067987413 := by
  unfold tailWord_460736
  simp only [CollatzResearch.WordTrace]
  refine ⟨8402211229419817144641031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11202948305893089526188041 8402211229419817144641031)
  ·
    refine ⟨12603316844129725716961547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8402211229419817144641031 12603316844129725716961547)
    ·
      refine ⟨18904975266194588575442321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12603316844129725716961547 18904975266194588575442321)
      ·
        refine ⟨14178731449645941431581741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18904975266194588575442321 14178731449645941431581741)
        ·
          refine ⟨5317024293617228036843153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14178731449645941431581741 5317024293617228036843153)
          ·
            refine ⟨3987768220212921027632365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5317024293617228036843153 3987768220212921027632365)
            ·
              refine ⟨1495413082579845385362137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3987768220212921027632365 1495413082579845385362137)
              ·
                refine ⟨1121559811934884039021603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1495413082579845385362137 1121559811934884039021603)
                ·
                  refine ⟨1682339717902326058532405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1121559811934884039021603 1682339717902326058532405)
                  ·
                    refine ⟨157719348553343067987413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1682339717902326058532405 157719348553343067987413)
                    ·
                      rfl

theorem cell22_460736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_460736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460736 prefixEnd_460736 := by exact prefixLift 460736
  have htrace : WordTrace (prefixWord ++ tailWord_460736) baseStart_460736 baseEnd_460736 := by
    simpa [prefixWord, tailWord_460736, baseEnd_460736] using wordTrace_append hprefix tailTrace_460736
  have hstable : (prefixWord ++ tailWord_460736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460736).length < 2 ^ (prefixWord ++ tailWord_460736).sum := by decide
  have hdescent : baseEnd_460736 < baseStart_460736 := by decide
  rcases family_descends (prefixWord ++ tailWord_460736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460751 : List Nat := [1, 1, 2, 1, 1, 5, 1, 4, 2, 4]
def baseStart_460751 : Nat := 118140960795 + 460751 * 2 ^ 59
def prefixEnd_460751 : Nat := 4983230072969 + 3 ^ 40 * 460751 * 2
def baseEnd_460751 : Nat := 157724483359888028862367

theorem tailTrace_460751 : CollatzResearch.WordTrace tailWord_460751 prefixEnd_460751 157724483359888028862367 := by
  unfold tailWord_460751
  simp only [CollatzResearch.WordTrace]
  refine ⟨16804969553785291851078107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11203313035856861234052071 16804969553785291851078107)
  ·
    refine ⟨25207454330677937776617161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16804969553785291851078107 25207454330677937776617161)
    ·
      refine ⟨18905590748008453332462871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25207454330677937776617161 18905590748008453332462871)
      ·
        refine ⟨28358386122012679998694307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18905590748008453332462871 28358386122012679998694307)
        ·
          refine ⟨42537579183019019998041461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28358386122012679998694307 42537579183019019998041461)
          ·
            refine ⟨3987898048408033124816387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42537579183019019998041461 3987898048408033124816387)
            ·
              refine ⟨5981847072612049687224581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3987898048408033124816387 5981847072612049687224581)
              ·
                refine ⟨1121596326114759316354609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5981847072612049687224581 1121596326114759316354609)
                ·
                  refine ⟨841197244586069487265957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1121596326114759316354609 841197244586069487265957)
                  ·
                    refine ⟨157724483359888028862367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 841197244586069487265957 157724483359888028862367)
                    ·
                      rfl

theorem cell22_460751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_460751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460751 prefixEnd_460751 := by exact prefixLift 460751
  have htrace : WordTrace (prefixWord ++ tailWord_460751) baseStart_460751 baseEnd_460751 := by
    simpa [prefixWord, tailWord_460751, baseEnd_460751] using wordTrace_append hprefix tailTrace_460751
  have hstable : (prefixWord ++ tailWord_460751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460751).length < 2 ^ (prefixWord ++ tailWord_460751).sum := by decide
  have hdescent : baseEnd_460751 < baseStart_460751 := by decide
  rcases family_descends (prefixWord ++ tailWord_460751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460785 : List Nat := [1, 2, 2, 2, 5, 2, 1, 1, 2, 4]
def baseStart_460785 : Nat := 118140960795 + 460785 * 2 ^ 59
def prefixEnd_460785 : Nat := 4983230072969 + 3 ^ 40 * 460785 * 2
def baseEnd_460785 : Nat := 157736122254723273512263

theorem tailTrace_460785 : CollatzResearch.WordTrace tailWord_460785 prefixEnd_460785 157736122254723273512263 := by
  unfold tailWord_460785
  simp only [CollatzResearch.WordTrace]
  refine ⟨16806209635662115657815809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11204139757108077105210539 16806209635662115657815809)
  ·
    refine ⟨12604657226746586743361857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16806209635662115657815809 12604657226746586743361857)
    ·
      refine ⟨9453492920059940057521393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12604657226746586743361857 9453492920059940057521393)
      ·
        refine ⟨7090119690044955043141045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9453492920059940057521393 7090119690044955043141045)
        ·
          refine ⟨664698720941714535294473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7090119690044955043141045 664698720941714535294473)
          ·
            refine ⟨498524040706285901470855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 664698720941714535294473 498524040706285901470855)
            ·
              refine ⟨747786061059428852206283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498524040706285901470855 747786061059428852206283)
              ·
                refine ⟨1121679091589143278309425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747786061059428852206283 1121679091589143278309425)
                ·
                  refine ⟨841259318691857458732069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1121679091589143278309425 841259318691857458732069)
                  ·
                    refine ⟨157736122254723273512263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 841259318691857458732069 157736122254723273512263)
                    ·
                      rfl

theorem cell22_460785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_460785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460785 prefixEnd_460785 := by exact prefixLift 460785
  have htrace : WordTrace (prefixWord ++ tailWord_460785) baseStart_460785 baseEnd_460785 := by
    simpa [prefixWord, tailWord_460785, baseEnd_460785] using wordTrace_append hprefix tailTrace_460785
  have hstable : (prefixWord ++ tailWord_460785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460785).length < 2 ^ (prefixWord ++ tailWord_460785).sum := by decide
  have hdescent : baseEnd_460785 < baseStart_460785 := by decide
  rcases family_descends (prefixWord ++ tailWord_460785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460804 : List Nat := [2, 3, 2, 4, 1, 2, 1, 2, 2, 3]
def baseStart_460804 : Nat := 118140960795 + 460804 * 2 ^ 59
def prefixEnd_460804 : Nat := 4983230072969 + 3 ^ 40 * 460804 * 2
def baseEnd_460804 : Nat := 157742626343013557287205

theorem tailTrace_460804 : CollatzResearch.WordTrace tailWord_460804 prefixEnd_460804 157742626343013557287205 := by
  unfold tailWord_460804
  simp only [CollatzResearch.WordTrace]
  refine ⟨8403451311296640951378733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11204601748395521268504977 8403451311296640951378733)
  ·
    refine ⟨3151294241736240356767025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8403451311296640951378733 3151294241736240356767025)
    ·
      refine ⟨2363470681302180267575269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3151294241736240356767025 2363470681302180267575269)
      ·
        refine ⟨443150752744158800170363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2363470681302180267575269 443150752744158800170363)
        ·
          refine ⟨664726129116238200255545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443150752744158800170363 664726129116238200255545)
          ·
            refine ⟨498544596837178650191659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 664726129116238200255545 498544596837178650191659)
            ·
              refine ⟨747816895255767975287489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498544596837178650191659 747816895255767975287489)
              ·
                refine ⟨560862671441825981465617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 747816895255767975287489 560862671441825981465617)
                ·
                  refine ⟨420647003581369486099213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560862671441825981465617 420647003581369486099213)
                  ·
                    refine ⟨157742626343013557287205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 420647003581369486099213 157742626343013557287205)
                    ·
                      rfl

theorem cell22_460804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_460804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460804 prefixEnd_460804 := by exact prefixLift 460804
  have htrace : WordTrace (prefixWord ++ tailWord_460804) baseStart_460804 baseEnd_460804 := by
    simpa [prefixWord, tailWord_460804, baseEnd_460804] using wordTrace_append hprefix tailTrace_460804
  have hstable : (prefixWord ++ tailWord_460804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460804).length < 2 ^ (prefixWord ++ tailWord_460804).sum := by decide
  have hdescent : baseEnd_460804 < baseStart_460804 := by decide
  rcases family_descends (prefixWord ++ tailWord_460804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460811 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 7]
def baseStart_460811 : Nat := 118140960795 + 460811 * 2 ^ 59
def prefixEnd_460811 : Nat := 4983230072969 + 3 ^ 40 * 460811 * 2
def baseEnd_460811 : Nat := 52581674195355957454061

theorem tailTrace_460811 : CollatzResearch.WordTrace tailWord_460811 prefixEnd_460811 52581674195355957454061 := by
  unfold tailWord_460811
  simp only [CollatzResearch.WordTrace]
  refine ⟨16807157933567922098262287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11204771955711948065508191 16807157933567922098262287)
  ·
    refine ⟨25210736900351883147393431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16807157933567922098262287 25210736900351883147393431)
    ·
      refine ⟨37816105350527824721090147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25210736900351883147393431 37816105350527824721090147)
      ·
        refine ⟨56724158025791737081635221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37816105350527824721090147 56724158025791737081635221)
        ·
          refine ⟨2658944907458987675701651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56724158025791737081635221 2658944907458987675701651)
          ·
            refine ⟨3988417361188481513552477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2658944907458987675701651 3988417361188481513552477)
            ·
              refine ⟨1495656510445680567582179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3988417361188481513552477 1495656510445680567582179)
              ·
                refine ⟨2243484765668520851373269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495656510445680567582179 2243484765668520851373269)
                ·
                  refine ⟨52581674195355957454061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2243484765668520851373269 52581674195355957454061)
                  ·
                    rfl

theorem cell22_460811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 7].length) (baseStart_460811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460811 prefixEnd_460811 := by exact prefixLift 460811
  have htrace : WordTrace (prefixWord ++ tailWord_460811) baseStart_460811 baseEnd_460811 := by
    simpa [prefixWord, tailWord_460811, baseEnd_460811] using wordTrace_append hprefix tailTrace_460811
  have hstable : (prefixWord ++ tailWord_460811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460811).length < 2 ^ (prefixWord ++ tailWord_460811).sum := by decide
  have hdescent : baseEnd_460811 < baseStart_460811 := by decide
  rcases family_descends (prefixWord ++ tailWord_460811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460841 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 9, 4]
def baseStart_460841 : Nat := 118140960795 + 460841 * 2 ^ 59
def prefixEnd_460841 : Nat := 4983230072969 + 3 ^ 40 * 460841 * 2
def baseEnd_460841 : Nat := 157755292199157794112091

theorem tailTrace_460841 : CollatzResearch.WordTrace tailWord_460841 prefixEnd_460841 157755292199157794112091 := by
  unfold tailWord_460841
  simp only [CollatzResearch.WordTrace]
  refine ⟨16808252123459237221854377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11205501415639491481236251 16808252123459237221854377)
  ·
    refine ⟨12606189092594427916390783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16808252123459237221854377 12606189092594427916390783)
    ·
      refine ⟨18909283638891641874586175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12606189092594427916390783 18909283638891641874586175)
      ·
        refine ⟨28363925458337462811879263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18909283638891641874586175 28363925458337462811879263)
        ·
          refine ⟨42545888187506194217818895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28363925458337462811879263 42545888187506194217818895)
          ·
            refine ⟨63818832281259291326728343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42545888187506194217818895 63818832281259291326728343)
            ·
              refine ⟨95728248421888936990092515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63818832281259291326728343 95728248421888936990092515)
              ·
                refine ⟨143592372632833405485138773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95728248421888936990092515 143592372632833405485138773)
                ·
                  refine ⟨841361558395508235264485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 143592372632833405485138773 841361558395508235264485)
                  ·
                    refine ⟨157755292199157794112091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 841361558395508235264485 157755292199157794112091)
                    ·
                      rfl

theorem cell22_460841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_460841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460841 prefixEnd_460841 := by exact prefixLift 460841
  have htrace : WordTrace (prefixWord ++ tailWord_460841) baseStart_460841 baseEnd_460841 := by
    simpa [prefixWord, tailWord_460841, baseEnd_460841] using wordTrace_append hprefix tailTrace_460841
  have hstable : (prefixWord ++ tailWord_460841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460841).length < 2 ^ (prefixWord ++ tailWord_460841).sum := by decide
  have hdescent : baseEnd_460841 < baseStart_460841 := by decide
  rcases family_descends (prefixWord ++ tailWord_460841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460892 : List Nat := [2, 2, 4, 1, 1, 4, 1, 2, 1, 4]
def baseStart_460892 : Nat := 118140960795 + 460892 * 2 ^ 59
def prefixEnd_460892 : Nat := 4983230072969 + 3 ^ 40 * 460892 * 2
def baseEnd_460892 : Nat := 157772750541410661086935

theorem tailTrace_460892 : CollatzResearch.WordTrace tailWord_460892 prefixEnd_460892 157772750541410661086935 := by
  unfold tailWord_460892
  simp only [CollatzResearch.WordTrace]
  refine ⟨8405056123137236465980465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11206741497516315287973953 8405056123137236465980465)
  ·
    refine ⟨6303792092352927349485349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8405056123137236465980465 6303792092352927349485349)
    ·
      refine ⟨1181961017316173878028503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6303792092352927349485349 1181961017316173878028503)
      ·
        refine ⟨1772941525974260817042755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1181961017316173878028503 1772941525974260817042755)
        ·
          refine ⟨2659412288961391225564133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1772941525974260817042755 2659412288961391225564133)
          ·
            refine ⟨498639804180260854793275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2659412288961391225564133 498639804180260854793275)
            ·
              refine ⟨747959706270391282189913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498639804180260854793275 747959706270391282189913)
              ·
                refine ⟨560969779702793461642435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 747959706270391282189913 560969779702793461642435)
                ·
                  refine ⟨841454669554190192463653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560969779702793461642435 841454669554190192463653)
                  ·
                    refine ⟨157772750541410661086935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 841454669554190192463653 157772750541410661086935)
                    ·
                      rfl

theorem cell22_460892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_460892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460892 prefixEnd_460892 := by exact prefixLift 460892
  have htrace : WordTrace (prefixWord ++ tailWord_460892) baseStart_460892 baseEnd_460892 := by
    simpa [prefixWord, tailWord_460892, baseEnd_460892] using wordTrace_append hprefix tailTrace_460892
  have hstable : (prefixWord ++ tailWord_460892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460892).length < 2 ^ (prefixWord ++ tailWord_460892).sum := by decide
  have hdescent : baseEnd_460892 < baseStart_460892 := by decide
  rcases family_descends (prefixWord ++ tailWord_460892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460918 : List Nat := [5, 1, 1, 2, 1, 12]
def baseStart_460918 : Nat := 118140960795 + 460918 * 2 ^ 59
def prefixEnd_460918 : Nat := 4983230072969 + 3 ^ 40 * 460918 * 2
def baseEnd_460918 : Nat := 1947921615713027900455

theorem tailTrace_460918 : CollatzResearch.WordTrace tailWord_460918 prefixEnd_460918 1947921615713027900455 := by
  unfold tailWord_460918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1050691284011267460775463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11207373696120186248271605 1050691284011267460775463)
  ·
    refine ⟨1576036926016901191163195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1050691284011267460775463 1576036926016901191163195)
    ·
      refine ⟨2364055389025351786744793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1576036926016901191163195 2364055389025351786744793)
      ·
        refine ⟨1773041541769013840058595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2364055389025351786744793 1773041541769013840058595)
        ·
          refine ⟨2659562312653520760087893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773041541769013840058595 2659562312653520760087893)
          ·
            refine ⟨1947921615713027900455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2659562312653520760087893 1947921615713027900455)
            ·
              rfl

theorem cell22_460918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 12].length) (baseStart_460918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460918 prefixEnd_460918 := by exact prefixLift 460918
  have htrace : WordTrace (prefixWord ++ tailWord_460918) baseStart_460918 baseEnd_460918 := by
    simpa [prefixWord, tailWord_460918, baseEnd_460918] using wordTrace_append hprefix tailTrace_460918
  have hstable : (prefixWord ++ tailWord_460918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460918).length < 2 ^ (prefixWord ++ tailWord_460918).sum := by decide
  have hdescent : baseEnd_460918 < baseStart_460918 := by decide
  rcases family_descends (prefixWord ++ tailWord_460918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460954 : List Nat := [3, 1, 1, 5, 3, 1, 1, 1, 2, 4]
def baseStart_460954 : Nat := 118140960795 + 460954 * 2 ^ 59
def prefixEnd_460954 : Nat := 4983230072969 + 3 ^ 40 * 460954 * 2
def baseEnd_460954 : Nat := 157793974408463166036745

theorem tailTrace_460954 : CollatzResearch.WordTrace tailWord_460954 prefixEnd_460954 157793974408463166036745 := by
  unfold tailWord_460954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4203093393012464380179479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11208249048033238347145277 4203093393012464380179479)
  ·
    refine ⟨6304640089518696570269219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4203093393012464380179479 6304640089518696570269219)
    ·
      refine ⟨9456960134278044855403829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6304640089518696570269219 9456960134278044855403829)
      ·
        refine ⟨886590012588566705194109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9456960134278044855403829 886590012588566705194109)
        ·
          refine ⟨332471254720712514447791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 886590012588566705194109 332471254720712514447791)
          ·
            refine ⟨498706882081068771671687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332471254720712514447791 498706882081068771671687)
            ·
              refine ⟨748060323121603157507531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498706882081068771671687 748060323121603157507531)
              ·
                refine ⟨1122090484682404736261297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748060323121603157507531 1122090484682404736261297)
                ·
                  refine ⟨841567863511803552195973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1122090484682404736261297 841567863511803552195973)
                  ·
                    refine ⟨157793974408463166036745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 841567863511803552195973 157793974408463166036745)
                    ·
                      rfl

theorem cell22_460954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 2, 4].length) (baseStart_460954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460954 prefixEnd_460954 := by exact prefixLift 460954
  have htrace : WordTrace (prefixWord ++ tailWord_460954) baseStart_460954 baseEnd_460954 := by
    simpa [prefixWord, tailWord_460954, baseEnd_460954] using wordTrace_append hprefix tailTrace_460954
  have hstable : (prefixWord ++ tailWord_460954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460954).length < 2 ^ (prefixWord ++ tailWord_460954).sum := by decide
  have hdescent : baseEnd_460954 < baseStart_460954 := by decide
  rcases family_descends (prefixWord ++ tailWord_460954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460978 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_460978 : Nat := 118140960795 + 460978 * 2 ^ 59
def prefixEnd_460978 : Nat := 4983230072969 + 3 ^ 40 * 460978 * 2
def baseEnd_460978 : Nat := 157802190098935103436671

theorem tailTrace_460978 : CollatzResearch.WordTrace tailWord_460978 prefixEnd_460978 157802190098935103436671 := by
  unfold tailWord_460978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4203312230990727404897897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11208832615975273079727725 4203312230990727404897897)
  ·
    refine ⟨3152484173243045553673423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4203312230990727404897897 3152484173243045553673423)
    ·
      refine ⟨4728726259864568330510135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3152484173243045553673423 4728726259864568330510135)
      ·
        refine ⟨7093089389796852495765203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4728726259864568330510135 7093089389796852495765203)
        ·
          refine ⟨10639634084695278743647805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7093089389796852495765203 10639634084695278743647805)
          ·
            refine ⟨3989862781760729528867927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10639634084695278743647805 3989862781760729528867927)
            ·
              refine ⟨5984794172641094293301891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3989862781760729528867927 5984794172641094293301891)
              ·
                refine ⟨8977191258961641439952837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5984794172641094293301891 8977191258961641439952837)
                ·
                  refine ⟨1683223361055307769991157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8977191258961641439952837 1683223361055307769991157)
                  ·
                    refine ⟨157802190098935103436671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1683223361055307769991157 157802190098935103436671)
                    ·
                      rfl

theorem cell22_460978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_460978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_460978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_460978 prefixEnd_460978 := by exact prefixLift 460978
  have htrace : WordTrace (prefixWord ++ tailWord_460978) baseStart_460978 baseEnd_460978 := by
    simpa [prefixWord, tailWord_460978, baseEnd_460978] using wordTrace_append hprefix tailTrace_460978
  have hstable : (prefixWord ++ tailWord_460978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460978).length < 2 ^ (prefixWord ++ tailWord_460978).sum := by decide
  have hdescent : baseEnd_460978 < baseStart_460978 := by decide
  rcases family_descends (prefixWord ++ tailWord_460978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461023 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 3, 5]
def baseStart_461023 : Nat := 118140960795 + 461023 * 2 ^ 59
def prefixEnd_461023 : Nat := 4983230072969 + 3 ^ 40 * 461023 * 2
def baseEnd_461023 : Nat := 157817594518569986061533

theorem tailTrace_461023 : CollatzResearch.WordTrace tailWord_461023 prefixEnd_461023 157817594518569986061533 := by
  unfold tailWord_461023
  simp only [CollatzResearch.WordTrace]
  refine ⟨16814890208799882304979723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11209926805866588203319815 16814890208799882304979723)
  ·
    refine ⟨25222335313199823457469585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16814890208799882304979723 25222335313199823457469585)
    ·
      refine ⟨18916751484899867593102189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25222335313199823457469585 18916751484899867593102189)
      ·
        refine ⟨7093781806837450347413321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18916751484899867593102189 7093781806837450347413321)
        ·
          refine ⟨5320336355128087760559991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7093781806837450347413321 5320336355128087760559991)
          ·
            refine ⟨7980504532692131640839987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5320336355128087760559991 7980504532692131640839987)
            ·
              refine ⟨11970756799038197461259981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7980504532692131640839987 11970756799038197461259981)
              ·
                refine ⟨4489033799639324047972493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11970756799038197461259981 4489033799639324047972493)
                ·
                  refine ⟨1683387674864746517989685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4489033799639324047972493 1683387674864746517989685)
                  ·
                    refine ⟨157817594518569986061533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1683387674864746517989685 157817594518569986061533)
                    ·
                      rfl

theorem cell22_461023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_461023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461023 prefixEnd_461023 := by exact prefixLift 461023
  have htrace : WordTrace (prefixWord ++ tailWord_461023) baseStart_461023 baseEnd_461023 := by
    simpa [prefixWord, tailWord_461023, baseEnd_461023] using wordTrace_append hprefix tailTrace_461023
  have hstable : (prefixWord ++ tailWord_461023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461023).length < 2 ^ (prefixWord ++ tailWord_461023).sum := by decide
  have hdescent : baseEnd_461023 < baseStart_461023 := by decide
  rcases family_descends (prefixWord ++ tailWord_461023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461042 : List Nat := [3, 2, 1, 3, 2, 3, 1, 1, 6]
def baseStart_461042 : Nat := 118140960795 + 461042 * 2 ^ 59
def prefixEnd_461042 : Nat := 4983230072969 + 3 ^ 40 * 461042 * 2
def baseEnd_461042 : Nat := 52608032868953423278825

theorem tailTrace_461042 : CollatzResearch.WordTrace tailWord_461042 prefixEnd_461042 52608032868953423278825 := by
  unfold tailWord_461042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4203895798932762137480345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11210388797154032366614253 4203895798932762137480345)
  ·
    refine ⟨3152921849199571603110259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4203895798932762137480345 3152921849199571603110259)
    ·
      refine ⟨4729382773799357404665389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3152921849199571603110259 4729382773799357404665389)
      ·
        refine ⟨1773518540174759026749521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4729382773799357404665389 1773518540174759026749521)
        ·
          refine ⟨1330138905131069270062141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1773518540174759026749521 1330138905131069270062141)
          ·
            refine ⟨498802089424150976273303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1330138905131069270062141 498802089424150976273303)
            ·
              refine ⟨748203134136226464409955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498802089424150976273303 748203134136226464409955)
              ·
                refine ⟨1122304701204339696614933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748203134136226464409955 1122304701204339696614933)
                ·
                  refine ⟨52608032868953423278825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1122304701204339696614933 52608032868953423278825)
                  ·
                    rfl

theorem cell22_461042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_461042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461042 prefixEnd_461042 := by exact prefixLift 461042
  have htrace : WordTrace (prefixWord ++ tailWord_461042) baseStart_461042 baseEnd_461042 := by
    simpa [prefixWord, tailWord_461042, baseEnd_461042] using wordTrace_append hprefix tailTrace_461042
  have hstable : (prefixWord ++ tailWord_461042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461042).length < 2 ^ (prefixWord ++ tailWord_461042).sum := by decide
  have hdescent : baseEnd_461042 < baseStart_461042 := by decide
  rcases family_descends (prefixWord ++ tailWord_461042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461057 : List Nat := [1, 2, 4, 1, 1, 2, 3, 3, 2, 3]
def baseStart_461057 : Nat := 118140960795 + 461057 * 2 ^ 59
def prefixEnd_461057 : Nat := 4983230072969 + 3 ^ 40 * 461057 * 2
def baseEnd_461057 : Nat := 157829233413405230711429

theorem tailTrace_461057 : CollatzResearch.WordTrace tailWord_461057 prefixEnd_461057 157829233413405230711429 := by
  unfold tailWord_461057
  simp only [CollatzResearch.WordTrace]
  refine ⟨16816130290676706111717425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11210753527117804074478283 16816130290676706111717425)
  ·
    refine ⟨12612097718007529583788069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16816130290676706111717425 12612097718007529583788069)
    ·
      refine ⟨2364768322126411796960263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12612097718007529583788069 2364768322126411796960263)
      ·
        refine ⟨3547152483189617695440395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2364768322126411796960263 3547152483189617695440395)
        ·
          refine ⟨5320728724784426543160593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3547152483189617695440395 5320728724784426543160593)
          ·
            refine ⟨3990546543588319907370445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5320728724784426543160593 3990546543588319907370445)
            ·
              refine ⟨1496454953845619965263917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3990546543588319907370445 1496454953845619965263917)
              ·
                refine ⟨561170607692107486973969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1496454953845619965263917 561170607692107486973969)
                ·
                  refine ⟨420877955769080615230477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561170607692107486973969 420877955769080615230477)
                  ·
                    refine ⟨157829233413405230711429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 420877955769080615230477 157829233413405230711429)
                    ·
                      rfl

theorem cell22_461057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_461057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461057 prefixEnd_461057 := by exact prefixLift 461057
  have htrace : WordTrace (prefixWord ++ tailWord_461057) baseStart_461057 baseEnd_461057 := by
    simpa [prefixWord, tailWord_461057, baseEnd_461057] using wordTrace_append hprefix tailTrace_461057
  have hstable : (prefixWord ++ tailWord_461057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461057).length < 2 ^ (prefixWord ++ tailWord_461057).sum := by decide
  have hdescent : baseEnd_461057 < baseStart_461057 := by decide
  rcases family_descends (prefixWord ++ tailWord_461057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461175 : List Nat := [1, 1, 3, 1, 1, 2, 2, 5, 1, 5]
def baseStart_461175 : Nat := 118140960795 + 461175 * 2 ^ 59
def prefixEnd_461175 : Nat := 4983230072969 + 3 ^ 40 * 461175 * 2
def baseEnd_461175 : Nat := 157869627224892256261067

theorem tailTrace_461175 : CollatzResearch.WordTrace tailWord_461175 prefixEnd_461175 157869627224892256261067 := by
  unfold tailWord_461175
  simp only [CollatzResearch.WordTrace]
  refine ⟨16820434104249212264512979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11213622736166141509675319 16820434104249212264512979)
  ·
    refine ⟨25230651156373818396769469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16820434104249212264512979 25230651156373818396769469)
    ·
      refine ⟨9461494183640181898788551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25230651156373818396769469 9461494183640181898788551)
      ·
        refine ⟨14192241275460272848182827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9461494183640181898788551 14192241275460272848182827)
        ·
          refine ⟨21288361913190409272274241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14192241275460272848182827 21288361913190409272274241)
          ·
            refine ⟨15966271434892806954205681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21288361913190409272274241 15966271434892806954205681)
            ·
              refine ⟨11974703576169605215654261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15966271434892806954205681 11974703576169605215654261)
              ·
                refine ⟨1122628460265900488967587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11974703576169605215654261 1122628460265900488967587)
                ·
                  refine ⟨1683942690398850733451381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122628460265900488967587 1683942690398850733451381)
                  ·
                    refine ⟨157869627224892256261067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1683942690398850733451381 157869627224892256261067)
                    ·
                      rfl

theorem cell22_461175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_461175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461175 prefixEnd_461175 := by exact prefixLift 461175
  have htrace : WordTrace (prefixWord ++ tailWord_461175) baseStart_461175 baseEnd_461175 := by
    simpa [prefixWord, tailWord_461175, baseEnd_461175] using wordTrace_append hprefix tailTrace_461175
  have hstable : (prefixWord ++ tailWord_461175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461175).length < 2 ^ (prefixWord ++ tailWord_461175).sum := by decide
  have hdescent : baseEnd_461175 < baseStart_461175 := by decide
  rcases family_descends (prefixWord ++ tailWord_461175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461192 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 6, 3]
def baseStart_461192 : Nat := 118140960795 + 461192 * 2 ^ 59
def prefixEnd_461192 : Nat := 4983230072969 + 3 ^ 40 * 461192 * 2
def baseEnd_461192 : Nat := 157875446672309878586015

theorem tailTrace_461192 : CollatzResearch.WordTrace tailWord_461192 prefixEnd_461192 157875446672309878586015 := by
  unfold tailWord_461192
  simp only [CollatzResearch.WordTrace]
  refine ⟨8410527072593812083940915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11214036096791749445254553 8410527072593812083940915)
  ·
    refine ⟨12615790608890718125911373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8410527072593812083940915 12615790608890718125911373)
    ·
      refine ⟨4730921478334019297216765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12615790608890718125911373 4730921478334019297216765)
      ·
        refine ⟨1774095554375257236456287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4730921478334019297216765 1774095554375257236456287)
        ·
          refine ⟨2661143331562885854684431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1774095554375257236456287 2661143331562885854684431)
          ·
            refine ⟨3991714997344328782026647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2661143331562885854684431 3991714997344328782026647)
            ·
              refine ⟨5987572496016493173039971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3991714997344328782026647 5987572496016493173039971)
              ·
                refine ⟨8981358744024739759559957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5987572496016493173039971 8981358744024739759559957)
                ·
                  refine ⟨421001191126159676229373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8981358744024739759559957 421001191126159676229373)
                  ·
                    refine ⟨157875446672309878586015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 421001191126159676229373 157875446672309878586015)
                    ·
                      rfl

theorem cell22_461192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_461192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461192 prefixEnd_461192 := by exact prefixLift 461192
  have htrace : WordTrace (prefixWord ++ tailWord_461192) baseStart_461192 baseEnd_461192 := by
    simpa [prefixWord, tailWord_461192, baseEnd_461192] using wordTrace_append hprefix tailTrace_461192
  have hstable : (prefixWord ++ tailWord_461192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461192).length < 2 ^ (prefixWord ++ tailWord_461192).sum := by decide
  have hdescent : baseEnd_461192 < baseStart_461192 := by decide
  rcases family_descends (prefixWord ++ tailWord_461192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461265 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 3, 7]
def baseStart_461265 : Nat := 118140960795 + 461265 * 2 ^ 59
def prefixEnd_461265 : Nat := 4983230072969 + 3 ^ 40 * 461265 * 2
def baseEnd_461265 : Nat := 157900436064162021510791

theorem tailTrace_461265 : CollatzResearch.WordTrace tailWord_461265 prefixEnd_461265 157900436064162021510791 := by
  unfold tailWord_461265
  simp only [CollatzResearch.WordTrace]
  refine ⟨16823716673923157635289249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11215811115948771756859499 16823716673923157635289249)
  ·
    refine ⟨12617787505442368226466937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16823716673923157635289249 12617787505442368226466937)
    ·
      refine ⟨9463340629081776169850203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12617787505442368226466937 9463340629081776169850203)
      ·
        refine ⟨14195010943622664254775305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9463340629081776169850203 14195010943622664254775305)
        ·
          refine ⟨10646258207716998191081479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14195010943622664254775305 10646258207716998191081479)
          ·
            refine ⟨15969387311575497286622219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10646258207716998191081479 15969387311575497286622219)
            ·
              refine ⟨23954080967363245929933329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15969387311575497286622219 23954080967363245929933329)
              ·
                refine ⟨17965560725522434447449997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23954080967363245929933329 17965560725522434447449997)
                ·
                  refine ⟨6737085272070912917793749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17965560725522434447449997 6737085272070912917793749)
                  ·
                    refine ⟨157900436064162021510791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6737085272070912917793749 157900436064162021510791)
                    ·
                      rfl

theorem cell22_461265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_461265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461265 prefixEnd_461265 := by exact prefixLift 461265
  have htrace : WordTrace (prefixWord ++ tailWord_461265) baseStart_461265 baseEnd_461265 := by
    simpa [prefixWord, tailWord_461265, baseEnd_461265] using wordTrace_append hprefix tailTrace_461265
  have hstable : (prefixWord ++ tailWord_461265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461265).length < 2 ^ (prefixWord ++ tailWord_461265).sum := by decide
  have hdescent : baseEnd_461265 < baseStart_461265 := by decide
  rcases family_descends (prefixWord ++ tailWord_461265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461297 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 3, 4]
def baseStart_461297 : Nat := 118140960795 + 461297 * 2 ^ 59
def prefixEnd_461297 : Nat := 4983230072969 + 3 ^ 40 * 461297 * 2
def baseEnd_461297 : Nat := 157911390318124604710693

theorem tailTrace_461297 : CollatzResearch.WordTrace tailWord_461297 prefixEnd_461297 157911390318124604710693 := by
  unfold tailWord_461297
  simp only [CollatzResearch.WordTrace]
  refine ⟨16824883809807227100454145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11216589206538151400302763 16824883809807227100454145)
  ·
    refine ⟨12618662857355420325340609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16824883809807227100454145 12618662857355420325340609)
    ·
      refine ⟨9463997143016565244005457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12618662857355420325340609 9463997143016565244005457)
      ·
        refine ⟨7097997857262423933004093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9463997143016565244005457 7097997857262423933004093)
        ·
          refine ⟨2661749196473408974876535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7097997857262423933004093 2661749196473408974876535)
          ·
            refine ⟨3992623794710113462314803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2661749196473408974876535 3992623794710113462314803)
            ·
              refine ⟨5988935692065170193472205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992623794710113462314803 5988935692065170193472205)
              ·
                refine ⟨2245850884524438822552077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5988935692065170193472205 2245850884524438822552077)
                ·
                  refine ⟨842194081696664558457029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2245850884524438822552077 842194081696664558457029)
                  ·
                    refine ⟨157911390318124604710693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 842194081696664558457029 157911390318124604710693)
                    ·
                      rfl

theorem cell22_461297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_461297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461297 prefixEnd_461297 := by exact prefixLift 461297
  have htrace : WordTrace (prefixWord ++ tailWord_461297) baseStart_461297 baseEnd_461297 := by
    simpa [prefixWord, tailWord_461297, baseEnd_461297] using wordTrace_append hprefix tailTrace_461297
  have hstable : (prefixWord ++ tailWord_461297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461297).length < 2 ^ (prefixWord ++ tailWord_461297).sum := by decide
  have hdescent : baseEnd_461297 < baseStart_461297 := by decide
  rcases family_descends (prefixWord ++ tailWord_461297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461318 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_461318 : Nat := 118140960795 + 461318 * 2 ^ 59
def prefixEnd_461318 : Nat := 4983230072969 + 3 ^ 40 * 461318 * 2
def baseEnd_461318 : Nat := 52639526349095849978543

theorem tailTrace_461318 : CollatzResearch.WordTrace tailWord_461318 prefixEnd_461318 52639526349095849978543 := by
  unfold tailWord_461318
  simp only [CollatzResearch.WordTrace]
  refine ⟨525801554460348365217769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11217099828487431791312405 525801554460348365217769)
  ·
    refine ⟨394351165845261273913327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 525801554460348365217769 394351165845261273913327)
    ·
      refine ⟨591526748767891910869991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394351165845261273913327 591526748767891910869991)
      ·
        refine ⟨887290123151837866304987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591526748767891910869991 887290123151837866304987)
        ·
          refine ⟨1330935184727756799457481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 887290123151837866304987 1330935184727756799457481)
          ·
            refine ⟨998201388545817599593111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1330935184727756799457481 998201388545817599593111)
            ·
              refine ⟨1497302082818726399389667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998201388545817599593111 1497302082818726399389667)
              ·
                refine ⟨2245953124228089599084501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497302082818726399389667 2245953124228089599084501)
                ·
                  refine ⟨52639526349095849978543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2245953124228089599084501 52639526349095849978543)
                  ·
                    rfl

theorem cell22_461318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_461318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461318 prefixEnd_461318 := by exact prefixLift 461318
  have htrace : WordTrace (prefixWord ++ tailWord_461318) baseStart_461318 baseEnd_461318 := by
    simpa [prefixWord, tailWord_461318, baseEnd_461318] using wordTrace_append hprefix tailTrace_461318
  have hstable : (prefixWord ++ tailWord_461318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461318).length < 2 ^ (prefixWord ++ tailWord_461318).sum := by decide
  have hdescent : baseEnd_461318 < baseStart_461318 := by decide
  rcases family_descends (prefixWord ++ tailWord_461318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461348 : List Nat := [2, 3, 1, 5, 1, 1, 2, 2, 1, 4]
def baseStart_461348 : Nat := 118140960795 + 461348 * 2 ^ 59
def prefixEnd_461348 : Nat := 4983230072969 + 3 ^ 40 * 461348 * 2
def baseEnd_461348 : Nat := 157928848660377471685537

theorem tailTrace_461348 : CollatzResearch.WordTrace tailWord_461348 prefixEnd_461348 157928848660377471685537 := by
  unfold tailWord_461348
  simp only [CollatzResearch.WordTrace]
  refine ⟨8413371966311231405280349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11217829288414975207040465 8413371966311231405280349)
  ·
    refine ⟨3155014487366711776980131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8413371966311231405280349 3155014487366711776980131)
    ·
      refine ⟨4732521731050067665470197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3155014487366711776980131 4732521731050067665470197)
      ·
        refine ⟨443673912285943843637831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4732521731050067665470197 443673912285943843637831)
        ·
          refine ⟨665510868428915765456747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443673912285943843637831 665510868428915765456747)
          ·
            refine ⟨998266302643373648185121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665510868428915765456747 998266302643373648185121)
            ·
              refine ⟨748699726982530236138841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 998266302643373648185121 748699726982530236138841)
              ·
                refine ⟨561524795236897677104131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 748699726982530236138841 561524795236897677104131)
                ·
                  refine ⟨842287192855346515656197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561524795236897677104131 842287192855346515656197)
                  ·
                    refine ⟨157928848660377471685537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 842287192855346515656197 157928848660377471685537)
                    ·
                      rfl

theorem cell22_461348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_461348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461348 prefixEnd_461348 := by exact prefixLift 461348
  have htrace : WordTrace (prefixWord ++ tailWord_461348) baseStart_461348 baseEnd_461348 := by
    simpa [prefixWord, tailWord_461348, baseEnd_461348] using wordTrace_append hprefix tailTrace_461348
  have hstable : (prefixWord ++ tailWord_461348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461348).length < 2 ^ (prefixWord ++ tailWord_461348).sum := by decide
  have hdescent : baseEnd_461348 < baseStart_461348 := by decide
  rcases family_descends (prefixWord ++ tailWord_461348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461380 : List Nat := [2, 3, 5, 1, 1, 2, 1, 1, 6]
def baseStart_461380 : Nat := 118140960795 + 461380 * 2 ^ 59
def prefixEnd_461380 : Nat := 4983230072969 + 3 ^ 40 * 461380 * 2
def baseEnd_461380 : Nat := 52646600971446684961813

theorem tailTrace_461380 : CollatzResearch.WordTrace tailWord_461380 prefixEnd_461380 52646600971446684961813 := by
  unfold tailWord_461380
  simp only [CollatzResearch.WordTrace]
  refine ⟨8413955534253266137862797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11218607379004354850483729 8413955534253266137862797)
  ·
    refine ⟨3155233325344974801698549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8413955534253266137862797 3155233325344974801698549)
    ·
      refine ⟨295803124251091387659239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3155233325344974801698549 295803124251091387659239)
      ·
        refine ⟨443704686376637081488859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295803124251091387659239 443704686376637081488859)
        ·
          refine ⟨665557029564955622233289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443704686376637081488859 665557029564955622233289)
          ·
            refine ⟨499167772173716716674967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 665557029564955622233289 499167772173716716674967)
            ·
              refine ⟨748751658260575075012451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499167772173716716674967 748751658260575075012451)
              ·
                refine ⟨1123127487390862612518677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748751658260575075012451 1123127487390862612518677)
                ·
                  refine ⟨52646600971446684961813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1123127487390862612518677 52646600971446684961813)
                  ·
                    rfl

theorem cell22_461380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_461380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461380 prefixEnd_461380 := by exact prefixLift 461380
  have htrace : WordTrace (prefixWord ++ tailWord_461380) baseStart_461380 baseEnd_461380 := by
    simpa [prefixWord, tailWord_461380, baseEnd_461380] using wordTrace_append hprefix tailTrace_461380
  have hstable : (prefixWord ++ tailWord_461380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461380).length < 2 ^ (prefixWord ++ tailWord_461380).sum := by decide
  have hdescent : baseEnd_461380 < baseStart_461380 := by decide
  rcases family_descends (prefixWord ++ tailWord_461380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461417 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 4, 5]
def baseStart_461417 : Nat := 118140960795 + 461417 * 2 ^ 59
def prefixEnd_461417 : Nat := 4983230072969 + 3 ^ 40 * 461417 * 2
def baseEnd_461417 : Nat := 157952468770484291710325

theorem tailTrace_461417 : CollatzResearch.WordTrace tailWord_461417 prefixEnd_461417 157952468770484291710325 := by
  unfold tailWord_461417
  simp only [CollatzResearch.WordTrace]
  refine ⟨16829260569372487594822505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11219507046248325063215003 16829260569372487594822505)
  ·
    refine ⟨12621945427029365696116879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16829260569372487594822505 12621945427029365696116879)
    ·
      refine ⟨18932918140544048544175319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12621945427029365696116879 18932918140544048544175319)
      ·
        refine ⟨28399377210816072816262979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18932918140544048544175319 28399377210816072816262979)
        ·
          refine ⟨42599065816224109224394469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28399377210816072816262979 42599065816224109224394469)
          ·
            refine ⟨7987324840542020479573963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42599065816224109224394469 7987324840542020479573963)
            ·
              refine ⟨11980987260813030719360945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7987324840542020479573963 11980987260813030719360945)
              ·
                refine ⟨8985740445609773039520709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11980987260813030719360945 8985740445609773039520709)
                ·
                  refine ⟨1684826333551832444910133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8985740445609773039520709 1684826333551832444910133)
                  ·
                    refine ⟨157952468770484291710325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1684826333551832444910133 157952468770484291710325)
                    ·
                      rfl

theorem cell22_461417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_461417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461417 prefixEnd_461417 := by exact prefixLift 461417
  have htrace : WordTrace (prefixWord ++ tailWord_461417) baseStart_461417 baseEnd_461417 := by
    simpa [prefixWord, tailWord_461417, baseEnd_461417] using wordTrace_append hprefix tailTrace_461417
  have hstable : (prefixWord ++ tailWord_461417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461417).length < 2 ^ (prefixWord ++ tailWord_461417).sum := by decide
  have hdescent : baseEnd_461417 < baseStart_461417 := by decide
  rcases family_descends (prefixWord ++ tailWord_461417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461440 : List Nat := [2, 1, 1, 2, 1, 7, 2, 2, 1, 3]
def baseStart_461440 : Nat := 118140960795 + 461440 * 2 ^ 59
def prefixEnd_461440 : Nat := 4983230072969 + 3 ^ 40 * 461440 * 2
def baseEnd_461440 : Nat := 157960342140519898385255

theorem tailTrace_461440 : CollatzResearch.WordTrace tailWord_461440 prefixEnd_461440 157960342140519898385255 := by
  unfold tailWord_461440
  simp only [CollatzResearch.WordTrace]
  refine ⟨8415049724144581261454887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11220066298859441681939849 8415049724144581261454887)
  ·
    refine ⟨12622574586216871892182331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8415049724144581261454887 12622574586216871892182331)
    ·
      refine ⟨18933861879325307838273497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12622574586216871892182331 18933861879325307838273497)
      ·
        refine ⟨14200396409493980878705123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18933861879325307838273497 14200396409493980878705123)
        ·
          refine ⟨21300594614240971318057685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14200396409493980878705123 21300594614240971318057685)
          ·
            refine ⟨499232686271272765266977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 21300594614240971318057685 499232686271272765266977)
            ·
              refine ⟨374424514703454573950233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499232686271272765266977 374424514703454573950233)
              ·
                refine ⟨280818386027590930462675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374424514703454573950233 280818386027590930462675)
                ·
                  refine ⟨421227579041386395694013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280818386027590930462675 421227579041386395694013)
                  ·
                    refine ⟨157960342140519898385255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 421227579041386395694013 157960342140519898385255)
                    ·
                      rfl

theorem cell22_461440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 1, 3].length) (baseStart_461440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461440 prefixEnd_461440 := by exact prefixLift 461440
  have htrace : WordTrace (prefixWord ++ tailWord_461440) baseStart_461440 baseEnd_461440 := by
    simpa [prefixWord, tailWord_461440, baseEnd_461440] using wordTrace_append hprefix tailTrace_461440
  have hstable : (prefixWord ++ tailWord_461440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461440).length < 2 ^ (prefixWord ++ tailWord_461440).sum := by decide
  have hdescent : baseEnd_461440 < baseStart_461440 := by decide
  rcases family_descends (prefixWord ++ tailWord_461440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461442 : List Nat := [3, 4, 3, 1, 2, 1, 1, 7]
def baseStart_461442 : Nat := 118140960795 + 461442 * 2 ^ 59
def prefixEnd_461442 : Nat := 4983230072969 + 3 ^ 40 * 461442 * 2
def baseEnd_461442 : Nat := 17551225197932506648361

theorem tailTrace_461442 : CollatzResearch.WordTrace tailWord_461442 prefixEnd_461442 17551225197932506648361 := by
  unfold tailWord_461442
  simp only [CollatzResearch.WordTrace]
  refine ⟨4207543098570479216120645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11220114929521277909655053 4207543098570479216120645)
  ·
    refine ⟨788914330981964853022621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4207543098570479216120645 788914330981964853022621)
    ·
      refine ⟨295842874118236819883483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 788914330981964853022621 295842874118236819883483)
      ·
        refine ⟨443764311177355229825225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295842874118236819883483 443764311177355229825225)
        ·
          refine ⟨332823233383016422368919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443764311177355229825225 332823233383016422368919)
          ·
            refine ⟨499234850074524633553379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332823233383016422368919 499234850074524633553379)
            ·
              refine ⟨748852275111786950330069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499234850074524633553379 748852275111786950330069)
              ·
                refine ⟨17551225197932506648361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 748852275111786950330069 17551225197932506648361)
                ·
                  rfl

theorem cell22_461442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 7].length) (baseStart_461442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461442 prefixEnd_461442 := by exact prefixLift 461442
  have htrace : WordTrace (prefixWord ++ tailWord_461442) baseStart_461442 baseEnd_461442 := by
    simpa [prefixWord, tailWord_461442, baseEnd_461442] using wordTrace_append hprefix tailTrace_461442
  have hstable : (prefixWord ++ tailWord_461442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461442).length < 2 ^ (prefixWord ++ tailWord_461442).sum := by decide
  have hdescent : baseEnd_461442 < baseStart_461442 := by decide
  rcases family_descends (prefixWord ++ tailWord_461442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461464 : List Nat := [2, 1, 2, 4, 1, 1, 3, 2, 6]
def baseStart_461464 : Nat := 118140960795 + 461464 * 2 ^ 59
def prefixEnd_461464 : Nat := 4983230072969 + 3 ^ 40 * 461464 * 2
def baseEnd_461464 : Nat := 52656185943663945261727

theorem tailTrace_461464 : CollatzResearch.WordTrace tailWord_461464 prefixEnd_461464 52656185943663945261727 := by
  unfold tailWord_461464
  simp only [CollatzResearch.WordTrace]
  refine ⟨8415487400101107310891723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11220649866801476414522297 8415487400101107310891723)
  ·
    refine ⟨12623231100151660966337585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8415487400101107310891723 12623231100151660966337585)
    ·
      refine ⟨9467423325113745724753189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12623231100151660966337585 9467423325113745724753189)
      ·
        refine ⟨1775141873458827323391223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9467423325113745724753189 1775141873458827323391223)
        ·
          refine ⟨2662712810188240985086835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1775141873458827323391223 2662712810188240985086835)
          ·
            refine ⟨3994069215282361477630253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662712810188240985086835 3994069215282361477630253)
            ·
              refine ⟨1497775955730885554111345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3994069215282361477630253 1497775955730885554111345)
              ·
                refine ⟨1123331966798164165583509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1497775955730885554111345 1123331966798164165583509)
                ·
                  refine ⟨52656185943663945261727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1123331966798164165583509 52656185943663945261727)
                  ·
                    rfl

theorem cell22_461464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 6].length) (baseStart_461464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461464 prefixEnd_461464 := by exact prefixLift 461464
  have htrace : WordTrace (prefixWord ++ tailWord_461464) baseStart_461464 baseEnd_461464 := by
    simpa [prefixWord, tailWord_461464, baseEnd_461464] using wordTrace_append hprefix tailTrace_461464
  have hstable : (prefixWord ++ tailWord_461464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461464).length < 2 ^ (prefixWord ++ tailWord_461464).sum := by decide
  have hdescent : baseEnd_461464 < baseStart_461464 := by decide
  rcases family_descends (prefixWord ++ tailWord_461464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461569 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 1, 7]
def baseStart_461569 : Nat := 118140960795 + 461569 * 2 ^ 59
def prefixEnd_461569 : Nat := 4983230072969 + 3 ^ 40 * 461569 * 2
def baseEnd_461569 : Nat := 158004501476806561909859

theorem tailTrace_461569 : CollatzResearch.WordTrace tailWord_461569 prefixEnd_461569 158004501476806561909859 := by
  unfold tailWord_461569
  simp only [CollatzResearch.WordTrace]
  refine ⟨16834804464821817554355761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11223202976547878369570507 16834804464821817554355761)
  ·
    refine ⟨12626103348616363165766821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16834804464821817554355761 12626103348616363165766821)
    ·
      refine ⟨2367394377865568093581279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12626103348616363165766821 2367394377865568093581279)
      ·
        refine ⟨3551091566798352140371919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2367394377865568093581279 3551091566798352140371919)
        ·
          refine ⟨5326637350197528210557879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3551091566798352140371919 5326637350197528210557879)
          ·
            refine ⟨7989956025296292315836819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5326637350197528210557879 7989956025296292315836819)
            ·
              refine ⟨11984934037944438473755229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7989956025296292315836819 11984934037944438473755229)
              ·
                refine ⟨4494350264229164427658211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11984934037944438473755229 4494350264229164427658211)
                ·
                  refine ⟨6741525396343746641487317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4494350264229164427658211 6741525396343746641487317)
                  ·
                    refine ⟨158004501476806561909859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6741525396343746641487317 158004501476806561909859)
                    ·
                      rfl

theorem cell22_461569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_461569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461569 prefixEnd_461569 := by exact prefixLift 461569
  have htrace : WordTrace (prefixWord ++ tailWord_461569) baseStart_461569 baseEnd_461569 := by
    simpa [prefixWord, tailWord_461569, baseEnd_461569] using wordTrace_append hprefix tailTrace_461569
  have hstable : (prefixWord ++ tailWord_461569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461569).length < 2 ^ (prefixWord ++ tailWord_461569).sum := by decide
  have hdescent : baseEnd_461569 < baseStart_461569 := by decide
  rcases family_descends (prefixWord ++ tailWord_461569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461631 : List Nat := [1, 1, 2, 2, 5, 1, 1, 3, 1, 5]
def baseStart_461631 : Nat := 118140960795 + 461631 * 2 ^ 59
def prefixEnd_461631 : Nat := 4983230072969 + 3 ^ 40 * 461631 * 2
def baseEnd_461631 : Nat := 158025725343859066859669

theorem tailTrace_461631 : CollatzResearch.WordTrace tailWord_461631 prefixEnd_461631 158025725343859066859669 := by
  unfold tailWord_461631
  simp only [CollatzResearch.WordTrace]
  refine ⟨16837065790597202143112747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11224710527064801428741831 16837065790597202143112747)
  ·
    refine ⟨25255598685895803214669121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16837065790597202143112747 25255598685895803214669121)
    ·
      refine ⟨18941699014421852411001841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25255598685895803214669121 18941699014421852411001841)
      ·
        refine ⟨14206274260816389308251381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18941699014421852411001841 14206274260816389308251381)
        ·
          refine ⟨1331838211951536497648567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14206274260816389308251381 1331838211951536497648567)
          ·
            refine ⟨1997757317927304746472851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331838211951536497648567 1997757317927304746472851)
            ·
              refine ⟨2996635976890957119709277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997757317927304746472851 2996635976890957119709277)
              ·
                refine ⟨1123738491334108919890979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2996635976890957119709277 1123738491334108919890979)
                ·
                  refine ⟨1685607737001163379836469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1123738491334108919890979 1685607737001163379836469)
                  ·
                    refine ⟨158025725343859066859669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1685607737001163379836469 158025725343859066859669)
                    ·
                      rfl

theorem cell22_461631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_461631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461631 prefixEnd_461631 := by exact prefixLift 461631
  have htrace : WordTrace (prefixWord ++ tailWord_461631) baseStart_461631 baseEnd_461631 := by
    simpa [prefixWord, tailWord_461631, baseEnd_461631] using wordTrace_append hprefix tailTrace_461631
  have hstable : (prefixWord ++ tailWord_461631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461631).length < 2 ^ (prefixWord ++ tailWord_461631).sum := by decide
  have hdescent : baseEnd_461631 < baseStart_461631 := by decide
  rcases family_descends (prefixWord ++ tailWord_461631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461652 : List Nat := [2, 4, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_461652 : Nat := 118140960795 + 461652 * 2 ^ 59
def prefixEnd_461652 : Nat := 4983230072969 + 3 ^ 40 * 461652 * 2
def baseEnd_461652 : Nat := 158032914073022012084605

theorem tailTrace_461652 : CollatzResearch.WordTrace tailWord_461652 prefixEnd_461652 158032914073022012084605 := by
  unfold tailWord_461652
  simp only [CollatzResearch.WordTrace]
  refine ⟨8418915861760561364813605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11225221149014081819751473 8418915861760561364813605)
  ·
    refine ⟨1578546724080105255902551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8418915861760561364813605 1578546724080105255902551)
    ·
      refine ⟨2367820086120157883853827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1578546724080105255902551 2367820086120157883853827)
      ·
        refine ⟨3551730129180236825780741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2367820086120157883853827 3551730129180236825780741)
        ·
          refine ⟨665949399221294404833889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3551730129180236825780741 665949399221294404833889)
          ·
            refine ⟨499462049415970803625417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 665949399221294404833889 499462049415970803625417)
            ·
              refine ⟨374596537061978102719063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499462049415970803625417 374596537061978102719063)
              ·
                refine ⟨561894805592967154078595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374596537061978102719063 561894805592967154078595)
                ·
                  refine ⟨842842208389450731117893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561894805592967154078595 842842208389450731117893)
                  ·
                    refine ⟨158032914073022012084605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 842842208389450731117893 158032914073022012084605)
                    ·
                      rfl

theorem cell22_461652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_461652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461652 prefixEnd_461652 := by exact prefixLift 461652
  have htrace : WordTrace (prefixWord ++ tailWord_461652) baseStart_461652 baseEnd_461652 := by
    simpa [prefixWord, tailWord_461652, baseEnd_461652] using wordTrace_append hprefix tailTrace_461652
  have hstable : (prefixWord ++ tailWord_461652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461652).length < 2 ^ (prefixWord ++ tailWord_461652).sum := by decide
  have hdescent : baseEnd_461652 < baseStart_461652 := by decide
  rcases family_descends (prefixWord ++ tailWord_461652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461693 : List Nat := [1, 4, 1, 1, 2, 1, 4, 2, 3, 3]
def baseStart_461693 : Nat := 118140960795 + 461693 * 2 ^ 59
def prefixEnd_461693 : Nat := 4983230072969 + 3 ^ 40 * 461693 * 2
def baseEnd_461693 : Nat := 158046949210911571809479

theorem tailTrace_461693 : CollatzResearch.WordTrace tailWord_461693 prefixEnd_461693 158046949210911571809479 := by
  unfold tailWord_461693
  simp only [CollatzResearch.WordTrace]
  refine ⟨16839327116372586731869733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11226218077581724487913155 16839327116372586731869733)
  ·
    refine ⟨3157373834319860012225575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16839327116372586731869733 3157373834319860012225575)
    ·
      refine ⟨4736060751479790018338363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3157373834319860012225575 4736060751479790018338363)
      ·
        refine ⟨7104091127219685027507545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4736060751479790018338363 7104091127219685027507545)
        ·
          refine ⟨5328068345414763770630659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7104091127219685027507545 5328068345414763770630659)
          ·
            refine ⟨7992102518122145655945989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5328068345414763770630659 7992102518122145655945989)
            ·
              refine ⟨1498519222147902310489873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7992102518122145655945989 1498519222147902310489873)
              ·
                refine ⟨1123889416610926732867405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1498519222147902310489873 1123889416610926732867405)
                ·
                  refine ⟨421458531229097524825277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1123889416610926732867405 421458531229097524825277)
                  ·
                    refine ⟨158046949210911571809479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 421458531229097524825277 158046949210911571809479)
                    ·
                      rfl

theorem cell22_461693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_461693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461693 prefixEnd_461693 := by exact prefixLift 461693
  have htrace : WordTrace (prefixWord ++ tailWord_461693) baseStart_461693 baseEnd_461693 := by
    simpa [prefixWord, tailWord_461693, baseEnd_461693] using wordTrace_append hprefix tailTrace_461693
  have hstable : (prefixWord ++ tailWord_461693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461693).length < 2 ^ (prefixWord ++ tailWord_461693).sum := by decide
  have hdescent : baseEnd_461693 < baseStart_461693 := by decide
  rcases family_descends (prefixWord ++ tailWord_461693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461751 : List Nat := [1, 1, 3, 1, 3, 1, 2, 4, 6]
def baseStart_461751 : Nat := 118140960795 + 461751 * 2 ^ 59
def prefixEnd_461751 : Nat := 4983230072969 + 3 ^ 40 * 461751 * 2
def baseEnd_461751 : Nat := 52688934598739584619767

theorem tailTrace_461751 : CollatzResearch.WordTrace tailWord_461751 prefixEnd_461751 52688934598739584619767 := by
  unfold tailWord_461751
  simp only [CollatzResearch.WordTrace]
  refine ⟨16841442550162462637481107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11227628366774975091654071 16841442550162462637481107)
  ·
    refine ⟨25262163825243693956221661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16841442550162462637481107 25262163825243693956221661)
    ·
      refine ⟨9473311434466385233583123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25262163825243693956221661 9473311434466385233583123)
      ·
        refine ⟨14209967151699577850374685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9473311434466385233583123 14209967151699577850374685)
        ·
          refine ⟨5328737681887341693890507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14209967151699577850374685 5328737681887341693890507)
          ·
            refine ⟨7993106522831012540835761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5328737681887341693890507 7993106522831012540835761)
            ·
              refine ⟨5994829892123259405626821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7993106522831012540835761 5994829892123259405626821)
              ·
                refine ⟨1124030604773111138555029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5994829892123259405626821 1124030604773111138555029)
                ·
                  refine ⟨52688934598739584619767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1124030604773111138555029 52688934598739584619767)
                  ·
                    rfl

theorem cell22_461751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 6].length) (baseStart_461751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461751 prefixEnd_461751 := by exact prefixLift 461751
  have htrace : WordTrace (prefixWord ++ tailWord_461751) baseStart_461751 baseEnd_461751 := by
    simpa [prefixWord, tailWord_461751, baseEnd_461751] using wordTrace_append hprefix tailTrace_461751
  have hstable : (prefixWord ++ tailWord_461751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461751).length < 2 ^ (prefixWord ++ tailWord_461751).sum := by decide
  have hdescent : baseEnd_461751 < baseStart_461751 := by decide
  rcases family_descends (prefixWord ++ tailWord_461751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461753 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 3, 4]
def baseStart_461753 : Nat := 118140960795 + 461753 * 2 ^ 59
def prefixEnd_461753 : Nat := 4983230072969 + 3 ^ 40 * 461753 * 2
def baseEnd_461753 : Nat := 158067488437091415309295

theorem tailTrace_461753 : CollatzResearch.WordTrace tailWord_461753 prefixEnd_461753 158067488437091415309295 := by
  unfold tailWord_461753
  simp only [CollatzResearch.WordTrace]
  refine ⟨16841515496155216979053913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11227676997436811319369275 16841515496155216979053913)
  ·
    refine ⟨12631136622116412734290435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16841515496155216979053913 12631136622116412734290435)
    ·
      refine ⟨18946704933174619101435653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12631136622116412734290435 18946704933174619101435653)
      ·
        refine ⟨3552507174970241081519185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18946704933174619101435653 3552507174970241081519185)
        ·
          refine ⟨2664380381227680811139389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3552507174970241081519185 2664380381227680811139389)
          ·
            refine ⟨999142642960380304177271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2664380381227680811139389 999142642960380304177271)
            ·
              refine ⟨1498713964440570456265907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999142642960380304177271 1498713964440570456265907)
              ·
                refine ⟨2248070946660855684398861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1498713964440570456265907 2248070946660855684398861)
                ·
                  refine ⟨843026604997820881649573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2248070946660855684398861 843026604997820881649573)
                  ·
                    refine ⟨158067488437091415309295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 843026604997820881649573 158067488437091415309295)
                    ·
                      rfl

theorem cell22_461753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_461753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461753 prefixEnd_461753 := by exact prefixLift 461753
  have htrace : WordTrace (prefixWord ++ tailWord_461753) baseStart_461753 baseEnd_461753 := by
    simpa [prefixWord, tailWord_461753, baseEnd_461753] using wordTrace_append hprefix tailTrace_461753
  have hstable : (prefixWord ++ tailWord_461753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461753).length < 2 ^ (prefixWord ++ tailWord_461753).sum := by decide
  have hdescent : baseEnd_461753 < baseStart_461753 := by decide
  rcases family_descends (prefixWord ++ tailWord_461753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461785 : List Nat := [1, 2, 1, 2, 5, 2, 1, 4, 4]
def baseStart_461785 : Nat := 118140960795 + 461785 * 2 ^ 59
def prefixEnd_461785 : Nat := 4983230072969 + 3 ^ 40 * 461785 * 2
def baseEnd_461785 : Nat := 52692814230351332836399

theorem tailTrace_461785 : CollatzResearch.WordTrace tailWord_461785 prefixEnd_461785 52692814230351332836399 := by
  unfold tailWord_461785
  simp only [CollatzResearch.WordTrace]
  refine ⟨16842682632039286444218809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11228455088026190962812539 16842682632039286444218809)
  ·
    refine ⟨12632011974029464833164107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16842682632039286444218809 12632011974029464833164107)
    ·
      refine ⟨18948017961044197249746161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12632011974029464833164107 18948017961044197249746161)
      ·
        refine ⟨14211013470783147937309621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18948017961044197249746161 14211013470783147937309621)
        ·
          refine ⟨1332282512885920119122777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14211013470783147937309621 1332282512885920119122777)
          ·
            refine ⟨999211884664440089342083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1332282512885920119122777 999211884664440089342083)
            ·
              refine ⟨1498817826996660134013125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999211884664440089342083 1498817826996660134013125)
              ·
                refine ⟨281028342561873775127461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1498817826996660134013125 281028342561873775127461)
                ·
                  refine ⟨52692814230351332836399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281028342561873775127461 52692814230351332836399)
                  ·
                    rfl

theorem cell22_461785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 4].length) (baseStart_461785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461785 prefixEnd_461785 := by exact prefixLift 461785
  have htrace : WordTrace (prefixWord ++ tailWord_461785) baseStart_461785 baseEnd_461785 := by
    simpa [prefixWord, tailWord_461785, baseEnd_461785] using wordTrace_append hprefix tailTrace_461785
  have hstable : (prefixWord ++ tailWord_461785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461785).length < 2 ^ (prefixWord ++ tailWord_461785).sum := by decide
  have hdescent : baseEnd_461785 < baseStart_461785 := by decide
  rcases family_descends (prefixWord ++ tailWord_461785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461796 : List Nat := [2, 3, 1, 1, 1, 1, 2, 11]
def baseStart_461796 : Nat := 118140960795 + 461796 * 2 ^ 59
def prefixEnd_461796 : Nat := 4983230072969 + 3 ^ 40 * 461796 * 2
def baseEnd_461796 : Nat := 17564689801761515164907

theorem tailTrace_461796 : CollatzResearch.WordTrace tailWord_461796 prefixEnd_461796 17564689801761515164907 := by
  unfold tailWord_461796
  simp only [CollatzResearch.WordTrace]
  refine ⟨8421541917499717661434621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11228722556666290215246161 8421541917499717661434621)
  ·
    refine ⟨3158078219062394123037983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8421541917499717661434621 3158078219062394123037983)
    ·
      refine ⟨4737117328593591184556975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3158078219062394123037983 4737117328593591184556975)
      ·
        refine ⟨7105675992890386776835463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4737117328593591184556975 7105675992890386776835463)
        ·
          refine ⟨10658513989335580165253195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7105675992890386776835463 10658513989335580165253195)
          ·
            refine ⟨15987770984003370247879793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10658513989335580165253195 15987770984003370247879793)
            ·
              refine ⟨11990828238002527685909845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15987770984003370247879793 11990828238002527685909845)
              ·
                refine ⟨17564689801761515164907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 11990828238002527685909845 17564689801761515164907)
                ·
                  rfl

theorem cell22_461796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 11].length) (baseStart_461796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461796 prefixEnd_461796 := by exact prefixLift 461796
  have htrace : WordTrace (prefixWord ++ tailWord_461796) baseStart_461796 baseEnd_461796 := by
    simpa [prefixWord, tailWord_461796, baseEnd_461796] using wordTrace_append hprefix tailTrace_461796
  have hstable : (prefixWord ++ tailWord_461796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461796).length < 2 ^ (prefixWord ++ tailWord_461796).sum := by decide
  have hdescent : baseEnd_461796 < baseStart_461796 := by decide
  rcases family_descends (prefixWord ++ tailWord_461796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461800 : List Nat := [2, 1, 4, 1, 1, 1, 4, 3, 2, 3]
def baseStart_461800 : Nat := 118140960795 + 461800 * 2 ^ 59
def prefixEnd_461800 : Nat := 4983230072969 + 3 ^ 40 * 461800 * 2
def baseEnd_461800 : Nat := 158083577497598959384151

theorem tailTrace_461800 : CollatzResearch.WordTrace tailWord_461800 prefixEnd_461800 158083577497598959384151 := by
  unfold tailWord_461800
  simp only [CollatzResearch.WordTrace]
  refine ⟨8421614863492472003007427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11228819817989962670676569 8421614863492472003007427)
  ·
    refine ⟨12632422295238708004511141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8421614863492472003007427 12632422295238708004511141)
    ·
      refine ⟨2368579180357257750845839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12632422295238708004511141 2368579180357257750845839)
      ·
        refine ⟨3552868770535886626268759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2368579180357257750845839 3552868770535886626268759)
        ·
          refine ⟨5329303155803829939403139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3552868770535886626268759 5329303155803829939403139)
          ·
            refine ⟨7993954733705744909104709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5329303155803829939403139 7993954733705744909104709)
            ·
              refine ⟨1498866512569827170457133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7993954733705744909104709 1498866512569827170457133)
              ·
                refine ⟨562074942213685188921425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1498866512569827170457133 562074942213685188921425)
                ·
                  refine ⟨421556206660263891691069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562074942213685188921425 421556206660263891691069)
                  ·
                    refine ⟨158083577497598959384151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 421556206660263891691069 158083577497598959384151)
                    ·
                      rfl

theorem cell22_461800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_461800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461800 prefixEnd_461800 := by exact prefixLift 461800
  have htrace : WordTrace (prefixWord ++ tailWord_461800) baseStart_461800 baseEnd_461800 := by
    simpa [prefixWord, tailWord_461800, baseEnd_461800] using wordTrace_append hprefix tailTrace_461800
  have hstable : (prefixWord ++ tailWord_461800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461800).length < 2 ^ (prefixWord ++ tailWord_461800).sum := by decide
  have hdescent : baseEnd_461800 < baseStart_461800 := by decide
  rcases family_descends (prefixWord ++ tailWord_461800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461845 : List Nat := [1, 3, 2, 1, 4, 1, 1, 3, 3, 3]
def baseStart_461845 : Nat := 118140960795 + 461845 * 2 ^ 59
def prefixEnd_461845 : Nat := 4983230072969 + 3 ^ 40 * 461845 * 2
def baseEnd_461845 : Nat := 158098981917233842009013

theorem tailTrace_461845 : CollatzResearch.WordTrace tailWord_461845 prefixEnd_461845 158098981917233842009013 := by
  unfold tailWord_461845
  simp only [CollatzResearch.WordTrace]
  refine ⟨16844871011821916691402989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11229914007881277794268659 16844871011821916691402989)
  ·
    refine ⟨6316826629433218759276121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16844871011821916691402989 6316826629433218759276121)
    ·
      refine ⟨4737619972074914069457091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6316826629433218759276121 4737619972074914069457091)
      ·
        refine ⟨7106429958112371104185637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4737619972074914069457091 7106429958112371104185637)
        ·
          refine ⟨1332455617146069582034807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7106429958112371104185637 1332455617146069582034807)
          ·
            refine ⟨1998683425719104373052211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332455617146069582034807 1998683425719104373052211)
            ·
              refine ⟨2998025138578656559578317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1998683425719104373052211 2998025138578656559578317)
              ·
                refine ⟨1124259426966996209841869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2998025138578656559578317 1124259426966996209841869)
                ·
                  refine ⟨421597285112623578690701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1124259426966996209841869 421597285112623578690701)
                  ·
                    refine ⟨158098981917233842009013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 421597285112623578690701 158098981917233842009013)
                    ·
                      rfl

theorem cell22_461845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_461845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461845 prefixEnd_461845 := by exact prefixLift 461845
  have htrace : WordTrace (prefixWord ++ tailWord_461845) baseStart_461845 baseEnd_461845 := by
    simpa [prefixWord, tailWord_461845, baseEnd_461845] using wordTrace_append hprefix tailTrace_461845
  have hstable : (prefixWord ++ tailWord_461845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461845).length < 2 ^ (prefixWord ++ tailWord_461845).sum := by decide
  have hdescent : baseEnd_461845 < baseStart_461845 := by decide
  rcases family_descends (prefixWord ++ tailWord_461845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461922 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_461922 : Nat := 118140960795 + 461922 * 2 ^ 59
def prefixEnd_461922 : Nat := 4983230072969 + 3 ^ 40 * 461922 * 2
def baseEnd_461922 : Nat := 158125340590831307833777

theorem tailTrace_461922 : CollatzResearch.WordTrace tailWord_461922 prefixEnd_461922 158125340590831307833777 := by
  unfold tailWord_461922
  simp only [CollatzResearch.WordTrace]
  refine ⟨4211919858135739710489005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11231786288361972561304013 4211919858135739710489005)
  ·
    refine ⟨1579469946800902391433377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4211919858135739710489005 1579469946800902391433377)
    ·
      refine ⟨1184602460100676793575033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1579469946800902391433377 1184602460100676793575033)
      ·
        refine ⟨888451845075507595181275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1184602460100676793575033 888451845075507595181275)
        ·
          refine ⟨1332677767613261392771913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888451845075507595181275 1332677767613261392771913)
          ·
            refine ⟨999508325709946044578935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1332677767613261392771913 999508325709946044578935)
            ·
              refine ⟨1499262488564919066868403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999508325709946044578935 1499262488564919066868403)
              ·
                refine ⟨2248893732847378600302605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1499262488564919066868403 2248893732847378600302605)
                ·
                  refine ⟨843335149817766975113477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2248893732847378600302605 843335149817766975113477)
                  ·
                    refine ⟨158125340590831307833777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 843335149817766975113477 158125340590831307833777)
                    ·
                      rfl

theorem cell22_461922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_461922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_461922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_461922 prefixEnd_461922 := by exact prefixLift 461922
  have htrace : WordTrace (prefixWord ++ tailWord_461922) baseStart_461922 baseEnd_461922 := by
    simpa [prefixWord, tailWord_461922, baseEnd_461922] using wordTrace_append hprefix tailTrace_461922
  have hstable : (prefixWord ++ tailWord_461922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461922).length < 2 ^ (prefixWord ++ tailWord_461922).sum := by decide
  have hdescent : baseEnd_461922 < baseStart_461922 := by decide
  rcases family_descends (prefixWord ++ tailWord_461922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462014 : List Nat := [4, 2, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_462014 : Nat := 118140960795 + 462014 * 2 ^ 59
def prefixEnd_462014 : Nat := 4983230072969 + 3 ^ 40 * 462014 * 2
def baseEnd_462014 : Nat := 158156834070973734533495

theorem tailTrace_462014 : CollatzResearch.WordTrace tailWord_462014 prefixEnd_462014 158156834070973734533495 := by
  unfold tailWord_462014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2106379368526207319288137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11234023298806439036203397 2106379368526207319288137)
  ·
    refine ⟨1579784526394655489466103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2106379368526207319288137 1579784526394655489466103)
    ·
      refine ⟨2369676789591983234199155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1579784526394655489466103 2369676789591983234199155)
      ·
        refine ⟨3554515184387974851298733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2369676789591983234199155 3554515184387974851298733)
        ·
          refine ⟨1332943194145490569237025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3554515184387974851298733 1332943194145490569237025)
          ·
            refine ⟨999707395609117926927769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1332943194145490569237025 999707395609117926927769)
            ·
              refine ⟨749780546706838445195827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 999707395609117926927769 749780546706838445195827)
              ·
                refine ⟨1124670820060257667793741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 749780546706838445195827 1124670820060257667793741)
                ·
                  refine ⟨421751557522596625422653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1124670820060257667793741 421751557522596625422653)
                  ·
                    refine ⟨158156834070973734533495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 421751557522596625422653 158156834070973734533495)
                    ·
                      rfl

theorem cell22_462014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_462014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462014 prefixEnd_462014 := by exact prefixLift 462014
  have htrace : WordTrace (prefixWord ++ tailWord_462014) baseStart_462014 baseEnd_462014 := by
    simpa [prefixWord, tailWord_462014, baseEnd_462014] using wordTrace_append hprefix tailTrace_462014
  have hstable : (prefixWord ++ tailWord_462014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462014).length < 2 ^ (prefixWord ++ tailWord_462014).sum := by decide
  have hdescent : baseEnd_462014 < baseStart_462014 := by decide
  rcases family_descends (prefixWord ++ tailWord_462014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462085 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 4, 4]
def baseStart_462085 : Nat := 118140960795 + 462085 * 2 ^ 59
def prefixEnd_462085 : Nat := 4983230072969 + 3 ^ 40 * 462085 * 2
def baseEnd_462085 : Nat := 158181138821953216008277

theorem tailTrace_462085 : CollatzResearch.WordTrace tailWord_462085 prefixEnd_462085 158181138821953216008277 := by
  unfold tailWord_462085
  simp only [CollatzResearch.WordTrace]
  refine ⟨16853624530952437680139709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11235749687301625120093139 16853624530952437680139709)
  ·
    refine ⟨6320109199107164130052391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16853624530952437680139709 6320109199107164130052391)
    ·
      refine ⟨9480163798660746195078587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6320109199107164130052391 9480163798660746195078587)
      ·
        refine ⟨14220245697991119292617881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9480163798660746195078587 14220245697991119292617881)
        ·
          refine ⟨10665184273493339469463411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14220245697991119292617881 10665184273493339469463411)
          ·
            refine ⟨15997776410240009204195117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10665184273493339469463411 15997776410240009204195117)
            ·
              refine ⟨5999166153840003451573169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15997776410240009204195117 5999166153840003451573169)
              ·
                refine ⟨4499374615380002588679877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5999166153840003451573169 4499374615380002588679877)
                ·
                  refine ⟨843632740383750485377477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4499374615380002588679877 843632740383750485377477)
                  ·
                    refine ⟨158181138821953216008277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 843632740383750485377477 158181138821953216008277)
                    ·
                      rfl

theorem cell22_462085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_462085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462085 prefixEnd_462085 := by exact prefixLift 462085
  have htrace : WordTrace (prefixWord ++ tailWord_462085) baseStart_462085 baseEnd_462085 := by
    simpa [prefixWord, tailWord_462085, baseEnd_462085] using wordTrace_append hprefix tailTrace_462085
  have hstable : (prefixWord ++ tailWord_462085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462085).length < 2 ^ (prefixWord ++ tailWord_462085).sum := by decide
  have hdescent : baseEnd_462085 < baseStart_462085 := by decide
  rcases family_descends (prefixWord ++ tailWord_462085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462160 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 1, 7]
def baseStart_462160 : Nat := 118140960795 + 462160 * 2 ^ 59
def prefixEnd_462160 : Nat := 4983230072969 + 3 ^ 40 * 462160 * 2
def baseEnd_462160 : Nat := 158206812854678020383047

theorem tailTrace_462160 : CollatzResearch.WordTrace tailWord_462160 prefixEnd_462160 158206812854678020383047 := by
  unfold tailWord_462160
  simp only [CollatzResearch.WordTrace]
  refine ⟨8428180002840362744559967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11237573337120483659413289 8428180002840362744559967)
  ·
    refine ⟨12642270004260544116839951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8428180002840362744559967 12642270004260544116839951)
    ·
      refine ⟨18963405006390816175259927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12642270004260544116839951 18963405006390816175259927)
      ·
        refine ⟨28445107509586224262889891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18963405006390816175259927 28445107509586224262889891)
        ·
          refine ⟨42667661264379336394334837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28445107509586224262889891 42667661264379336394334837)
          ·
            refine ⟨4000093243535562786968891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42667661264379336394334837 4000093243535562786968891)
            ·
              refine ⟨6000139865303344180453337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4000093243535562786968891 6000139865303344180453337)
              ·
                refine ⟨4500104898977508135340003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6000139865303344180453337 4500104898977508135340003)
                ·
                  refine ⟨6750157348466262203010005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4500104898977508135340003 6750157348466262203010005)
                  ·
                    refine ⟨158206812854678020383047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6750157348466262203010005 158206812854678020383047)
                    ·
                      rfl

theorem cell22_462160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_462160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462160 prefixEnd_462160 := by exact prefixLift 462160
  have htrace : WordTrace (prefixWord ++ tailWord_462160) baseStart_462160 baseEnd_462160 := by
    simpa [prefixWord, tailWord_462160, baseEnd_462160] using wordTrace_append hprefix tailTrace_462160
  have hstable : (prefixWord ++ tailWord_462160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462160).length < 2 ^ (prefixWord ++ tailWord_462160).sum := by decide
  have hdescent : baseEnd_462160 < baseStart_462160 := by decide
  rcases family_descends (prefixWord ++ tailWord_462160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462179 : List Nat := [1, 1, 1, 5, 2, 4, 1, 2, 5]
def baseStart_462179 : Nat := 118140960795 + 462179 * 2 ^ 59
def prefixEnd_462179 : Nat := 4983230072969 + 3 ^ 40 * 462179 * 2
def baseEnd_462179 : Nat := 52737772314322768052663

theorem tailTrace_462179 : CollatzResearch.WordTrace tailWord_462179 prefixEnd_462179 52737772314322768052663 := by
  unfold tailWord_462179
  simp only [CollatzResearch.WordTrace]
  refine ⟨16857052992611891734061591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11238035328407927822707727 16857052992611891734061591)
  ·
    refine ⟨25285579488917837601092387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16857052992611891734061591 25285579488917837601092387)
    ·
      refine ⟨37928369233376756401638581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25285579488917837601092387 37928369233376756401638581)
      ·
        refine ⟨3555784615629070912653617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37928369233376756401638581 3555784615629070912653617)
        ·
          refine ⟨2666838461721803184490213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3555784615629070912653617 2666838461721803184490213)
          ·
            refine ⟨500032211572838097091915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2666838461721803184490213 500032211572838097091915)
            ·
              refine ⟨750048317359257145637873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500032211572838097091915 750048317359257145637873)
              ·
                refine ⟨562536238019442859228405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750048317359257145637873 562536238019442859228405)
                ·
                  refine ⟨52737772314322768052663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 562536238019442859228405 52737772314322768052663)
                  ·
                    rfl

theorem cell22_462179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 5].length) (baseStart_462179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462179 prefixEnd_462179 := by exact prefixLift 462179
  have htrace : WordTrace (prefixWord ++ tailWord_462179) baseStart_462179 baseEnd_462179 := by
    simpa [prefixWord, tailWord_462179, baseEnd_462179] using wordTrace_append hprefix tailTrace_462179
  have hstable : (prefixWord ++ tailWord_462179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462179).length < 2 ^ (prefixWord ++ tailWord_462179).sum := by decide
  have hdescent : baseEnd_462179 < baseStart_462179 := by decide
  rcases family_descends (prefixWord ++ tailWord_462179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462239 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 4, 3]
def baseStart_462239 : Nat := 118140960795 + 462239 * 2 ^ 59
def prefixEnd_462239 : Nat := 4983230072969 + 3 ^ 40 * 462239 * 2
def baseEnd_462239 : Nat := 158233856169148147657805

theorem tailTrace_462239 : CollatzResearch.WordTrace tailWord_462239 prefixEnd_462239 158233856169148147657805 := by
  unfold tailWord_462239
  simp only [CollatzResearch.WordTrace]
  refine ⟨16859241372394521981245771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11239494248263014654163847 16859241372394521981245771)
  ·
    refine ⟨25288862058591782971868657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16859241372394521981245771 25288862058591782971868657)
    ·
      refine ⟨18966646543943837228901493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25288862058591782971868657 18966646543943837228901493)
      ·
        refine ⟨1778123113494734740209515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18966646543943837228901493 1778123113494734740209515)
        ·
          refine ⟨2667184670242102110314273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1778123113494734740209515 2667184670242102110314273)
          ·
            refine ⟨2000388502681576582735705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2667184670242102110314273 2000388502681576582735705)
            ·
              refine ⟨1500291377011182437051779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2000388502681576582735705 1500291377011182437051779)
              ·
                refine ⟨2250437065516773655577669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1500291377011182437051779 2250437065516773655577669)
                ·
                  refine ⟨421956949784395060420813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2250437065516773655577669 421956949784395060420813)
                  ·
                    refine ⟨158233856169148147657805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 421956949784395060420813 158233856169148147657805)
                    ·
                      rfl

theorem cell22_462239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 3].length) (baseStart_462239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462239 prefixEnd_462239 := by exact prefixLift 462239
  have htrace : WordTrace (prefixWord ++ tailWord_462239) baseStart_462239 baseEnd_462239 := by
    simpa [prefixWord, tailWord_462239, baseEnd_462239] using wordTrace_append hprefix tailTrace_462239
  have hstable : (prefixWord ++ tailWord_462239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462239).length < 2 ^ (prefixWord ++ tailWord_462239).sum := by decide
  have hdescent : baseEnd_462239 < baseStart_462239 := by decide
  rcases family_descends (prefixWord ++ tailWord_462239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462348 : List Nat := [2, 2, 1, 2, 6, 1, 1, 2, 5]
def baseStart_462348 : Nat := 118140960795 + 462348 * 2 ^ 59
def prefixEnd_462348 : Nat := 4983230072969 + 3 ^ 40 * 462348 * 2
def baseEnd_462348 : Nat := 52757056365569398894157

theorem tailTrace_462348 : CollatzResearch.WordTrace tailWord_462348 prefixEnd_462348 52757056365569398894157 := by
  unfold tailWord_462348
  simp only [CollatzResearch.WordTrace]
  refine ⟨8431608464499816798481849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11242144619333089064642465 8431608464499816798481849)
  ·
    refine ⟨6323706348374862598861387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8431608464499816798481849 6323706348374862598861387)
    ·
      refine ⟨9485559522562293898292081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6323706348374862598861387 9485559522562293898292081)
      ·
        refine ⟨7114169641921720423719061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9485559522562293898292081 7114169641921720423719061)
        ·
          refine ⟨333476701965080644861831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7114169641921720423719061 333476701965080644861831)
          ·
            refine ⟨500215052947620967292747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333476701965080644861831 500215052947620967292747)
            ·
              refine ⟨750322579421431450939121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500215052947620967292747 750322579421431450939121)
              ·
                refine ⟨562741934566073588204341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750322579421431450939121 562741934566073588204341)
                ·
                  refine ⟨52757056365569398894157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 562741934566073588204341 52757056365569398894157)
                  ·
                    rfl

theorem cell22_462348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_462348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462348 prefixEnd_462348 := by exact prefixLift 462348
  have htrace : WordTrace (prefixWord ++ tailWord_462348) baseStart_462348 baseEnd_462348 := by
    simpa [prefixWord, tailWord_462348, baseEnd_462348] using wordTrace_append hprefix tailTrace_462348
  have hstable : (prefixWord ++ tailWord_462348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462348).length < 2 ^ (prefixWord ++ tailWord_462348).sum := by decide
  have hdescent : baseEnd_462348 < baseStart_462348 := by decide
  rcases family_descends (prefixWord ++ tailWord_462348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462389 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 1, 6]
def baseStart_462389 : Nat := 118140960795 + 462389 * 2 ^ 59
def prefixEnd_462389 : Nat := 4983230072969 + 3 ^ 40 * 462389 * 2
def baseEnd_462389 : Nat := 158285204234597756407345

theorem tailTrace_462389 : CollatzResearch.WordTrace tailWord_462389 prefixEnd_462389 158285204234597756407345 := by
  unfold tailWord_462389
  simp only [CollatzResearch.WordTrace]
  refine ⟨16864712321851097599206221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11243141547900731732804147 16864712321851097599206221)
  ·
    refine ⟨6324267120694161599702333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16864712321851097599206221 6324267120694161599702333)
    ·
      refine ⟨2371600170260310599888375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6324267120694161599702333 2371600170260310599888375)
      ·
        refine ⟨3557400255390465899832563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2371600170260310599888375 3557400255390465899832563)
        ·
          refine ⟨5336100383085698849748845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3557400255390465899832563 5336100383085698849748845)
          ·
            refine ⟨2001037643657137068655817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5336100383085698849748845 2001037643657137068655817)
            ·
              refine ⟨1500778232742852801491863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2001037643657137068655817 1500778232742852801491863)
              ·
                refine ⟨2251167349114279202237795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1500778232742852801491863 2251167349114279202237795)
                ·
                  refine ⟨3376751023671418803356693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251167349114279202237795 3376751023671418803356693)
                  ·
                    refine ⟨158285204234597756407345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3376751023671418803356693 158285204234597756407345)
                    ·
                      rfl

theorem cell22_462389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_462389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462389 prefixEnd_462389 := by exact prefixLift 462389
  have htrace : WordTrace (prefixWord ++ tailWord_462389) baseStart_462389 baseEnd_462389 := by
    simpa [prefixWord, tailWord_462389, baseEnd_462389] using wordTrace_append hprefix tailTrace_462389
  have hstable : (prefixWord ++ tailWord_462389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462389).length < 2 ^ (prefixWord ++ tailWord_462389).sum := by decide
  have hdescent : baseEnd_462389 < baseStart_462389 := by decide
  rcases family_descends (prefixWord ++ tailWord_462389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462393 : List Nat := [1, 2, 1, 5, 1, 4, 1, 3, 4]
def baseStart_462393 : Nat := 118140960795 + 462393 * 2 ^ 59
def prefixEnd_462393 : Nat := 4983230072969 + 3 ^ 40 * 462393 * 2
def baseEnd_462393 : Nat := 52762191172114359769111

theorem tailTrace_462393 : CollatzResearch.WordTrace tailWord_462393 prefixEnd_462393 52762191172114359769111 := by
  unfold tailWord_462393
  simp only [CollatzResearch.WordTrace]
  refine ⟨16864858213836606282351833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11243238809224404188234555 16864858213836606282351833)
  ·
    refine ⟨12648643660377454711763875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16864858213836606282351833 12648643660377454711763875)
    ·
      refine ⟨18972965490566182067645813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12648643660377454711763875 18972965490566182067645813)
      ·
        refine ⟨1778715514740579568841795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18972965490566182067645813 1778715514740579568841795)
        ·
          refine ⟨2668073272110869353262693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1778715514740579568841795 2668073272110869353262693)
          ·
            refine ⟨500263738520788003736755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2668073272110869353262693 500263738520788003736755)
            ·
              refine ⟨750395607781182005605133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500263738520788003736755 750395607781182005605133)
              ·
                refine ⟨281398352917943252101925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 750395607781182005605133 281398352917943252101925)
                ·
                  refine ⟨52762191172114359769111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281398352917943252101925 52762191172114359769111)
                  ·
                    rfl

theorem cell22_462393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 4].length) (baseStart_462393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462393 prefixEnd_462393 := by exact prefixLift 462393
  have htrace : WordTrace (prefixWord ++ tailWord_462393) baseStart_462393 baseEnd_462393 := by
    simpa [prefixWord, tailWord_462393, baseEnd_462393] using wordTrace_append hprefix tailTrace_462393
  have hstable : (prefixWord ++ tailWord_462393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462393).length < 2 ^ (prefixWord ++ tailWord_462393).sum := by decide
  have hdescent : baseEnd_462393 < baseStart_462393 := by decide
  rcases family_descends (prefixWord ++ tailWord_462393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462419 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 9, 3]
def baseStart_462419 : Nat := 118140960795 + 462419 * 2 ^ 59
def prefixEnd_462419 : Nat := 4983230072969 + 3 ^ 40 * 462419 * 2
def baseEnd_462419 : Nat := 158295473847687678157253

theorem tailTrace_462419 : CollatzResearch.WordTrace tailWord_462419 prefixEnd_462419 158295473847687678157253 := by
  unfold tailWord_462419
  simp only [CollatzResearch.WordTrace]
  refine ⟨16865806511742412722798311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11243871007828275148532207 16865806511742412722798311)
  ·
    refine ⟨25298709767613619084197467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16865806511742412722798311 25298709767613619084197467)
    ·
      refine ⟨37948064651420428626296201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25298709767613619084197467 37948064651420428626296201)
      ·
        refine ⟨28461048488565321469722151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37948064651420428626296201 28461048488565321469722151)
        ·
          refine ⟨42691572732847982204583227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28461048488565321469722151 42691572732847982204583227)
          ·
            refine ⟨64037359099271973306874841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42691572732847982204583227 64037359099271973306874841)
            ·
              refine ⟨48028019324453979980156131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64037359099271973306874841 48028019324453979980156131)
              ·
                refine ⟨72042028986680969970234197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48028019324453979980156131 72042028986680969970234197)
                ·
                  refine ⟨422121263593833808419341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72042028986680969970234197 422121263593833808419341)
                  ·
                    refine ⟨158295473847687678157253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 422121263593833808419341 158295473847687678157253)
                    ·
                      rfl

theorem cell22_462419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 3].length) (baseStart_462419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462419 prefixEnd_462419 := by exact prefixLift 462419
  have htrace : WordTrace (prefixWord ++ tailWord_462419) baseStart_462419 baseEnd_462419 := by
    simpa [prefixWord, tailWord_462419, baseEnd_462419] using wordTrace_append hprefix tailTrace_462419
  have hstable : (prefixWord ++ tailWord_462419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462419).length < 2 ^ (prefixWord ++ tailWord_462419).sum := by decide
  have hdescent : baseEnd_462419 < baseStart_462419 := by decide
  rcases family_descends (prefixWord ++ tailWord_462419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462464 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 2, 5]
def baseStart_462464 : Nat := 118140960795 + 462464 * 2 ^ 59
def prefixEnd_462464 : Nat := 4983230072969 + 3 ^ 40 * 462464 * 2
def baseEnd_462464 : Nat := 158310878267322560782115

theorem tailTrace_462464 : CollatzResearch.WordTrace tailWord_462464 prefixEnd_462464 158310878267322560782115 := by
  unfold tailWord_462464
  simp only [CollatzResearch.WordTrace]
  refine ⟨8433723898289692704093223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11244965197719590272124297 8433723898289692704093223)
  ·
    refine ⟨12650585847434539056139835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8433723898289692704093223 12650585847434539056139835)
    ·
      refine ⟨18975878771151808584209753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12650585847434539056139835 18975878771151808584209753)
      ·
        refine ⟨14231909078363856438157315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18975878771151808584209753 14231909078363856438157315)
        ·
          refine ⟨21347863617545784657235973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14231909078363856438157315 21347863617545784657235973)
          ·
            refine ⟨4002724428289834623231745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21347863617545784657235973 4002724428289834623231745)
            ·
              refine ⟨3002043321217375967423809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4002724428289834623231745 3002043321217375967423809)
              ·
                refine ⟨2251532490913031975567857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3002043321217375967423809 2251532490913031975567857)
                ·
                  refine ⟨1688649368184773981675893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2251532490913031975567857 1688649368184773981675893)
                  ·
                    refine ⟨158310878267322560782115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1688649368184773981675893 158310878267322560782115)
                    ·
                      rfl

theorem cell22_462464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_462464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462464 prefixEnd_462464 := by exact prefixLift 462464
  have htrace : WordTrace (prefixWord ++ tailWord_462464) baseStart_462464 baseEnd_462464 := by
    simpa [prefixWord, tailWord_462464, baseEnd_462464] using wordTrace_append hprefix tailTrace_462464
  have hstable : (prefixWord ++ tailWord_462464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462464).length < 2 ^ (prefixWord ++ tailWord_462464).sum := by decide
  have hdescent : baseEnd_462464 < baseStart_462464 := by decide
  rcases family_descends (prefixWord ++ tailWord_462464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462496 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 3, 4]
def baseStart_462496 : Nat := 118140960795 + 462496 * 2 ^ 59
def prefixEnd_462496 : Nat := 4983230072969 + 3 ^ 40 * 462496 * 2
def baseEnd_462496 : Nat := 158321832521285143982017

theorem tailTrace_462496 : CollatzResearch.WordTrace tailWord_462496 prefixEnd_462496 158321832521285143982017 := by
  unfold tailWord_462496
  simp only [CollatzResearch.WordTrace]
  refine ⟨8434307466231727436675671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11245743288308969915567561 8434307466231727436675671)
  ·
    refine ⟨12651461199347591155013507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8434307466231727436675671 12651461199347591155013507)
    ·
      refine ⟨18977191799021386732520261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12651461199347591155013507 18977191799021386732520261)
      ·
        refine ⟨3558223462316510012347549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18977191799021386732520261 3558223462316510012347549)
        ·
          refine ⟨1334333798368691254630331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3558223462316510012347549 1334333798368691254630331)
          ·
            refine ⟨2001500697553036881945497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334333798368691254630331 2001500697553036881945497)
            ·
              refine ⟨1501125523164777661459123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2001500697553036881945497 1501125523164777661459123)
              ·
                refine ⟨2251688284747166492188685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501125523164777661459123 2251688284747166492188685)
                ·
                  refine ⟨844383106780187434570757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2251688284747166492188685 844383106780187434570757)
                  ·
                    refine ⟨158321832521285143982017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 844383106780187434570757 158321832521285143982017)
                    ·
                      rfl

theorem cell22_462496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_462496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462496 prefixEnd_462496 := by exact prefixLift 462496
  have htrace : WordTrace (prefixWord ++ tailWord_462496) baseStart_462496 baseEnd_462496 := by
    simpa [prefixWord, tailWord_462496, baseEnd_462496] using wordTrace_append hprefix tailTrace_462496
  have hstable : (prefixWord ++ tailWord_462496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462496).length < 2 ^ (prefixWord ++ tailWord_462496).sum := by decide
  have hdescent : baseEnd_462496 < baseStart_462496 := by decide
  rcases family_descends (prefixWord ++ tailWord_462496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462569 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 1, 8]
def baseStart_462569 : Nat := 118140960795 + 462569 * 2 ^ 59
def prefixEnd_462569 : Nat := 4983230072969 + 3 ^ 40 * 462569 * 2
def baseEnd_462569 : Nat := 158346821913137286906793

theorem tailTrace_462569 : CollatzResearch.WordTrace tailWord_462569 prefixEnd_462569 158346821913137286906793 := by
  unfold tailWord_462569
  simp only [CollatzResearch.WordTrace]
  refine ⟨16871277461198988340758761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11247518307465992227172507 16871277461198988340758761)
  ·
    refine ⟨12653458095899241255569071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16871277461198988340758761 12653458095899241255569071)
    ·
      refine ⟨18980187143848861883353607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12653458095899241255569071 18980187143848861883353607)
      ·
        refine ⟨28470280715773292825030411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18980187143848861883353607 28470280715773292825030411)
        ·
          refine ⟨42705421073659939237545617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28470280715773292825030411 42705421073659939237545617)
          ·
            refine ⟨32029065805244954428159213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42705421073659939237545617 32029065805244954428159213)
            ·
              refine ⟨12010899676966857910559705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32029065805244954428159213 12010899676966857910559705)
              ·
                refine ⟨9008174757725143432919779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12010899676966857910559705 9008174757725143432919779)
                ·
                  refine ⟨13512262136587715149379669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9008174757725143432919779 13512262136587715149379669)
                  ·
                    refine ⟨158346821913137286906793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13512262136587715149379669 158346821913137286906793)
                    ·
                      rfl

theorem cell22_462569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_462569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462569 prefixEnd_462569 := by exact prefixLift 462569
  have htrace : WordTrace (prefixWord ++ tailWord_462569) baseStart_462569 baseEnd_462569 := by
    simpa [prefixWord, tailWord_462569, baseEnd_462569] using wordTrace_append hprefix tailTrace_462569
  have hstable : (prefixWord ++ tailWord_462569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462569).length < 2 ^ (prefixWord ++ tailWord_462569).sum := by decide
  have hdescent : baseEnd_462569 < baseStart_462569 := by decide
  rcases family_descends (prefixWord ++ tailWord_462569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462571 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 5, 3]
def baseStart_462571 : Nat := 118140960795 + 462571 * 2 ^ 59
def prefixEnd_462571 : Nat := 4983230072969 + 3 ^ 40 * 462571 * 2
def baseEnd_462571 : Nat := 158347506554009948356787

theorem tailTrace_462571 : CollatzResearch.WordTrace tailWord_462571 prefixEnd_462571 158347506554009948356787 := by
  unfold tailWord_462571
  simp only [CollatzResearch.WordTrace]
  refine ⟨16871350407191742682331567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11247566938127828454887711 16871350407191742682331567)
  ·
    refine ⟨25307025610787614023497351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16871350407191742682331567 25307025610787614023497351)
    ·
      refine ⟨37960538416181421035246027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25307025610787614023497351 37960538416181421035246027)
      ·
        refine ⟨56940807624272131552869041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37960538416181421035246027 56940807624272131552869041)
        ·
          refine ⟨42705605718204098664651781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56940807624272131552869041 42705605718204098664651781)
          ·
            refine ⟨8007301072163268499622209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42705605718204098664651781 8007301072163268499622209)
            ·
              refine ⟨6005475804122451374716657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8007301072163268499622209 6005475804122451374716657)
              ·
                refine ⟨4504106853091838531037493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6005475804122451374716657 4504106853091838531037493)
                ·
                  refine ⟨422260017477359862284765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4504106853091838531037493 422260017477359862284765)
                  ·
                    refine ⟨158347506554009948356787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 422260017477359862284765 158347506554009948356787)
                    ·
                      rfl

theorem cell22_462571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 3].length) (baseStart_462571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462571 prefixEnd_462571 := by exact prefixLift 462571
  have htrace : WordTrace (prefixWord ++ tailWord_462571) baseStart_462571 baseEnd_462571 := by
    simpa [prefixWord, tailWord_462571, baseEnd_462571] using wordTrace_append hprefix tailTrace_462571
  have hstable : (prefixWord ++ tailWord_462571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462571).length < 2 ^ (prefixWord ++ tailWord_462571).sum := by decide
  have hdescent : baseEnd_462571 < baseStart_462571 := by decide
  rcases family_descends (prefixWord ++ tailWord_462571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462598 : List Nat := [6, 2, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_462598 : Nat := 118140960795 + 462598 * 2 ^ 59
def prefixEnd_462598 : Nat := 4983230072969 + 3 ^ 40 * 462598 * 2
def baseEnd_462598 : Nat := 158356749205790877931705

theorem tailTrace_462598 : CollatzResearch.WordTrace tailWord_462598 prefixEnd_462598 158356749205790877931705 := by
  unfold tailWord_462598
  simp only [CollatzResearch.WordTrace]
  refine ⟨527260474315435196673889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11248223452062617529042965 527260474315435196673889)
  ·
    refine ⟨395445355736576397505417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 527260474315435196673889 395445355736576397505417)
    ·
      refine ⟨296584016802432298129063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395445355736576397505417 296584016802432298129063)
      ·
        refine ⟨444876025203648447193595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296584016802432298129063 444876025203648447193595)
        ·
          refine ⟨667314037805472670790393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444876025203648447193595 667314037805472670790393)
          ·
            refine ⟨500485528354104503092795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667314037805472670790393 500485528354104503092795)
            ·
              refine ⟨750728292531156754639193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500485528354104503092795 750728292531156754639193)
              ·
                refine ⟨563046219398367565979395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750728292531156754639193 563046219398367565979395)
                ·
                  refine ⟨844569329097551348969093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563046219398367565979395 844569329097551348969093)
                  ·
                    refine ⟨158356749205790877931705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 844569329097551348969093 158356749205790877931705)
                    ·
                      rfl

theorem cell22_462598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_462598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462598 prefixEnd_462598 := by exact prefixLift 462598
  have htrace : WordTrace (prefixWord ++ tailWord_462598) baseStart_462598 baseEnd_462598 := by
    simpa [prefixWord, tailWord_462598, baseEnd_462598] using wordTrace_append hprefix tailTrace_462598
  have hstable : (prefixWord ++ tailWord_462598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462598).length < 2 ^ (prefixWord ++ tailWord_462598).sum := by decide
  have hdescent : baseEnd_462598 < baseStart_462598 := by decide
  rcases family_descends (prefixWord ++ tailWord_462598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462736 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 7]
def baseStart_462736 : Nat := 118140960795 + 462736 * 2 ^ 59
def prefixEnd_462736 : Nat := 4983230072969 + 3 ^ 40 * 462736 * 2
def baseEnd_462736 : Nat := 52801329808668172660427

theorem tailTrace_462736 : CollatzResearch.WordTrace tailWord_462736 prefixEnd_462736 52801329808668172660427 := by
  unfold tailWord_462736
  simp only [CollatzResearch.WordTrace]
  refine ⟨8438684225796987931044031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11251578967729317241392041 8438684225796987931044031)
  ·
    refine ⟨12658026338695481896566047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8438684225796987931044031 12658026338695481896566047)
    ·
      refine ⟨18987039508043222844849071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12658026338695481896566047 18987039508043222844849071)
      ·
        refine ⟨28480559262064834267273607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18987039508043222844849071 28480559262064834267273607)
        ·
          refine ⟨42720838893097251400910411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28480559262064834267273607 42720838893097251400910411)
          ·
            refine ⟨64081258339645877101365617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42720838893097251400910411 64081258339645877101365617)
            ·
              refine ⟨48060943754734407826024213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64081258339645877101365617 48060943754734407826024213)
              ·
                refine ⟨2252856738503175366844885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48060943754734407826024213 2252856738503175366844885)
                ·
                  refine ⟨52801329808668172660427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2252856738503175366844885 52801329808668172660427)
                  ·
                    rfl

theorem cell22_462736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 7].length) (baseStart_462736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462736 prefixEnd_462736 := by exact prefixLift 462736
  have htrace : WordTrace (prefixWord ++ tailWord_462736) baseStart_462736 baseEnd_462736 := by
    simpa [prefixWord, tailWord_462736, baseEnd_462736] using wordTrace_append hprefix tailTrace_462736
  have hstable : (prefixWord ++ tailWord_462736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462736).length < 2 ^ (prefixWord ++ tailWord_462736).sum := by decide
  have hdescent : baseEnd_462736 < baseStart_462736 := by decide
  rcases family_descends (prefixWord ++ tailWord_462736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462783 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 3, 4]
def baseStart_462783 : Nat := 118140960795 + 462783 * 2 ^ 59
def prefixEnd_462783 : Nat := 4983230072969 + 3 ^ 40 * 462783 * 2
def baseEnd_462783 : Nat := 158420078486512062056137

theorem tailTrace_462783 : CollatzResearch.WordTrace tailWord_462783 prefixEnd_462783 158420078486512062056137 := by
  unfold tailWord_462783
  simp only [CollatzResearch.WordTrace]
  refine ⟨16879082682423702889049003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11252721788282468592699335 16879082682423702889049003)
  ·
    refine ⟨25318624023635554333573505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16879082682423702889049003 25318624023635554333573505)
    ·
      refine ⟨18988968017726665750180129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25318624023635554333573505 18988968017726665750180129)
      ·
        refine ⟨14241726013294999312635097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18988968017726665750180129 14241726013294999312635097)
        ·
          refine ⟨10681294509971249484476323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14241726013294999312635097 10681294509971249484476323)
          ·
            refine ⟨16021941764956874226714485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10681294509971249484476323 16021941764956874226714485)
            ·
              refine ⟨1502057040464706958754483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16021941764956874226714485 1502057040464706958754483)
              ·
                refine ⟨2253085560697060438131725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502057040464706958754483 2253085560697060438131725)
                ·
                  refine ⟨844907085261397664299397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2253085560697060438131725 844907085261397664299397)
                  ·
                    refine ⟨158420078486512062056137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 844907085261397664299397 158420078486512062056137)
                    ·
                      rfl

theorem cell22_462783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_462783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462783 prefixEnd_462783 := by exact prefixLift 462783
  have htrace : WordTrace (prefixWord ++ tailWord_462783) baseStart_462783 baseEnd_462783 := by
    simpa [prefixWord, tailWord_462783, baseEnd_462783] using wordTrace_append hprefix tailTrace_462783
  have hstable : (prefixWord ++ tailWord_462783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462783).length < 2 ^ (prefixWord ++ tailWord_462783).sum := by decide
  have hdescent : baseEnd_462783 < baseStart_462783 := by decide
  rcases family_descends (prefixWord ++ tailWord_462783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462828 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 4, 4]
def baseStart_462828 : Nat := 118140960795 + 462828 * 2 ^ 59
def prefixEnd_462828 : Nat := 4983230072969 + 3 ^ 40 * 462828 * 2
def baseEnd_462828 : Nat := 158435482906146944680999

theorem tailTrace_462828 : CollatzResearch.WordTrace tailWord_462828 prefixEnd_462828 158435482906146944680999 := by
  unfold tailWord_462828
  simp only [CollatzResearch.WordTrace]
  refine ⟨8440361983630337787218569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11253815978173783716291425 8440361983630337787218569)
  ·
    refine ⟨6330271487722753340413927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8440361983630337787218569 6330271487722753340413927)
    ·
      refine ⟨9495407231584130010620891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6330271487722753340413927 9495407231584130010620891)
      ·
        refine ⟨14243110847376195015931337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9495407231584130010620891 14243110847376195015931337)
        ·
          refine ⟨10682333135532146261948503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14243110847376195015931337 10682333135532146261948503)
          ·
            refine ⟨16023499703298219392922755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10682333135532146261948503 16023499703298219392922755)
            ·
              refine ⟨24035249554947329089384133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16023499703298219392922755 24035249554947329089384133)
              ·
                refine ⟨4506609291552624204259525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24035249554947329089384133 4506609291552624204259525)
                ·
                  refine ⟨844989242166117038298661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4506609291552624204259525 844989242166117038298661)
                  ·
                    refine ⟨158435482906146944680999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 844989242166117038298661 158435482906146944680999)
                    ·
                      rfl

theorem cell22_462828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_462828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462828 prefixEnd_462828 := by exact prefixLift 462828
  have htrace : WordTrace (prefixWord ++ tailWord_462828) baseStart_462828 baseEnd_462828 := by
    simpa [prefixWord, tailWord_462828, baseEnd_462828] using wordTrace_append hprefix tailTrace_462828
  have hstable : (prefixWord ++ tailWord_462828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462828).length < 2 ^ (prefixWord ++ tailWord_462828).sum := by decide
  have hdescent : baseEnd_462828 < baseStart_462828 := by decide
  rcases family_descends (prefixWord ++ tailWord_462828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462830 : List Nat := [4, 1, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_462830 : Nat := 118140960795 + 462830 * 2 ^ 59
def prefixEnd_462830 : Nat := 4983230072969 + 3 ^ 40 * 462830 * 2
def baseEnd_462830 : Nat := 158436167547019606130993

theorem tailTrace_462830 : CollatzResearch.WordTrace tailWord_462830 prefixEnd_462830 158436167547019606130993 := by
  unfold tailWord_462830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2110099614156678739501243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11253864608835619944006629 2110099614156678739501243)
  ·
    refine ⟨3165149421235018109251865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2110099614156678739501243 3165149421235018109251865)
    ·
      refine ⟨2373862065926263581938899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3165149421235018109251865 2373862065926263581938899)
      ·
        refine ⟨3560793098889395372908349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2373862065926263581938899 3560793098889395372908349)
        ·
          refine ⟨1335297412083523264840631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3560793098889395372908349 1335297412083523264840631)
          ·
            refine ⟨2002946118125284897260947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335297412083523264840631 2002946118125284897260947)
            ·
              refine ⟨3004419177187927345891421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2002946118125284897260947 3004419177187927345891421)
              ·
                refine ⟨1126657191445472754709283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3004419177187927345891421 1126657191445472754709283)
                ·
                  refine ⟨1689985787168209132063925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126657191445472754709283 1689985787168209132063925)
                  ·
                    refine ⟨158436167547019606130993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1689985787168209132063925 158436167547019606130993)
                    ·
                      rfl

theorem cell22_462830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_462830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462830 prefixEnd_462830 := by exact prefixLift 462830
  have htrace : WordTrace (prefixWord ++ tailWord_462830) baseStart_462830 baseEnd_462830 := by
    simpa [prefixWord, tailWord_462830, baseEnd_462830] using wordTrace_append hprefix tailTrace_462830
  have hstable : (prefixWord ++ tailWord_462830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462830).length < 2 ^ (prefixWord ++ tailWord_462830).sum := by decide
  have hdescent : baseEnd_462830 < baseStart_462830 := by decide
  rcases family_descends (prefixWord ++ tailWord_462830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462845 : List Nat := [1, 4, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_462845 : Nat := 118140960795 + 462845 * 2 ^ 59
def prefixEnd_462845 : Nat := 4983230072969 + 3 ^ 40 * 462845 * 2
def baseEnd_462845 : Nat := 158441302353564567005947

theorem tailTrace_462845 : CollatzResearch.WordTrace tailWord_462845 prefixEnd_462845 158441302353564567005947 := by
  unfold tailWord_462845
  simp only [CollatzResearch.WordTrace]
  refine ⟨16881344008199087477805989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11254229338799391651870659 16881344008199087477805989)
  ·
    refine ⟨3165252001537328902088623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16881344008199087477805989 3165252001537328902088623)
    ·
      refine ⟨4747878002305993353132935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3165252001537328902088623 4747878002305993353132935)
      ·
        refine ⟨7121817003458990029699403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4747878002305993353132935 7121817003458990029699403)
        ·
          refine ⟨10682725505188485044549105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7121817003458990029699403 10682725505188485044549105)
          ·
            refine ⟨8012044128891363783411829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10682725505188485044549105 8012044128891363783411829)
            ·
              refine ⟨751129137083565354694859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8012044128891363783411829 751129137083565354694859)
              ·
                refine ⟨1126693705625348032042289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751129137083565354694859 1126693705625348032042289)
                ·
                  refine ⟨845020279219011024031717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1126693705625348032042289 845020279219011024031717)
                  ·
                    refine ⟨158441302353564567005947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 845020279219011024031717 158441302353564567005947)
                    ·
                      rfl

theorem cell22_462845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_462845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462845 prefixEnd_462845 := by exact prefixLift 462845
  have htrace : WordTrace (prefixWord ++ tailWord_462845) baseStart_462845 baseEnd_462845 := by
    simpa [prefixWord, tailWord_462845, baseEnd_462845] using wordTrace_append hprefix tailTrace_462845
  have hstable : (prefixWord ++ tailWord_462845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462845).length < 2 ^ (prefixWord ++ tailWord_462845).sum := by decide
  have hdescent : baseEnd_462845 < baseStart_462845 := by decide
  rcases family_descends (prefixWord ++ tailWord_462845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462903 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 1, 7]
def baseStart_462903 : Nat := 118140960795 + 462903 * 2 ^ 59
def prefixEnd_462903 : Nat := 4983230072969 + 3 ^ 40 * 462903 * 2
def baseEnd_462903 : Nat := 158461156938871749055769

theorem tailTrace_462903 : CollatzResearch.WordTrace tailWord_462903 prefixEnd_462903 158461156938871749055769 := by
  unfold tailWord_462903
  simp only [CollatzResearch.WordTrace]
  refine ⟨16883459441988963383417363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11255639627992642255611575 16883459441988963383417363)
  ·
    refine ⟨25325189162983445075126045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16883459441988963383417363 25325189162983445075126045)
    ·
      refine ⟨9496945936118791903172267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25325189162983445075126045 9496945936118791903172267)
      ·
        refine ⟨14245418904178187854758401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9496945936118791903172267 14245418904178187854758401)
        ·
          refine ⟨10684064178133640891068801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14245418904178187854758401 10684064178133640891068801)
          ·
            refine ⟨8013048133600230668301601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10684064178133640891068801 8013048133600230668301601)
            ·
              refine ⟨6009786100200173001226201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8013048133600230668301601 6009786100200173001226201)
              ·
                refine ⟨4507339575150129750919651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6009786100200173001226201 4507339575150129750919651)
                ·
                  refine ⟨6761009362725194626379477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4507339575150129750919651 6761009362725194626379477)
                  ·
                    refine ⟨158461156938871749055769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6761009362725194626379477 158461156938871749055769)
                    ·
                      rfl

theorem cell22_462903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_462903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462903 prefixEnd_462903 := by exact prefixLift 462903
  have htrace : WordTrace (prefixWord ++ tailWord_462903) baseStart_462903 baseEnd_462903 := by
    simpa [prefixWord, tailWord_462903, baseEnd_462903] using wordTrace_append hprefix tailTrace_462903
  have hstable : (prefixWord ++ tailWord_462903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462903).length < 2 ^ (prefixWord ++ tailWord_462903).sum := by decide
  have hdescent : baseEnd_462903 < baseStart_462903 := by decide
  rcases family_descends (prefixWord ++ tailWord_462903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462926 : List Nat := [4, 1, 1, 1, 1, 5, 3, 2, 1, 3]
def baseStart_462926 : Nat := 118140960795 + 462926 * 2 ^ 59
def prefixEnd_462926 : Nat := 4983230072969 + 3 ^ 40 * 462926 * 2
def baseEnd_462926 : Nat := 158469030308907355730699

theorem tailTrace_462926 : CollatzResearch.WordTrace tailWord_462926 prefixEnd_462926 158469030308907355730699 := by
  unfold tailWord_462926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2110537290113204788938079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11256198880603758874336421 2110537290113204788938079)
  ·
    refine ⟨3165805935169807183407119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2110537290113204788938079 3165805935169807183407119)
    ·
      refine ⟨4748708902754710775110679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3165805935169807183407119 4748708902754710775110679)
      ·
        refine ⟨7123063354132066162666019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4748708902754710775110679 7123063354132066162666019)
        ·
          refine ⟨10684595031198099243999029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7123063354132066162666019 10684595031198099243999029)
          ·
            refine ⟨1001680784174821804124909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10684595031198099243999029 1001680784174821804124909)
            ·
              refine ⟨375630294065558176546841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1001680784174821804124909 375630294065558176546841)
              ·
                refine ⟨281722720549168632410131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375630294065558176546841 281722720549168632410131)
                ·
                  refine ⟨422584080823752948615197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281722720549168632410131 422584080823752948615197)
                  ·
                    refine ⟨158469030308907355730699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 422584080823752948615197 158469030308907355730699)
                    ·
                      rfl

theorem cell22_462926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_462926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462926 prefixEnd_462926 := by exact prefixLift 462926
  have htrace : WordTrace (prefixWord ++ tailWord_462926) baseStart_462926 baseEnd_462926 := by
    simpa [prefixWord, tailWord_462926, baseEnd_462926] using wordTrace_append hprefix tailTrace_462926
  have hstable : (prefixWord ++ tailWord_462926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462926).length < 2 ^ (prefixWord ++ tailWord_462926).sum := by decide
  have hdescent : baseEnd_462926 < baseStart_462926 := by decide
  rcases family_descends (prefixWord ++ tailWord_462926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462969 : List Nat := [1, 2, 1, 3, 4, 2, 3, 1, 1, 4]
def baseStart_462969 : Nat := 118140960795 + 462969 * 2 ^ 59
def prefixEnd_462969 : Nat := 4983230072969 + 3 ^ 40 * 462969 * 2
def baseEnd_462969 : Nat := 158483750087669576905567

theorem tailTrace_462969 : CollatzResearch.WordTrace tailWord_462969 prefixEnd_462969 158483750087669576905567 := by
  unfold tailWord_462969
  simp only [CollatzResearch.WordTrace]
  refine ⟨16885866659749856655319961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11257244439833237770213307 16885866659749856655319961)
  ·
    refine ⟨12664399994812392491489971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16885866659749856655319961 12664399994812392491489971)
    ·
      refine ⟨18996599992218588737234957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12664399994812392491489971 18996599992218588737234957)
      ·
        refine ⟨7123724997081970776463109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18996599992218588737234957 7123724997081970776463109)
        ·
          refine ⟨1335698436952869520586833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7123724997081970776463109 1335698436952869520586833)
          ·
            refine ⟨1001773827714652140440125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1335698436952869520586833 1001773827714652140440125)
            ·
              refine ⟨375665185392994552665047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1001773827714652140440125 375665185392994552665047)
              ·
                refine ⟨563497778089491828997571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375665185392994552665047 563497778089491828997571)
                ·
                  refine ⟨845246667134237743496357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563497778089491828997571 845246667134237743496357)
                  ·
                    refine ⟨158483750087669576905567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 845246667134237743496357 158483750087669576905567)
                    ·
                      rfl

theorem cell22_462969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 1, 4].length) (baseStart_462969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462969 prefixEnd_462969 := by exact prefixLift 462969
  have htrace : WordTrace (prefixWord ++ tailWord_462969) baseStart_462969 baseEnd_462969 := by
    simpa [prefixWord, tailWord_462969, baseEnd_462969] using wordTrace_append hprefix tailTrace_462969
  have hstable : (prefixWord ++ tailWord_462969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462969).length < 2 ^ (prefixWord ++ tailWord_462969).sum := by decide
  have hdescent : baseEnd_462969 < baseStart_462969 := by decide
  rcases family_descends (prefixWord ++ tailWord_462969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462984 : List Nat := [2, 1, 3, 4, 1, 2, 1, 4, 4]
def baseStart_462984 : Nat := 118140960795 + 462984 * 2 ^ 59
def prefixEnd_462984 : Nat := 4983230072969 + 3 ^ 40 * 462984 * 2
def baseEnd_462984 : Nat := 52829628298071512593507

theorem tailTrace_462984 : CollatzResearch.WordTrace tailWord_462984 prefixEnd_462984 52829628298071512593507 := by
  unfold tailWord_462984
  simp only [CollatzResearch.WordTrace]
  refine ⟨8443206877347757108558003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11257609169797009478077337 8443206877347757108558003)
  ·
    refine ⟨12664810316021635662837005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8443206877347757108558003 12664810316021635662837005)
    ·
      refine ⟨4749303868508113373563877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12664810316021635662837005 4749303868508113373563877)
      ·
        refine ⟨890494475345271257543227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4749303868508113373563877 890494475345271257543227)
        ·
          refine ⟨1335741713017906886314841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890494475345271257543227 1335741713017906886314841)
          ·
            refine ⟨1001806284763430164736131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1335741713017906886314841 1001806284763430164736131)
            ·
              refine ⟨1502709427145145247104197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001806284763430164736131 1502709427145145247104197)
              ·
                refine ⟨281758017589714733832037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1502709427145145247104197 281758017589714733832037)
                ·
                  refine ⟨52829628298071512593507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281758017589714733832037 52829628298071512593507)
                  ·
                    rfl

theorem cell22_462984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 4].length) (baseStart_462984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_462984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_462984 prefixEnd_462984 := by exact prefixLift 462984
  have htrace : WordTrace (prefixWord ++ tailWord_462984) baseStart_462984 baseEnd_462984 := by
    simpa [prefixWord, tailWord_462984, baseEnd_462984] using wordTrace_append hprefix tailTrace_462984
  have hstable : (prefixWord ++ tailWord_462984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462984).length < 2 ^ (prefixWord ++ tailWord_462984).sum := by decide
  have hdescent : baseEnd_462984 < baseStart_462984 := by decide
  rcases family_descends (prefixWord ++ tailWord_462984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463044 : List Nat := [2, 3, 3, 1, 2, 1, 1, 3, 3, 3]
def baseStart_463044 : Nat := 118140960795 + 463044 * 2 ^ 59
def prefixEnd_463044 : Nat := 4983230072969 + 3 ^ 40 * 463044 * 2
def baseEnd_463044 : Nat := 158509424120394381280337

theorem tailTrace_463044 : CollatzResearch.WordTrace tailWord_463044 prefixEnd_463044 158509424120394381280337 := by
  unfold tailWord_463044
  simp only [CollatzResearch.WordTrace]
  refine ⟨8444301067239072232150093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11259068089652096309533457 8444301067239072232150093)
  ·
    refine ⟨3166612900214652087056285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8444301067239072232150093 3166612900214652087056285)
    ·
      refine ⟨1187479837580494532646107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3166612900214652087056285 1187479837580494532646107)
      ·
        refine ⟨1781219756370741798969161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1187479837580494532646107 1781219756370741798969161)
        ·
          refine ⟨1335914817278056349226871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1781219756370741798969161 1335914817278056349226871)
          ·
            refine ⟨2003872225917084523840307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335914817278056349226871 2003872225917084523840307)
            ·
              refine ⟨3005808338875626785760461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003872225917084523840307 3005808338875626785760461)
              ·
                refine ⟨1127178127078360044660173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3005808338875626785760461 1127178127078360044660173)
                ·
                  refine ⟨422691797654385016747565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1127178127078360044660173 422691797654385016747565)
                  ·
                    refine ⟨158509424120394381280337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 422691797654385016747565 158509424120394381280337)
                    ·
                      rfl

theorem cell22_463044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_463044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463044 prefixEnd_463044 := by exact prefixLift 463044
  have htrace : WordTrace (prefixWord ++ tailWord_463044) baseStart_463044 baseEnd_463044 := by
    simpa [prefixWord, tailWord_463044, baseEnd_463044] using wordTrace_append hprefix tailTrace_463044
  have hstable : (prefixWord ++ tailWord_463044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463044).length < 2 ^ (prefixWord ++ tailWord_463044).sum := by decide
  have hdescent : baseEnd_463044 < baseStart_463044 := by decide
  rcases family_descends (prefixWord ++ tailWord_463044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463055 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 2, 5]
def baseStart_463055 : Nat := 118140960795 + 463055 * 2 ^ 59
def prefixEnd_463055 : Nat := 4983230072969 + 3 ^ 40 * 463055 * 2
def baseEnd_463055 : Nat := 158513189645194019255303

theorem tailTrace_463055 : CollatzResearch.WordTrace tailWord_463055 prefixEnd_463055 158513189645194019255303 := by
  unfold tailWord_463055
  simp only [CollatzResearch.WordTrace]
  refine ⟨16889003337438293342950619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11259335558292195561967079 16889003337438293342950619)
  ·
    refine ⟨25333505006157440014425929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16889003337438293342950619 25333505006157440014425929)
    ·
      refine ⟨19000128754618080010819447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25333505006157440014425929 19000128754618080010819447)
      ·
        refine ⟨28500193131927120016229171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19000128754618080010819447 28500193131927120016229171)
        ·
          refine ⟨42750289697890680024343757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28500193131927120016229171 42750289697890680024343757)
          ·
            refine ⟨16031358636709005009128909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42750289697890680024343757 16031358636709005009128909)
            ·
              refine ⟨6011759488765876878423341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16031358636709005009128909 6011759488765876878423341)
              ·
                refine ⟨2254409808287203829408753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6011759488765876878423341 2254409808287203829408753)
                ·
                  refine ⟨1690807356215402872056565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2254409808287203829408753 1690807356215402872056565)
                  ·
                    refine ⟨158513189645194019255303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1690807356215402872056565 158513189645194019255303)
                    ·
                      rfl

theorem cell22_463055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_463055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463055 prefixEnd_463055 := by exact prefixLift 463055
  have htrace : WordTrace (prefixWord ++ tailWord_463055) baseStart_463055 baseEnd_463055 := by
    simpa [prefixWord, tailWord_463055, baseEnd_463055] using wordTrace_append hprefix tailTrace_463055
  have hstable : (prefixWord ++ tailWord_463055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463055).length < 2 ^ (prefixWord ++ tailWord_463055).sum := by decide
  have hdescent : baseEnd_463055 < baseStart_463055 := by decide
  rcases family_descends (prefixWord ++ tailWord_463055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463108 : List Nat := [2, 3, 2, 2, 4, 1, 2, 1, 5]
def baseStart_463108 : Nat := 118140960795 + 463108 * 2 ^ 59
def prefixEnd_463108 : Nat := 4983230072969 + 3 ^ 40 * 463108 * 2
def baseEnd_463108 : Nat := 52843777542773182560047

theorem tailTrace_463108 : CollatzResearch.WordTrace tailWord_463108 prefixEnd_463108 52843777542773182560047 := by
  unfold tailWord_463108
  simp only [CollatzResearch.WordTrace]
  refine ⟨8445468203123141697314989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11260624270830855596419985 8445468203123141697314989)
  ·
    refine ⟨3167050576171178136493121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8445468203123141697314989 3167050576171178136493121)
    ·
      refine ⟨2375287932128383602369841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3167050576171178136493121 2375287932128383602369841)
      ·
        refine ⟨1781465949096287701777381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2375287932128383602369841 1781465949096287701777381)
        ·
          refine ⟨334024865455553944083259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1781465949096287701777381 334024865455553944083259)
          ·
            refine ⟨501037298183330916124889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334024865455553944083259 501037298183330916124889)
            ·
              refine ⟨375777973637498187093667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501037298183330916124889 375777973637498187093667)
              ·
                refine ⟨563666960456247280640501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375777973637498187093667 563666960456247280640501)
                ·
                  refine ⟨52843777542773182560047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 563666960456247280640501 52843777542773182560047)
                  ·
                    rfl

theorem cell22_463108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_463108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463108 prefixEnd_463108 := by exact prefixLift 463108
  have htrace : WordTrace (prefixWord ++ tailWord_463108) baseStart_463108 baseEnd_463108 := by
    simpa [prefixWord, tailWord_463108, baseEnd_463108] using wordTrace_append hprefix tailTrace_463108
  have hstable : (prefixWord ++ tailWord_463108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463108).length < 2 ^ (prefixWord ++ tailWord_463108).sum := by decide
  have hdescent : baseEnd_463108 < baseStart_463108 := by decide
  rcases family_descends (prefixWord ++ tailWord_463108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463153 : List Nat := [1, 2, 2, 3, 4, 2, 2, 2, 4]
def baseStart_463153 : Nat := 118140960795 + 463153 * 2 ^ 59
def prefixEnd_463153 : Nat := 4983230072969 + 3 ^ 40 * 463153 * 2
def baseEnd_463153 : Nat := 52848912349318143435001

theorem tailTrace_463153 : CollatzResearch.WordTrace tailWord_463153 prefixEnd_463153 52848912349318143435001 := by
  unfold tailWord_463153
  simp only [CollatzResearch.WordTrace]
  refine ⟨16892577691083256080018113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11261718460722170720012075 16892577691083256080018113)
  ·
    refine ⟨12669433268312442060013585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16892577691083256080018113 12669433268312442060013585)
    ·
      refine ⟨9502074951234331545010189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12669433268312442060013585 9502074951234331545010189)
      ·
        refine ⟨3563278106712874329378821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9502074951234331545010189 3563278106712874329378821)
        ·
          refine ⟨668114645008663936758529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3563278106712874329378821 668114645008663936758529)
          ·
            refine ⟨501085983756497952568897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 668114645008663936758529 501085983756497952568897)
            ·
              refine ⟨375814487817373464426673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501085983756497952568897 375814487817373464426673)
              ·
                refine ⟨281860865863030098320005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375814487817373464426673 281860865863030098320005)
                ·
                  refine ⟨52848912349318143435001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281860865863030098320005 52848912349318143435001)
                  ·
                    rfl

theorem cell22_463153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 4].length) (baseStart_463153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463153 prefixEnd_463153 := by exact prefixLift 463153
  have htrace : WordTrace (prefixWord ++ tailWord_463153) baseStart_463153 baseEnd_463153 := by
    simpa [prefixWord, tailWord_463153, baseEnd_463153] using wordTrace_append hprefix tailTrace_463153
  have hstable : (prefixWord ++ tailWord_463153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463153).length < 2 ^ (prefixWord ++ tailWord_463153).sum := by decide
  have hdescent : baseEnd_463153 < baseStart_463153 := by decide
  rcases family_descends (prefixWord ++ tailWord_463153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463256 : List Nat := [2, 1, 2, 5, 1, 1, 2, 3, 1, 4]
def baseStart_463256 : Nat := 118140960795 + 463256 * 2 ^ 59
def prefixEnd_463256 : Nat := 4983230072969 + 3 ^ 40 * 463256 * 2
def baseEnd_463256 : Nat := 158581996052896494979687

theorem tailTrace_463256 : CollatzResearch.WordTrace tailWord_463256 prefixEnd_463256 158581996052896494979687 := by
  unfold tailWord_463256
  simp only [CollatzResearch.WordTrace]
  refine ⟨8448167204855052335508811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11264222939806736447345081 8448167204855052335508811)
  ·
    refine ⟨12672250807282578503263217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8448167204855052335508811 12672250807282578503263217)
    ·
      refine ⟨9504188105461933877447413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12672250807282578503263217 9504188105461933877447413)
      ·
        refine ⟨891017634887056301010695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9504188105461933877447413 891017634887056301010695)
        ·
          refine ⟨1336526452330584451516043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891017634887056301010695 1336526452330584451516043)
          ·
            refine ⟨2004789678495876677274065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336526452330584451516043 2004789678495876677274065)
            ·
              refine ⟨1503592258871907507955549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2004789678495876677274065 1503592258871907507955549)
              ·
                refine ⟨563847097076965315483331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1503592258871907507955549 563847097076965315483331)
                ·
                  refine ⟨845770645615447973224997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563847097076965315483331 845770645615447973224997)
                  ·
                    refine ⟨158581996052896494979687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 845770645615447973224997 158581996052896494979687)
                    ·
                      rfl

theorem cell22_463256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_463256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463256 prefixEnd_463256 := by exact prefixLift 463256
  have htrace : WordTrace (prefixWord ++ tailWord_463256) baseStart_463256 baseEnd_463256 := by
    simpa [prefixWord, tailWord_463256, baseEnd_463256] using wordTrace_append hprefix tailTrace_463256
  have hstable : (prefixWord ++ tailWord_463256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463256).length < 2 ^ (prefixWord ++ tailWord_463256).sum := by decide
  have hdescent : baseEnd_463256 < baseStart_463256 := by decide
  rcases family_descends (prefixWord ++ tailWord_463256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463269 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 4, 3]
def baseStart_463269 : Nat := 118140960795 + 463269 * 2 ^ 59
def prefixEnd_463269 : Nat := 4983230072969 + 3 ^ 40 * 463269 * 2
def baseEnd_463269 : Nat := 158586446218568794404647

theorem tailTrace_463269 : CollatzResearch.WordTrace tailWord_463269 prefixEnd_463269 158586446218568794404647 := by
  unfold tailWord_463269
  simp only [CollatzResearch.WordTrace]
  refine ⟨16896808558663007891240861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11264539039108671927493907 16896808558663007891240861)
  ·
    refine ⟨6336303209498627959215323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16896808558663007891240861 6336303209498627959215323)
    ·
      refine ⟨9504454814247941938822985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6336303209498627959215323 9504454814247941938822985)
      ·
        refine ⟨7128341110685956454117239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9504454814247941938822985 7128341110685956454117239)
        ·
          refine ⟨10692511666028934681175859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7128341110685956454117239 10692511666028934681175859)
          ·
            refine ⟨16038767499043402021763789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10692511666028934681175859 16038767499043402021763789)
            ·
              refine ⟨6014537812141275758161421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16038767499043402021763789 6014537812141275758161421)
              ·
                refine ⟨2255451679552978409310533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6014537812141275758161421 2255451679552978409310533)
                ·
                  refine ⟨422897189916183451745725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2255451679552978409310533 422897189916183451745725)
                  ·
                    refine ⟨158586446218568794404647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 422897189916183451745725 158586446218568794404647)
                    ·
                      rfl

theorem cell22_463269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_463269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463269 prefixEnd_463269 := by exact prefixLift 463269
  have htrace : WordTrace (prefixWord ++ tailWord_463269) baseStart_463269 baseEnd_463269 := by
    simpa [prefixWord, tailWord_463269, baseEnd_463269] using wordTrace_append hprefix tailTrace_463269
  have hstable : (prefixWord ++ tailWord_463269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463269).length < 2 ^ (prefixWord ++ tailWord_463269).sum := by decide
  have hdescent : baseEnd_463269 < baseStart_463269 := by decide
  rcases family_descends (prefixWord ++ tailWord_463269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463271 : List Nat := [1, 1, 6, 1, 1, 4, 1, 1, 6]
def baseStart_463271 : Nat := 118140960795 + 463271 * 2 ^ 59
def prefixEnd_463271 : Nat := 4983230072969 + 3 ^ 40 * 463271 * 2
def baseEnd_463271 : Nat := 52862376953147151951547

theorem tailTrace_463271 : CollatzResearch.WordTrace tailWord_463271 prefixEnd_463271 52862376953147151951547 := by
  unfold tailWord_463271
  simp only [CollatzResearch.WordTrace]
  refine ⟨16896881504655762232813667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11264587669770508155209111 16896881504655762232813667)
  ·
    refine ⟨25345322256983643349220501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16896881504655762232813667 25345322256983643349220501)
    ·
      refine ⟨1188061980796108281994711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25345322256983643349220501 1188061980796108281994711)
      ·
        refine ⟨1782092971194162422992067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188061980796108281994711 1782092971194162422992067)
        ·
          refine ⟨2673139456791243634488101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1782092971194162422992067 2673139456791243634488101)
          ·
            refine ⟨501213648148358181466519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2673139456791243634488101 501213648148358181466519)
            ·
              refine ⟨751820472222537272199779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501213648148358181466519 751820472222537272199779)
              ·
                refine ⟨1127730708333805908299669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751820472222537272199779 1127730708333805908299669)
                ·
                  refine ⟨52862376953147151951547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1127730708333805908299669 52862376953147151951547)
                  ·
                    rfl

theorem cell22_463271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 6].length) (baseStart_463271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463271 prefixEnd_463271 := by exact prefixLift 463271
  have htrace : WordTrace (prefixWord ++ tailWord_463271) baseStart_463271 baseEnd_463271 := by
    simpa [prefixWord, tailWord_463271, baseEnd_463271] using wordTrace_append hprefix tailTrace_463271
  have hstable : (prefixWord ++ tailWord_463271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463271).length < 2 ^ (prefixWord ++ tailWord_463271).sum := by decide
  have hdescent : baseEnd_463271 < baseStart_463271 := by decide
  rcases family_descends (prefixWord ++ tailWord_463271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463312 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 3, 8]
def baseStart_463312 : Nat := 118140960795 + 463312 * 2 ^ 59
def prefixEnd_463312 : Nat := 4983230072969 + 3 ^ 40 * 463312 * 2
def baseEnd_463312 : Nat := 158601165997331015579515

theorem tailTrace_463312 : CollatzResearch.WordTrace tailWord_463312 prefixEnd_463312 158601165997331015579515 := by
  unfold tailWord_463312
  simp only [CollatzResearch.WordTrace]
  refine ⟨8449188448753613117528095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11265584598338150823370793 8449188448753613117528095)
  ·
    refine ⟨12673782673130419676292143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8449188448753613117528095 12673782673130419676292143)
    ·
      refine ⟨19010674009695629514438215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12673782673130419676292143 19010674009695629514438215)
      ·
        refine ⟨28516011014543444271657323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19010674009695629514438215 28516011014543444271657323)
        ·
          refine ⟨42774016521815166407485985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28516011014543444271657323 42774016521815166407485985)
          ·
            refine ⟨32080512391361374805614489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42774016521815166407485985 32080512391361374805614489)
            ·
              refine ⟨24060384293521031104210867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32080512391361374805614489 24060384293521031104210867)
              ·
                refine ⟨36090576440281546656316301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24060384293521031104210867 36090576440281546656316301)
                ·
                  refine ⟨13533966165105579996118613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36090576440281546656316301 13533966165105579996118613)
                  ·
                    refine ⟨158601165997331015579515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13533966165105579996118613 158601165997331015579515)
                    ·
                      rfl

theorem cell22_463312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_463312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463312 prefixEnd_463312 := by exact prefixLift 463312
  have htrace : WordTrace (prefixWord ++ tailWord_463312) baseStart_463312 baseEnd_463312 := by
    simpa [prefixWord, tailWord_463312, baseEnd_463312] using wordTrace_append hprefix tailTrace_463312
  have hstable : (prefixWord ++ tailWord_463312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463312).length < 2 ^ (prefixWord ++ tailWord_463312).sum := by decide
  have hdescent : baseEnd_463312 < baseStart_463312 := by decide
  rcases family_descends (prefixWord ++ tailWord_463312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463333 : List Nat := [1, 3, 1, 5, 3, 1, 1, 7]
def baseStart_463333 : Nat := 118140960795 + 463333 * 2 ^ 59
def prefixEnd_463333 : Nat := 4983230072969 + 3 ^ 40 * 463333 * 2
def baseEnd_463333 : Nat := 17623150525165995644939

theorem tailTrace_463333 : CollatzResearch.WordTrace tailWord_463333 prefixEnd_463333 17623150525165995644939 := by
  unfold tailWord_463333
  simp only [CollatzResearch.WordTrace]
  refine ⟨16899142830431146821570653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11266095220287431214380435 16899142830431146821570653)
  ·
    refine ⟨6337178561411680058088995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16899142830431146821570653 6337178561411680058088995)
    ·
      refine ⟨9505767842117520087133493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6337178561411680058088995 9505767842117520087133493)
      ·
        refine ⟨891165735198517508168765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9505767842117520087133493 891165735198517508168765)
        ·
          refine ⟨334187150699444065563287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 891165735198517508168765 334187150699444065563287)
          ·
            refine ⟨501280726049166098344931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334187150699444065563287 501280726049166098344931)
            ·
              refine ⟨751921089073749147517397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501280726049166098344931 751921089073749147517397)
              ·
                refine ⟨17623150525165995644939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 751921089073749147517397 17623150525165995644939)
                ·
                  rfl

theorem cell22_463333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 7].length) (baseStart_463333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463333 prefixEnd_463333 := by exact prefixLift 463333
  have htrace : WordTrace (prefixWord ++ tailWord_463333) baseStart_463333 baseEnd_463333 := by
    simpa [prefixWord, tailWord_463333, baseEnd_463333] using wordTrace_append hprefix tailTrace_463333
  have hstable : (prefixWord ++ tailWord_463333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463333).length < 2 ^ (prefixWord ++ tailWord_463333).sum := by decide
  have hdescent : baseEnd_463333 < baseStart_463333 := by decide
  rcases family_descends (prefixWord ++ tailWord_463333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463344 : List Nat := [2, 1, 1, 1, 3, 3, 1, 5, 5]
def baseStart_463344 : Nat := 118140960795 + 463344 * 2 ^ 59
def prefixEnd_463344 : Nat := 4983230072969 + 3 ^ 40 * 463344 * 2
def baseEnd_463344 : Nat := 52870706750431199593139

theorem tailTrace_463344 : CollatzResearch.WordTrace tailWord_463344 prefixEnd_463344 52870706750431199593139 := by
  unfold tailWord_463344
  simp only [CollatzResearch.WordTrace]
  refine ⟨8449772016695647850110543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11266362688927530466814057 8449772016695647850110543)
  ·
    refine ⟨12674658025043471775165815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8449772016695647850110543 12674658025043471775165815)
    ·
      refine ⟨19011987037565207662748723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12674658025043471775165815 19011987037565207662748723)
      ·
        refine ⟨28517980556347811494123085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19011987037565207662748723 28517980556347811494123085)
        ·
          refine ⟨10694242708630429310296157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28517980556347811494123085 10694242708630429310296157)
          ·
            refine ⟨4010341015736410991361059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10694242708630429310296157 4010341015736410991361059)
            ·
              refine ⟨6015511523604616487041589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010341015736410991361059 6015511523604616487041589)
              ·
                refine ⟨563954205337932795660149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6015511523604616487041589 563954205337932795660149)
                ·
                  refine ⟨52870706750431199593139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 563954205337932795660149 52870706750431199593139)
                  ·
                    rfl

theorem cell22_463344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 5].length) (baseStart_463344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463344 prefixEnd_463344 := by exact prefixLift 463344
  have htrace : WordTrace (prefixWord ++ tailWord_463344) baseStart_463344 baseEnd_463344 := by
    simpa [prefixWord, tailWord_463344, baseEnd_463344] using wordTrace_append hprefix tailTrace_463344
  have hstable : (prefixWord ++ tailWord_463344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463344).length < 2 ^ (prefixWord ++ tailWord_463344).sum := by decide
  have hdescent : baseEnd_463344 < baseStart_463344 := by decide
  rcases family_descends (prefixWord ++ tailWord_463344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463434 : List Nat := [3, 1, 2, 1, 1, 4, 10]
def baseStart_463434 : Nat := 118140960795 + 463434 * 2 ^ 59
def prefixEnd_463434 : Nat := 4983230072969 + 3 ^ 40 * 463434 * 2
def baseEnd_463434 : Nat := 5875664040391235704783

theorem tailTrace_463434 : CollatzResearch.WordTrace tailWord_463434 prefixEnd_463434 5875664040391235704783 := by
  unfold tailWord_463434
  simp only [CollatzResearch.WordTrace]
  refine ⟨4225706650766310267749339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11268551068710160713998237 4225706650766310267749339)
  ·
    refine ⟨6338559976149465401624009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4225706650766310267749339 6338559976149465401624009)
    ·
      refine ⟨4753919982112099051218007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6338559976149465401624009 4753919982112099051218007)
      ·
        refine ⟨7130879973168148576827011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4753919982112099051218007 7130879973168148576827011)
        ·
          refine ⟨10696319959752222865240517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7130879973168148576827011 10696319959752222865240517)
          ·
            refine ⟨2005559992453541787232597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10696319959752222865240517 2005559992453541787232597)
            ·
              refine ⟨5875664040391235704783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2005559992453541787232597 5875664040391235704783)
              ·
                rfl

theorem cell22_463434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 10].length) (baseStart_463434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463434 prefixEnd_463434 := by exact prefixLift 463434
  have htrace : WordTrace (prefixWord ++ tailWord_463434) baseStart_463434 baseEnd_463434 := by
    simpa [prefixWord, tailWord_463434, baseEnd_463434] using wordTrace_append hprefix tailTrace_463434
  have hstable : (prefixWord ++ tailWord_463434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463434).length < 2 ^ (prefixWord ++ tailWord_463434).sum := by decide
  have hdescent : baseEnd_463434 < baseStart_463434 := by decide
  rcases family_descends (prefixWord ++ tailWord_463434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463436 : List Nat := [2, 2, 1, 3, 1, 2, 3, 2, 2, 4]
def baseStart_463436 : Nat := 118140960795 + 463436 * 2 ^ 59
def prefixEnd_463436 : Nat := 4983230072969 + 3 ^ 40 * 463436 * 2
def baseEnd_463436 : Nat := 158643613731436025479135

theorem tailTrace_463436 : CollatzResearch.WordTrace tailWord_463436 prefixEnd_463436 158643613731436025479135 := by
  unfold tailWord_463436
  simp only [CollatzResearch.WordTrace]
  refine ⟨8451449774528997706285081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11268599699371996941713441 8451449774528997706285081)
  ·
    refine ⟨6338587330896748279713811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8451449774528997706285081 6338587330896748279713811)
    ·
      refine ⟨9507880996345122419570717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6338587330896748279713811 9507880996345122419570717)
      ·
        refine ⟨3565455373629420907339019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9507880996345122419570717 3565455373629420907339019)
        ·
          refine ⟨5348183060444131361008529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3565455373629420907339019 5348183060444131361008529)
          ·
            refine ⟨4011137295333098520756397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5348183060444131361008529 4011137295333098520756397)
            ·
              refine ⟨1504176485749911945283649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4011137295333098520756397 1504176485749911945283649)
              ·
                refine ⟨1128132364312433958962737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504176485749911945283649 1128132364312433958962737)
                ·
                  refine ⟨846099273234325469222053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1128132364312433958962737 846099273234325469222053)
                  ·
                    refine ⟨158643613731436025479135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 846099273234325469222053 158643613731436025479135)
                    ·
                      rfl

theorem cell22_463436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_463436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463436 prefixEnd_463436 := by exact prefixLift 463436
  have htrace : WordTrace (prefixWord ++ tailWord_463436) baseStart_463436 baseEnd_463436 := by
    simpa [prefixWord, tailWord_463436, baseEnd_463436] using wordTrace_append hprefix tailTrace_463436
  have hstable : (prefixWord ++ tailWord_463436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463436).length < 2 ^ (prefixWord ++ tailWord_463436).sum := by decide
  have hdescent : baseEnd_463436 < baseStart_463436 := by decide
  rcases family_descends (prefixWord ++ tailWord_463436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463479 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 9]
def baseStart_463479 : Nat := 118140960795 + 463479 * 2 ^ 59
def prefixEnd_463479 : Nat := 4983230072969 + 3 ^ 40 * 463479 * 2
def baseEnd_463479 : Nat := 52886111170066082218001

theorem tailTrace_463479 : CollatzResearch.WordTrace tailWord_463479 prefixEnd_463479 52886111170066082218001 := by
  unfold tailWord_463479
  simp only [CollatzResearch.WordTrace]
  refine ⟨16904467887902213756385491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11269645258601475837590327 16904467887902213756385491)
  ·
    refine ⟨25356701831853320634578237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16904467887902213756385491 25356701831853320634578237)
    ·
      refine ⟨9508763186944995237966839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25356701831853320634578237 9508763186944995237966839)
      ·
        refine ⟨14263144780417492856950259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9508763186944995237966839 14263144780417492856950259)
        ·
          refine ⟨21394717170626239285425389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14263144780417492856950259 21394717170626239285425389)
          ·
            refine ⟨8023018938984839732034521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21394717170626239285425389 8023018938984839732034521)
            ·
              refine ⟨6017264204238629799025891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8023018938984839732034521 6017264204238629799025891)
              ·
                refine ⟨9025896306357944698538837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6017264204238629799025891 9025896306357944698538837)
                ·
                  refine ⟨52886111170066082218001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9025896306357944698538837 52886111170066082218001)
                  ·
                    rfl

theorem cell22_463479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 9].length) (baseStart_463479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463479 prefixEnd_463479 := by exact prefixLift 463479
  have htrace : WordTrace (prefixWord ++ tailWord_463479) baseStart_463479 baseEnd_463479 := by
    simpa [prefixWord, tailWord_463479, baseEnd_463479] using wordTrace_append hprefix tailTrace_463479
  have hstable : (prefixWord ++ tailWord_463479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463479).length < 2 ^ (prefixWord ++ tailWord_463479).sum := by decide
  have hdescent : baseEnd_463479 < baseStart_463479 := by decide
  rcases family_descends (prefixWord ++ tailWord_463479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463511 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 2, 5]
def baseStart_463511 : Nat := 118140960795 + 463511 * 2 ^ 59
def prefixEnd_463511 : Nat := 4983230072969 + 3 ^ 40 * 463511 * 2
def baseEnd_463511 : Nat := 158669287764160829853905

theorem tailTrace_463511 : CollatzResearch.WordTrace tailWord_463511 prefixEnd_463511 158669287764160829853905 := by
  unfold tailWord_463511
  simp only [CollatzResearch.WordTrace]
  refine ⟨16905635023786283221550387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11270423349190855481033591 16905635023786283221550387)
  ·
    refine ⟨25358452535679424832325581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16905635023786283221550387 25358452535679424832325581)
    ·
      refine ⟨9509419700879784312122093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25358452535679424832325581 9509419700879784312122093)
      ·
        refine ⟨3566032387829919117045785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9509419700879784312122093 3566032387829919117045785)
        ·
          refine ⟨2674524290872439337784339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3566032387829919117045785 2674524290872439337784339)
          ·
            refine ⟨4011786436308659006676509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674524290872439337784339 4011786436308659006676509)
            ·
              refine ⟨1504419913615747127503691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4011786436308659006676509 1504419913615747127503691)
              ·
                refine ⟨2256629870423620691255537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1504419913615747127503691 2256629870423620691255537)
                ·
                  refine ⟨1692472402817715518441653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2256629870423620691255537 1692472402817715518441653)
                  ·
                    refine ⟨158669287764160829853905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1692472402817715518441653 158669287764160829853905)
                    ·
                      rfl

theorem cell22_463511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_463511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463511 prefixEnd_463511 := by exact prefixLift 463511
  have htrace : WordTrace (prefixWord ++ tailWord_463511) baseStart_463511 baseEnd_463511 := by
    simpa [prefixWord, tailWord_463511, baseEnd_463511] using wordTrace_append hprefix tailTrace_463511
  have hstable : (prefixWord ++ tailWord_463511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463511).length < 2 ^ (prefixWord ++ tailWord_463511).sum := by decide
  have hdescent : baseEnd_463511 < baseStart_463511 := by decide
  rcases family_descends (prefixWord ++ tailWord_463511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463534 : List Nat := [4, 1, 4, 1, 1, 2, 2, 3, 1, 3]
def baseStart_463534 : Nat := 118140960795 + 463534 * 2 ^ 59
def prefixEnd_463534 : Nat := 4983230072969 + 3 ^ 40 * 463534 * 2
def baseEnd_463534 : Nat := 158677161134196436528835

theorem tailTrace_463534 : CollatzResearch.WordTrace tailWord_463534 prefixEnd_463534 158677161134196436528835 := by
  unfold tailWord_463534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2113309237837869768704707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11270982601801972099758437 2113309237837869768704707)
  ·
    refine ⟨3169963856756804653057061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2113309237837869768704707 3169963856756804653057061)
    ·
      refine ⟨594368223141900872448199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3169963856756804653057061 594368223141900872448199)
      ·
        refine ⟨891552334712851308672299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594368223141900872448199 891552334712851308672299)
        ·
          refine ⟨1337328502069276963008449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891552334712851308672299 1337328502069276963008449)
          ·
            refine ⟨1002996376551957722256337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1337328502069276963008449 1002996376551957722256337)
            ·
              refine ⟨752247282413968291692253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002996376551957722256337 752247282413968291692253)
              ·
                refine ⟨282092730905238109384595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 752247282413968291692253 282092730905238109384595)
                ·
                  refine ⟨423139096357857164076893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282092730905238109384595 423139096357857164076893)
                  ·
                    refine ⟨158677161134196436528835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 423139096357857164076893 158677161134196436528835)
                    ·
                      rfl

theorem cell22_463534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_463534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463534 prefixEnd_463534 := by exact prefixLift 463534
  have htrace : WordTrace (prefixWord ++ tailWord_463534) baseStart_463534 baseEnd_463534 := by
    simpa [prefixWord, tailWord_463534, baseEnd_463534] using wordTrace_append hprefix tailTrace_463534
  have hstable : (prefixWord ++ tailWord_463534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463534).length < 2 ^ (prefixWord ++ tailWord_463534).sum := by decide
  have hdescent : baseEnd_463534 < baseStart_463534 := by decide
  rcases family_descends (prefixWord ++ tailWord_463534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463592 : List Nat := [2, 1, 4, 1, 4, 2, 1, 3, 4]
def baseStart_463592 : Nat := 118140960795 + 463592 * 2 ^ 59
def prefixEnd_463592 : Nat := 4983230072969 + 3 ^ 40 * 463592 * 2
def baseEnd_463592 : Nat := 52899005239834539526219

theorem tailTrace_463592 : CollatzResearch.WordTrace tailWord_463592 prefixEnd_463592 52899005239834539526219 := by
  unfold tailWord_463592
  simp only [CollatzResearch.WordTrace]
  refine ⟨8454294668246417027624515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11272392890995222703499353 8454294668246417027624515)
  ·
    refine ⟨12681442002369625541436773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8454294668246417027624515 12681442002369625541436773)
    ·
      refine ⟨2377770375444304789019395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12681442002369625541436773 2377770375444304789019395)
      ·
        refine ⟨3566655563166457183529093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2377770375444304789019395 3566655563166457183529093)
        ·
          refine ⟨668747918093710721911705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3566655563166457183529093 668747918093710721911705)
          ·
            refine ⟨501560938570283041433779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 668747918093710721911705 501560938570283041433779)
            ·
              refine ⟨752341407855424562150669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501560938570283041433779 752341407855424562150669)
              ·
                refine ⟨282128027945784210806501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 752341407855424562150669 282128027945784210806501)
                ·
                  refine ⟨52899005239834539526219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282128027945784210806501 52899005239834539526219)
                  ·
                    rfl

theorem cell22_463592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 4].length) (baseStart_463592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463592 prefixEnd_463592 := by exact prefixLift 463592
  have htrace : WordTrace (prefixWord ++ tailWord_463592) baseStart_463592 baseEnd_463592 := by
    simpa [prefixWord, tailWord_463592, baseEnd_463592] using wordTrace_append hprefix tailTrace_463592
  have hstable : (prefixWord ++ tailWord_463592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463592).length < 2 ^ (prefixWord ++ tailWord_463592).sum := by decide
  have hdescent : baseEnd_463592 < baseStart_463592 := by decide
  rcases family_descends (prefixWord ++ tailWord_463592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463669 : List Nat := [1, 3, 3, 1, 3, 1, 4, 2, 1, 3]
def baseStart_463669 : Nat := 118140960795 + 463669 * 2 ^ 59
def prefixEnd_463669 : Nat := 4983230072969 + 3 ^ 40 * 463669 * 2
def baseEnd_463669 : Nat := 158723374393101084403421

theorem tailTrace_463669 : CollatzResearch.WordTrace tailWord_463669 prefixEnd_463669 158723374393101084403421 := by
  unfold tailWord_463669
  simp only [CollatzResearch.WordTrace]
  refine ⟨16911397757213876205802061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11274265171475917470534707 16911397757213876205802061)
  ·
    refine ⟨6341774158955203577175773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16911397757213876205802061 6341774158955203577175773)
    ·
      refine ⟨2378165309608201341440915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6341774158955203577175773 2378165309608201341440915)
      ·
        refine ⟨3567247964412302012161373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2378165309608201341440915 3567247964412302012161373)
        ·
          refine ⟨1337717986654613254560515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3567247964412302012161373 1337717986654613254560515)
          ·
            refine ⟨2006576979981919881840773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337717986654613254560515 2006576979981919881840773)
            ·
              refine ⟨376233183746609977845145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2006576979981919881840773 376233183746609977845145)
              ·
                refine ⟨282174887809957483383859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376233183746609977845145 282174887809957483383859)
                ·
                  refine ⟨423262331714936225075789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282174887809957483383859 423262331714936225075789)
                  ·
                    refine ⟨158723374393101084403421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 423262331714936225075789 158723374393101084403421)
                    ·
                      rfl

theorem cell22_463669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_463669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463669 prefixEnd_463669 := by exact prefixLift 463669
  have htrace : WordTrace (prefixWord ++ tailWord_463669) baseStart_463669 baseEnd_463669 := by
    simpa [prefixWord, tailWord_463669, baseEnd_463669] using wordTrace_append hprefix tailTrace_463669
  have hstable : (prefixWord ++ tailWord_463669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463669).length < 2 ^ (prefixWord ++ tailWord_463669).sum := by decide
  have hdescent : baseEnd_463669 < baseStart_463669 := by decide
  rcases family_descends (prefixWord ++ tailWord_463669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463723 : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 2, 4]
def baseStart_463723 : Nat := 118140960795 + 463723 * 2 ^ 59
def prefixEnd_463723 : Nat := 4983230072969 + 3 ^ 40 * 463723 * 2
def baseEnd_463723 : Nat := 158741859696662943553255

theorem tailTrace_463723 : CollatzResearch.WordTrace tailWord_463723 prefixEnd_463723 158741859696662943553255 := by
  unfold tailWord_463723
  simp only [CollatzResearch.WordTrace]
  refine ⟨16913367299018243428267823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11275578199345495618845215 16913367299018243428267823)
  ·
    refine ⟨25370050948527365142401735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16913367299018243428267823 25370050948527365142401735)
    ·
      refine ⟨38055076422791047713602603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25370050948527365142401735 38055076422791047713602603)
      ·
        refine ⟨57082614634186571570403905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38055076422791047713602603 57082614634186571570403905)
        ·
          refine ⟨42811960975639928677802929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57082614634186571570403905 42811960975639928677802929)
          ·
            refine ⟨32108970731729946508352197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42811960975639928677802929 32108970731729946508352197)
            ·
              refine ⟨6020432012199364970316037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32108970731729946508352197 6020432012199364970316037)
              ·
                refine ⟨1128831002287380931934257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6020432012199364970316037 1128831002287380931934257)
                ·
                  refine ⟨846623251715535698950693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1128831002287380931934257 846623251715535698950693)
                  ·
                    refine ⟨158741859696662943553255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 846623251715535698950693 158741859696662943553255)
                    ·
                      rfl

theorem cell22_463723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 4].length) (baseStart_463723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463723 prefixEnd_463723 := by exact prefixLift 463723
  have htrace : WordTrace (prefixWord ++ tailWord_463723) baseStart_463723 baseEnd_463723 := by
    simpa [prefixWord, tailWord_463723, baseEnd_463723] using wordTrace_append hprefix tailTrace_463723
  have hstable : (prefixWord ++ tailWord_463723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463723).length < 2 ^ (prefixWord ++ tailWord_463723).sum := by decide
  have hdescent : baseEnd_463723 < baseStart_463723 := by decide
  rcases family_descends (prefixWord ++ tailWord_463723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463746 : List Nat := [3, 4, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_463746 : Nat := 118140960795 + 463746 * 2 ^ 59
def prefixEnd_463746 : Nat := 4983230072969 + 3 ^ 40 * 463746 * 2
def baseEnd_463746 : Nat := 158749733066698550228185

theorem tailTrace_463746 : CollatzResearch.WordTrace tailWord_463746 prefixEnd_463746 158749733066698550228185 := by
  unfold tailWord_463746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4228551544483729589088773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11276137451956612237570061 4228551544483729589088773)
  ·
    refine ⟨792853414590699297954145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4228551544483729589088773 792853414590699297954145)
    ·
      refine ⟨594640060943024473465609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 792853414590699297954145 594640060943024473465609)
      ·
        refine ⟨445980045707268355099207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594640060943024473465609 445980045707268355099207)
        ·
          refine ⟨668970068560902532648811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445980045707268355099207 668970068560902532648811)
          ·
            refine ⟨1003455102841353798973217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668970068560902532648811 1003455102841353798973217)
            ·
              refine ⟨752591327131015349229913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1003455102841353798973217 752591327131015349229913)
              ·
                refine ⟨564443495348261511922435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 752591327131015349229913 564443495348261511922435)
                ·
                  refine ⟨846665243022392267883653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 564443495348261511922435 846665243022392267883653)
                  ·
                    refine ⟨158749733066698550228185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 846665243022392267883653 158749733066698550228185)
                    ·
                      rfl

theorem cell22_463746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_463746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463746 prefixEnd_463746 := by exact prefixLift 463746
  have htrace : WordTrace (prefixWord ++ tailWord_463746) baseStart_463746 baseEnd_463746 := by
    simpa [prefixWord, tailWord_463746, baseEnd_463746] using wordTrace_append hprefix tailTrace_463746
  have hstable : (prefixWord ++ tailWord_463746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463746).length < 2 ^ (prefixWord ++ tailWord_463746).sum := by decide
  have hdescent : baseEnd_463746 < baseStart_463746 := by decide
  rcases family_descends (prefixWord ++ tailWord_463746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463772 : List Nat := [2, 2, 3, 3, 3, 1, 8]
def baseStart_463772 : Nat := 118140960795 + 463772 * 2 ^ 59
def prefixEnd_463772 : Nat := 4983230072969 + 3 ^ 40 * 463772 * 2
def baseEnd_463772 : Nat := 5879949385112709225115

theorem tailTrace_463772 : CollatzResearch.WordTrace tailWord_463772 prefixEnd_463772 5879949385112709225115 := by
  unfold tailWord_463772
  simp only [CollatzResearch.WordTrace]
  refine ⟨8457577237920362398400785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11276769650560483197867713 8457577237920362398400785)
  ·
    refine ⟨6343182928440271798800589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8457577237920362398400785 6343182928440271798800589)
    ·
      refine ⟨2378693598165101924550221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6343182928440271798800589 2378693598165101924550221)
      ·
        refine ⟨892010099311913221706333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2378693598165101924550221 892010099311913221706333)
        ·
          refine ⟨334503787241967458139875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 892010099311913221706333 334503787241967458139875)
          ·
            refine ⟨501755680862951187209813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334503787241967458139875 501755680862951187209813)
            ·
              refine ⟨5879949385112709225115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 501755680862951187209813 5879949385112709225115)
              ·
                rfl

theorem cell22_463772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 8].length) (baseStart_463772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463772 prefixEnd_463772 := by exact prefixLift 463772
  have htrace : WordTrace (prefixWord ++ tailWord_463772) baseStart_463772 baseEnd_463772 := by
    simpa [prefixWord, tailWord_463772, baseEnd_463772] using wordTrace_append hprefix tailTrace_463772
  have hstable : (prefixWord ++ tailWord_463772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463772).length < 2 ^ (prefixWord ++ tailWord_463772).sum := by decide
  have hdescent : baseEnd_463772 < baseStart_463772 := by decide
  rcases family_descends (prefixWord ++ tailWord_463772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463800 : List Nat := [2, 1, 2, 1, 2, 5, 1, 3, 5]
def baseStart_463800 : Nat := 118140960795 + 463800 * 2 ^ 59
def prefixEnd_463800 : Nat := 4983230072969 + 3 ^ 40 * 463800 * 2
def baseEnd_463800 : Nat := 52922739456753469792673

theorem tailTrace_463800 : CollatzResearch.WordTrace tailWord_463800 prefixEnd_463800 52922739456753469792673 := by
  unfold tailWord_463800
  simp only [CollatzResearch.WordTrace]
  refine ⟨8458087859869642789410427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11277450479826190385880569 8458087859869642789410427)
  ·
    refine ⟨12687131789804464184115641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8458087859869642789410427 12687131789804464184115641)
    ·
      refine ⟨9515348842353348138086731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12687131789804464184115641 9515348842353348138086731)
      ·
        refine ⟨14273023263530022207130097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9515348842353348138086731 14273023263530022207130097)
        ·
          refine ⟨10704767447647516655347573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14273023263530022207130097 10704767447647516655347573)
          ·
            refine ⟨1003571948216954686438835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10704767447647516655347573 1003571948216954686438835)
            ·
              refine ⟨1505357922325432029658253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003571948216954686438835 1505357922325432029658253)
              ·
                refine ⟨564509220872037011121845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1505357922325432029658253 564509220872037011121845)
                ·
                  refine ⟨52922739456753469792673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 564509220872037011121845 52922739456753469792673)
                  ·
                    rfl

theorem cell22_463800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 5].length) (baseStart_463800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463800 prefixEnd_463800 := by exact prefixLift 463800
  have htrace : WordTrace (prefixWord ++ tailWord_463800) baseStart_463800 baseEnd_463800 := by
    simpa [prefixWord, tailWord_463800, baseEnd_463800] using wordTrace_append hprefix tailTrace_463800
  have hstable : (prefixWord ++ tailWord_463800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463800).length < 2 ^ (prefixWord ++ tailWord_463800).sum := by decide
  have hdescent : baseEnd_463800 < baseStart_463800 := by decide
  rcases family_descends (prefixWord ++ tailWord_463800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463862 : List Nat := [5, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_463862 : Nat := 118140960795 + 463862 * 2 ^ 59
def prefixEnd_463862 : Nat := 4983230072969 + 3 ^ 40 * 463862 * 2
def baseEnd_463862 : Nat := 52929814079104304775943

theorem tailTrace_463862 : CollatzResearch.WordTrace tailWord_463862 prefixEnd_463862 52929814079104304775943 := by
  unfold tailWord_463862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1057402315344666885473615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11278958030343113445051893 1057402315344666885473615)
  ·
    refine ⟨1586103473017000328210423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1057402315344666885473615 1586103473017000328210423)
    ·
      refine ⟨2379155209525500492315635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1586103473017000328210423 2379155209525500492315635)
      ·
        refine ⟨3568732814288250738473453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2379155209525500492315635 3568732814288250738473453)
        ·
          refine ⟨1338274805358094026927545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3568732814288250738473453 1338274805358094026927545)
          ·
            refine ⟨1003706104018570520195659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1338274805358094026927545 1003706104018570520195659)
            ·
              refine ⟨1505559156027855780293489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003706104018570520195659 1505559156027855780293489)
              ·
                refine ⟨1129169367020891835220117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1505559156027855780293489 1129169367020891835220117)
                ·
                  refine ⟨52929814079104304775943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1129169367020891835220117 52929814079104304775943)
                  ·
                    rfl

theorem cell22_463862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_463862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463862 prefixEnd_463862 := by exact prefixLift 463862
  have htrace : WordTrace (prefixWord ++ tailWord_463862) baseStart_463862 baseEnd_463862 := by
    simpa [prefixWord, tailWord_463862, baseEnd_463862] using wordTrace_append hprefix tailTrace_463862
  have hstable : (prefixWord ++ tailWord_463862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463862).length < 2 ^ (prefixWord ++ tailWord_463862).sum := by decide
  have hdescent : baseEnd_463862 < baseStart_463862 := by decide
  rcases family_descends (prefixWord ++ tailWord_463862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463922 : List Nat := [3, 2, 1, 1, 2, 2, 1, 4, 3, 3]
def baseStart_463922 : Nat := 118140960795 + 463922 * 2 ^ 59
def prefixEnd_463922 : Nat := 4983230072969 + 3 ^ 40 * 463922 * 2
def baseEnd_463922 : Nat := 158809981463492757827645

theorem tailTrace_463922 : CollatzResearch.WordTrace tailWord_463922 prefixEnd_463922 158809981463492757827645 := by
  unfold tailWord_463922
  simp only [CollatzResearch.WordTrace]
  refine ⟨4230156356324325103690505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11280416950198200276508013 4230156356324325103690505)
  ·
    refine ⟨3172617267243243827767879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4230156356324325103690505 3172617267243243827767879)
    ·
      refine ⟨4758925900864865741651819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3172617267243243827767879 4758925900864865741651819)
      ·
        refine ⟨7138388851297298612477729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4758925900864865741651819 7138388851297298612477729)
        ·
          refine ⟨5353791638472973959358297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7138388851297298612477729 5353791638472973959358297)
          ·
            refine ⟨4015343728854730469518723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5353791638472973959358297 4015343728854730469518723)
            ·
              refine ⟨6023015593282095704278085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4015343728854730469518723 6023015593282095704278085)
              ·
                refine ⟨1129315423740392944552141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6023015593282095704278085 1129315423740392944552141)
                ·
                  refine ⟨423493283902647354207053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1129315423740392944552141 423493283902647354207053)
                  ·
                    refine ⟨158809981463492757827645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 423493283902647354207053 158809981463492757827645)
                    ·
                      rfl

theorem cell22_463922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_463922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463922 prefixEnd_463922 := by exact prefixLift 463922
  have htrace : WordTrace (prefixWord ++ tailWord_463922) baseStart_463922 baseEnd_463922 := by
    simpa [prefixWord, tailWord_463922, baseEnd_463922] using wordTrace_append hprefix tailTrace_463922
  have hstable : (prefixWord ++ tailWord_463922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463922).length < 2 ^ (prefixWord ++ tailWord_463922).sum := by decide
  have hdescent : baseEnd_463922 < baseStart_463922 := by decide
  rcases family_descends (prefixWord ++ tailWord_463922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463924 : List Nat := [2, 5, 1, 2, 1, 1, 4, 6]
def baseStart_463924 : Nat := 118140960795 + 463924 * 2 ^ 59
def prefixEnd_463924 : Nat := 4983230072969 + 3 ^ 40 * 463924 * 2
def baseEnd_463924 : Nat := 17645629567151713253071

theorem tailTrace_463924 : CollatzResearch.WordTrace tailWord_463924 prefixEnd_463924 17645629567151713253071 := by
  unfold tailWord_463924
  simp only [CollatzResearch.WordTrace]
  refine ⟨8460349185645027378167413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11280465580860036504223217 8460349185645027378167413)
  ·
    refine ⟨793157736154221316703195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8460349185645027378167413 793157736154221316703195)
    ·
      refine ⟨1189736604231331975054793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 793157736154221316703195 1189736604231331975054793)
      ·
        refine ⟨892302453173498981291095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1189736604231331975054793 892302453173498981291095)
        ·
          refine ⟨1338453679760248471936643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892302453173498981291095 1338453679760248471936643)
          ·
            refine ⟨2007680519640372707904965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338453679760248471936643 2007680519640372707904965)
            ·
              refine ⟨376440097432569882732181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2007680519640372707904965 376440097432569882732181)
              ·
                refine ⟨17645629567151713253071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 376440097432569882732181 17645629567151713253071)
                ·
                  rfl

theorem cell22_463924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 6].length) (baseStart_463924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463924 prefixEnd_463924 := by exact prefixLift 463924
  have htrace : WordTrace (prefixWord ++ tailWord_463924) baseStart_463924 baseEnd_463924 := by
    simpa [prefixWord, tailWord_463924, baseEnd_463924] using wordTrace_append hprefix tailTrace_463924
  have hstable : (prefixWord ++ tailWord_463924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463924).length < 2 ^ (prefixWord ++ tailWord_463924).sum := by decide
  have hdescent : baseEnd_463924 < baseStart_463924 := by decide
  rcases family_descends (prefixWord ++ tailWord_463924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463980 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 8]
def baseStart_463980 : Nat := 118140960795 + 463980 * 2 ^ 59
def prefixEnd_463980 : Nat := 4983230072969 + 3 ^ 40 * 463980 * 2
def baseEnd_463980 : Nat := 52943278682933313292489

theorem tailTrace_463980 : CollatzResearch.WordTrace tailWord_463980 prefixEnd_463980 52943278682933313292489 := by
  unfold tailWord_463980
  simp only [CollatzResearch.WordTrace]
  refine ⟨8461370429543588160186697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11281827239391450880248929 8461370429543588160186697)
  ·
    refine ⟨6346027822157691120140023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8461370429543588160186697 6346027822157691120140023)
    ·
      refine ⟨9519041733236536680210035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6346027822157691120140023 9519041733236536680210035)
      ·
        refine ⟨14278562599854805020315053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9519041733236536680210035 14278562599854805020315053)
        ·
          refine ⟨5354460974945551882618145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14278562599854805020315053 5354460974945551882618145)
          ·
            refine ⟨4015845731209163911963609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5354460974945551882618145 4015845731209163911963609)
            ·
              refine ⟨3011884298406872933972707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4015845731209163911963609 3011884298406872933972707)
              ·
                refine ⟨4517826447610309400959061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3011884298406872933972707 4517826447610309400959061)
                ·
                  refine ⟨52943278682933313292489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4517826447610309400959061 52943278682933313292489)
                  ·
                    rfl

theorem cell22_463980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_463980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_463980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_463980 prefixEnd_463980 := by exact prefixLift 463980
  have htrace : WordTrace (prefixWord ++ tailWord_463980) baseStart_463980 baseEnd_463980 := by
    simpa [prefixWord, tailWord_463980, baseEnd_463980] using wordTrace_append hprefix tailTrace_463980
  have hstable : (prefixWord ++ tailWord_463980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463980).length < 2 ^ (prefixWord ++ tailWord_463980).sum := by decide
  have hdescent : baseEnd_463980 < baseStart_463980 := by decide
  rcases family_descends (prefixWord ++ tailWord_463980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464012 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 4, 3]
def baseStart_464012 : Nat := 118140960795 + 464012 * 2 ^ 59
def prefixEnd_464012 : Nat := 4983230072969 + 3 ^ 40 * 464012 * 2
def baseEnd_464012 : Nat := 158840790302762523077369

theorem tailTrace_464012 : CollatzResearch.WordTrace tailWord_464012 prefixEnd_464012 158840790302762523077369 := by
  unfold tailWord_464012
  simp only [CollatzResearch.WordTrace]
  refine ⟨8461953997485622892769145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11282605329980830523692193 8461953997485622892769145)
  ·
    refine ⟨6346465498114217169576859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8461953997485622892769145 6346465498114217169576859)
    ·
      refine ⟨9519698247171325754365289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6346465498114217169576859 9519698247171325754365289)
      ·
        refine ⟨7139773685378494315773967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9519698247171325754365289 7139773685378494315773967)
        ·
          refine ⟨10709660528067741473660951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7139773685378494315773967 10709660528067741473660951)
          ·
            refine ⟨16064490792101612210491427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10709660528067741473660951 16064490792101612210491427)
            ·
              refine ⟨24096736188152418315737141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16064490792101612210491427 24096736188152418315737141)
              ·
                refine ⟨2259069017639289217100357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24096736188152418315737141 2259069017639289217100357)
                ·
                  refine ⟨423575440807366728206317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2259069017639289217100357 423575440807366728206317)
                  ·
                    refine ⟨158840790302762523077369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 423575440807366728206317 158840790302762523077369)
                    ·
                      rfl

theorem cell22_464012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_464012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464012 prefixEnd_464012 := by exact prefixLift 464012
  have htrace : WordTrace (prefixWord ++ tailWord_464012) baseStart_464012 baseEnd_464012 := by
    simpa [prefixWord, tailWord_464012, baseEnd_464012] using wordTrace_append hprefix tailTrace_464012
  have hstable : (prefixWord ++ tailWord_464012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464012).length < 2 ^ (prefixWord ++ tailWord_464012).sum := by decide
  have hdescent : baseEnd_464012 < baseStart_464012 := by decide
  rcases family_descends (prefixWord ++ tailWord_464012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464029 : List Nat := [1, 4, 2, 1, 1, 2, 1, 5, 2, 3]
def baseStart_464029 : Nat := 118140960795 + 464029 * 2 ^ 59
def prefixEnd_464029 : Nat := 4983230072969 + 3 ^ 40 * 464029 * 2
def baseEnd_464029 : Nat := 158846609750180145402317

theorem tailTrace_464029 : CollatzResearch.WordTrace tailWord_464029 prefixEnd_464029 158846609750180145402317 := by
  unfold tailWord_464029
  simp only [CollatzResearch.WordTrace]
  refine ⟨16924528035909657688907141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11283018690606438459271427 16924528035909657688907141)
  ·
    refine ⟨3173349006733060816670089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16924528035909657688907141 3173349006733060816670089)
    ·
      refine ⟨2380011755049795612502567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3173349006733060816670089 2380011755049795612502567)
      ·
        refine ⟨3570017632574693418753851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2380011755049795612502567 3570017632574693418753851)
        ·
          refine ⟨5355026448862040128130777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3570017632574693418753851 5355026448862040128130777)
          ·
            refine ⟨4016269836646530096098083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5355026448862040128130777 4016269836646530096098083)
            ·
              refine ⟨6024404754969795144147125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4016269836646530096098083 6024404754969795144147125)
              ·
                refine ⟨564787945778418294763793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6024404754969795144147125 564787945778418294763793)
                ·
                  refine ⟨423590959333813721072845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564787945778418294763793 423590959333813721072845)
                  ·
                    refine ⟨158846609750180145402317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 423590959333813721072845 158846609750180145402317)
                    ·
                      rfl

theorem cell22_464029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_464029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464029 prefixEnd_464029 := by exact prefixLift 464029
  have htrace : WordTrace (prefixWord ++ tailWord_464029) baseStart_464029 baseEnd_464029 := by
    simpa [prefixWord, tailWord_464029, baseEnd_464029] using wordTrace_append hprefix tailTrace_464029
  have hstable : (prefixWord ++ tailWord_464029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464029).length < 2 ^ (prefixWord ++ tailWord_464029).sum := by decide
  have hdescent : baseEnd_464029 < baseStart_464029 := by decide
  rcases family_descends (prefixWord ++ tailWord_464029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464074 : List Nat := [3, 1, 2, 1, 3, 2, 1, 3, 3, 3]
def baseStart_464074 : Nat := 118140960795 + 464074 * 2 ^ 59
def prefixEnd_464074 : Nat := 4983230072969 + 3 ^ 40 * 464074 * 2
def baseEnd_464074 : Nat := 158862014169815028027179

theorem tailTrace_464074 : CollatzResearch.WordTrace tailWord_464074 prefixEnd_464074 158862014169815028027179 := by
  unfold tailWord_464074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4231542330186657593573819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11284112880497753582863517 4231542330186657593573819)
  ·
    refine ⟨6347313495279986390360729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4231542330186657593573819 6347313495279986390360729)
    ·
      refine ⟨4760485121459989792770547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6347313495279986390360729 4760485121459989792770547)
      ·
        refine ⟨7140727682189984689155821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4760485121459989792770547 7140727682189984689155821)
        ·
          refine ⟨2677772880821244258433433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7140727682189984689155821 2677772880821244258433433)
          ·
            refine ⟨2008329660615933193825075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2677772880821244258433433 2008329660615933193825075)
            ·
              refine ⟨3012494490923899790737613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008329660615933193825075 3012494490923899790737613)
              ·
                refine ⟨1129685434096462421526605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3012494490923899790737613 1129685434096462421526605)
                ·
                  refine ⟨423632037786173408072477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1129685434096462421526605 423632037786173408072477)
                  ·
                    refine ⟨158862014169815028027179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 423632037786173408072477 158862014169815028027179)
                    ·
                      rfl

theorem cell22_464074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_464074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464074 prefixEnd_464074 := by exact prefixLift 464074
  have htrace : WordTrace (prefixWord ++ tailWord_464074) baseStart_464074 baseEnd_464074 := by
    simpa [prefixWord, tailWord_464074, baseEnd_464074] using wordTrace_append hprefix tailTrace_464074
  have hstable : (prefixWord ++ tailWord_464074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464074).length < 2 ^ (prefixWord ++ tailWord_464074).sum := by decide
  have hdescent : baseEnd_464074 < baseStart_464074 := by decide
  rcases family_descends (prefixWord ++ tailWord_464074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464087 : List Nat := [1, 1, 3, 2, 1, 2, 2, 5, 5]
def baseStart_464087 : Nat := 118140960795 + 464087 * 2 ^ 59
def prefixEnd_464087 : Nat := 4983230072969 + 3 ^ 40 * 464087 * 2
def baseEnd_464087 : Nat := 52955488111829109150713

theorem tailTrace_464087 : CollatzResearch.WordTrace tailWord_464087 prefixEnd_464087 52955488111829109150713 := by
  unfold tailWord_464087
  simp only [CollatzResearch.WordTrace]
  refine ⟨16926643469699533594518515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11284428979799689063012343 16926643469699533594518515)
  ·
    refine ⟨25389965204549300391777773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16926643469699533594518515 25389965204549300391777773)
    ·
      refine ⟨9521236951705987646916665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25389965204549300391777773 9521236951705987646916665)
      ·
        refine ⟨7140927713779490735187499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9521236951705987646916665 7140927713779490735187499)
        ·
          refine ⟨10711391570669236102781249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7140927713779490735187499 10711391570669236102781249)
          ·
            refine ⟨8033543678001927077085937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10711391570669236102781249 8033543678001927077085937)
            ·
              refine ⟨6025157758501445307814453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8033543678001927077085937 6025157758501445307814453)
              ·
                refine ⟨564858539859510497607605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6025157758501445307814453 564858539859510497607605)
                ·
                  refine ⟨52955488111829109150713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 564858539859510497607605 52955488111829109150713)
                  ·
                    rfl

theorem cell22_464087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 5].length) (baseStart_464087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464087 prefixEnd_464087 := by exact prefixLift 464087
  have htrace : WordTrace (prefixWord ++ tailWord_464087) baseStart_464087 baseEnd_464087 := by
    simpa [prefixWord, tailWord_464087, baseEnd_464087] using wordTrace_append hprefix tailTrace_464087
  have hstable : (prefixWord ++ tailWord_464087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464087).length < 2 ^ (prefixWord ++ tailWord_464087).sum := by decide
  have hdescent : baseEnd_464087 < baseStart_464087 := by decide
  rcases family_descends (prefixWord ++ tailWord_464087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464093 : List Nat := [1, 4, 3, 2, 3, 1, 2, 6]
def baseStart_464093 : Nat := 118140960795 + 464093 * 2 ^ 59
def prefixEnd_464093 : Nat := 4983230072969 + 3 ^ 40 * 464093 * 2
def baseEnd_464093 : Nat := 17652057584233923533569

theorem tailTrace_464093 : CollatzResearch.WordTrace tailWord_464093 prefixEnd_464093 17652057584233923533569 := by
  unfold tailWord_464093
  simp only [CollatzResearch.WordTrace]
  refine ⟨16926862307677796619236933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11284574871785197746157955 16926862307677796619236933)
  ·
    refine ⟨3173786682689586866106925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16926862307677796619236933 3173786682689586866106925)
    ·
      refine ⟨1190170006008595074790097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3173786682689586866106925 1190170006008595074790097)
      ·
        refine ⟨892627504506446306092573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1190170006008595074790097 892627504506446306092573)
        ·
          refine ⟨334735314189917364784715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 892627504506446306092573 334735314189917364784715)
          ·
            refine ⟨502102971284876047177073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334735314189917364784715 502102971284876047177073)
            ·
              refine ⟨376577228463657035382805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502102971284876047177073 376577228463657035382805)
              ·
                refine ⟨17652057584233923533569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 376577228463657035382805 17652057584233923533569)
                ·
                  rfl

theorem cell22_464093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 6].length) (baseStart_464093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464093 prefixEnd_464093 := by exact prefixLift 464093
  have htrace : WordTrace (prefixWord ++ tailWord_464093) baseStart_464093 baseEnd_464093 := by
    simpa [prefixWord, tailWord_464093, baseEnd_464093] using wordTrace_append hprefix tailTrace_464093
  have hstable : (prefixWord ++ tailWord_464093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464093).length < 2 ^ (prefixWord ++ tailWord_464093).sum := by decide
  have hdescent : baseEnd_464093 < baseStart_464093 := by decide
  rcases family_descends (prefixWord ++ tailWord_464093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464108 : List Nat := [2, 2, 1, 1, 2, 6, 1, 3, 1, 3]
def baseStart_464108 : Nat := 118140960795 + 464108 * 2 ^ 59
def prefixEnd_464108 : Nat := 4983230072969 + 3 ^ 40 * 464108 * 2
def baseEnd_464108 : Nat := 158873653064650272677075

theorem tailTrace_464108 : CollatzResearch.WordTrace tailWord_464108 prefixEnd_464108 158873653064650272677075 := by
  unfold tailWord_464108
  simp only [CollatzResearch.WordTrace]
  refine ⟨8463704701311727090516489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11284939601748969454021985 8463704701311727090516489)
  ·
    refine ⟨6347778525983795317887367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8463704701311727090516489 6347778525983795317887367)
    ·
      refine ⟨9521667788975692976831051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6347778525983795317887367 9521667788975692976831051)
      ·
        refine ⟨14282501683463539465246577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9521667788975692976831051 14282501683463539465246577)
        ·
          refine ⟨10711876262597654598934933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14282501683463539465246577 10711876262597654598934933)
          ·
            refine ⟨502119199809265059325075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10711876262597654598934933 502119199809265059325075)
            ·
              refine ⟨753178799713897588987613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502119199809265059325075 753178799713897588987613)
              ·
                refine ⟨282442049892711595870355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 753178799713897588987613 282442049892711595870355)
                ·
                  refine ⟨423663074839067393805533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282442049892711595870355 423663074839067393805533)
                  ·
                    refine ⟨158873653064650272677075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 423663074839067393805533 158873653064650272677075)
                    ·
                      rfl

theorem cell22_464108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 1, 3].length) (baseStart_464108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464108 prefixEnd_464108 := by exact prefixLift 464108
  have htrace : WordTrace (prefixWord ++ tailWord_464108) baseStart_464108 baseEnd_464108 := by
    simpa [prefixWord, tailWord_464108, baseEnd_464108] using wordTrace_append hprefix tailTrace_464108
  have hstable : (prefixWord ++ tailWord_464108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464108).length < 2 ^ (prefixWord ++ tailWord_464108).sum := by decide
  have hdescent : baseEnd_464108 < baseStart_464108 := by decide
  rcases family_descends (prefixWord ++ tailWord_464108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464164 : List Nat := [2, 3, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_464164 : Nat := 118140960795 + 464164 * 2 ^ 59
def prefixEnd_464164 : Nat := 4983230072969 + 3 ^ 40 * 464164 * 2
def baseEnd_464164 : Nat := 158892823009084793276903

theorem tailTrace_464164 : CollatzResearch.WordTrace tailWord_464164 prefixEnd_464164 158892823009084793276903 := by
  unfold tailWord_464164
  simp only [CollatzResearch.WordTrace]
  refine ⟨8464725945210287872535773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11286301260280383830047697 8464725945210287872535773)
  ·
    refine ⟨3174272229453857952200915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8464725945210287872535773 3174272229453857952200915)
    ·
      refine ⟨4761408344180786928301373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3174272229453857952200915 4761408344180786928301373)
      ·
        refine ⟨1785528129067795098113015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4761408344180786928301373 1785528129067795098113015)
        ·
          refine ⟨2678292193601692647169523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1785528129067795098113015 2678292193601692647169523)
          ·
            refine ⟨4017438290402538970754285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2678292193601692647169523 4017438290402538970754285)
            ·
              refine ⟨1506539358900952114032857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4017438290402538970754285 1506539358900952114032857)
              ·
                refine ⟨1129904519175714085524643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1506539358900952114032857 1129904519175714085524643)
                ·
                  refine ⟨1694856778763571128286965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1129904519175714085524643 1694856778763571128286965)
                  ·
                    refine ⟨158892823009084793276903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1694856778763571128286965 158892823009084793276903)
                    ·
                      rfl

theorem cell22_464164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_464164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464164 prefixEnd_464164 := by exact prefixLift 464164
  have htrace : WordTrace (prefixWord ++ tailWord_464164) baseStart_464164 baseEnd_464164 := by
    simpa [prefixWord, tailWord_464164, baseEnd_464164] using wordTrace_append hprefix tailTrace_464164
  have hstable : (prefixWord ++ tailWord_464164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464164).length < 2 ^ (prefixWord ++ tailWord_464164).sum := by decide
  have hdescent : baseEnd_464164 < baseStart_464164 := by decide
  rcases family_descends (prefixWord ++ tailWord_464164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464168 : List Nat := [2, 1, 5, 1, 2, 2, 3, 1, 1, 4]
def baseStart_464168 : Nat := 118140960795 + 464168 * 2 ^ 59
def prefixEnd_464168 : Nat := 4983230072969 + 3 ^ 40 * 464168 * 2
def baseEnd_464168 : Nat := 158894192290830116176891

theorem tailTrace_464168 : CollatzResearch.WordTrace tailWord_464168 prefixEnd_464168 158894192290830116176891 := by
  unfold tailWord_464168
  simp only [CollatzResearch.WordTrace]
  refine ⟨8464798891203042214108579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11286398521604056285478105 8464798891203042214108579)
  ·
    refine ⟨12697198336804563321162869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8464798891203042214108579 12697198336804563321162869)
    ·
      refine ⟨1190362344075427811359019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12697198336804563321162869 1190362344075427811359019)
      ·
        refine ⟨1785543516113141717038529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1190362344075427811359019 1785543516113141717038529)
        ·
          refine ⟨1339157637084856287778897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1785543516113141717038529 1339157637084856287778897)
          ·
            refine ⟨1004368227813642215834173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1339157637084856287778897 1004368227813642215834173)
            ·
              refine ⟨376638085430115830937815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1004368227813642215834173 376638085430115830937815)
              ·
                refine ⟨564957128145173746406723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376638085430115830937815 564957128145173746406723)
                ·
                  refine ⟨847435692217760619610085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 564957128145173746406723 847435692217760619610085)
                  ·
                    refine ⟨158894192290830116176891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 847435692217760619610085 158894192290830116176891)
                    ·
                      rfl

theorem cell22_464168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_464168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464168 prefixEnd_464168 := by exact prefixLift 464168
  have htrace : WordTrace (prefixWord ++ tailWord_464168) baseStart_464168 baseEnd_464168 := by
    simpa [prefixWord, tailWord_464168, baseEnd_464168] using wordTrace_append hprefix tailTrace_464168
  have hstable : (prefixWord ++ tailWord_464168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464168).length < 2 ^ (prefixWord ++ tailWord_464168).sum := by decide
  have hdescent : baseEnd_464168 < baseStart_464168 := by decide
  rcases family_descends (prefixWord ++ tailWord_464168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464177 : List Nat := [1, 2, 2, 3, 3, 11]
def baseStart_464177 : Nat := 118140960795 + 464177 * 2 ^ 59
def prefixEnd_464177 : Nat := 4983230072969 + 3 ^ 40 * 464177 * 2
def baseEnd_464177 : Nat := 1961694730552556700023

theorem tailTrace_464177 : CollatzResearch.WordTrace tailWord_464177 prefixEnd_464177 1961694730552556700023 := by
  unfold tailWord_464177
  simp only [CollatzResearch.WordTrace]
  refine ⟨16929926039373478965294785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11286617359582319310196523 16929926039373478965294785)
  ·
    refine ⟨12697444529530109223971089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16929926039373478965294785 12697444529530109223971089)
    ·
      refine ⟨9523083397147581917978317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12697444529530109223971089 9523083397147581917978317)
      ·
        refine ⟨3571156273930343219241869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9523083397147581917978317 3571156273930343219241869)
        ·
          refine ⟨1339183602723878707215701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3571156273930343219241869 1339183602723878707215701)
          ·
            refine ⟨1961694730552556700023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1339183602723878707215701 1961694730552556700023)
            ·
              rfl

theorem cell22_464177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 11].length) (baseStart_464177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464177 prefixEnd_464177 := by exact prefixLift 464177
  have htrace : WordTrace (prefixWord ++ tailWord_464177) baseStart_464177 baseEnd_464177 := by
    simpa [prefixWord, tailWord_464177, baseEnd_464177] using wordTrace_append hprefix tailTrace_464177
  have hstable : (prefixWord ++ tailWord_464177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464177).length < 2 ^ (prefixWord ++ tailWord_464177).sum := by decide
  have hdescent : baseEnd_464177 < baseStart_464177 := by decide
  rcases family_descends (prefixWord ++ tailWord_464177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464179 : List Nat := [1, 1, 1, 2, 5, 2, 2, 2, 2, 4]
def baseStart_464179 : Nat := 118140960795 + 464179 * 2 ^ 59
def prefixEnd_464179 : Nat := 4983230072969 + 3 ^ 40 * 464179 * 2
def baseEnd_464179 : Nat := 158897957815629754151857

theorem tailTrace_464179 : CollatzResearch.WordTrace tailWord_464179 prefixEnd_464179 158897957815629754151857 := by
  unfold tailWord_464179
  simp only [CollatzResearch.WordTrace]
  refine ⟨16929998985366233306867591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11286665990244155537911727 16929998985366233306867591)
  ·
    refine ⟨25394998478049349960301387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16929998985366233306867591 25394998478049349960301387)
    ·
      refine ⟨38092497717074024940452081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25394998478049349960301387 38092497717074024940452081)
      ·
        refine ⟨28569373287805518705339061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38092497717074024940452081 28569373287805518705339061)
        ·
          refine ⟨2678378745731767378625537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28569373287805518705339061 2678378745731767378625537)
          ·
            refine ⟨2008784059298825533969153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2678378745731767378625537 2008784059298825533969153)
            ·
              refine ⟨1506588044474119150476865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2008784059298825533969153 1506588044474119150476865)
              ·
                refine ⟨1129941033355589362857649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1506588044474119150476865 1129941033355589362857649)
                ·
                  refine ⟨847455775016692022143237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1129941033355589362857649 847455775016692022143237)
                  ·
                    refine ⟨158897957815629754151857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 847455775016692022143237 158897957815629754151857)
                    ·
                      rfl

theorem cell22_464179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 4].length) (baseStart_464179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464179 prefixEnd_464179 := by exact prefixLift 464179
  have htrace : WordTrace (prefixWord ++ tailWord_464179) baseStart_464179 baseEnd_464179 := by
    simpa [prefixWord, tailWord_464179, baseEnd_464179] using wordTrace_append hprefix tailTrace_464179
  have hstable : (prefixWord ++ tailWord_464179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464179).length < 2 ^ (prefixWord ++ tailWord_464179).sum := by decide
  have hdescent : baseEnd_464179 < baseStart_464179 := by decide
  rcases family_descends (prefixWord ++ tailWord_464179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464181 : List Nat := [1, 3, 3, 1, 2, 2, 1, 4, 2, 3]
def baseStart_464181 : Nat := 118140960795 + 464181 * 2 ^ 59
def prefixEnd_464181 : Nat := 4983230072969 + 3 ^ 40 * 464181 * 2
def baseEnd_464181 : Nat := 158898642456502415601851

theorem tailTrace_464181 : CollatzResearch.WordTrace tailWord_464181 prefixEnd_464181 158898642456502415601851 := by
  unfold tailWord_464181
  simp only [CollatzResearch.WordTrace]
  refine ⟨16930071931358987648440397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11286714620905991765626931 16930071931358987648440397)
  ·
    refine ⟨6348776974259620368165149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16930071931358987648440397 6348776974259620368165149)
    ·
      refine ⟨2380791365347357638061931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6348776974259620368165149 2380791365347357638061931)
      ·
        refine ⟨3571187048021036457092897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2380791365347357638061931 3571187048021036457092897)
        ·
          refine ⟨2678390286015777342819673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3571187048021036457092897 2678390286015777342819673)
          ·
            refine ⟨2008792714511833007114755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2678390286015777342819673 2008792714511833007114755)
            ·
              refine ⟨3013189071767749510672133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008792714511833007114755 3013189071767749510672133)
              ·
                refine ⟨564972950956453033251025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3013189071767749510672133 564972950956453033251025)
                ·
                  refine ⟨423729713217339774938269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564972950956453033251025 423729713217339774938269)
                  ·
                    refine ⟨158898642456502415601851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 423729713217339774938269 158898642456502415601851)
                    ·
                      rfl

theorem cell22_464181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_464181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464181 prefixEnd_464181 := by exact prefixLift 464181
  have htrace : WordTrace (prefixWord ++ tailWord_464181) baseStart_464181 baseEnd_464181 := by
    simpa [prefixWord, tailWord_464181, baseEnd_464181] using wordTrace_append hprefix tailTrace_464181
  have hstable : (prefixWord ++ tailWord_464181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464181).length < 2 ^ (prefixWord ++ tailWord_464181).sum := by decide
  have hdescent : baseEnd_464181 < baseStart_464181 := by decide
  rcases family_descends (prefixWord ++ tailWord_464181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464226 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_464226 : Nat := 118140960795 + 464226 * 2 ^ 59
def prefixEnd_464226 : Nat := 4983230072969 + 3 ^ 40 * 464226 * 2
def baseEnd_464226 : Nat := 158914046876137298226713

theorem tailTrace_464226 : CollatzResearch.WordTrace tailWord_464226 prefixEnd_464226 158914046876137298226713 := by
  unfold tailWord_464226
  simp only [CollatzResearch.WordTrace]
  refine ⟨4232928304048990083457133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11287808810797306889219021 4232928304048990083457133)
  ·
    refine ⟨1587348114018371281296425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4232928304048990083457133 1587348114018371281296425)
    ·
      refine ⟨1190511085513778460972319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1587348114018371281296425 1190511085513778460972319)
      ·
        refine ⟨1785766628270667691458479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1190511085513778460972319 1785766628270667691458479)
        ·
          refine ⟨2678649942406001537187719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1785766628270667691458479 2678649942406001537187719)
          ·
            refine ⟨4017974913609002305781579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2678649942406001537187719 4017974913609002305781579)
            ·
              refine ⟨6026962370413503458672369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4017974913609002305781579 6026962370413503458672369)
              ·
                refine ⟨4520221777810127594004277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6026962370413503458672369 4520221777810127594004277)
                ·
                  refine ⟨423770791669699461937901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4520221777810127594004277 423770791669699461937901)
                  ·
                    refine ⟨158914046876137298226713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 423770791669699461937901 158914046876137298226713)
                    ·
                      rfl

theorem cell22_464226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_464226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464226 prefixEnd_464226 := by exact prefixLift 464226
  have htrace : WordTrace (prefixWord ++ tailWord_464226) baseStart_464226 baseEnd_464226 := by
    simpa [prefixWord, tailWord_464226, baseEnd_464226] using wordTrace_append hprefix tailTrace_464226
  have hstable : (prefixWord ++ tailWord_464226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464226).length < 2 ^ (prefixWord ++ tailWord_464226).sum := by decide
  have hdescent : baseEnd_464226 < baseStart_464226 := by decide
  rcases family_descends (prefixWord ++ tailWord_464226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464382 : List Nat := [4, 2, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_464382 : Nat := 118140960795 + 464382 * 2 ^ 59
def prefixEnd_464382 : Nat := 4983230072969 + 3 ^ 40 * 464382 * 2
def baseEnd_464382 : Nat := 158967448864204891326235

theorem tailTrace_464382 : CollatzResearch.WordTrace tailWord_464382 prefixEnd_464382 158967448864204891326235 := by
  unfold tailWord_464382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2117175375453849872063425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11291602002420532651004933 2117175375453849872063425)
  ·
    refine ⟨1587881531590387404047569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2117175375453849872063425 1587881531590387404047569)
    ·
      refine ⟨1190911148692790553035677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1587881531590387404047569 1190911148692790553035677)
      ·
        refine ⟨446591680759796457388379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1190911148692790553035677 446591680759796457388379)
        ·
          refine ⟨669887521139694686082569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446591680759796457388379 669887521139694686082569)
          ·
            refine ⟨502415640854771014561927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 669887521139694686082569 502415640854771014561927)
            ·
              refine ⟨753623461282156521842891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502415640854771014561927 753623461282156521842891)
              ·
                refine ⟨1130435191923234782764337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753623461282156521842891 1130435191923234782764337)
                ·
                  refine ⟨847826393942426087073253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1130435191923234782764337 847826393942426087073253)
                  ·
                    refine ⟨158967448864204891326235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 847826393942426087073253 158967448864204891326235)
                    ·
                      rfl

theorem cell22_464382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_464382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464382 prefixEnd_464382 := by exact prefixLift 464382
  have htrace : WordTrace (prefixWord ++ tailWord_464382) baseStart_464382 baseEnd_464382 := by
    simpa [prefixWord, tailWord_464382, baseEnd_464382] using wordTrace_append hprefix tailTrace_464382
  have hstable : (prefixWord ++ tailWord_464382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464382).length < 2 ^ (prefixWord ++ tailWord_464382).sum := by decide
  have hdescent : baseEnd_464382 < baseStart_464382 := by decide
  rcases family_descends (prefixWord ++ tailWord_464382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464389 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 3, 7]
def baseStart_464389 : Nat := 118140960795 + 464389 * 2 ^ 59
def prefixEnd_464389 : Nat := 4983230072969 + 3 ^ 40 * 464389 * 2
def baseEnd_464389 : Nat := 158969845107259206401213

theorem tailTrace_464389 : CollatzResearch.WordTrace tailWord_464389 prefixEnd_464389 158969845107259206401213 := by
  unfold tailWord_464389
  simp only [CollatzResearch.WordTrace]
  refine ⟨16937658314605439172012221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11291772209736959448008147 16937658314605439172012221)
  ·
    refine ⟨6351621867977039689504583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16937658314605439172012221 6351621867977039689504583)
    ·
      refine ⟨9527432801965559534256875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6351621867977039689504583 9527432801965559534256875)
      ·
        refine ⟨14291149202948339301385313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9527432801965559534256875 14291149202948339301385313)
        ·
          refine ⟨10718361902211254476038985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14291149202948339301385313 10718361902211254476038985)
          ·
            refine ⟨8038771426658440857029239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10718361902211254476038985 8038771426658440857029239)
            ·
              refine ⟨12058157139987661285543859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8038771426658440857029239 12058157139987661285543859)
              ·
                refine ⟨18087235709981491928315789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12058157139987661285543859 18087235709981491928315789)
                ·
                  refine ⟨6782713391243059473118421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18087235709981491928315789 6782713391243059473118421)
                  ·
                    refine ⟨158969845107259206401213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6782713391243059473118421 158969845107259206401213)
                    ·
                      rfl

theorem cell22_464389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_464389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464389 prefixEnd_464389 := by exact prefixLift 464389
  have htrace : WordTrace (prefixWord ++ tailWord_464389) baseStart_464389 baseEnd_464389 := by
    simpa [prefixWord, tailWord_464389, baseEnd_464389] using wordTrace_append hprefix tailTrace_464389
  have hstable : (prefixWord ++ tailWord_464389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464389).length < 2 ^ (prefixWord ++ tailWord_464389).sum := by decide
  have hdescent : baseEnd_464389 < baseStart_464389 := by decide
  rcases family_descends (prefixWord ++ tailWord_464389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464468 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_464468 : Nat := 118140960795 + 464468 * 2 ^ 59
def prefixEnd_464468 : Nat := 4983230072969 + 3 ^ 40 * 464468 * 2
def baseEnd_464468 : Nat := 158996888421729333675971

theorem tailTrace_464468 : CollatzResearch.WordTrace tailWord_464468 prefixEnd_464468 158996888421729333675971 := by
  unfold tailWord_464468
  simp only [CollatzResearch.WordTrace]
  refine ⟨8470269840659617832069029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11293693120879490442758705 8470269840659617832069029)
  ·
    refine ⟨1588175595123678343512943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8470269840659617832069029 1588175595123678343512943)
    ·
      refine ⟨2382263392685517515269415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1588175595123678343512943 2382263392685517515269415)
      ·
        refine ⟨3573395089028276272904123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2382263392685517515269415 3573395089028276272904123)
        ·
          refine ⟨5360092633542414409356185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3573395089028276272904123 5360092633542414409356185)
          ·
            refine ⟨4020069475156810807017139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5360092633542414409356185 4020069475156810807017139)
            ·
              refine ⟨6030104212735216210525709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4020069475156810807017139 6030104212735216210525709)
              ·
                refine ⟨2261289079775706078947141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6030104212735216210525709 2261289079775706078947141)
                ·
                  refine ⟨423991702457944889802589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2261289079775706078947141 423991702457944889802589)
                  ·
                    refine ⟨158996888421729333675971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 423991702457944889802589 158996888421729333675971)
                    ·
                      rfl

theorem cell22_464468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_464468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464468 prefixEnd_464468 := by exact prefixLift 464468
  have htrace : WordTrace (prefixWord ++ tailWord_464468) baseStart_464468 baseEnd_464468 := by
    simpa [prefixWord, tailWord_464468, baseEnd_464468] using wordTrace_append hprefix tailTrace_464468
  have hstable : (prefixWord ++ tailWord_464468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464468).length < 2 ^ (prefixWord ++ tailWord_464468).sum := by decide
  have hdescent : baseEnd_464468 < baseStart_464468 := by decide
  rcases family_descends (prefixWord ++ tailWord_464468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464481 : List Nat := [1, 2, 3, 1, 1, 3, 4, 7]
def baseStart_464481 : Nat := 118140960795 + 464481 * 2 ^ 59
def prefixEnd_464481 : Nat := 4983230072969 + 3 ^ 40 * 464481 * 2
def baseEnd_464481 : Nat := 17666815398600181455659

theorem tailTrace_464481 : CollatzResearch.WordTrace tailWord_464481 prefixEnd_464481 17666815398600181455659 := by
  unfold tailWord_464481
  simp only [CollatzResearch.WordTrace]
  refine ⟨16941013830272138884361297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11294009220181425922907531 16941013830272138884361297)
  ·
    refine ⟨12705760372704104163270973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16941013830272138884361297 12705760372704104163270973)
    ·
      refine ⟨4764660139764039061226615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12705760372704104163270973 4764660139764039061226615)
      ·
        refine ⟨7146990209646058591839923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4764660139764039061226615 7146990209646058591839923)
        ·
          refine ⟨10720485314469087887759885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7146990209646058591839923 10720485314469087887759885)
          ·
            refine ⟨4020181992925907957909957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10720485314469087887759885 4020181992925907957909957)
            ·
              refine ⟨753784123673607742108117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4020181992925907957909957 753784123673607742108117)
              ·
                refine ⟨17666815398600181455659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 753784123673607742108117 17666815398600181455659)
                ·
                  rfl

theorem cell22_464481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 7].length) (baseStart_464481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464481 prefixEnd_464481 := by exact prefixLift 464481
  have htrace : WordTrace (prefixWord ++ tailWord_464481) baseStart_464481 baseEnd_464481 := by
    simpa [prefixWord, tailWord_464481, baseEnd_464481] using wordTrace_append hprefix tailTrace_464481
  have hstable : (prefixWord ++ tailWord_464481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464481).length < 2 ^ (prefixWord ++ tailWord_464481).sum := by decide
  have hdescent : baseEnd_464481 < baseStart_464481 := by decide
  rcases family_descends (prefixWord ++ tailWord_464481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464485 : List Nat := [1, 3, 1, 3, 3, 2, 1, 3, 2, 3]
def baseStart_464485 : Nat := 118140960795 + 464485 * 2 ^ 59
def prefixEnd_464485 : Nat := 4983230072969 + 3 ^ 40 * 464485 * 2
def baseEnd_464485 : Nat := 159002707869146956000919

theorem tailTrace_464485 : CollatzResearch.WordTrace tailWord_464485 prefixEnd_464485 159002707869146956000919 := by
  unfold tailWord_464485
  simp only [CollatzResearch.WordTrace]
  refine ⟨16941159722257647567506909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11294106481505098378337939 16941159722257647567506909)
  ·
    refine ⟨6352934895846617837815091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16941159722257647567506909 6352934895846617837815091)
    ·
      refine ⟨9529402343769926756722637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6352934895846617837815091 9529402343769926756722637)
      ·
        refine ⟨3573525878913722533770989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9529402343769926756722637 3573525878913722533770989)
        ·
          refine ⟨1340072204592645950164121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3573525878913722533770989 1340072204592645950164121)
          ·
            refine ⟨1005054153444484462623091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1340072204592645950164121 1005054153444484462623091)
            ·
              refine ⟨1507581230166726693934637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005054153444484462623091 1507581230166726693934637)
              ·
                refine ⟨565342961312522510225489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1507581230166726693934637 565342961312522510225489)
                ·
                  refine ⟨424007220984391882669117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565342961312522510225489 424007220984391882669117)
                  ·
                    refine ⟨159002707869146956000919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 424007220984391882669117 159002707869146956000919)
                    ·
                      rfl

theorem cell22_464485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_464485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464485 prefixEnd_464485 := by exact prefixLift 464485
  have htrace : WordTrace (prefixWord ++ tailWord_464485) baseStart_464485 baseEnd_464485 := by
    simpa [prefixWord, tailWord_464485, baseEnd_464485] using wordTrace_append hprefix tailTrace_464485
  have hstable : (prefixWord ++ tailWord_464485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464485).length < 2 ^ (prefixWord ++ tailWord_464485).sum := by decide
  have hdescent : baseEnd_464485 < baseStart_464485 := by decide
  rcases family_descends (prefixWord ++ tailWord_464485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464532 : List Nat := [2, 4, 2, 2, 3, 1, 1, 7]
def baseStart_464532 : Nat := 118140960795 + 464532 * 2 ^ 59
def prefixEnd_464532 : Nat := 4983230072969 + 3 ^ 40 * 464532 * 2
def baseEnd_464532 : Nat := 17668755214406055563975

theorem tailTrace_464532 : CollatzResearch.WordTrace tailWord_464532 prefixEnd_464532 17668755214406055563975 := by
  unfold tailWord_464532
  simp only [CollatzResearch.WordTrace]
  refine ⟨8471436976543687297233925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11295249302058249729645233 8471436976543687297233925)
  ·
    refine ⟨1588394433101941368231361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8471436976543687297233925 1588394433101941368231361)
    ·
      refine ⟨1191295824826456026173521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1588394433101941368231361 1191295824826456026173521)
      ·
        refine ⟨893471868619842019630141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1191295824826456026173521 893471868619842019630141)
        ·
          refine ⟨335051950732440757361303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 893471868619842019630141 335051950732440757361303)
          ·
            refine ⟨502577926098661136041955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335051950732440757361303 502577926098661136041955)
            ·
              refine ⟨753866889147991704062933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502577926098661136041955 753866889147991704062933)
              ·
                refine ⟨17668755214406055563975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 753866889147991704062933 17668755214406055563975)
                ·
                  rfl

theorem cell22_464532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 7].length) (baseStart_464532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464532 prefixEnd_464532 := by exact prefixLift 464532
  have htrace : WordTrace (prefixWord ++ tailWord_464532) baseStart_464532 baseEnd_464532 := by
    simpa [prefixWord, tailWord_464532, baseEnd_464532] using wordTrace_append hprefix tailTrace_464532
  have hstable : (prefixWord ++ tailWord_464532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464532).length < 2 ^ (prefixWord ++ tailWord_464532).sum := by decide
  have hdescent : baseEnd_464532 < baseStart_464532 := by decide
  rcases family_descends (prefixWord ++ tailWord_464532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464618 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 1, 6]
def baseStart_464618 : Nat := 118140960795 + 464618 * 2 ^ 59
def prefixEnd_464618 : Nat := 4983230072969 + 3 ^ 40 * 464618 * 2
def baseEnd_464618 : Nat := 159048236487178942425511

theorem tailTrace_464618 : CollatzResearch.WordTrace tailWord_464618 prefixEnd_464618 159048236487178942425511 := by
  unfold tailWord_464618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4236502657693952820524627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11297340420517207521399005 4236502657693952820524627)
  ·
    refine ⟨6354753986540929230786941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4236502657693952820524627 6354753986540929230786941)
    ·
      refine ⟨2383032744952848461545103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6354753986540929230786941 2383032744952848461545103)
      ·
        refine ⟨3574549117429272692317655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2383032744952848461545103 3574549117429272692317655)
        ·
          refine ⟨5361823676143909038476483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3574549117429272692317655 5361823676143909038476483)
          ·
            refine ⟨8042735514215863557714725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5361823676143909038476483 8042735514215863557714725)
            ·
              refine ⟨1508012908915474417071511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8042735514215863557714725 1508012908915474417071511)
              ·
                refine ⟨2262019363373211625607267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508012908915474417071511 2262019363373211625607267)
                ·
                  refine ⟨3393029045059817438410901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2262019363373211625607267 3393029045059817438410901)
                  ·
                    refine ⟨159048236487178942425511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3393029045059817438410901 159048236487178942425511)
                    ·
                      rfl

theorem cell22_464618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_464618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464618 prefixEnd_464618 := by exact prefixLift 464618
  have htrace : WordTrace (prefixWord ++ tailWord_464618) baseStart_464618 baseEnd_464618 := by
    simpa [prefixWord, tailWord_464618, baseEnd_464618] using wordTrace_append hprefix tailTrace_464618
  have hstable : (prefixWord ++ tailWord_464618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464618).length < 2 ^ (prefixWord ++ tailWord_464618).sum := by decide
  have hdescent : baseEnd_464618 < baseStart_464618 := by decide
  rcases family_descends (prefixWord ++ tailWord_464618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464725 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 3, 4]
def baseStart_464725 : Nat := 118140960795 + 464725 * 2 ^ 59
def prefixEnd_464725 : Nat := 4983230072969 + 3 ^ 40 * 464725 * 2
def baseEnd_464725 : Nat := 159084864773866330000183

theorem tailTrace_464725 : CollatzResearch.WordTrace tailWord_464725 prefixEnd_464725 159084864773866330000183 := by
  unfold tailWord_464725
  simp only [CollatzResearch.WordTrace]
  refine ⟨16949913241388168556243629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11299942160925445704162419 16949913241388168556243629)
  ·
    refine ⟨6356217465520563208591361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16949913241388168556243629 6356217465520563208591361)
    ·
      refine ⟨4767163099140422406443521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6356217465520563208591361 4767163099140422406443521)
      ·
        refine ⟨3575372324355316804832641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4767163099140422406443521 3575372324355316804832641)
        ·
          refine ⟨2681529243266487603624481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3575372324355316804832641 2681529243266487603624481)
          ·
            refine ⟨2011146932449865702718361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2681529243266487603624481 2011146932449865702718361)
            ·
              refine ⟨1508360199337399277038771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2011146932449865702718361 1508360199337399277038771)
              ·
                refine ⟨2262540299006098915558157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508360199337399277038771 2262540299006098915558157)
                ·
                  refine ⟨848452612127287093334309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2262540299006098915558157 848452612127287093334309)
                  ·
                    refine ⟨159084864773866330000183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 848452612127287093334309 159084864773866330000183)
                    ·
                      rfl

theorem cell22_464725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_464725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464725 prefixEnd_464725 := by exact prefixLift 464725
  have htrace : WordTrace (prefixWord ++ tailWord_464725) baseStart_464725 baseEnd_464725 := by
    simpa [prefixWord, tailWord_464725, baseEnd_464725] using wordTrace_append hprefix tailTrace_464725
  have hstable : (prefixWord ++ tailWord_464725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464725).length < 2 ^ (prefixWord ++ tailWord_464725).sum := by decide
  have hdescent : baseEnd_464725 < baseStart_464725 := by decide
  rcases family_descends (prefixWord ++ tailWord_464725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464746 : List Nat := [3, 1, 3, 4, 2, 1, 1, 2, 5]
def baseStart_464746 : Nat := 118140960795 + 464746 * 2 ^ 59
def prefixEnd_464746 : Nat := 4983230072969 + 3 ^ 40 * 464746 * 2
def baseEnd_464746 : Nat := 53030684501009758408373

theorem tailTrace_464746 : CollatzResearch.WordTrace tailWord_464746 prefixEnd_464746 53030684501009758408373 := by
  unfold tailWord_464746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4237669793578022285689523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11300452782874726095172061 4237669793578022285689523)
  ·
    refine ⟨6356504690367033428534285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4237669793578022285689523 6356504690367033428534285)
    ·
      refine ⟨2383689258887637535700357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6356504690367033428534285 2383689258887637535700357)
      ·
        refine ⟨446941736041432037943817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2383689258887637535700357 446941736041432037943817)
        ·
          refine ⟨335206302031074028457863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446941736041432037943817 335206302031074028457863)
          ·
            refine ⟨502809453046611042686795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335206302031074028457863 502809453046611042686795)
            ·
              refine ⟨754214179569916564030193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502809453046611042686795 754214179569916564030193)
              ·
                refine ⟨565660634677437423022645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754214179569916564030193 565660634677437423022645)
                ·
                  refine ⟨53030684501009758408373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 565660634677437423022645 53030684501009758408373)
                  ·
                    rfl

theorem cell22_464746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_464746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464746 prefixEnd_464746 := by exact prefixLift 464746
  have htrace : WordTrace (prefixWord ++ tailWord_464746) baseStart_464746 baseEnd_464746 := by
    simpa [prefixWord, tailWord_464746, baseEnd_464746] using wordTrace_append hprefix tailTrace_464746
  have hstable : (prefixWord ++ tailWord_464746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464746).length < 2 ^ (prefixWord ++ tailWord_464746).sum := by decide
  have hdescent : baseEnd_464746 < baseStart_464746 := by decide
  rcases family_descends (prefixWord ++ tailWord_464746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464757 : List Nat := [1, 3, 4, 1, 1, 1, 1, 6, 4]
def baseStart_464757 : Nat := 118140960795 + 464757 * 2 ^ 59
def prefixEnd_464757 : Nat := 4983230072969 + 3 ^ 40 * 464757 * 2
def baseEnd_464757 : Nat := 53031939675942971066695

theorem tailTrace_464757 : CollatzResearch.WordTrace tailWord_464757 prefixEnd_464757 53031939675942971066695 := by
  unfold tailWord_464757
  simp only [CollatzResearch.WordTrace]
  refine ⟨16951080377272238021408525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11300720251514825347605683 16951080377272238021408525)
  ·
    refine ⟨6356655141477089258028197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16951080377272238021408525 6356655141477089258028197)
    ·
      refine ⟨1191872839026954235880287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6356655141477089258028197 1191872839026954235880287)
      ·
        refine ⟨1787809258540431353820431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1191872839026954235880287 1787809258540431353820431)
        ·
          refine ⟨2681713887810647030730647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1787809258540431353820431 2681713887810647030730647)
          ·
            refine ⟨4022570831715970546095971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2681713887810647030730647 4022570831715970546095971)
            ·
              refine ⟨6033856247573955819143957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4022570831715970546095971 6033856247573955819143957)
              ·
                refine ⟨282837011605029179022373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6033856247573955819143957 282837011605029179022373)
                ·
                  refine ⟨53031939675942971066695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282837011605029179022373 53031939675942971066695)
                  ·
                    rfl

theorem cell22_464757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_464757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464757 prefixEnd_464757 := by exact prefixLift 464757
  have htrace : WordTrace (prefixWord ++ tailWord_464757) baseStart_464757 baseEnd_464757 := by
    simpa [prefixWord, tailWord_464757, baseEnd_464757] using wordTrace_append hprefix tailTrace_464757
  have hstable : (prefixWord ++ tailWord_464757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464757).length < 2 ^ (prefixWord ++ tailWord_464757).sum := by decide
  have hdescent : baseEnd_464757 < baseStart_464757 := by decide
  rcases family_descends (prefixWord ++ tailWord_464757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464768 : List Nat := [2, 1, 1, 2, 1, 2, 4, 9]
def baseStart_464768 : Nat := 118140960795 + 464768 * 2 ^ 59
def prefixEnd_464768 : Nat := 4983230072969 + 3 ^ 40 * 464768 * 2
def baseEnd_464768 : Nat := 17677731616958727908339

theorem tailTrace_464768 : CollatzResearch.WordTrace tailWord_464768 prefixEnd_464768 17677731616958727908339 := by
  unfold tailWord_464768
  simp only [CollatzResearch.WordTrace]
  refine ⟨8475740790116193450029479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11300987720154924600039305 8475740790116193450029479)
  ·
    refine ⟨12713611185174290175044219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8475740790116193450029479 12713611185174290175044219)
    ·
      refine ⟨19070416777761435262566329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12713611185174290175044219 19070416777761435262566329)
      ·
        refine ⟨14302812583321076446924747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19070416777761435262566329 14302812583321076446924747)
        ·
          refine ⟨21454218874981614670387121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14302812583321076446924747 21454218874981614670387121)
          ·
            refine ⟨16090664156236211002790341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21454218874981614670387121 16090664156236211002790341)
            ·
              refine ⟨3016999529294289563023189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16090664156236211002790341 3016999529294289563023189)
              ·
                refine ⟨17677731616958727908339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3016999529294289563023189 17677731616958727908339)
                ·
                  rfl

theorem cell22_464768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 9].length) (baseStart_464768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464768 prefixEnd_464768 := by exact prefixLift 464768
  have htrace : WordTrace (prefixWord ++ tailWord_464768) baseStart_464768 baseEnd_464768 := by
    simpa [prefixWord, tailWord_464768, baseEnd_464768] using wordTrace_append hprefix tailTrace_464768
  have hstable : (prefixWord ++ tailWord_464768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464768).length < 2 ^ (prefixWord ++ tailWord_464768).sum := by decide
  have hdescent : baseEnd_464768 < baseStart_464768 := by decide
  rcases family_descends (prefixWord ++ tailWord_464768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464772 : List Nat := [2, 3, 2, 1, 1, 1, 2, 5, 2, 3]
def baseStart_464772 : Nat := 118140960795 + 464772 * 2 ^ 59
def prefixEnd_464772 : Nat := 4983230072969 + 3 ^ 40 * 464772 * 2
def baseEnd_464772 : Nat := 159100953834373874075039

theorem tailTrace_464772 : CollatzResearch.WordTrace tailWord_464772 prefixEnd_464772 159100953834373874075039 := by
  unfold tailWord_464772
  simp only [CollatzResearch.WordTrace]
  refine ⟨8475813736108947791602285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11301084981478597055469713 8475813736108947791602285)
  ·
    refine ⟨3178430151040855421850857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8475813736108947791602285 3178430151040855421850857)
    ·
      refine ⟨2383822613280641566388143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3178430151040855421850857 2383822613280641566388143)
      ·
        refine ⟨3575733919920962349582215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2383822613280641566388143 3575733919920962349582215)
        ·
          refine ⟨5363600879881443524373323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3575733919920962349582215 5363600879881443524373323)
          ·
            refine ⟨8045401319822165286559985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5363600879881443524373323 8045401319822165286559985)
            ·
              refine ⟨6034050989866623964919989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8045401319822165286559985 6034050989866623964919989)
              ·
                refine ⟨565692280299995996711249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6034050989866623964919989 565692280299995996711249)
                ·
                  refine ⟨424269210224996997533437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565692280299995996711249 424269210224996997533437)
                  ·
                    refine ⟨159100953834373874075039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 424269210224996997533437 159100953834373874075039)
                    ·
                      rfl

theorem cell22_464772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_464772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464772 prefixEnd_464772 := by exact prefixLift 464772
  have htrace : WordTrace (prefixWord ++ tailWord_464772) baseStart_464772 baseEnd_464772 := by
    simpa [prefixWord, tailWord_464772, baseEnd_464772] using wordTrace_append hprefix tailTrace_464772
  have hstable : (prefixWord ++ tailWord_464772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464772).length < 2 ^ (prefixWord ++ tailWord_464772).sum := by decide
  have hdescent : baseEnd_464772 < baseStart_464772 := by decide
  rcases family_descends (prefixWord ++ tailWord_464772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464785 : List Nat := [1, 2, 2, 1, 1, 1, 8, 6]
def baseStart_464785 : Nat := 118140960795 + 464785 * 2 ^ 59
def prefixEnd_464785 : Nat := 4983230072969 + 3 ^ 40 * 464785 * 2
def baseEnd_464785 : Nat := 17678378222227352611111

theorem tailTrace_464785 : CollatzResearch.WordTrace tailWord_464785 prefixEnd_464785 17678378222227352611111 := by
  unfold tailWord_464785
  simp only [CollatzResearch.WordTrace]
  refine ⟨16952101621170798803427809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11301401080780532535618539 16952101621170798803427809)
  ·
    refine ⟨12714076215878099102570857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16952101621170798803427809 12714076215878099102570857)
    ·
      refine ⟨9535557161908574326928143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12714076215878099102570857 9535557161908574326928143)
      ·
        refine ⟨14303335742862861490392215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9535557161908574326928143 14303335742862861490392215)
        ·
          refine ⟨21455003614294292235588323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14303335742862861490392215 21455003614294292235588323)
          ·
            refine ⟨32182505421441438353382485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21455003614294292235588323 32182505421441438353382485)
            ·
              refine ⟨377138735407516855703701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 32182505421441438353382485 377138735407516855703701)
              ·
                refine ⟨17678378222227352611111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 377138735407516855703701 17678378222227352611111)
                ·
                  rfl

theorem cell22_464785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 6].length) (baseStart_464785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464785 prefixEnd_464785 := by exact prefixLift 464785
  have htrace : WordTrace (prefixWord ++ tailWord_464785) baseStart_464785 baseEnd_464785 := by
    simpa [prefixWord, tailWord_464785, baseEnd_464785] using wordTrace_append hprefix tailTrace_464785
  have hstable : (prefixWord ++ tailWord_464785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464785).length < 2 ^ (prefixWord ++ tailWord_464785).sum := by decide
  have hdescent : baseEnd_464785 < baseStart_464785 := by decide
  rcases family_descends (prefixWord ++ tailWord_464785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464802 : List Nat := [3, 3, 1, 2, 3, 2, 8]
def baseStart_464802 : Nat := 118140960795 + 464802 * 2 ^ 59
def prefixEnd_464802 : Nat := 4983230072969 + 3 ^ 40 * 464802 * 2
def baseEnd_464802 : Nat := 5893008275831992437961

theorem tailTrace_464802 : CollatzResearch.WordTrace tailWord_464802 prefixEnd_464802 5893008275831992437961 := by
  unfold tailWord_464802
  simp only [CollatzResearch.WordTrace]
  refine ⟨4238180415527302676699165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11301814441406140471197773 4238180415527302676699165)
  ·
    refine ⟨1589317655822738503762187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4238180415527302676699165 1589317655822738503762187)
    ·
      refine ⟨2383976483734107755643281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1589317655822738503762187 2383976483734107755643281)
      ·
        refine ⟨1787982362800580816732461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2383976483734107755643281 1787982362800580816732461)
        ·
          refine ⟨670493386050217806274673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1787982362800580816732461 670493386050217806274673)
          ·
            refine ⟨502870039537663354706005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670493386050217806274673 502870039537663354706005)
            ·
              refine ⟨5893008275831992437961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 502870039537663354706005 5893008275831992437961)
              ·
                rfl

theorem cell22_464802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 8].length) (baseStart_464802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464802 prefixEnd_464802 := by exact prefixLift 464802
  have htrace : WordTrace (prefixWord ++ tailWord_464802) baseStart_464802 baseEnd_464802 := by
    simpa [prefixWord, tailWord_464802, baseEnd_464802] using wordTrace_append hprefix tailTrace_464802
  have hstable : (prefixWord ++ tailWord_464802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464802).length < 2 ^ (prefixWord ++ tailWord_464802).sum := by decide
  have hdescent : baseEnd_464802 < baseStart_464802 := by decide
  rcases family_descends (prefixWord ++ tailWord_464802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464808 : List Nat := [2, 1, 6, 2, 1, 1, 3, 2, 4]
def baseStart_464808 : Nat := 118140960795 + 464808 * 2 ^ 59
def prefixEnd_464808 : Nat := 4983230072969 + 3 ^ 40 * 464808 * 2
def baseEnd_464808 : Nat := 53037759123360593391643

theorem tailTrace_464808 : CollatzResearch.WordTrace tailWord_464808 prefixEnd_464808 53037759123360593391643 := by
  unfold tailWord_464808
  simp only [CollatzResearch.WordTrace]
  refine ⟨8476470250043736865757539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11301960333391649154343385 8476470250043736865757539)
  ·
    refine ⟨12714705375065605298636309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8476470250043736865757539 12714705375065605298636309)
    ·
      refine ⟨596001814456200248373577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12714705375065605298636309 596001814456200248373577)
      ·
        refine ⟨447001360842150186280183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596001814456200248373577 447001360842150186280183)
        ·
          refine ⟨670502041263225279420275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447001360842150186280183 670502041263225279420275)
          ·
            refine ⟨1005753061894837919130413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670502041263225279420275 1005753061894837919130413)
            ·
              refine ⟨377157398210564219673905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1005753061894837919130413 377157398210564219673905)
              ·
                refine ⟨282868048657923164755429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377157398210564219673905 282868048657923164755429)
                ·
                  refine ⟨53037759123360593391643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282868048657923164755429 53037759123360593391643)
                  ·
                    rfl

theorem cell22_464808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 4].length) (baseStart_464808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464808 prefixEnd_464808 := by exact prefixLift 464808
  have htrace : WordTrace (prefixWord ++ tailWord_464808) baseStart_464808 baseEnd_464808 := by
    simpa [prefixWord, tailWord_464808, baseEnd_464808] using wordTrace_append hprefix tailTrace_464808
  have hstable : (prefixWord ++ tailWord_464808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464808).length < 2 ^ (prefixWord ++ tailWord_464808).sum := by decide
  have hdescent : baseEnd_464808 < baseStart_464808 := by decide
  rcases family_descends (prefixWord ++ tailWord_464808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464894 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_464894 : Nat := 118140960795 + 464894 * 2 ^ 59
def prefixEnd_464894 : Nat := 4983230072969 + 3 ^ 40 * 464894 * 2
def baseEnd_464894 : Nat := 159142716927606222524665

theorem tailTrace_464894 : CollatzResearch.WordTrace tailWord_464894 prefixEnd_464894 159142716927606222524665 := by
  unfold tailWord_464894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119509647221988802393217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11304051451850606946097157 2119509647221988802393217)
  ·
    refine ⟨1589632235416491601794913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2119509647221988802393217 1589632235416491601794913)
    ·
      refine ⟨1192224176562368701346185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1589632235416491601794913 1192224176562368701346185)
      ·
        refine ⟨894168132421776526009639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1192224176562368701346185 894168132421776526009639)
        ·
          refine ⟨1341252198632664789014459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894168132421776526009639 1341252198632664789014459)
          ·
            refine ⟨2011878297948997183521689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341252198632664789014459 2011878297948997183521689)
            ·
              refine ⟨1508908723461747887641267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2011878297948997183521689 1508908723461747887641267)
              ·
                refine ⟨2263363085192621831461901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508908723461747887641267 2263363085192621831461901)
                ·
                  refine ⟨848761156947233186798213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2263363085192621831461901 848761156947233186798213)
                  ·
                    refine ⟨159142716927606222524665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 848761156947233186798213 159142716927606222524665)
                    ·
                      rfl

theorem cell22_464894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_464894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464894 prefixEnd_464894 := by exact prefixLift 464894
  have htrace : WordTrace (prefixWord ++ tailWord_464894) baseStart_464894 baseEnd_464894 := by
    simpa [prefixWord, tailWord_464894, baseEnd_464894] using wordTrace_append hprefix tailTrace_464894
  have hstable : (prefixWord ++ tailWord_464894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464894).length < 2 ^ (prefixWord ++ tailWord_464894).sum := by decide
  have hdescent : baseEnd_464894 < baseStart_464894 := by decide
  rcases family_descends (prefixWord ++ tailWord_464894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464907 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 4, 3]
def baseStart_464907 : Nat := 118140960795 + 464907 * 2 ^ 59
def prefixEnd_464907 : Nat := 4983230072969 + 3 ^ 40 * 464907 * 2
def baseEnd_464907 : Nat := 159147167093278521949625

theorem tailTrace_464907 : CollatzResearch.WordTrace tailWord_464907 prefixEnd_464907 159147167093278521949625 := by
  unfold tailWord_464907
  simp only [CollatzResearch.WordTrace]
  refine ⟨16956551326728813639368975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11304367551152542426245983 16956551326728813639368975)
  ·
    refine ⟨25434826990093220459053463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16956551326728813639368975 25434826990093220459053463)
    ·
      refine ⟨38152240485139830688580195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25434826990093220459053463 38152240485139830688580195)
      ·
        refine ⟨57228360727709746032870293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38152240485139830688580195 57228360727709746032870293)
        ·
          refine ⟨2682579409111394345290795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57228360727709746032870293 2682579409111394345290795)
          ·
            refine ⟨4023869113667091517936193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2682579409111394345290795 4023869113667091517936193)
            ·
              refine ⟨3017901835250318638452145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4023869113667091517936193 3017901835250318638452145)
              ·
                refine ⟨2263426376437738978839109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3017901835250318638452145 2263426376437738978839109)
                ·
                  refine ⟨424392445582076058532333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2263426376437738978839109 424392445582076058532333)
                  ·
                    refine ⟨159147167093278521949625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 424392445582076058532333 159147167093278521949625)
                    ·
                      rfl

theorem cell22_464907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 3].length) (baseStart_464907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464907 prefixEnd_464907 := by exact prefixLift 464907
  have htrace : WordTrace (prefixWord ++ tailWord_464907) baseStart_464907 baseEnd_464907 := by
    simpa [prefixWord, tailWord_464907, baseEnd_464907] using wordTrace_append hprefix tailTrace_464907
  have hstable : (prefixWord ++ tailWord_464907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464907).length < 2 ^ (prefixWord ++ tailWord_464907).sum := by decide
  have hdescent : baseEnd_464907 < baseStart_464907 := by decide
  rcases family_descends (prefixWord ++ tailWord_464907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464920 : List Nat := [2, 1, 2, 3, 2, 1, 11]
def baseStart_464920 : Nat := 118140960795 + 464920 * 2 ^ 59
def prefixEnd_464920 : Nat := 4983230072969 + 3 ^ 40 * 464920 * 2
def baseEnd_464920 : Nat := 5894504342924104495355

theorem tailTrace_464920 : CollatzResearch.WordTrace tailWord_464920 prefixEnd_464920 5894504342924104495355 := by
  unfold tailWord_464920
  simp only [CollatzResearch.WordTrace]
  refine ⟨8478512737840858429796107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11304683650454477906394809 8478512737840858429796107)
  ·
    refine ⟨12717769106761287644694161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8478512737840858429796107 12717769106761287644694161)
    ·
      refine ⟨9538326830070965733520621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12717769106761287644694161 9538326830070965733520621)
      ·
        refine ⟨3576872561276612150070233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9538326830070965733520621 3576872561276612150070233)
        ·
          refine ⟨2682654420957459112552675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3576872561276612150070233 2682654420957459112552675)
          ·
            refine ⟨4023981631436188668829013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2682654420957459112552675 4023981631436188668829013)
            ·
              refine ⟨5894504342924104495355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4023981631436188668829013 5894504342924104495355)
              ·
                rfl

theorem cell22_464920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 11].length) (baseStart_464920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464920 prefixEnd_464920 := by exact prefixLift 464920
  have htrace : WordTrace (prefixWord ++ tailWord_464920) baseStart_464920 baseEnd_464920 := by
    simpa [prefixWord, tailWord_464920, baseEnd_464920] using wordTrace_append hprefix tailTrace_464920
  have hstable : (prefixWord ++ tailWord_464920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464920).length < 2 ^ (prefixWord ++ tailWord_464920).sum := by decide
  have hdescent : baseEnd_464920 < baseStart_464920 := by decide
  rcases family_descends (prefixWord ++ tailWord_464920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464924 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 4, 3]
def baseStart_464924 : Nat := 118140960795 + 464924 * 2 ^ 59
def prefixEnd_464924 : Nat := 4983230072969 + 3 ^ 40 * 464924 * 2
def baseEnd_464924 : Nat := 159152986540696144274573

theorem tailTrace_464924 : CollatzResearch.WordTrace tailWord_464924 prefixEnd_464924 159152986540696144274573 := by
  unfold tailWord_464924
  simp only [CollatzResearch.WordTrace]
  refine ⟨8478585683833612771368913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11304780911778150361825217 8478585683833612771368913)
  ·
    refine ⟨6358939262875209578526685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8478585683833612771368913 6358939262875209578526685)
    ·
      refine ⟨2384602223578203591947507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6358939262875209578526685 2384602223578203591947507)
      ·
        refine ⟨3576903335367305387921261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2384602223578203591947507 3576903335367305387921261)
        ·
          refine ⟨1341338750762739520470473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3576903335367305387921261 1341338750762739520470473)
          ·
            refine ⟨1006004063072054640352855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1341338750762739520470473 1006004063072054640352855)
            ·
              refine ⟨1509006094608081960529283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006004063072054640352855 1509006094608081960529283)
              ·
                refine ⟨2263509141912122940793925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1509006094608081960529283 2263509141912122940793925)
                ·
                  refine ⟨424407964108523051398861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2263509141912122940793925 424407964108523051398861)
                  ·
                    refine ⟨159152986540696144274573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 424407964108523051398861 159152986540696144274573)
                    ·
                      rfl

theorem cell22_464924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_464924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_464924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_464924 prefixEnd_464924 := by exact prefixLift 464924
  have htrace : WordTrace (prefixWord ++ tailWord_464924) baseStart_464924 baseEnd_464924 := by
    simpa [prefixWord, tailWord_464924, baseEnd_464924] using wordTrace_append hprefix tailTrace_464924
  have hstable : (prefixWord ++ tailWord_464924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464924).length < 2 ^ (prefixWord ++ tailWord_464924).sum := by decide
  have hdescent : baseEnd_464924 < baseStart_464924 := by decide
  rcases family_descends (prefixWord ++ tailWord_464924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465123 : List Nat := [1, 1, 1, 8, 1, 2, 2, 6]
def baseStart_465123 : Nat := 118140960795 + 465123 * 2 ^ 59
def prefixEnd_465123 : Nat := 4983230072969 + 3 ^ 40 * 465123 * 2
def baseEnd_465123 : Nat := 17691234256391773172107

theorem tailTrace_465123 : CollatzResearch.WordTrace tailWord_465123 prefixEnd_465123 17691234256391773172107 := by
  unfold tailWord_465123
  simp only [CollatzResearch.WordTrace]
  refine ⟨16964429493946282529232023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11309619662630855019488015 16964429493946282529232023)
  ·
    refine ⟨25446644240919423793848035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16964429493946282529232023 25446644240919423793848035)
    ·
      refine ⟨38169966361379135690772053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25446644240919423793848035 38169966361379135690772053)
      ·
        refine ⟨447304293297411746376235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 38169966361379135690772053 447304293297411746376235)
        ·
          refine ⟨670956439946117619564353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447304293297411746376235 670956439946117619564353)
          ·
            refine ⟨503217329959588214673265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670956439946117619564353 503217329959588214673265)
            ·
              refine ⟨377412997469691161004949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503217329959588214673265 377412997469691161004949)
              ·
                refine ⟨17691234256391773172107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 377412997469691161004949 17691234256391773172107)
                ·
                  rfl

theorem cell22_465123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 6].length) (baseStart_465123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_465123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_465123 prefixEnd_465123 := by exact prefixLift 465123
  have htrace : WordTrace (prefixWord ++ tailWord_465123) baseStart_465123 baseEnd_465123 := by
    simpa [prefixWord, tailWord_465123, baseEnd_465123] using wordTrace_append hprefix tailTrace_465123
  have hstable : (prefixWord ++ tailWord_465123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465123).length < 2 ^ (prefixWord ++ tailWord_465123).sum := by decide
  have hdescent : baseEnd_465123 < baseStart_465123 := by decide
  rcases family_descends (prefixWord ++ tailWord_465123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465164 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 3, 4]
def baseStart_465164 : Nat := 118140960795 + 465164 * 2 ^ 59
def prefixEnd_465164 : Nat := 4983230072969 + 3 ^ 40 * 465164 * 2
def baseEnd_465164 : Nat := 159235143445415518273837

theorem tailTrace_465164 : CollatzResearch.WordTrace tailWord_465164 prefixEnd_465164 159235143445415518273837 := by
  unfold tailWord_465164
  simp only [CollatzResearch.WordTrace]
  refine ⟨8482962443398873265737273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11310616591198497687649697 8482962443398873265737273)
  ·
    refine ⟨6362221832549154949302955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8482962443398873265737273 6362221832549154949302955)
    ·
      refine ⟨9543332748823732423954433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6362221832549154949302955 9543332748823732423954433)
      ·
        refine ⟨7157499561617799317965825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9543332748823732423954433 7157499561617799317965825)
        ·
          refine ⟨5368124671213349488474369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7157499561617799317965825 5368124671213349488474369)
          ·
            refine ⟨4026093503410012116355777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5368124671213349488474369 4026093503410012116355777)
            ·
              refine ⟨3019570127557509087266833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4026093503410012116355777 3019570127557509087266833)
              ·
                refine ⟨2264677595668131815450125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3019570127557509087266833 2264677595668131815450125)
                ·
                  refine ⟨849254098375549430793797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2264677595668131815450125 849254098375549430793797)
                  ·
                    refine ⟨159235143445415518273837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 849254098375549430793797 159235143445415518273837)
                    ·
                      rfl

theorem cell22_465164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_465164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_465164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_465164 prefixEnd_465164 := by exact prefixLift 465164
  have htrace : WordTrace (prefixWord ++ tailWord_465164) baseStart_465164 baseEnd_465164 := by
    simpa [prefixWord, tailWord_465164, baseEnd_465164] using wordTrace_append hprefix tailTrace_465164
  have hstable : (prefixWord ++ tailWord_465164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465164).length < 2 ^ (prefixWord ++ tailWord_465164).sum := by decide
  have hdescent : baseEnd_465164 < baseStart_465164 := by decide
  rcases family_descends (prefixWord ++ tailWord_465164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465224 : List Nat := [2, 1, 3, 1, 1, 2, 5, 7]
def baseStart_465224 : Nat := 118140960795 + 465224 * 2 ^ 59
def prefixEnd_465224 : Nat := 4983230072969 + 3 ^ 40 * 465224 * 2
def baseEnd_465224 : Nat := 17695075852399484641517

theorem tailTrace_465224 : CollatzResearch.WordTrace tailWord_465224 prefixEnd_465224 17695075852399484641517 := by
  unfold tailWord_465224
  simp only [CollatzResearch.WordTrace]
  refine ⟨8484056633290188389329363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11312075511053584519105817 8484056633290188389329363)
  ·
    refine ⟨12726084949935282583994045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8484056633290188389329363 12726084949935282583994045)
    ·
      refine ⟨4772281856225730968997767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12726084949935282583994045 4772281856225730968997767)
      ·
        refine ⟨7158422784338596453496651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4772281856225730968997767 7158422784338596453496651)
        ·
          refine ⟨10737634176507894680244977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7158422784338596453496651 10737634176507894680244977)
          ·
            refine ⟨8053225632380921010183733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10737634176507894680244977 8053225632380921010183733)
            ·
              refine ⟨754989903035711344704725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8053225632380921010183733 754989903035711344704725)
              ·
                refine ⟨17695075852399484641517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 754989903035711344704725 17695075852399484641517)
                ·
                  rfl

theorem cell22_465224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 7].length) (baseStart_465224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_465224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_465224 prefixEnd_465224 := by exact prefixLift 465224
  have htrace : WordTrace (prefixWord ++ tailWord_465224) baseStart_465224 baseEnd_465224 := by
    simpa [prefixWord, tailWord_465224, baseEnd_465224] using wordTrace_append hprefix tailTrace_465224
  have hstable : (prefixWord ++ tailWord_465224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465224).length < 2 ^ (prefixWord ++ tailWord_465224).sum := by decide
  have hdescent : baseEnd_465224 < baseStart_465224 := by decide
  rcases family_descends (prefixWord ++ tailWord_465224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465451 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 5, 4]
def baseStart_465451 : Nat := 118140960795 + 465451 * 2 ^ 59
def prefixEnd_465451 : Nat := 4983230072969 + 3 ^ 40 * 465451 * 2
def baseEnd_465451 : Nat := 159333389410642436347957

theorem tailTrace_465451 : CollatzResearch.WordTrace tailWord_465451 prefixEnd_465451 159333389410642436347957 := by
  unfold tailWord_465451
  simp only [CollatzResearch.WordTrace]
  refine ⟨16976392636757994547172207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11317595091171996364781471 16976392636757994547172207)
  ·
    refine ⟨25464588955136991820758311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16976392636757994547172207 25464588955136991820758311)
    ·
      refine ⟨38196883432705487731137467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25464588955136991820758311 38196883432705487731137467)
      ·
        refine ⟨57295325149058231596706201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38196883432705487731137467 57295325149058231596706201)
        ·
          refine ⟨42971493861793673697529651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57295325149058231596706201 42971493861793673697529651)
          ·
            refine ⟨64457240792690510546294477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42971493861793673697529651 64457240792690510546294477)
            ·
              refine ⟨24171465297258941454860429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64457240792690510546294477 24171465297258941454860429)
              ·
                refine ⟨9064299486472103045572661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24171465297258941454860429 9064299486472103045572661)
                ·
                  refine ⟨849778076856759660522437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9064299486472103045572661 849778076856759660522437)
                  ·
                    refine ⟨159333389410642436347957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 849778076856759660522437 159333389410642436347957)
                    ·
                      rfl

theorem cell22_465451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 4].length) (baseStart_465451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_465451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_465451 prefixEnd_465451 := by exact prefixLift 465451
  have htrace : WordTrace (prefixWord ++ tailWord_465451) baseStart_465451 baseEnd_465451 := by
    simpa [prefixWord, tailWord_465451, baseEnd_465451] using wordTrace_append hprefix tailTrace_465451
  have hstable : (prefixWord ++ tailWord_465451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465451).length < 2 ^ (prefixWord ++ tailWord_465451).sum := by decide
  have hdescent : baseEnd_465451 < baseStart_465451 := by decide
  rcases family_descends (prefixWord ++ tailWord_465451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465506 : List Nat := [3, 3, 2, 3, 2, 1, 2, 1, 5]
def baseStart_465506 : Nat := 118140960795 + 465506 * 2 ^ 59
def prefixEnd_465506 : Nat := 4983230072969 + 3 ^ 40 * 465506 * 2
def baseEnd_465506 : Nat := 53117405678213542074263

theorem tailTrace_465506 : CollatzResearch.WordTrace tailWord_465506 prefixEnd_465506 53117405678213542074263 := by
  unfold tailWord_465506
  simp only [CollatzResearch.WordTrace]
  refine ⟨4244599662889684735106093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11318932434372492626949581 4244599662889684735106093)
  ·
    refine ⟨1591724873583631775664785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4244599662889684735106093 1591724873583631775664785)
    ·
      refine ⟨1193793655187723831748589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1591724873583631775664785 1193793655187723831748589)
      ·
        refine ⟨447672620695396436905721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1193793655187723831748589 447672620695396436905721)
        ·
          refine ⟨335754465521547327679291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447672620695396436905721 335754465521547327679291)
          ·
            refine ⟨503631698282320991518937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335754465521547327679291 503631698282320991518937)
            ·
              refine ⟨377723773711740743639203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503631698282320991518937 377723773711740743639203)
              ·
                refine ⟨566585660567611115458805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377723773711740743639203 566585660567611115458805)
                ·
                  refine ⟨53117405678213542074263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 566585660567611115458805 53117405678213542074263)
                  ·
                    rfl

theorem cell22_465506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_465506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_465506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_465506 prefixEnd_465506 := by exact prefixLift 465506
  have htrace : WordTrace (prefixWord ++ tailWord_465506) baseStart_465506 baseEnd_465506 := by
    simpa [prefixWord, tailWord_465506, baseEnd_465506] using wordTrace_append hprefix tailTrace_465506
  have hstable : (prefixWord ++ tailWord_465506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465506).length < 2 ^ (prefixWord ++ tailWord_465506).sum := by decide
  have hdescent : baseEnd_465506 < baseStart_465506 := by decide
  rcases family_descends (prefixWord ++ tailWord_465506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465560 : List Nat := [2, 1, 2, 4, 1, 1, 2, 3, 3, 3]
def baseStart_465560 : Nat := 118140960795 + 465560 * 2 ^ 59
def prefixEnd_465560 : Nat := 4983230072969 + 3 ^ 40 * 465560 * 2
def baseEnd_465560 : Nat := 159370702338202485372623

theorem tailTrace_465560 : CollatzResearch.WordTrace tailWord_465560 prefixEnd_465560 159370702338202485372623 := by
  unfold tailWord_465560
  simp only [CollatzResearch.WordTrace]
  refine ⟨8490184096681553081445067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11320245462242070775260089 8490184096681553081445067)
  ·
    refine ⟨12735276145022329622167601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8490184096681553081445067 12735276145022329622167601)
    ·
      refine ⟨9551457108766747216625701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12735276145022329622167601 9551457108766747216625701)
      ·
        refine ⟨1790898207893765103117319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9551457108766747216625701 1790898207893765103117319)
        ·
          refine ⟨2686347311840647654675979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1790898207893765103117319 2686347311840647654675979)
          ·
            refine ⟨4029520967760971482013969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2686347311840647654675979 4029520967760971482013969)
            ·
              refine ⟨3022140725820728611510477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4029520967760971482013969 3022140725820728611510477)
              ·
                refine ⟨1133302772182773229316429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3022140725820728611510477 1133302772182773229316429)
                ·
                  refine ⟨424988539568539960993661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1133302772182773229316429 424988539568539960993661)
                  ·
                    refine ⟨159370702338202485372623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 424988539568539960993661 159370702338202485372623)
                    ·
                      rfl

theorem cell22_465560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_465560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_465560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_465560 prefixEnd_465560 := by exact prefixLift 465560
  have htrace : WordTrace (prefixWord ++ tailWord_465560) baseStart_465560 baseEnd_465560 := by
    simpa [prefixWord, tailWord_465560, baseEnd_465560] using wordTrace_append hprefix tailTrace_465560
  have hstable : (prefixWord ++ tailWord_465560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465560).length < 2 ^ (prefixWord ++ tailWord_465560).sum := by decide
  have hdescent : baseEnd_465560 < baseStart_465560 := by decide
  rcases family_descends (prefixWord ++ tailWord_465560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465562 : List Nat := [3, 1, 1, 6, 1, 2, 1, 7]
def baseStart_465562 : Nat := 118140960795 + 465562 * 2 ^ 59
def prefixEnd_465562 : Nat := 4983230072969 + 3 ^ 40 * 465562 * 2
def baseEnd_465562 : Nat := 17707931886563905202513

theorem tailTrace_465562 : CollatzResearch.WordTrace tailWord_465562 prefixEnd_465562 17707931886563905202513 := by
  unfold tailWord_465562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4245110284838965126115735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11320294092903907002975293 4245110284838965126115735)
  ·
    refine ⟨6367665427258447689173603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4245110284838965126115735 6367665427258447689173603)
    ·
      refine ⟨9551498140887671533760405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6367665427258447689173603 9551498140887671533760405)
      ·
        refine ⟨447726475354109603145019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9551498140887671533760405 447726475354109603145019)
        ·
          refine ⟨671589713031164404717529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447726475354109603145019 671589713031164404717529)
          ·
            refine ⟨503692284773373303538147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671589713031164404717529 503692284773373303538147)
            ·
              refine ⟨755538427160059955307221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503692284773373303538147 755538427160059955307221)
              ·
                refine ⟨17707931886563905202513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 755538427160059955307221 17707931886563905202513)
                ·
                  rfl

theorem cell22_465562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 7].length) (baseStart_465562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_465562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_465562 prefixEnd_465562 := by exact prefixLift 465562
  have htrace : WordTrace (prefixWord ++ tailWord_465562) baseStart_465562 baseEnd_465562 := by
    simpa [prefixWord, tailWord_465562, baseEnd_465562] using wordTrace_append hprefix tailTrace_465562
  have hstable : (prefixWord ++ tailWord_465562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465562).length < 2 ^ (prefixWord ++ tailWord_465562).sum := by decide
  have hdescent : baseEnd_465562 < baseStart_465562 := by decide
  rcases family_descends (prefixWord ++ tailWord_465562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465635 : List Nat := [1, 1, 1, 7, 1, 1, 2, 2, 6]
def baseStart_465635 : Nat := 118140960795 + 465635 * 2 ^ 59
def prefixEnd_465635 : Nat := 4983230072969 + 3 ^ 40 * 465635 * 2
def baseEnd_465635 : Nat := 53132125456975763249131

theorem tailTrace_465635 : CollatzResearch.WordTrace tailWord_465635 prefixEnd_465635 53132125456975763249131 := by
  unfold tailWord_465635
  simp only [CollatzResearch.WordTrace]
  refine ⟨16983103668091393971870359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11322069112060929314580239 16983103668091393971870359)
  ·
    refine ⟨25474655502137090957805539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16983103668091393971870359 25474655502137090957805539)
    ·
      refine ⟨38211983253205636436708309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25474655502137090957805539 38211983253205636436708309)
      ·
        refine ⟨895593357497007103985351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 38211983253205636436708309 895593357497007103985351)
        ·
          refine ⟨1343390036245510655978027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 895593357497007103985351 1343390036245510655978027)
          ·
            refine ⟨2015085054368265983967041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343390036245510655978027 2015085054368265983967041)
            ·
              refine ⟨1511313790776199487975281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2015085054368265983967041 1511313790776199487975281)
              ·
                refine ⟨1133485343082149615981461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1511313790776199487975281 1133485343082149615981461)
                ·
                  refine ⟨53132125456975763249131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1133485343082149615981461 53132125456975763249131)
                  ·
                    rfl

theorem cell22_465635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 6].length) (baseStart_465635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_465635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_465635 prefixEnd_465635 := by exact prefixLift 465635
  have htrace : WordTrace (prefixWord ++ tailWord_465635) baseStart_465635 baseEnd_465635 := by
    simpa [prefixWord, tailWord_465635, baseEnd_465635] using wordTrace_append hprefix tailTrace_465635
  have hstable : (prefixWord ++ tailWord_465635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465635).length < 2 ^ (prefixWord ++ tailWord_465635).sum := by decide
  have hdescent : baseEnd_465635 < baseStart_465635 := by decide
  rcases family_descends (prefixWord ++ tailWord_465635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465637 : List Nat := [1, 3, 1, 4, 1, 3, 2, 2, 1, 4]
def baseStart_465637 : Nat := 118140960795 + 465637 * 2 ^ 59
def prefixEnd_465637 : Nat := 4983230072969 + 3 ^ 40 * 465637 * 2
def baseEnd_465637 : Nat := 159397061011799951197387

theorem tailTrace_465637 : CollatzResearch.WordTrace tailWord_465637 prefixEnd_465637 159397061011799951197387 := by
  unfold tailWord_465637
  simp only [CollatzResearch.WordTrace]
  refine ⟨16983176614084148313443165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11322117742722765542295443 16983176614084148313443165)
  ·
    refine ⟨6368691230281555617541187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16983176614084148313443165 6368691230281555617541187)
    ·
      refine ⟨9553036845422333426311781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6368691230281555617541187 9553036845422333426311781)
      ·
        refine ⟨1791194408516687517433459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9553036845422333426311781 1791194408516687517433459)
        ·
          refine ⟨2686791612775031276150189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791194408516687517433459 2686791612775031276150189)
          ·
            refine ⟨1007546854790636728556321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2686791612775031276150189 1007546854790636728556321)
            ·
              refine ⟨755660141092977546417241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1007546854790636728556321 755660141092977546417241)
              ·
                refine ⟨566745105819733159812931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 755660141092977546417241 566745105819733159812931)
                ·
                  refine ⟨850117658729599739719397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566745105819733159812931 850117658729599739719397)
                  ·
                    refine ⟨159397061011799951197387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 850117658729599739719397 159397061011799951197387)
                    ·
                      rfl

theorem cell22_465637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_465637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_465637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_465637 prefixEnd_465637 := by exact prefixLift 465637
  have htrace : WordTrace (prefixWord ++ tailWord_465637) baseStart_465637 baseEnd_465637 := by
    simpa [prefixWord, tailWord_465637, baseEnd_465637] using wordTrace_append hprefix tailTrace_465637
  have hstable : (prefixWord ++ tailWord_465637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465637).length < 2 ^ (prefixWord ++ tailWord_465637).sum := by decide
  have hdescent : baseEnd_465637 < baseStart_465637 := by decide
  rcases family_descends (prefixWord ++ tailWord_465637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465648 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 1, 6]
def baseStart_465648 : Nat := 118140960795 + 465648 * 2 ^ 59
def prefixEnd_465648 : Nat := 4983230072969 + 3 ^ 40 * 465648 * 2
def baseEnd_465648 : Nat := 159400826536599589172353

theorem tailTrace_465648 : CollatzResearch.WordTrace tailWord_465648 prefixEnd_465648 159400826536599589172353 := by
  unfold tailWord_465648
  simp only [CollatzResearch.WordTrace]
  refine ⟨8491788908522148596046799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11322385211362864794729065 8491788908522148596046799)
  ·
    refine ⟨12737683362783222894070199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8491788908522148596046799 12737683362783222894070199)
    ·
      refine ⟨19106525044174834341105299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12737683362783222894070199 19106525044174834341105299)
      ·
        refine ⟨28659787566262251511657949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19106525044174834341105299 28659787566262251511657949)
        ·
          refine ⟨10747420337348344316871731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28659787566262251511657949 10747420337348344316871731)
          ·
            refine ⟨16121130506022516475307597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10747420337348344316871731 16121130506022516475307597)
            ·
              refine ⟨6045423939758443678240349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16121130506022516475307597 6045423939758443678240349)
              ·
                refine ⟨2267033977409416379340131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6045423939758443678240349 2267033977409416379340131)
                ·
                  refine ⟨3400550966114124569010197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2267033977409416379340131 3400550966114124569010197)
                  ·
                    refine ⟨159400826536599589172353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3400550966114124569010197 159400826536599589172353)
                    ·
                      rfl

theorem cell22_465648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_465648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_465648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_465648 prefixEnd_465648 := by exact prefixLift 465648
  have htrace : WordTrace (prefixWord ++ tailWord_465648) baseStart_465648 baseEnd_465648 := by
    simpa [prefixWord, tailWord_465648, baseEnd_465648] using wordTrace_append hprefix tailTrace_465648
  have hstable : (prefixWord ++ tailWord_465648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465648).length < 2 ^ (prefixWord ++ tailWord_465648).sum := by decide
  have hdescent : baseEnd_465648 < baseStart_465648 := by decide
  rcases family_descends (prefixWord ++ tailWord_465648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465740 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 1, 7]
def baseStart_465740 : Nat := 118140960795 + 465740 * 2 ^ 59
def prefixEnd_465740 : Nat := 4983230072969 + 3 ^ 40 * 465740 * 2
def baseEnd_465740 : Nat := 159432320016742015872071

theorem tailTrace_465740 : CollatzResearch.WordTrace tailWord_465740 prefixEnd_465740 159432320016742015872071 := by
  unfold tailWord_465740
  simp only [CollatzResearch.WordTrace]
  refine ⟨8493466666355498452221337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11324622221807331269628449 8493466666355498452221337)
  ·
    refine ⟨6370099999766623839166003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8493466666355498452221337 6370099999766623839166003)
    ·
      refine ⟨9555149999649935758749005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6370099999766623839166003 9555149999649935758749005)
      ·
        refine ⟨3583181249868725909530877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9555149999649935758749005 3583181249868725909530877)
        ·
          refine ⟨1343692968700772216074079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3583181249868725909530877 1343692968700772216074079)
          ·
            refine ⟨2015539453051158324111119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343692968700772216074079 2015539453051158324111119)
            ·
              refine ⟨3023309179576737486166679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2015539453051158324111119 3023309179576737486166679)
              ·
                refine ⟨4534963769365106229250019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3023309179576737486166679 4534963769365106229250019)
                ·
                  refine ⟨6802445654047659343875029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4534963769365106229250019 6802445654047659343875029)
                  ·
                    refine ⟨159432320016742015872071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6802445654047659343875029 159432320016742015872071)
                    ·
                      rfl

theorem cell22_465740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_465740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_465740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_465740 prefixEnd_465740 := by exact prefixLift 465740
  have htrace : WordTrace (prefixWord ++ tailWord_465740) baseStart_465740 baseEnd_465740 := by
    simpa [prefixWord, tailWord_465740, baseEnd_465740] using wordTrace_append hprefix tailTrace_465740
  have hstable : (prefixWord ++ tailWord_465740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465740).length < 2 ^ (prefixWord ++ tailWord_465740).sum := by decide
  have hdescent : baseEnd_465740 < baseStart_465740 := by decide
  rcases family_descends (prefixWord ++ tailWord_465740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465772 : List Nat := [2, 2, 1, 1, 4, 1, 3, 3, 1, 4]
def baseStart_465772 : Nat := 118140960795 + 465772 * 2 ^ 59
def prefixEnd_465772 : Nat := 4983230072969 + 3 ^ 40 * 465772 * 2
def baseEnd_465772 : Nat := 159443274270704599071973

theorem tailTrace_465772 : CollatzResearch.WordTrace tailWord_465772 prefixEnd_465772 159443274270704599071973 := by
  unfold tailWord_465772
  simp only [CollatzResearch.WordTrace]
  refine ⟨8494050234297533184803785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11325400312396710913071713 8494050234297533184803785)
  ·
    refine ⟨6370537675723149888602839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8494050234297533184803785 6370537675723149888602839)
    ·
      refine ⟨9555806513584724832904259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6370537675723149888602839 9555806513584724832904259)
      ·
        refine ⟨14333709770377087249356389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9555806513584724832904259 14333709770377087249356389)
        ·
          refine ⟨2687570581945703859254323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14333709770377087249356389 2687570581945703859254323)
          ·
            refine ⟨4031355872918555788881485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2687570581945703859254323 4031355872918555788881485)
            ·
              refine ⟨1511758452344458420830557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4031355872918555788881485 1511758452344458420830557)
              ·
                refine ⟨566909419629171907811459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1511758452344458420830557 566909419629171907811459)
                ·
                  refine ⟨850364129443757861717189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566909419629171907811459 850364129443757861717189)
                  ·
                    refine ⟨159443274270704599071973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 850364129443757861717189 159443274270704599071973)
                    ·
                      rfl

theorem cell22_465772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_465772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_465772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_465772 prefixEnd_465772 := by exact prefixLift 465772
  have htrace : WordTrace (prefixWord ++ tailWord_465772) baseStart_465772 baseEnd_465772 := by
    simpa [prefixWord, tailWord_465772, baseEnd_465772] using wordTrace_append hprefix tailTrace_465772
  have hstable : (prefixWord ++ tailWord_465772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465772).length < 2 ^ (prefixWord ++ tailWord_465772).sum := by decide
  have hdescent : baseEnd_465772 < baseStart_465772 := by decide
  rcases family_descends (prefixWord ++ tailWord_465772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465787 : List Nat := [1, 1, 1, 1, 1, 5, 4, 4, 4]
def baseStart_465787 : Nat := 118140960795 + 465787 * 2 ^ 59
def prefixEnd_465787 : Nat := 4983230072969 + 3 ^ 40 * 465787 * 2
def baseEnd_465787 : Nat := 53149469692416519982309

theorem tailTrace_465787 : CollatzResearch.WordTrace tailWord_465787 prefixEnd_465787 53149469692416519982309 := by
  unfold tailWord_465787
  simp only [CollatzResearch.WordTrace]
  refine ⟨16988647563540723931403615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11325765042360482620935743 16988647563540723931403615)
  ·
    refine ⟨25482971345311085897105423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16988647563540723931403615 25482971345311085897105423)
    ·
      refine ⟨38224457017966628845658135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25482971345311085897105423 38224457017966628845658135)
      ·
        refine ⟨57336685526949943268487203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38224457017966628845658135 57336685526949943268487203)
        ·
          refine ⟨86005028290424914902730805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57336685526949943268487203 86005028290424914902730805)
          ·
            refine ⟨8062971402227335772131013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86005028290424914902730805 8062971402227335772131013)
            ·
              refine ⟨1511807137917625457274565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8062971402227335772131013 1511807137917625457274565)
              ·
                refine ⟨283463838359554773238981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1511807137917625457274565 283463838359554773238981)
                ·
                  refine ⟨53149469692416519982309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 283463838359554773238981 53149469692416519982309)
                  ·
                    rfl

theorem cell22_465787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 4].length) (baseStart_465787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_465787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_465787 prefixEnd_465787 := by exact prefixLift 465787
  have htrace : WordTrace (prefixWord ++ tailWord_465787) baseStart_465787 baseEnd_465787 := by
    simpa [prefixWord, tailWord_465787, baseEnd_465787] using wordTrace_append hprefix tailTrace_465787
  have hstable : (prefixWord ++ tailWord_465787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465787).length < 2 ^ (prefixWord ++ tailWord_465787).sum := by decide
  have hdescent : baseEnd_465787 < baseStart_465787 := by decide
  rcases family_descends (prefixWord ++ tailWord_465787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465815 : List Nat := [1, 1, 3, 3, 1, 2, 3, 8]
def baseStart_465815 : Nat := 118140960795 + 465815 * 2 ^ 59
def prefixEnd_465815 : Nat := 4983230072969 + 3 ^ 40 * 465815 * 2
def baseEnd_465815 : Nat := 17717554894385202249649

theorem tailTrace_465815 : CollatzResearch.WordTrace tailWord_465815 prefixEnd_465815 17717554894385202249649 := by
  unfold tailWord_465815
  simp only [CollatzResearch.WordTrace]
  refine ⟨16989668807439284713422899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11326445871626189808948599 16989668807439284713422899)
  ·
    refine ⟨25484503211158927070134349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16989668807439284713422899 25484503211158927070134349)
    ·
      refine ⟨9556688704184597651300381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25484503211158927070134349 9556688704184597651300381)
      ·
        refine ⟨3583758264069224119237643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9556688704184597651300381 3583758264069224119237643)
        ·
          refine ⟨5375637396103836178856465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3583758264069224119237643 5375637396103836178856465)
          ·
            refine ⟨4031728047077877134142349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5375637396103836178856465 4031728047077877134142349)
            ·
              refine ⟨1511898017654203925303381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4031728047077877134142349 1511898017654203925303381)
              ·
                refine ⟨17717554894385202249649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1511898017654203925303381 17717554894385202249649)
                ·
                  rfl

theorem cell22_465815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 8].length) (baseStart_465815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_465815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_465815 prefixEnd_465815 := by exact prefixLift 465815
  have htrace : WordTrace (prefixWord ++ tailWord_465815) baseStart_465815 baseEnd_465815 := by
    simpa [prefixWord, tailWord_465815, baseEnd_465815] using wordTrace_append hprefix tailTrace_465815
  have hstable : (prefixWord ++ tailWord_465815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465815).length < 2 ^ (prefixWord ++ tailWord_465815).sum := by decide
  have hdescent : baseEnd_465815 < baseStart_465815 := by decide
  rcases family_descends (prefixWord ++ tailWord_465815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465853 : List Nat := [1, 4, 1, 2, 4, 2, 2, 1, 2, 3]
def baseStart_465853 : Nat := 118140960795 + 465853 * 2 ^ 59
def prefixEnd_465853 : Nat := 4983230072969 + 3 ^ 40 * 465853 * 2
def baseEnd_465853 : Nat := 159471002226047387796725

theorem tailTrace_465853 : CollatzResearch.WordTrace tailWord_465853 prefixEnd_465853 159471002226047387796725 := by
  unfold tailWord_465853
  simp only [CollatzResearch.WordTrace]
  refine ⟨16991054781301617203306213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11327369854201078135537475 16991054781301617203306213)
  ·
    refine ⟨3185822771494053225619915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16991054781301617203306213 3185822771494053225619915)
    ·
      refine ⟨4778734157241079838429873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3185822771494053225619915 4778734157241079838429873)
      ·
        refine ⟨3584050617930809878822405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4778734157241079838429873 3584050617930809878822405)
        ·
          refine ⟨672009490862026852279201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3584050617930809878822405 672009490862026852279201)
          ·
            refine ⟨504007118146520139209401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 672009490862026852279201 504007118146520139209401)
            ·
              refine ⟨378005338609890104407051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504007118146520139209401 378005338609890104407051)
              ·
                refine ⟨567008007914835156610577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378005338609890104407051 567008007914835156610577)
                ·
                  refine ⟨425256005936126367457933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 567008007914835156610577 425256005936126367457933)
                  ·
                    refine ⟨159471002226047387796725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 425256005936126367457933 159471002226047387796725)
                    ·
                      rfl

theorem cell22_465853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_465853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_465853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_465853 prefixEnd_465853 := by exact prefixLift 465853
  have htrace : WordTrace (prefixWord ++ tailWord_465853) baseStart_465853 baseEnd_465853 := by
    simpa [prefixWord, tailWord_465853, baseEnd_465853] using wordTrace_append hprefix tailTrace_465853
  have hstable : (prefixWord ++ tailWord_465853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465853).length < 2 ^ (prefixWord ++ tailWord_465853).sum := by decide
  have hdescent : baseEnd_465853 < baseStart_465853 := by decide
  rcases family_descends (prefixWord ++ tailWord_465853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465898 : List Nat := [3, 1, 3, 1, 2, 2, 4, 2, 1, 3]
def baseStart_465898 : Nat := 118140960795 + 465898 * 2 ^ 59
def prefixEnd_465898 : Nat := 4983230072969 + 3 ^ 40 * 465898 * 2
def baseEnd_465898 : Nat := 159486406645682270421587

theorem tailTrace_465898 : CollatzResearch.WordTrace tailWord_465898 prefixEnd_465898 159486406645682270421587 := by
  unfold tailWord_465898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4248174016534647472173587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11328464044092393259129565 4248174016534647472173587)
  ·
    refine ⟨6372261024801971208260381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4248174016534647472173587 6372261024801971208260381)
    ·
      refine ⟨2389597884300739203097643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6372261024801971208260381 2389597884300739203097643)
      ·
        refine ⟨3584396826451108804646465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2389597884300739203097643 3584396826451108804646465)
        ·
          refine ⟨2688297619838331603484849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3584396826451108804646465 2688297619838331603484849)
          ·
            refine ⟨2016223214878748702613637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2688297619838331603484849 2016223214878748702613637)
            ·
              refine ⟨378041852789765381740057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2016223214878748702613637 378041852789765381740057)
              ·
                refine ⟨283531389592324036305043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378041852789765381740057 283531389592324036305043)
                ·
                  refine ⟨425297084388486054457565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283531389592324036305043 425297084388486054457565)
                  ·
                    refine ⟨159486406645682270421587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 425297084388486054457565 159486406645682270421587)
                    ·
                      rfl

theorem cell22_465898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_465898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_465898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_465898 prefixEnd_465898 := by exact prefixLift 465898
  have htrace : WordTrace (prefixWord ++ tailWord_465898) baseStart_465898 baseEnd_465898 := by
    simpa [prefixWord, tailWord_465898, baseEnd_465898] using wordTrace_append hprefix tailTrace_465898
  have hstable : (prefixWord ++ tailWord_465898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465898).length < 2 ^ (prefixWord ++ tailWord_465898).sum := by decide
  have hdescent : baseEnd_465898 < baseStart_465898 := by decide
  rcases family_descends (prefixWord ++ tailWord_465898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465941 : List Nat := [1, 3, 2, 1, 4, 1, 4, 1, 1, 4]
def baseStart_465941 : Nat := 118140960795 + 465941 * 2 ^ 59
def prefixEnd_465941 : Nat := 4983230072969 + 3 ^ 40 * 465941 * 2
def baseEnd_465941 : Nat := 159501126424444491596455

theorem tailTrace_465941 : CollatzResearch.WordTrace tailWord_465941 prefixEnd_465941 159501126424444491596455 := by
  unfold tailWord_465941
  simp only [CollatzResearch.WordTrace]
  refine ⟨16994264404982808232509677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11329509603321872155006451 16994264404982808232509677)
  ·
    refine ⟨6372849151868553087191129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16994264404982808232509677 6372849151868553087191129)
    ·
      refine ⟨4779636863901414815393347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6372849151868553087191129 4779636863901414815393347)
      ·
        refine ⟨7169455295852122223090021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4779636863901414815393347 7169455295852122223090021)
        ·
          refine ⟨1344272867972272916829379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7169455295852122223090021 1344272867972272916829379)
          ·
            refine ⟨2016409301958409375244069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1344272867972272916829379 2016409301958409375244069)
            ·
              refine ⟨378076744117201757858263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2016409301958409375244069 378076744117201757858263)
              ·
                refine ⟨567115116175802636787395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378076744117201757858263 567115116175802636787395)
                ·
                  refine ⟨850672674263703955181093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567115116175802636787395 850672674263703955181093)
                  ·
                    refine ⟨159501126424444491596455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 850672674263703955181093 159501126424444491596455)
                    ·
                      rfl

theorem cell22_465941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_465941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_465941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_465941 prefixEnd_465941 := by exact prefixLift 465941
  have htrace : WordTrace (prefixWord ++ tailWord_465941) baseStart_465941 baseEnd_465941 := by
    simpa [prefixWord, tailWord_465941, baseEnd_465941] using wordTrace_append hprefix tailTrace_465941
  have hstable : (prefixWord ++ tailWord_465941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465941).length < 2 ^ (prefixWord ++ tailWord_465941).sum := by decide
  have hdescent : baseEnd_465941 < baseStart_465941 := by decide
  rcases family_descends (prefixWord ++ tailWord_465941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465956 : List Nat := [2, 3, 1, 4, 1, 1, 2, 4, 4]
def baseStart_465956 : Nat := 118140960795 + 465956 * 2 ^ 59
def prefixEnd_465956 : Nat := 4983230072969 + 3 ^ 40 * 465956 * 2
def baseEnd_465956 : Nat := 53168753743663150823803

theorem tailTrace_465956 : CollatzResearch.WordTrace tailWord_465956 prefixEnd_465956 53168753743663150823803 := by
  unfold tailWord_465956
  simp only [CollatzResearch.WordTrace]
  refine ⟨8497405749964232897152861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11329874333285643862870481 8497405749964232897152861)
  ·
    refine ⟨3186527156236587336432323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8497405749964232897152861 3186527156236587336432323)
    ·
      refine ⟨4779790734354881004648485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3186527156236587336432323 4779790734354881004648485)
      ·
        refine ⟨896210762691540188371591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4779790734354881004648485 896210762691540188371591)
        ·
          refine ⟨1344316144037310282557387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896210762691540188371591 1344316144037310282557387)
          ·
            refine ⟨2016474216055965423836081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1344316144037310282557387 2016474216055965423836081)
            ·
              refine ⟨1512355662041974067877061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2016474216055965423836081 1512355662041974067877061)
              ·
                refine ⟨283566686632870137726949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1512355662041974067877061 283566686632870137726949)
                ·
                  refine ⟨53168753743663150823803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 283566686632870137726949 53168753743663150823803)
                  ·
                    rfl

theorem cell22_465956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_465956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_465956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_465956 prefixEnd_465956 := by exact prefixLift 465956
  have htrace : WordTrace (prefixWord ++ tailWord_465956) baseStart_465956 baseEnd_465956 := by
    simpa [prefixWord, tailWord_465956, baseEnd_465956] using wordTrace_append hprefix tailTrace_465956
  have hstable : (prefixWord ++ tailWord_465956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465956).length < 2 ^ (prefixWord ++ tailWord_465956).sum := by decide
  have hdescent : baseEnd_465956 < baseStart_465956 := by decide
  rcases family_descends (prefixWord ++ tailWord_465956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465990 : List Nat := [6, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_465990 : Nat := 118140960795 + 465990 * 2 ^ 59
def prefixEnd_465990 : Nat := 4983230072969 + 3 ^ 40 * 465990 * 2
def baseEnd_465990 : Nat := 53172633375274899040435

theorem tailTrace_465990 : CollatzResearch.WordTrace tailWord_465990 prefixEnd_465990 53172633375274899040435 := by
  unfold tailWord_465990
  simp only [CollatzResearch.WordTrace]
  refine ⟨531126611931415300032607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11330701054536859734028949 531126611931415300032607)
  ·
    refine ⟨796689917897122950048911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 531126611931415300032607 796689917897122950048911)
    ·
      refine ⟨1195034876845684425073367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 796689917897122950048911 1195034876845684425073367)
      ·
        refine ⟨1792552315268526637610051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1195034876845684425073367 1792552315268526637610051)
        ·
          refine ⟨2688828472902789956415077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1792552315268526637610051 2688828472902789956415077)
          ·
            refine ⟨504155338669273116827827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2688828472902789956415077 504155338669273116827827)
            ·
              refine ⟨756233008003909675241741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504155338669273116827827 756233008003909675241741)
              ·
                refine ⟨283587378001466128215653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 756233008003909675241741 283587378001466128215653)
                ·
                  refine ⟨53172633375274899040435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 283587378001466128215653 53172633375274899040435)
                  ·
                    rfl

theorem cell22_465990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_465990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_465990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_465990 prefixEnd_465990 := by exact prefixLift 465990
  have htrace : WordTrace (prefixWord ++ tailWord_465990) baseStart_465990 baseEnd_465990 := by
    simpa [prefixWord, tailWord_465990, baseEnd_465990] using wordTrace_append hprefix tailTrace_465990
  have hstable : (prefixWord ++ tailWord_465990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465990).length < 2 ^ (prefixWord ++ tailWord_465990).sum := by decide
  have hdescent : baseEnd_465990 < baseStart_465990 := by decide
  rcases family_descends (prefixWord ++ tailWord_465990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466059 : List Nat := [1, 1, 1, 1, 4, 1, 1, 7, 1, 4]
def baseStart_466059 : Nat := 118140960795 + 466059 * 2 ^ 59
def prefixEnd_466059 : Nat := 4983230072969 + 3 ^ 40 * 466059 * 2
def baseEnd_466059 : Nat := 159541520235931517146093

theorem tailTrace_466059 : CollatzResearch.WordTrace tailWord_466059 prefixEnd_466059 159541520235931517146093 := by
  unfold tailWord_466059
  simp only [CollatzResearch.WordTrace]
  refine ⟨16998568218555314385305231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11332378812370209590203487 16998568218555314385305231)
  ·
    refine ⟨25497852327832971577957847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16998568218555314385305231 25497852327832971577957847)
    ·
      refine ⟨38246778491749457366936771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25497852327832971577957847 38246778491749457366936771)
      ·
        refine ⟨57370167737624186050405157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38246778491749457366936771 57370167737624186050405157)
        ·
          refine ⟨10756906450804534884450967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57370167737624186050405157 10756906450804534884450967)
          ·
            refine ⟨16135359676206802326676451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10756906450804534884450967 16135359676206802326676451)
            ·
              refine ⟨24203039514310203490014677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16135359676206802326676451 24203039514310203490014677)
              ·
                refine ⟨567258738616645394297219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24203039514310203490014677 567258738616645394297219)
                ·
                  refine ⟨850888107924968091445829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567258738616645394297219 850888107924968091445829)
                  ·
                    refine ⟨159541520235931517146093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 850888107924968091445829 159541520235931517146093)
                    ·
                      rfl

theorem cell22_466059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 4].length) (baseStart_466059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466059 prefixEnd_466059 := by exact prefixLift 466059
  have htrace : WordTrace (prefixWord ++ tailWord_466059) baseStart_466059 baseEnd_466059 := by
    simpa [prefixWord, tailWord_466059, baseEnd_466059] using wordTrace_append hprefix tailTrace_466059
  have hstable : (prefixWord ++ tailWord_466059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466059).length < 2 ^ (prefixWord ++ tailWord_466059).sum := by decide
  have hdescent : baseEnd_466059 < baseStart_466059 := by decide
  rcases family_descends (prefixWord ++ tailWord_466059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466104 : List Nat := [2, 1, 2, 1, 2, 1, 2, 5, 2, 4]
def baseStart_466104 : Nat := 118140960795 + 466104 * 2 ^ 59
def prefixEnd_466104 : Nat := 4983230072969 + 3 ^ 40 * 466104 * 2
def baseEnd_466104 : Nat := 159556924655566399770955

theorem tailTrace_466104 : CollatzResearch.WordTrace tailWord_466104 prefixEnd_466104 159556924655566399770955 := by
  unfold tailWord_466104
  simp only [CollatzResearch.WordTrace]
  refine ⟨8500104751696143535346683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11333473002261524713795577 8500104751696143535346683)
  ·
    refine ⟨12750157127544215303020025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8500104751696143535346683 12750157127544215303020025)
    ·
      refine ⟨9562617845658161477265019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12750157127544215303020025 9562617845658161477265019)
      ·
        refine ⟨14343926768487242215897529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9562617845658161477265019 14343926768487242215897529)
        ·
          refine ⟨10757945076365431661923147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14343926768487242215897529 10757945076365431661923147)
          ·
            refine ⟨16136917614548147492884721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10757945076365431661923147 16136917614548147492884721)
            ·
              refine ⟨12102688210911110619663541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16136917614548147492884721 12102688210911110619663541)
              ·
                refine ⟨1134627019772916620593457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12102688210911110619663541 1134627019772916620593457)
                ·
                  refine ⟨850970264829687465445093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1134627019772916620593457 850970264829687465445093)
                  ·
                    refine ⟨159556924655566399770955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 850970264829687465445093 159556924655566399770955)
                    ·
                      rfl

theorem cell22_466104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_466104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466104 prefixEnd_466104 := by exact prefixLift 466104
  have htrace : WordTrace (prefixWord ++ tailWord_466104) baseStart_466104 baseEnd_466104 := by
    simpa [prefixWord, tailWord_466104, baseEnd_466104] using wordTrace_append hprefix tailTrace_466104
  have hstable : (prefixWord ++ tailWord_466104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466104).length < 2 ^ (prefixWord ++ tailWord_466104).sum := by decide
  have hdescent : baseEnd_466104 < baseStart_466104 := by decide
  rcases family_descends (prefixWord ++ tailWord_466104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466108 : List Nat := [2, 2, 2, 3, 2, 2, 2, 3, 4]
def baseStart_466108 : Nat := 118140960795 + 466108 * 2 ^ 59
def prefixEnd_466108 : Nat := 4983230072969 + 3 ^ 40 * 466108 * 2
def baseEnd_466108 : Nat := 53186097979103907556981

theorem tailTrace_466108 : CollatzResearch.WordTrace tailWord_466108 prefixEnd_466108 53186097979103907556981 := by
  unfold tailWord_466108
  simp only [CollatzResearch.WordTrace]
  refine ⟨8500177697688897876919489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11333570263585197169225985 8500177697688897876919489)
  ·
    refine ⟨6375133273266673407689617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8500177697688897876919489 6375133273266673407689617)
    ·
      refine ⟨4781349954950005055767213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6375133273266673407689617 4781349954950005055767213)
      ·
        refine ⟨1793006233106251895912705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4781349954950005055767213 1793006233106251895912705)
        ·
          refine ⟨1344754674829688921934529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1793006233106251895912705 1344754674829688921934529)
          ·
            refine ⟨1008566006122266691450897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1344754674829688921934529 1008566006122266691450897)
            ·
              refine ⟨756424504591700018588173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1008566006122266691450897 756424504591700018588173)
              ·
                refine ⟨283659189221887506970565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 756424504591700018588173 283659189221887506970565)
                ·
                  refine ⟨53186097979103907556981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 283659189221887506970565 53186097979103907556981)
                  ·
                    rfl

theorem cell22_466108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_466108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466108 prefixEnd_466108 := by exact prefixLift 466108
  have htrace : WordTrace (prefixWord ++ tailWord_466108) baseStart_466108 baseEnd_466108 := by
    simpa [prefixWord, tailWord_466108, baseEnd_466108] using wordTrace_append hprefix tailTrace_466108
  have hstable : (prefixWord ++ tailWord_466108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466108).length < 2 ^ (prefixWord ++ tailWord_466108).sum := by decide
  have hdescent : baseEnd_466108 < baseStart_466108 := by decide
  rcases family_descends (prefixWord ++ tailWord_466108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466110 : List Nat := [4, 2, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_466110 : Nat := 118140960795 + 466110 * 2 ^ 59
def prefixEnd_466110 : Nat := 4983230072969 + 3 ^ 40 * 466110 * 2
def baseEnd_466110 : Nat := 159558978578184384120937

theorem tailTrace_466110 : CollatzResearch.WordTrace tailWord_466110 prefixEnd_466110 159558978578184384120937 := by
  unfold tailWord_466110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2125053542671318761926473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11333618894247033396941189 2125053542671318761926473)
  ·
    refine ⟨1593790157003489071444855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2125053542671318761926473 1593790157003489071444855)
    ·
      refine ⟨2390685235505233607167283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1593790157003489071444855 2390685235505233607167283)
      ·
        refine ⟨3586027853257850410750925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2390685235505233607167283 3586027853257850410750925)
        ·
          refine ⟨1344760444971693904031597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3586027853257850410750925 1344760444971693904031597)
          ·
            refine ⟨504285166864385214011849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1344760444971693904031597 504285166864385214011849)
            ·
              refine ⟨378213875148288910508887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504285166864385214011849 378213875148288910508887)
              ·
                refine ⟨567320812722433365763331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378213875148288910508887 567320812722433365763331)
                ·
                  refine ⟨850981219083650048644997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567320812722433365763331 850981219083650048644997)
                  ·
                    refine ⟨159558978578184384120937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 850981219083650048644997 159558978578184384120937)
                    ·
                      rfl

theorem cell22_466110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_466110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466110 prefixEnd_466110 := by exact prefixLift 466110
  have htrace : WordTrace (prefixWord ++ tailWord_466110) baseStart_466110 baseEnd_466110 := by
    simpa [prefixWord, tailWord_466110, baseEnd_466110] using wordTrace_append hprefix tailTrace_466110
  have hstable : (prefixWord ++ tailWord_466110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466110).length < 2 ^ (prefixWord ++ tailWord_466110).sum := by decide
  have hdescent : baseEnd_466110 < baseStart_466110 := by decide
  rcases family_descends (prefixWord ++ tailWord_466110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466125 : List Nat := [1, 6, 2, 2, 1, 1, 2, 1, 6]
def baseStart_466125 : Nat := 118140960795 + 466125 * 2 ^ 59
def prefixEnd_466125 : Nat := 4983230072969 + 3 ^ 40 * 466125 * 2
def baseEnd_466125 : Nat := 53188037794909781665297

theorem tailTrace_466125 : CollatzResearch.WordTrace tailWord_466125 prefixEnd_466125 53188037794909781665297 := by
  unfold tailWord_466125
  simp only [CollatzResearch.WordTrace]
  refine ⟨17000975436316207657207829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11333983624210805104805219 17000975436316207657207829)
  ·
    refine ⟨796920723577322233931617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17000975436316207657207829 796920723577322233931617)
    ·
      refine ⟨597690542682991675448713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 796920723577322233931617 597690542682991675448713)
      ·
        refine ⟨448267907012243756586535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597690542682991675448713 448267907012243756586535)
        ·
          refine ⟨672401860518365634879803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448267907012243756586535 672401860518365634879803)
          ·
            refine ⟨1008602790777548452319705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672401860518365634879803 1008602790777548452319705)
            ·
              refine ⟨756452093083161339239779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1008602790777548452319705 756452093083161339239779)
              ·
                refine ⟨1134678139624742008859669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756452093083161339239779 1134678139624742008859669)
                ·
                  refine ⟨53188037794909781665297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1134678139624742008859669 53188037794909781665297)
                  ·
                    rfl

theorem cell22_466125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_466125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466125 prefixEnd_466125 := by exact prefixLift 466125
  have htrace : WordTrace (prefixWord ++ tailWord_466125) baseStart_466125 baseEnd_466125 := by
    simpa [prefixWord, tailWord_466125, baseEnd_466125] using wordTrace_append hprefix tailTrace_466125
  have hstable : (prefixWord ++ tailWord_466125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466125).length < 2 ^ (prefixWord ++ tailWord_466125).sum := by decide
  have hdescent : baseEnd_466125 < baseStart_466125 := by decide
  rcases family_descends (prefixWord ++ tailWord_466125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466185 : List Nat := [1, 2, 1, 1, 3, 3, 5, 2, 1, 3]
def baseStart_466185 : Nat := 118140960795 + 466185 * 2 ^ 59
def prefixEnd_466185 : Nat := 4983230072969 + 3 ^ 40 * 466185 * 2
def baseEnd_466185 : Nat := 159584652610909188495707

theorem tailTrace_466185 : CollatzResearch.WordTrace tailWord_466185 prefixEnd_466185 159584652610909188495707 := by
  unfold tailWord_466185
  simp only [CollatzResearch.WordTrace]
  refine ⟨17003163816098837904392009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11335442544065891936261339 17003163816098837904392009)
  ·
    refine ⟨12752372862074128428294007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17003163816098837904392009 12752372862074128428294007)
    ·
      refine ⟨19128559293111192642441011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12752372862074128428294007 19128559293111192642441011)
      ·
        refine ⟨28692838939666788963661517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19128559293111192642441011 28692838939666788963661517)
        ·
          refine ⟨10759814602375045861373069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28692838939666788963661517 10759814602375045861373069)
          ·
            refine ⟨4034930475890642198014901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10759814602375045861373069 4034930475890642198014901)
            ·
              refine ⟨378274732114747706063897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4034930475890642198014901 378274732114747706063897)
              ·
                refine ⟨283706049086060779547923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378274732114747706063897 283706049086060779547923)
                ·
                  refine ⟨425559073629091169321885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283706049086060779547923 425559073629091169321885)
                  ·
                    refine ⟨159584652610909188495707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 425559073629091169321885 159584652610909188495707)
                    ·
                      rfl

theorem cell22_466185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 1, 3].length) (baseStart_466185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466185 prefixEnd_466185 := by exact prefixLift 466185
  have htrace : WordTrace (prefixWord ++ tailWord_466185) baseStart_466185 baseEnd_466185 := by
    simpa [prefixWord, tailWord_466185, baseEnd_466185] using wordTrace_append hprefix tailTrace_466185
  have hstable : (prefixWord ++ tailWord_466185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466185).length < 2 ^ (prefixWord ++ tailWord_466185).sum := by decide
  have hdescent : baseEnd_466185 < baseStart_466185 := by decide
  rcases family_descends (prefixWord ++ tailWord_466185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466209 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 8]
def baseStart_466209 : Nat := 118140960795 + 466209 * 2 ^ 59
def prefixEnd_466209 : Nat := 4983230072969 + 3 ^ 40 * 466209 * 2
def baseEnd_466209 : Nat := 53197622767127041965211

theorem tailTrace_466209 : CollatzResearch.WordTrace tailWord_466209 prefixEnd_466209 53197622767127041965211 := by
  unfold tailWord_466209
  simp only [CollatzResearch.WordTrace]
  refine ⟨17004039168011890003265681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11336026112007926668843787 17004039168011890003265681)
  ·
    refine ⟨12753029376008917502449261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17004039168011890003265681 12753029376008917502449261)
    ·
      refine ⟨4782386016003344063418473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12753029376008917502449261 4782386016003344063418473)
      ·
        refine ⟨3586789512002508047563855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4782386016003344063418473 3586789512002508047563855)
        ·
          refine ⟨5380184268003762071345783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3586789512002508047563855 5380184268003762071345783)
          ·
            refine ⟨8070276402005643107018675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5380184268003762071345783 8070276402005643107018675)
            ·
              refine ⟨12105414603008464660528013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8070276402005643107018675 12105414603008464660528013)
              ·
                refine ⟨4539530476128174247698005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12105414603008464660528013 4539530476128174247698005)
                ·
                  refine ⟨53197622767127041965211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4539530476128174247698005 53197622767127041965211)
                  ·
                    rfl

theorem cell22_466209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 8].length) (baseStart_466209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466209 prefixEnd_466209 := by exact prefixLift 466209
  have htrace : WordTrace (prefixWord ++ tailWord_466209) baseStart_466209 baseEnd_466209 := by
    simpa [prefixWord, tailWord_466209, baseEnd_466209] using wordTrace_append hprefix tailTrace_466209
  have hstable : (prefixWord ++ tailWord_466209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466209).length < 2 ^ (prefixWord ++ tailWord_466209).sum := by decide
  have hdescent : baseEnd_466209 < baseStart_466209 := by decide
  rcases family_descends (prefixWord ++ tailWord_466209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466211 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 3, 4]
def baseStart_466211 : Nat := 118140960795 + 466211 * 2 ^ 59
def prefixEnd_466211 : Nat := 4983230072969 + 3 ^ 40 * 466211 * 2
def baseEnd_466211 : Nat := 159593552942253787345627

theorem tailTrace_466211 : CollatzResearch.WordTrace tailWord_466211 prefixEnd_466211 159593552942253787345627 := by
  unfold tailWord_466211
  simp only [CollatzResearch.WordTrace]
  refine ⟨17004112114004644344838487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11336074742669762896558991 17004112114004644344838487)
  ·
    refine ⟨25506168171006966517257731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17004112114004644344838487 25506168171006966517257731)
    ·
      refine ⟨38259252256510449775886597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25506168171006966517257731 38259252256510449775886597)
      ·
        refine ⟨7173609798095709332978737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38259252256510449775886597 7173609798095709332978737)
        ·
          refine ⟨5380207348571781999734053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7173609798095709332978737 5380207348571781999734053)
          ·
            refine ⟨1008788877857209124950135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5380207348571781999734053 1008788877857209124950135)
            ·
              refine ⟨1513183316785813687425203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008788877857209124950135 1513183316785813687425203)
              ·
                refine ⟨2269774975178720531137805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1513183316785813687425203 2269774975178720531137805)
                ·
                  refine ⟨851165615692020199176677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2269774975178720531137805 851165615692020199176677)
                  ·
                    refine ⟨159593552942253787345627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 851165615692020199176677 159593552942253787345627)
                    ·
                      rfl

theorem cell22_466211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 4].length) (baseStart_466211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466211 prefixEnd_466211 := by exact prefixLift 466211
  have htrace : WordTrace (prefixWord ++ tailWord_466211) baseStart_466211 baseEnd_466211 := by
    simpa [prefixWord, tailWord_466211, baseEnd_466211] using wordTrace_append hprefix tailTrace_466211
  have hstable : (prefixWord ++ tailWord_466211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466211).length < 2 ^ (prefixWord ++ tailWord_466211).sum := by decide
  have hdescent : baseEnd_466211 < baseStart_466211 := by decide
  rcases family_descends (prefixWord ++ tailWord_466211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466322 : List Nat := [3, 2, 3, 3, 1, 2, 2, 6]
def baseStart_466322 : Nat := 118140960795 + 466322 * 2 ^ 59
def prefixEnd_466322 : Nat := 4983230072969 + 3 ^ 40 * 466322 * 2
def baseEnd_466322 : Nat := 17736838945631833091143

theorem tailTrace_466322 : CollatzResearch.WordTrace tailWord_466322 prefixEnd_466322 17736838945631833091143 := by
  unfold tailWord_466322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4252040154150627575532305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11338773744401673534752813 4252040154150627575532305)
  ·
    refine ⟨3189030115612970681649229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4252040154150627575532305 3189030115612970681649229)
    ·
      refine ⟨1195886293354864005618461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3189030115612970681649229 1195886293354864005618461)
      ·
        refine ⟨448457360008074002106923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1195886293354864005618461 448457360008074002106923)
        ·
          refine ⟨672686040012111003160385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448457360008074002106923 672686040012111003160385)
          ·
            refine ⟨504514530009083252370289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 672686040012111003160385 504514530009083252370289)
            ·
              refine ⟨378385897506812439277717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504514530009083252370289 378385897506812439277717)
              ·
                refine ⟨17736838945631833091143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 378385897506812439277717 17736838945631833091143)
                ·
                  rfl

theorem cell22_466322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 6].length) (baseStart_466322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466322 prefixEnd_466322 := by exact prefixLift 466322
  have htrace : WordTrace (prefixWord ++ tailWord_466322) baseStart_466322 baseEnd_466322 := by
    simpa [prefixWord, tailWord_466322, baseEnd_466322] using wordTrace_append hprefix tailTrace_466322
  have hstable : (prefixWord ++ tailWord_466322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466322).length < 2 ^ (prefixWord ++ tailWord_466322).sum := by decide
  have hdescent : baseEnd_466322 < baseStart_466322 := by decide
  rcases family_descends (prefixWord ++ tailWord_466322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466380 : List Nat := [2, 2, 1, 4, 2, 1, 3, 2, 1, 4]
def baseStart_466380 : Nat := 118140960795 + 466380 * 2 ^ 59
def prefixEnd_466380 : Nat := 4983230072969 + 3 ^ 40 * 466380 * 2
def baseEnd_466380 : Nat := 159651405095993679870109

theorem tailTrace_466380 : CollatzResearch.WordTrace tailWord_466380 prefixEnd_466380 159651405095993679870109 := by
  unfold tailWord_466380
  simp only [CollatzResearch.WordTrace]
  refine ⟨8505138025196193103870297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11340184033594924138493729 8505138025196193103870297)
  ·
    refine ⟨6378853518897144827902723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8505138025196193103870297 6378853518897144827902723)
    ·
      refine ⟨9568280278345717241854085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6378853518897144827902723 9568280278345717241854085)
      ·
        refine ⟨1794052552189821982847641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9568280278345717241854085 1794052552189821982847641)
        ·
          refine ⟨1345539414142366487135731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1794052552189821982847641 1345539414142366487135731)
          ·
            refine ⟨2018309121213549730703597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345539414142366487135731 2018309121213549730703597)
            ·
              refine ⟨756865920455081149013849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2018309121213549730703597 756865920455081149013849)
              ·
                refine ⟨567649440341310861760387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 756865920455081149013849 567649440341310861760387)
                ·
                  refine ⟨851474160511966292640581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567649440341310861760387 851474160511966292640581)
                  ·
                    refine ⟨159651405095993679870109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 851474160511966292640581 159651405095993679870109)
                    ·
                      rfl

theorem cell22_466380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_466380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466380 prefixEnd_466380 := by exact prefixLift 466380
  have htrace : WordTrace (prefixWord ++ tailWord_466380) baseStart_466380 baseEnd_466380 := by
    simpa [prefixWord, tailWord_466380, baseEnd_466380] using wordTrace_append hprefix tailTrace_466380
  have hstable : (prefixWord ++ tailWord_466380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466380).length < 2 ^ (prefixWord ++ tailWord_466380).sum := by decide
  have hdescent : baseEnd_466380 < baseStart_466380 := by decide
  rcases family_descends (prefixWord ++ tailWord_466380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466391 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 1, 6]
def baseStart_466391 : Nat := 118140960795 + 466391 * 2 ^ 59
def prefixEnd_466391 : Nat := 4983230072969 + 3 ^ 40 * 466391 * 2
def baseEnd_466391 : Nat := 159655170620793317845075

theorem tailTrace_466391 : CollatzResearch.WordTrace tailWord_466391 prefixEnd_466391 159655170620793317845075 := by
  unfold tailWord_466391
  simp only [CollatzResearch.WordTrace]
  refine ⟨17010677253352535086391027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11340451502235023390927351 17010677253352535086391027)
  ·
    refine ⟨25516015880028802629586541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17010677253352535086391027 25516015880028802629586541)
    ·
      refine ⟨9568505955010800986094953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25516015880028802629586541 9568505955010800986094953)
      ·
        refine ⟨7176379466258100739571215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9568505955010800986094953 7176379466258100739571215)
        ·
          refine ⟨10764569199387151109356823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7176379466258100739571215 10764569199387151109356823)
          ·
            refine ⟨16146853799080726664035235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10764569199387151109356823 16146853799080726664035235)
            ·
              refine ⟨24220280698621089996052853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16146853799080726664035235 24220280698621089996052853)
              ·
                refine ⟨2270651315495727187129955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24220280698621089996052853 2270651315495727187129955)
                ·
                  refine ⟨3405976973243590780694933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2270651315495727187129955 3405976973243590780694933)
                  ·
                    refine ⟨159655170620793317845075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3405976973243590780694933 159655170620793317845075)
                    ·
                      rfl

theorem cell22_466391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_466391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466391 prefixEnd_466391 := by exact prefixLift 466391
  have htrace : WordTrace (prefixWord ++ tailWord_466391) baseStart_466391 baseEnd_466391 := by
    simpa [prefixWord, tailWord_466391, baseEnd_466391] using wordTrace_append hprefix tailTrace_466391
  have hstable : (prefixWord ++ tailWord_466391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466391).length < 2 ^ (prefixWord ++ tailWord_466391).sum := by decide
  have hdescent : baseEnd_466391 < baseStart_466391 := by decide
  rcases family_descends (prefixWord ++ tailWord_466391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466393 : List Nat := [1, 2, 1, 2, 4, 3, 1, 2, 1, 5]
def baseStart_466393 : Nat := 118140960795 + 466393 * 2 ^ 59
def prefixEnd_466393 : Nat := 4983230072969 + 3 ^ 40 * 466393 * 2
def baseEnd_466393 : Nat := 159655855261665979295069

theorem tailTrace_466393 : CollatzResearch.WordTrace tailWord_466393 prefixEnd_466393 159655855261665979295069 := by
  unfold tailWord_466393
  simp only [CollatzResearch.WordTrace]
  refine ⟨17010750199345289427963833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11340500132896859618642555 17010750199345289427963833)
  ·
    refine ⟨12758062649508967070972875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17010750199345289427963833 12758062649508967070972875)
    ·
      refine ⟨19137093974263450606459313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12758062649508967070972875 19137093974263450606459313)
      ·
        refine ⟨14352820480697587954844485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19137093974263450606459313 14352820480697587954844485)
        ·
          refine ⟨2691153840130797741533341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14352820480697587954844485 2691153840130797741533341)
          ·
            refine ⟨1009182690049049153075003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2691153840130797741533341 1009182690049049153075003)
            ·
              refine ⟨1513774035073573729612505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009182690049049153075003 1513774035073573729612505)
              ·
                refine ⟨1135330526305180297209379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1513774035073573729612505 1135330526305180297209379)
                ·
                  refine ⟨1702995789457770445814069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1135330526305180297209379 1702995789457770445814069)
                  ·
                    refine ⟨159655855261665979295069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1702995789457770445814069 159655855261665979295069)
                    ·
                      rfl

theorem cell22_466393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_466393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466393 prefixEnd_466393 := by exact prefixLift 466393
  have htrace : WordTrace (prefixWord ++ tailWord_466393) baseStart_466393 baseEnd_466393 := by
    simpa [prefixWord, tailWord_466393, baseEnd_466393] using wordTrace_append hprefix tailTrace_466393
  have hstable : (prefixWord ++ tailWord_466393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466393).length < 2 ^ (prefixWord ++ tailWord_466393).sum := by decide
  have hdescent : baseEnd_466393 < baseStart_466393 := by decide
  rcases family_descends (prefixWord ++ tailWord_466393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466397 : List Nat := [1, 4, 3, 1, 1, 3, 3, 1, 1, 4]
def baseStart_466397 : Nat := 118140960795 + 466397 * 2 ^ 59
def prefixEnd_466397 : Nat := 4983230072969 + 3 ^ 40 * 466397 * 2
def baseEnd_466397 : Nat := 159657224543411302195057

theorem tailTrace_466397 : CollatzResearch.WordTrace tailWord_466397 prefixEnd_466397 159657224543411302195057 := by
  unfold tailWord_466397
  simp only [CollatzResearch.WordTrace]
  refine ⟨17010896091330798111109445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11340597394220532074072963 17010896091330798111109445)
  ·
    refine ⟨3189543017124524645833021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17010896091330798111109445 3189543017124524645833021)
    ·
      refine ⟨1196078631421696742187383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3189543017124524645833021 1196078631421696742187383)
      ·
        refine ⟨1794117947132545113281075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1196078631421696742187383 1794117947132545113281075)
        ·
          refine ⟨2691176920698817669921613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1794117947132545113281075 2691176920698817669921613)
          ·
            refine ⟨1009191345262056626220605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2691176920698817669921613 1009191345262056626220605)
            ·
              refine ⟨378446754473271234832727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1009191345262056626220605 378446754473271234832727)
              ·
                refine ⟨567670131709906852249091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378446754473271234832727 567670131709906852249091)
                ·
                  refine ⟨851505197564860278373637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567670131709906852249091 851505197564860278373637)
                  ·
                    refine ⟨159657224543411302195057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 851505197564860278373637 159657224543411302195057)
                    ·
                      rfl

theorem cell22_466397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_466397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466397 prefixEnd_466397 := by exact prefixLift 466397
  have htrace : WordTrace (prefixWord ++ tailWord_466397) baseStart_466397 baseEnd_466397 := by
    simpa [prefixWord, tailWord_466397, baseEnd_466397] using wordTrace_append hprefix tailTrace_466397
  have hstable : (prefixWord ++ tailWord_466397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466397).length < 2 ^ (prefixWord ++ tailWord_466397).sum := by decide
  have hdescent : baseEnd_466397 < baseStart_466397 := by decide
  rcases family_descends (prefixWord ++ tailWord_466397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466408 : List Nat := [2, 1, 4, 1, 1, 2, 1, 4, 2, 4]
def baseStart_466408 : Nat := 118140960795 + 466408 * 2 ^ 59
def prefixEnd_466408 : Nat := 4983230072969 + 3 ^ 40 * 466408 * 2
def baseEnd_466408 : Nat := 159660990068210940170023

theorem tailTrace_466408 : CollatzResearch.WordTrace tailWord_466408 prefixEnd_466408 159660990068210940170023 := by
  unfold tailWord_466408
  simp only [CollatzResearch.WordTrace]
  refine ⟨8505648647145473494879939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11340864862860631326506585 8505648647145473494879939)
  ·
    refine ⟨12758472970718210242319909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8505648647145473494879939 12758472970718210242319909)
    ·
      refine ⟨2392213682009664420434983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12758472970718210242319909 2392213682009664420434983)
      ·
        refine ⟨3588320523014496630652475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2392213682009664420434983 3588320523014496630652475)
        ·
          refine ⟨5382480784521744945978713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3588320523014496630652475 5382480784521744945978713)
          ·
            refine ⟨4036860588391308709484035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5382480784521744945978713 4036860588391308709484035)
            ·
              refine ⟨6055290882586963064226053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4036860588391308709484035 6055290882586963064226053)
              ·
                refine ⟨1135367040485055574542385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6055290882586963064226053 1135367040485055574542385)
                ·
                  refine ⟨851525280363791680906789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1135367040485055574542385 851525280363791680906789)
                  ·
                    refine ⟨159660990068210940170023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 851525280363791680906789 159660990068210940170023)
                    ·
                      rfl

theorem cell22_466408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_466408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466408 prefixEnd_466408 := by exact prefixLift 466408
  have htrace : WordTrace (prefixWord ++ tailWord_466408) baseStart_466408 baseEnd_466408 := by
    simpa [prefixWord, tailWord_466408, baseEnd_466408] using wordTrace_append hprefix tailTrace_466408
  have hstable : (prefixWord ++ tailWord_466408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466408).length < 2 ^ (prefixWord ++ tailWord_466408).sum := by decide
  have hdescent : baseEnd_466408 < baseStart_466408 := by decide
  rcases family_descends (prefixWord ++ tailWord_466408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466483 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 2, 5]
def baseStart_466483 : Nat := 118140960795 + 466483 * 2 ^ 59
def prefixEnd_466483 : Nat := 4983230072969 + 3 ^ 40 * 466483 * 2
def baseEnd_466483 : Nat := 159686664100935744544793

theorem tailTrace_466483 : CollatzResearch.WordTrace tailWord_466483 prefixEnd_466483 159686664100935744544793 := by
  unfold tailWord_466483
  simp only [CollatzResearch.WordTrace]
  refine ⟨17014032769019234798740103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11342688512679489865826735 17014032769019234798740103)
  ·
    refine ⟨25521049153528852198110155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17014032769019234798740103 25521049153528852198110155)
    ·
      refine ⟨38281573730293278297165233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25521049153528852198110155 38281573730293278297165233)
      ·
        refine ⟨28711180297719958722873925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38281573730293278297165233 28711180297719958722873925)
        ·
          refine ⟨5383346305822492260538861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28711180297719958722873925 5383346305822492260538861)
          ·
            refine ⟨2018754864683434597702073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5383346305822492260538861 2018754864683434597702073)
            ·
              refine ⟨1514066148512575948276555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2018754864683434597702073 1514066148512575948276555)
              ·
                refine ⟨2271099222768863922414833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1514066148512575948276555 2271099222768863922414833)
                ·
                  refine ⟨1703324417076647941811125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2271099222768863922414833 1703324417076647941811125)
                  ·
                    refine ⟨159686664100935744544793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1703324417076647941811125 159686664100935744544793)
                    ·
                      rfl

theorem cell22_466483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 5].length) (baseStart_466483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466483 prefixEnd_466483 := by exact prefixLift 466483
  have htrace : WordTrace (prefixWord ++ tailWord_466483) baseStart_466483 baseEnd_466483 := by
    simpa [prefixWord, tailWord_466483, baseEnd_466483] using wordTrace_append hprefix tailTrace_466483
  have hstable : (prefixWord ++ tailWord_466483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466483).length < 2 ^ (prefixWord ++ tailWord_466483).sum := by decide
  have hdescent : baseEnd_466483 < baseStart_466483 := by decide
  rcases family_descends (prefixWord ++ tailWord_466483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466543 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 6, 4]
def baseStart_466543 : Nat := 118140960795 + 466543 * 2 ^ 59
def prefixEnd_466543 : Nat := 4983230072969 + 3 ^ 40 * 466543 * 2
def baseEnd_466543 : Nat := 159707203327115588044609

theorem tailTrace_466543 : CollatzResearch.WordTrace tailWord_466543 prefixEnd_466543 159707203327115588044609 := by
  unfold tailWord_466543
  simp only [CollatzResearch.WordTrace]
  refine ⟨17016221148801865045924283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11344147432534576697282855 17016221148801865045924283)
  ·
    refine ⟨25524331723202797568886425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17016221148801865045924283 25524331723202797568886425)
    ·
      refine ⟨19143248792402098176664819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25524331723202797568886425 19143248792402098176664819)
      ·
        refine ⟨28714873188603147264997229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19143248792402098176664819 28714873188603147264997229)
        ·
          refine ⟨10768077445726180224373961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28714873188603147264997229 10768077445726180224373961)
          ·
            refine ⟨8076058084294635168280471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10768077445726180224373961 8076058084294635168280471)
            ·
              refine ⟨12114087126441952752420707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8076058084294635168280471 12114087126441952752420707)
              ·
                refine ⟨18171130689662929128631061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12114087126441952752420707 18171130689662929128631061)
                ·
                  refine ⟨851771751077949802904581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18171130689662929128631061 851771751077949802904581)
                  ·
                    refine ⟨159707203327115588044609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 851771751077949802904581 159707203327115588044609)
                    ·
                      rfl

theorem cell22_466543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_466543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466543 prefixEnd_466543 := by exact prefixLift 466543
  have htrace : WordTrace (prefixWord ++ tailWord_466543) baseStart_466543 baseEnd_466543 := by
    simpa [prefixWord, tailWord_466543, baseEnd_466543] using wordTrace_append hprefix tailTrace_466543
  have hstable : (prefixWord ++ tailWord_466543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466543).length < 2 ^ (prefixWord ++ tailWord_466543).sum := by decide
  have hdescent : baseEnd_466543 < baseStart_466543 := by decide
  rcases family_descends (prefixWord ++ tailWord_466543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466549 : List Nat := [1, 3, 4, 2, 1, 3, 1, 2, 1, 4]
def baseStart_466549 : Nat := 118140960795 + 466549 * 2 ^ 59
def prefixEnd_466549 : Nat := 4983230072969 + 3 ^ 40 * 466549 * 2
def baseEnd_466549 : Nat := 159709257249733572394591

theorem tailTrace_466549 : CollatzResearch.WordTrace tailWord_466549 prefixEnd_466549 159709257249733572394591 := by
  unfold tailWord_466549
  simp only [CollatzResearch.WordTrace]
  refine ⟨17016439986780128070642701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11344293324520085380428467 17016439986780128070642701)
  ·
    refine ⟨6381164995042548026491013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17016439986780128070642701 6381164995042548026491013)
    ·
      refine ⟨1196468436570477754967065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6381164995042548026491013 1196468436570477754967065)
      ·
        refine ⟨897351327427858316225299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1196468436570477754967065 897351327427858316225299)
        ·
          refine ⟨1346026991141787474337949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897351327427858316225299 1346026991141787474337949)
          ·
            refine ⟨504760121678170302876731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1346026991141787474337949 504760121678170302876731)
            ·
              refine ⟨757140182517255454315097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504760121678170302876731 757140182517255454315097)
              ·
                refine ⟨567855136887941590736323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 757140182517255454315097 567855136887941590736323)
                ·
                  refine ⟨851782705331912386104485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567855136887941590736323 851782705331912386104485)
                  ·
                    refine ⟨159709257249733572394591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 851782705331912386104485 159709257249733572394591)
                    ·
                      rfl

theorem cell22_466549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_466549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466549 prefixEnd_466549 := by exact prefixLift 466549
  have htrace : WordTrace (prefixWord ++ tailWord_466549) baseStart_466549 baseEnd_466549 := by
    simpa [prefixWord, tailWord_466549, baseEnd_466549] using wordTrace_append hprefix tailTrace_466549
  have hstable : (prefixWord ++ tailWord_466549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466549).length < 2 ^ (prefixWord ++ tailWord_466549).sum := by decide
  have hdescent : baseEnd_466549 < baseStart_466549 := by decide
  rcases family_descends (prefixWord ++ tailWord_466549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466560 : List Nat := [2, 1, 1, 2, 1, 4, 4, 1, 2, 4]
def baseStart_466560 : Nat := 118140960795 + 466560 * 2 ^ 59
def prefixEnd_466560 : Nat := 4983230072969 + 3 ^ 40 * 466560 * 2
def baseEnd_466560 : Nat := 159713022774533210369557

theorem tailTrace_466560 : CollatzResearch.WordTrace tailWord_466560 prefixEnd_466560 159713022774533210369557 := by
  unfold tailWord_466560
  simp only [CollatzResearch.WordTrace]
  refine ⟨8508420594870138474646567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11344560793160184632862089 8508420594870138474646567)
  ·
    refine ⟨12762630892305207711969851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8508420594870138474646567 12762630892305207711969851)
    ·
      refine ⟨19143946338457811567954777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12762630892305207711969851 19143946338457811567954777)
      ·
        refine ⟨14357959753843358675966083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19143946338457811567954777 14357959753843358675966083)
        ·
          refine ⟨21536939630765038013949125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14357959753843358675966083 21536939630765038013949125)
          ·
            refine ⟨4038176180768444627615461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21536939630765038013949125 4038176180768444627615461)
            ·
              refine ⟨757158033894083367677899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4038176180768444627615461 757158033894083367677899)
              ·
                refine ⟨1135737050841125051516849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757158033894083367677899 1135737050841125051516849)
                ·
                  refine ⟨851802788130843788637637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1135737050841125051516849 851802788130843788637637)
                  ·
                    refine ⟨159713022774533210369557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 851802788130843788637637 159713022774533210369557)
                    ·
                      rfl

theorem cell22_466560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 2, 4].length) (baseStart_466560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466560 prefixEnd_466560 := by exact prefixLift 466560
  have htrace : WordTrace (prefixWord ++ tailWord_466560) baseStart_466560 baseEnd_466560 := by
    simpa [prefixWord, tailWord_466560, baseEnd_466560] using wordTrace_append hprefix tailTrace_466560
  have hstable : (prefixWord ++ tailWord_466560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466560).length < 2 ^ (prefixWord ++ tailWord_466560).sum := by decide
  have hdescent : baseEnd_466560 < baseStart_466560 := by decide
  rcases family_descends (prefixWord ++ tailWord_466560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466605 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_466605 : Nat := 118140960795 + 466605 * 2 ^ 59
def prefixEnd_466605 : Nat := 4983230072969 + 3 ^ 40 * 466605 * 2
def baseEnd_466605 : Nat := 159728427194168092994419

theorem tailTrace_466605 : CollatzResearch.WordTrace tailWord_466605 prefixEnd_466605 159728427194168092994419 := by
  unfold tailWord_466605
  simp only [CollatzResearch.WordTrace]
  refine ⟨17018482474577249634681269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11345654983051499756454179 17018482474577249634681269)
  ·
    refine ⟨1595482731991617153251369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17018482474577249634681269 1595482731991617153251369)
    ·
      refine ⟨1196612048993712864938527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1595482731991617153251369 1196612048993712864938527)
      ·
        refine ⟨1794918073490569297407791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1196612048993712864938527 1794918073490569297407791)
        ·
          refine ⟨2692377110235853946111687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1794918073490569297407791 2692377110235853946111687)
          ·
            refine ⟨4038565665353780919167531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2692377110235853946111687 4038565665353780919167531)
            ·
              refine ⟨6057848498030671378751297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4038565665353780919167531 6057848498030671378751297)
              ·
                refine ⟨4543386373523003534063473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6057848498030671378751297 4543386373523003534063473)
                ·
                  refine ⟨3407539780142252650547605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4543386373523003534063473 3407539780142252650547605)
                  ·
                    refine ⟨159728427194168092994419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3407539780142252650547605 159728427194168092994419)
                    ·
                      rfl

theorem cell22_466605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_466605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466605 prefixEnd_466605 := by exact prefixLift 466605
  have htrace : WordTrace (prefixWord ++ tailWord_466605) baseStart_466605 baseEnd_466605 := by
    simpa [prefixWord, tailWord_466605, baseEnd_466605] using wordTrace_append hprefix tailTrace_466605
  have hstable : (prefixWord ++ tailWord_466605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466605).length < 2 ^ (prefixWord ++ tailWord_466605).sum := by decide
  have hdescent : baseEnd_466605 < baseStart_466605 := by decide
  rcases family_descends (prefixWord ++ tailWord_466605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466624 : List Nat := [2, 1, 1, 2, 4, 1, 4, 3, 1, 3]
def baseStart_466624 : Nat := 118140960795 + 466624 * 2 ^ 59
def prefixEnd_466624 : Nat := 4983230072969 + 3 ^ 40 * 466624 * 2
def baseEnd_466624 : Nat := 159734931282458376769361

theorem tailTrace_466624 : CollatzResearch.WordTrace tailWord_466624 prefixEnd_466624 159734931282458376769361 := by
  unfold tailWord_466624
  simp only [CollatzResearch.WordTrace]
  refine ⟨8509587730754207939811463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11346116974338943919748617 8509587730754207939811463)
  ·
    refine ⟨12764381596131311909717195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8509587730754207939811463 12764381596131311909717195)
    ·
      refine ⟨19146572394196967864575793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12764381596131311909717195 19146572394196967864575793)
      ·
        refine ⟨14359929295647725898431845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19146572394196967864575793 14359929295647725898431845)
        ·
          refine ⟨2692486742933948605955971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14359929295647725898431845 2692486742933948605955971)
          ·
            refine ⟨4038730114400922908933957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2692486742933948605955971 4038730114400922908933957)
            ·
              refine ⟨757261896450173045425117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4038730114400922908933957 757261896450173045425117)
              ·
                refine ⟨283973211168814892034419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 757261896450173045425117 283973211168814892034419)
                ·
                  refine ⟨425959816753222338051629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283973211168814892034419 425959816753222338051629)
                  ·
                    refine ⟨159734931282458376769361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 425959816753222338051629 159734931282458376769361)
                    ·
                      rfl

theorem cell22_466624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 1, 3].length) (baseStart_466624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466624 prefixEnd_466624 := by exact prefixLift 466624
  have htrace : WordTrace (prefixWord ++ tailWord_466624) baseStart_466624 baseEnd_466624 := by
    simpa [prefixWord, tailWord_466624, baseEnd_466624] using wordTrace_append hprefix tailTrace_466624
  have hstable : (prefixWord ++ tailWord_466624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466624).length < 2 ^ (prefixWord ++ tailWord_466624).sum := by decide
  have hdescent : baseEnd_466624 < baseStart_466624 := by decide
  rcases family_descends (prefixWord ++ tailWord_466624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466697 : List Nat := [1, 2, 1, 1, 3, 2, 1, 6, 2, 3]
def baseStart_466697 : Nat := 118140960795 + 466697 * 2 ^ 59
def prefixEnd_466697 : Nat := 4983230072969 + 3 ^ 40 * 466697 * 2
def baseEnd_466697 : Nat := 159759920674310519694137

theorem tailTrace_466697 : CollatzResearch.WordTrace tailWord_466697 prefixEnd_466697 159759920674310519694137 := by
  unfold tailWord_466697
  simp only [CollatzResearch.WordTrace]
  refine ⟨17021837990243949347030345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11347891993495966231353563 17021837990243949347030345)
  ·
    refine ⟨12766378492682962010272759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17021837990243949347030345 12766378492682962010272759)
    ·
      refine ⟨19149567739024443015409139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12766378492682962010272759 19149567739024443015409139)
      ·
        refine ⟨28724351608536664523113709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19149567739024443015409139 28724351608536664523113709)
        ·
          refine ⟨10771631853201249196167641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28724351608536664523113709 10771631853201249196167641)
          ·
            refine ⟨8078723889900936897125731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10771631853201249196167641 8078723889900936897125731)
            ·
              refine ⟨12118085834851405345688597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8078723889900936897125731 12118085834851405345688597)
              ·
                refine ⟨568035273508659625579153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12118085834851405345688597 568035273508659625579153)
                ·
                  refine ⟨426026455131494719184365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568035273508659625579153 426026455131494719184365)
                  ·
                    refine ⟨159759920674310519694137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 426026455131494719184365 159759920674310519694137)
                    ·
                      rfl

theorem cell22_466697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 3].length) (baseStart_466697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466697 prefixEnd_466697 := by exact prefixLift 466697
  have htrace : WordTrace (prefixWord ++ tailWord_466697) baseStart_466697 baseEnd_466697 := by
    simpa [prefixWord, tailWord_466697, baseEnd_466697] using wordTrace_append hprefix tailTrace_466697
  have hstable : (prefixWord ++ tailWord_466697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466697).length < 2 ^ (prefixWord ++ tailWord_466697).sum := by decide
  have hdescent : baseEnd_466697 < baseStart_466697 := by decide
  rcases family_descends (prefixWord ++ tailWord_466697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466714 : List Nat := [3, 1, 1, 3, 2, 3, 1, 3, 2, 3]
def baseStart_466714 : Nat := 118140960795 + 466714 * 2 ^ 59
def prefixEnd_466714 : Nat := 4983230072969 + 3 ^ 40 * 466714 * 2
def baseEnd_466714 : Nat := 159765740121728142019085

theorem tailTrace_466714 : CollatzResearch.WordTrace tailWord_466714 prefixEnd_466714 159765740121728142019085 := by
  unfold tailWord_466714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4255614507795590312599799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11348305354121574166932797 4255614507795590312599799)
  ·
    refine ⟨6383421761693385468899699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4255614507795590312599799 6383421761693385468899699)
    ·
      refine ⟨9575132642540078203349549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6383421761693385468899699 9575132642540078203349549)
      ·
        refine ⟨3590674740952529326256081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9575132642540078203349549 3590674740952529326256081)
        ·
          refine ⟨2693006055714396994692061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3590674740952529326256081 2693006055714396994692061)
          ·
            refine ⟨1009877270892898873009523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2693006055714396994692061 1009877270892898873009523)
            ·
              refine ⟨1514815906339348309514285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009877270892898873009523 1514815906339348309514285)
              ·
                refine ⟨568055964877255616067857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1514815906339348309514285 568055964877255616067857)
                ·
                  refine ⟨426041973657941712050893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568055964877255616067857 426041973657941712050893)
                  ·
                    refine ⟨159765740121728142019085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 426041973657941712050893 159765740121728142019085)
                    ·
                      rfl

theorem cell22_466714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_466714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466714 prefixEnd_466714 := by exact prefixLift 466714
  have htrace : WordTrace (prefixWord ++ tailWord_466714) baseStart_466714 baseEnd_466714 := by
    simpa [prefixWord, tailWord_466714, baseEnd_466714] using wordTrace_append hprefix tailTrace_466714
  have hstable : (prefixWord ++ tailWord_466714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466714).length < 2 ^ (prefixWord ++ tailWord_466714).sum := by decide
  have hdescent : baseEnd_466714 < baseStart_466714 := by decide
  rcases family_descends (prefixWord ++ tailWord_466714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466800 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 10]
def baseStart_466800 : Nat := 118140960795 + 466800 * 2 ^ 59
def prefixEnd_466800 : Nat := 4983230072969 + 3 ^ 40 * 466800 * 2
def baseEnd_466800 : Nat := 53265059893084194789607

theorem tailTrace_466800 : CollatzResearch.WordTrace tailWord_466800 prefixEnd_466800 53265059893084194789607 := by
  unfold tailWord_466800
  simp only [CollatzResearch.WordTrace]
  refine ⟨8512797354435398969014927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11350396472580531958686569 8512797354435398969014927)
  ·
    refine ⟨12769196031653098453522391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8512797354435398969014927 12769196031653098453522391)
    ·
      refine ⟨19153794047479647680283587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12769196031653098453522391 19153794047479647680283587)
      ·
        refine ⟨28730691071219471520425381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19153794047479647680283587 28730691071219471520425381)
        ·
          refine ⟨5387004575853650910079759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28730691071219471520425381 5387004575853650910079759)
          ·
            refine ⟨8080506863780476365119639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5387004575853650910079759 8080506863780476365119639)
            ·
              refine ⟨12120760295670714547679459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8080506863780476365119639 12120760295670714547679459)
              ·
                refine ⟨18181140443506071821519189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12120760295670714547679459 18181140443506071821519189)
                ·
                  refine ⟨53265059893084194789607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 18181140443506071821519189 53265059893084194789607)
                  ·
                    rfl

theorem cell22_466800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 10].length) (baseStart_466800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466800 prefixEnd_466800 := by exact prefixLift 466800
  have htrace : WordTrace (prefixWord ++ tailWord_466800) baseStart_466800 baseEnd_466800 := by
    simpa [prefixWord, tailWord_466800, baseEnd_466800] using wordTrace_append hprefix tailTrace_466800
  have hstable : (prefixWord ++ tailWord_466800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466800).length < 2 ^ (prefixWord ++ tailWord_466800).sum := by decide
  have hdescent : baseEnd_466800 < baseStart_466800 := by decide
  rcases family_descends (prefixWord ++ tailWord_466800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466832 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 6, 3]
def baseStart_466832 : Nat := 118140960795 + 466832 * 2 ^ 59
def prefixEnd_466832 : Nat := 4983230072969 + 3 ^ 40 * 466832 * 2
def baseEnd_466832 : Nat := 159806133933215167568723

theorem tailTrace_466832 : CollatzResearch.WordTrace tailWord_466832 prefixEnd_466832 159806133933215167568723 := by
  unfold tailWord_466832
  simp only [CollatzResearch.WordTrace]
  refine ⟨8513380922377433701597375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11351174563169911602129833 8513380922377433701597375)
  ·
    refine ⟨12770071383566150552396063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8513380922377433701597375 12770071383566150552396063)
    ·
      refine ⟨19155107075349225828594095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12770071383566150552396063 19155107075349225828594095)
      ·
        refine ⟨28732660613023838742891143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19155107075349225828594095 28732660613023838742891143)
        ·
          refine ⟨43098990919535758114336715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28732660613023838742891143 43098990919535758114336715)
          ·
            refine ⟨64648486379303637171505073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43098990919535758114336715 64648486379303637171505073)
            ·
              refine ⟨48486364784477727878628805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64648486379303637171505073 48486364784477727878628805)
              ·
                refine ⟨9091193397089573977242901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48486364784477727878628805 9091193397089573977242901)
                ·
                  refine ⟨426149690488573780183261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9091193397089573977242901 426149690488573780183261)
                  ·
                    refine ⟨159806133933215167568723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 426149690488573780183261 159806133933215167568723)
                    ·
                      rfl

theorem cell22_466832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 6, 3].length) (baseStart_466832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466832 prefixEnd_466832 := by exact prefixLift 466832
  have htrace : WordTrace (prefixWord ++ tailWord_466832) baseStart_466832 baseEnd_466832 := by
    simpa [prefixWord, tailWord_466832, baseEnd_466832] using wordTrace_append hprefix tailTrace_466832
  have hstable : (prefixWord ++ tailWord_466832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466832).length < 2 ^ (prefixWord ++ tailWord_466832).sum := by decide
  have hdescent : baseEnd_466832 < baseStart_466832 := by decide
  rcases family_descends (prefixWord ++ tailWord_466832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466834 : List Nat := [3, 2, 3, 2, 1, 1, 2, 2, 6]
def baseStart_466834 : Nat := 118140960795 + 466834 * 2 ^ 59
def prefixEnd_466834 : Nat := 4983230072969 + 3 ^ 40 * 466834 * 2
def baseEnd_466834 : Nat := 53268939524695943006239

theorem tailTrace_466834 : CollatzResearch.WordTrace tailWord_466834 prefixEnd_466834 53268939524695943006239 := by
  unfold tailWord_466834
  simp only [CollatzResearch.WordTrace]
  refine ⟨4256708697686905436191889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11351223193831747829845037 4256708697686905436191889)
  ·
    refine ⟨3192531523265179077143917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4256708697686905436191889 3192531523265179077143917)
    ·
      refine ⟨1197199321224442153928969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3192531523265179077143917 1197199321224442153928969)
      ·
        refine ⟨897899490918331615446727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1197199321224442153928969 897899490918331615446727)
        ·
          refine ⟨1346849236377497423170091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897899490918331615446727 1346849236377497423170091)
          ·
            refine ⟨2020273854566246134755137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346849236377497423170091 2020273854566246134755137)
            ·
              refine ⟨1515205390924684601066353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2020273854566246134755137 1515205390924684601066353)
              ·
                refine ⟨1136404043193513450799765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1515205390924684601066353 1136404043193513450799765)
                ·
                  refine ⟨53268939524695943006239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1136404043193513450799765 53268939524695943006239)
                  ·
                    rfl

theorem cell22_466834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_466834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466834 prefixEnd_466834 := by exact prefixLift 466834
  have htrace : WordTrace (prefixWord ++ tailWord_466834) baseStart_466834 baseEnd_466834 := by
    simpa [prefixWord, tailWord_466834, baseEnd_466834] using wordTrace_append hprefix tailTrace_466834
  have hstable : (prefixWord ++ tailWord_466834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466834).length < 2 ^ (prefixWord ++ tailWord_466834).sum := by decide
  have hdescent : baseEnd_466834 < baseStart_466834 := by decide
  rcases family_descends (prefixWord ++ tailWord_466834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466836 : List Nat := [2, 4, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_466836 : Nat := 118140960795 + 466836 * 2 ^ 59
def prefixEnd_466836 : Nat := 4983230072969 + 3 ^ 40 * 466836 * 2
def baseEnd_466836 : Nat := 159807503214960490468711

theorem tailTrace_466836 : CollatzResearch.WordTrace tailWord_466836 prefixEnd_466836 159807503214960490468711 := by
  unfold tailWord_466836
  simp only [CollatzResearch.WordTrace]
  refine ⟨8513453868370188043170181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11351271824493584057560241 8513453868370188043170181)
  ·
    refine ⟨1596272600319410258094409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8513453868370188043170181 1596272600319410258094409)
    ·
      refine ⟨1197204450239557693570807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1596272600319410258094409 1197204450239557693570807)
      ·
        refine ⟨1795806675359336540356211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1197204450239557693570807 1795806675359336540356211)
        ·
          refine ⟨2693710013039004810534317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1795806675359336540356211 2693710013039004810534317)
          ·
            refine ⟨1010141254889626803950369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2693710013039004810534317 1010141254889626803950369)
            ·
              refine ⟨757605941167220102962777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010141254889626803950369 757605941167220102962777)
              ·
                refine ⟨568204455875415077222083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 757605941167220102962777 568204455875415077222083)
                ·
                  refine ⟨852306683813122615833125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 568204455875415077222083 852306683813122615833125)
                  ·
                    refine ⟨159807503214960490468711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 852306683813122615833125 159807503214960490468711)
                    ·
                      rfl

theorem cell22_466836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_466836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466836 prefixEnd_466836 := by exact prefixLift 466836
  have htrace : WordTrace (prefixWord ++ tailWord_466836) baseStart_466836 baseEnd_466836 := by
    simpa [prefixWord, tailWord_466836, baseEnd_466836] using wordTrace_append hprefix tailTrace_466836
  have hstable : (prefixWord ++ tailWord_466836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466836).length < 2 ^ (prefixWord ++ tailWord_466836).sum := by decide
  have hdescent : baseEnd_466836 < baseStart_466836 := by decide
  rcases family_descends (prefixWord ++ tailWord_466836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466868 : List Nat := [2, 5, 2, 1, 2, 2, 1, 1, 6]
def baseStart_466868 : Nat := 118140960795 + 466868 * 2 ^ 59
def prefixEnd_466868 : Nat := 4983230072969 + 3 ^ 40 * 466868 * 2
def baseEnd_466868 : Nat := 53272819156307691222871

theorem tailTrace_466868 : CollatzResearch.WordTrace tailWord_466868 prefixEnd_466868 53272819156307691222871 := by
  unfold tailWord_466868
  simp only [CollatzResearch.WordTrace]
  refine ⟨8514037436312222775752629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11352049915082963701003505 8514037436312222775752629)
  ·
    refine ⟨798191009654270885226809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8514037436312222775752629 798191009654270885226809)
    ·
      refine ⟨598643257240703163920107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 798191009654270885226809 598643257240703163920107)
      ·
        refine ⟨897964885861054745880161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598643257240703163920107 897964885861054745880161)
        ·
          refine ⟨673473664395791059410121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 897964885861054745880161 673473664395791059410121)
          ·
            refine ⟨505105248296843294557591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 673473664395791059410121 505105248296843294557591)
            ·
              refine ⟨757657872445264941836387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505105248296843294557591 757657872445264941836387)
              ·
                refine ⟨1136486808667897412754581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757657872445264941836387 1136486808667897412754581)
                ·
                  refine ⟨53272819156307691222871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1136486808667897412754581 53272819156307691222871)
                  ·
                    rfl

theorem cell22_466868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_466868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466868 prefixEnd_466868 := by exact prefixLift 466868
  have htrace : WordTrace (prefixWord ++ tailWord_466868) baseStart_466868 baseEnd_466868 := by
    simpa [prefixWord, tailWord_466868, baseEnd_466868] using wordTrace_append hprefix tailTrace_466868
  have hstable : (prefixWord ++ tailWord_466868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466868).length < 2 ^ (prefixWord ++ tailWord_466868).sum := by decide
  have hdescent : baseEnd_466868 < baseStart_466868 := by decide
  rcases family_descends (prefixWord ++ tailWord_466868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466894 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 5, 3]
def baseStart_466894 : Nat := 118140960795 + 466894 * 2 ^ 59
def prefixEnd_466894 : Nat := 4983230072969 + 3 ^ 40 * 466894 * 2
def baseEnd_466894 : Nat := 159827357800267672518533

theorem tailTrace_466894 : CollatzResearch.WordTrace tailWord_466894 prefixEnd_466894 159827357800267672518533 := by
  unfold tailWord_466894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2128627896316281498993967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11352682113686834661301157 2128627896316281498993967)
  ·
    refine ⟨3192941844474422248490951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2128627896316281498993967 3192941844474422248490951)
    ·
      refine ⟨4789412766711633372736427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3192941844474422248490951 4789412766711633372736427)
      ·
        refine ⟨7184119150067450059104641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4789412766711633372736427 7184119150067450059104641)
        ·
          refine ⟨5388089362550587544328481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7184119150067450059104641 5388089362550587544328481)
          ·
            refine ⟨4041067021912940658246361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5388089362550587544328481 4041067021912940658246361)
            ·
              refine ⟨3030800266434705493684771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4041067021912940658246361 3030800266434705493684771)
              ·
                refine ⟨4546200399652058240527157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3030800266434705493684771 4546200399652058240527157)
                ·
                  refine ⟨426206287467380460049421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4546200399652058240527157 426206287467380460049421)
                  ·
                    refine ⟨159827357800267672518533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 426206287467380460049421 159827357800267672518533)
                    ·
                      rfl

theorem cell22_466894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_466894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466894 prefixEnd_466894 := by exact prefixLift 466894
  have htrace : WordTrace (prefixWord ++ tailWord_466894) baseStart_466894 baseEnd_466894 := by
    simpa [prefixWord, tailWord_466894, baseEnd_466894] using wordTrace_append hprefix tailTrace_466894
  have hstable : (prefixWord ++ tailWord_466894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466894).length < 2 ^ (prefixWord ++ tailWord_466894).sum := by decide
  have hdescent : baseEnd_466894 < baseStart_466894 := by decide
  rcases family_descends (prefixWord ++ tailWord_466894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466928 : List Nat := [2, 1, 1, 1, 3, 2, 6, 2, 1, 3]
def baseStart_466928 : Nat := 118140960795 + 466928 * 2 ^ 59
def prefixEnd_466928 : Nat := 4983230072969 + 3 ^ 40 * 466928 * 2
def baseEnd_466928 : Nat := 159838996695102917168429

theorem tailTrace_466928 : CollatzResearch.WordTrace tailWord_466928 prefixEnd_466928 159838996695102917168429 := by
  unfold tailWord_466928
  simp only [CollatzResearch.WordTrace]
  refine ⟨8515131626203537899344719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11353508834938050532459625 8515131626203537899344719)
  ·
    refine ⟨12772697439305306849017079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8515131626203537899344719 12772697439305306849017079)
    ·
      refine ⟨19159046158957960273525619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12772697439305306849017079 19159046158957960273525619)
      ·
        refine ⟨28738569238436940410288429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19159046158957960273525619 28738569238436940410288429)
        ·
          refine ⟨10776963464413852653858161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28738569238436940410288429 10776963464413852653858161)
          ·
            refine ⟨8082722598310389490393621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10776963464413852653858161 8082722598310389490393621)
            ·
              refine ⟨378877621795799507362201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8082722598310389490393621 378877621795799507362201)
              ·
                refine ⟨284158216346849630521651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378877621795799507362201 284158216346849630521651)
                ·
                  refine ⟨426237324520274445782477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284158216346849630521651 426237324520274445782477)
                  ·
                    refine ⟨159838996695102917168429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 426237324520274445782477 159838996695102917168429)
                    ·
                      rfl

theorem cell22_466928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 1, 3].length) (baseStart_466928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466928 prefixEnd_466928 := by exact prefixLift 466928
  have htrace : WordTrace (prefixWord ++ tailWord_466928) baseStart_466928 baseEnd_466928 := by
    simpa [prefixWord, tailWord_466928, baseEnd_466928] using wordTrace_append hprefix tailTrace_466928
  have hstable : (prefixWord ++ tailWord_466928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466928).length < 2 ^ (prefixWord ++ tailWord_466928).sum := by decide
  have hdescent : baseEnd_466928 < baseStart_466928 := by decide
  rcases family_descends (prefixWord ++ tailWord_466928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466986 : List Nat := [3, 1, 4, 1, 2, 2, 2, 1, 6]
def baseStart_466986 : Nat := 118140960795 + 466986 * 2 ^ 59
def prefixEnd_466986 : Nat := 4983230072969 + 3 ^ 40 * 466986 * 2
def baseEnd_466986 : Nat := 53286283760136699739417

theorem tailTrace_466986 : CollatzResearch.WordTrace tailWord_466986 prefixEnd_466986 53286283760136699739417 := by
  unfold tailWord_466986
  simp only [CollatzResearch.WordTrace]
  refine ⟨4258094671549237926075203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11354919124131301136200541 4258094671549237926075203)
  ·
    refine ⟨6387142007323856889112805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4258094671549237926075203 6387142007323856889112805)
    ·
      refine ⟨1197589126373223166708651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6387142007323856889112805 1197589126373223166708651)
      ·
        refine ⟨1796383689559834750062977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1197589126373223166708651 1796383689559834750062977)
        ·
          refine ⟨1347287767169876062547233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1796383689559834750062977 1347287767169876062547233)
          ·
            refine ⟨1010465825377407046910425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1347287767169876062547233 1010465825377407046910425)
            ·
              refine ⟨757849369033055285182819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010465825377407046910425 757849369033055285182819)
              ·
                refine ⟨1136774053549582927774229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757849369033055285182819 1136774053549582927774229)
                ·
                  refine ⟨53286283760136699739417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1136774053549582927774229 53286283760136699739417)
                  ·
                    rfl

theorem cell22_466986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_466986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_466986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_466986 prefixEnd_466986 := by exact prefixLift 466986
  have htrace : WordTrace (prefixWord ++ tailWord_466986) baseStart_466986 baseEnd_466986 := by
    simpa [prefixWord, tailWord_466986, baseEnd_466986] using wordTrace_append hprefix tailTrace_466986
  have hstable : (prefixWord ++ tailWord_466986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466986).length < 2 ^ (prefixWord ++ tailWord_466986).sum := by decide
  have hdescent : baseEnd_466986 < baseStart_466986 := by decide
  rcases family_descends (prefixWord ++ tailWord_466986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467136 : List Nat := [2, 1, 1, 2, 5, 1, 2, 2, 1, 5]
def baseStart_467136 : Nat := 118140960795 + 467136 * 2 ^ 59
def prefixEnd_467136 : Nat := 4983230072969 + 3 ^ 40 * 467136 * 2
def baseEnd_467136 : Nat := 159910199345859707967791

theorem tailTrace_467136 : CollatzResearch.WordTrace tailWord_467136 prefixEnd_467136 159910199345859707967791 := by
  unfold tailWord_467136
  simp only [CollatzResearch.WordTrace]
  refine ⟨8518924817826763661130631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11358566423769018214840841 8518924817826763661130631)
  ·
    refine ⟨12778387226740145491695947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8518924817826763661130631 12778387226740145491695947)
    ·
      refine ⟨19167580840110218237543921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12778387226740145491695947 19167580840110218237543921)
      ·
        refine ⟨14375685630082663678157941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19167580840110218237543921 14375685630082663678157941)
        ·
          refine ⟨1347720527820249719827307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14375685630082663678157941 1347720527820249719827307)
          ·
            refine ⟨2021580791730374579740961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347720527820249719827307 2021580791730374579740961)
            ·
              refine ⟨1516185593797780934805721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2021580791730374579740961 1516185593797780934805721)
              ·
                refine ⟨1137139195348335701104291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1516185593797780934805721 1137139195348335701104291)
                ·
                  refine ⟨1705708793022503551656437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137139195348335701104291 1705708793022503551656437)
                  ·
                    refine ⟨159910199345859707967791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1705708793022503551656437 159910199345859707967791)
                    ·
                      rfl

theorem cell22_467136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_467136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467136 prefixEnd_467136 := by exact prefixLift 467136
  have htrace : WordTrace (prefixWord ++ tailWord_467136) baseStart_467136 baseEnd_467136 := by
    simpa [prefixWord, tailWord_467136, baseEnd_467136] using wordTrace_append hprefix tailTrace_467136
  have hstable : (prefixWord ++ tailWord_467136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467136).length < 2 ^ (prefixWord ++ tailWord_467136).sum := by decide
  have hdescent : baseEnd_467136 < baseStart_467136 := by decide
  rcases family_descends (prefixWord ++ tailWord_467136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467140 : List Nat := [2, 3, 3, 1, 2, 1, 4, 1, 1, 4]
def baseStart_467140 : Nat := 118140960795 + 467140 * 2 ^ 59
def prefixEnd_467140 : Nat := 4983230072969 + 3 ^ 40 * 467140 * 2
def baseEnd_467140 : Nat := 159911568627605030867779

theorem tailTrace_467140 : CollatzResearch.WordTrace tailWord_467140 prefixEnd_467140 159911568627605030867779 := by
  unfold tailWord_467140
  simp only [CollatzResearch.WordTrace]
  refine ⟨8518997763819518002703437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11358663685092690670271249 8518997763819518002703437)
  ·
    refine ⟨3194624161432319251013789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8518997763819518002703437 3194624161432319251013789)
    ·
      refine ⟨1197984060537119719130171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3194624161432319251013789 1197984060537119719130171)
      ·
        refine ⟨1796976090805679578695257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1197984060537119719130171 1796976090805679578695257)
        ·
          refine ⟨1347732068104259684021443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1796976090805679578695257 1347732068104259684021443)
          ·
            refine ⟨2021598102156389526032165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347732068104259684021443 2021598102156389526032165)
            ·
              refine ⟨379049644154323036131031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2021598102156389526032165 379049644154323036131031)
              ·
                refine ⟨568574466231484554196547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379049644154323036131031 568574466231484554196547)
                ·
                  refine ⟨852861699347226831294821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 568574466231484554196547 852861699347226831294821)
                  ·
                    refine ⟨159911568627605030867779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 852861699347226831294821 159911568627605030867779)
                    ·
                      rfl

theorem cell22_467140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_467140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467140 prefixEnd_467140 := by exact prefixLift 467140
  have htrace : WordTrace (prefixWord ++ tailWord_467140) baseStart_467140 baseEnd_467140 := by
    simpa [prefixWord, tailWord_467140, baseEnd_467140] using wordTrace_append hprefix tailTrace_467140
  have hstable : (prefixWord ++ tailWord_467140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467140).length < 2 ^ (prefixWord ++ tailWord_467140).sum := by decide
  have hdescent : baseEnd_467140 < baseStart_467140 := by decide
  rcases family_descends (prefixWord ++ tailWord_467140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467153 : List Nat := [1, 2, 2, 1, 2, 2, 5, 2, 2, 3]
def baseStart_467153 : Nat := 118140960795 + 467153 * 2 ^ 59
def prefixEnd_467153 : Nat := 4983230072969 + 3 ^ 40 * 467153 * 2
def baseEnd_467153 : Nat := 159916018793277330292739

theorem tailTrace_467153 : CollatzResearch.WordTrace tailWord_467153 prefixEnd_467153 159916018793277330292739 := by
  unfold tailWord_467153
  simp only [CollatzResearch.WordTrace]
  refine ⟨17038469676591939225630113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11358979784394626150420075 17038469676591939225630113)
  ·
    refine ⟨12778852257443954419222585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17038469676591939225630113 12778852257443954419222585)
    ·
      refine ⟨9584139193082965814416939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12778852257443954419222585 9584139193082965814416939)
      ·
        refine ⟨14376208789624448721625409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9584139193082965814416939 14376208789624448721625409)
        ·
          refine ⟨10782156592218336541219057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14376208789624448721625409 10782156592218336541219057)
          ·
            refine ⟨8086617444163752405914293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10782156592218336541219057 8086617444163752405914293)
            ·
              refine ⟨758120385390351788054465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8086617444163752405914293 758120385390351788054465)
              ·
                refine ⟨568590289042763841040849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 758120385390351788054465 568590289042763841040849)
                ·
                  refine ⟨426442716782072880780637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568590289042763841040849 426442716782072880780637)
                  ·
                    refine ⟨159916018793277330292739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 426442716782072880780637 159916018793277330292739)
                    ·
                      rfl

theorem cell22_467153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_467153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_467153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_467153 prefixEnd_467153 := by exact prefixLift 467153
  have htrace : WordTrace (prefixWord ++ tailWord_467153) baseStart_467153 baseEnd_467153 := by
    simpa [prefixWord, tailWord_467153, baseEnd_467153] using wordTrace_append hprefix tailTrace_467153
  have hstable : (prefixWord ++ tailWord_467153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467153).length < 2 ^ (prefixWord ++ tailWord_467153).sum := by decide
  have hdescent : baseEnd_467153 < baseStart_467153 := by decide
  rcases family_descends (prefixWord ++ tailWord_467153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
