import V185TrunkScan23Chunk1268

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7518172 : List Nat := [2, 2, 6, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_7518172 : Nat := 118140960795 + 7518172 * 2 ^ 59
def prefixEnd_7518172 : Nat := 4983230072969 + 3 ^ 40 * 7518172 * 2
def baseEnd_7518172 : Nat := 3860435879174264351174563

theorem tailTrace_7518172 : CollatzResearch.WordTrace tailWord_7518172 prefixEnd_7518172 3860435879174264351174563 := by
  unfold tailWord_7518172
  simp only [CollatzResearch.WordTrace]
  refine ⟨137105130059477160199062385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182806840079302880265416513 137105130059477160199062385)
  ·
    refine ⟨102828847544607870149296789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137105130059477160199062385 102828847544607870149296789)
    ·
      refine ⟨4820102228653493913248287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102828847544607870149296789 4820102228653493913248287)
      ·
        refine ⟨7230153342980240869872431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4820102228653493913248287 7230153342980240869872431)
        ·
          refine ⟨10845230014470361304808647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7230153342980240869872431 10845230014470361304808647)
          ·
            refine ⟨16267845021705541957212971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10845230014470361304808647 16267845021705541957212971)
            ·
              refine ⟨24401767532558312935819457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16267845021705541957212971 24401767532558312935819457)
              ·
                refine ⟨18301325649418734701864593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24401767532558312935819457 18301325649418734701864593)
                ·
                  refine ⟨13725994237064051026398445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18301325649418734701864593 13725994237064051026398445)
                  ·
                    refine ⟨5147247838899019134899417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13725994237064051026398445 5147247838899019134899417)
                    ·
                      refine ⟨3860435879174264351174563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147247838899019134899417 3860435879174264351174563)
                      ·
                        rfl

theorem cell23_7518172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_7518172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518172 prefixEnd_7518172 := by exact prefixLift 7518172
  have htrace : WordTrace (prefixWord ++ tailWord_7518172) baseStart_7518172 baseEnd_7518172 := by
    simpa [prefixWord, tailWord_7518172, baseEnd_7518172] using wordTrace_append hprefix tailTrace_7518172
  have hstable : (prefixWord ++ tailWord_7518172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518172).length < 2 ^ (prefixWord ++ tailWord_7518172).sum := by decide
  have hdescent : baseEnd_7518172 < baseStart_7518172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518217 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 6, 6]
def baseStart_7518217 : Nat := 118140960795 + 7518217 * 2 ^ 59
def prefixEnd_7518217 : Nat := 4983230072969 + 3 ^ 40 * 7518217 * 2
def baseEnd_7518217 : Nat := 1286819661934572225037285

theorem tailTrace_7518217 : CollatzResearch.WordTrace tailWord_7518217 prefixEnd_7518217 1286819661934572225037285 := by
  unfold tailWord_7518217
  simp only [CollatzResearch.WordTrace]
  refine ⟨274211901403791293083512905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182807934269194195389008603 274211901403791293083512905)
  ·
    refine ⟨205658926052843469812634679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274211901403791293083512905 205658926052843469812634679)
    ·
      refine ⟨308488389079265204718952019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205658926052843469812634679 308488389079265204718952019)
      ·
        refine ⟨462732583618897807078428029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308488389079265204718952019 462732583618897807078428029)
        ·
          refine ⟨173524718857086677654410511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462732583618897807078428029 173524718857086677654410511)
          ·
            refine ⟨260287078285630016481615767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173524718857086677654410511 260287078285630016481615767)
            ·
              refine ⟨390430617428445024722423651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260287078285630016481615767 390430617428445024722423651)
              ·
                refine ⟨585645926142667537083635477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390430617428445024722423651 585645926142667537083635477)
                ·
                  refine ⟨27452152787937540800795413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 585645926142667537083635477 27452152787937540800795413)
                  ·
                    refine ⟨1286819661934572225037285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27452152787937540800795413 1286819661934572225037285)
                    ·
                      rfl

theorem cell23_7518217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 6].length) (baseStart_7518217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518217 prefixEnd_7518217 := by exact prefixLift 7518217
  have htrace : WordTrace (prefixWord ++ tailWord_7518217) baseStart_7518217 baseEnd_7518217 := by
    simpa [prefixWord, tailWord_7518217, baseEnd_7518217] using wordTrace_append hprefix tailTrace_7518217
  have hstable : (prefixWord ++ tailWord_7518217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518217).length < 2 ^ (prefixWord ++ tailWord_7518217).sum := by decide
  have hdescent : baseEnd_7518217 < baseStart_7518217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518258 : List Nat := [3, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2]
def baseStart_7518258 : Nat := 118140960795 + 7518258 * 2 ^ 59
def prefixEnd_7518258 : Nat := 4983230072969 + 3 ^ 40 * 7518258 * 2
def baseEnd_7518258 : Nat := 3860480038510551014699167

theorem tailTrace_7518258 : CollatzResearch.WordTrace tailWord_7518258 prefixEnd_7518258 3860480038510551014699167 := by
  unfold tailWord_7518258
  simp only [CollatzResearch.WordTrace]
  refine ⟨68553349199160689271438857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182808931197761838057170285 68553349199160689271438857)
  ·
    refine ⟨51415011899370516953579143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68553349199160689271438857 51415011899370516953579143)
    ·
      refine ⟨77122517849055775430368715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51415011899370516953579143 77122517849055775430368715)
      ·
        refine ⟨115683776773583663145553073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77122517849055775430368715 115683776773583663145553073)
        ·
          refine ⟨86762832580187747359164805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115683776773583663145553073 86762832580187747359164805)
          ·
            refine ⟨16268031108785202629843401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86762832580187747359164805 16268031108785202629843401)
            ·
              refine ⟨12201023331588901972382551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16268031108785202629843401 12201023331588901972382551)
              ·
                refine ⟨18301534997383352958573827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12201023331588901972382551 18301534997383352958573827)
                ·
                  refine ⟨27452302496075029437860741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18301534997383352958573827 27452302496075029437860741)
                  ·
                    refine ⟨5147306718014068019598889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27452302496075029437860741 5147306718014068019598889)
                    ·
                      refine ⟨3860480038510551014699167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147306718014068019598889 3860480038510551014699167)
                      ·
                        rfl

theorem cell23_7518258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_7518258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518258 prefixEnd_7518258 := by exact prefixLift 7518258
  have htrace : WordTrace (prefixWord ++ tailWord_7518258) baseStart_7518258 baseEnd_7518258 := by
    simpa [prefixWord, tailWord_7518258, baseEnd_7518258] using wordTrace_append hprefix tailTrace_7518258
  have hstable : (prefixWord ++ tailWord_7518258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518258).length < 2 ^ (prefixWord ++ tailWord_7518258).sum := by decide
  have hdescent : baseEnd_7518258 < baseStart_7518258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518267 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 8]
def baseStart_7518267 : Nat := 118140960795 + 7518267 * 2 ^ 59
def prefixEnd_7518267 : Nat := 4983230072969 + 3 ^ 40 * 7518267 * 2
def baseEnd_7518267 : Nat := 3860484659836441479486625

theorem tailTrace_7518267 : CollatzResearch.WordTrace tailWord_7518267 prefixEnd_7518267 3860484659836441479486625 := by
  unfold tailWord_7518267
  simp only [CollatzResearch.WordTrace]
  refine ⟨274213725053610151622833055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182809150035740101081888703 274213725053610151622833055)
  ·
    refine ⟨411320587580415227434249583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274213725053610151622833055 411320587580415227434249583)
    ·
      refine ⟨616980881370622841151374375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411320587580415227434249583 616980881370622841151374375)
      ·
        refine ⟨925471322055934261727061563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616980881370622841151374375 925471322055934261727061563)
        ·
          refine ⟨1388206983083901392590592345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925471322055934261727061563 1388206983083901392590592345)
          ·
            refine ⟨1041155237312926044442944259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1388206983083901392590592345 1041155237312926044442944259)
            ·
              refine ⟨1561732855969389066664416389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041155237312926044442944259 1561732855969389066664416389)
              ·
                refine ⟨292824910494260449999578073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1561732855969389066664416389 292824910494260449999578073)
                ·
                  refine ⟨219618682870695337499683555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292824910494260449999578073 219618682870695337499683555)
                  ·
                    refine ⟨329428024306043006249525333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 219618682870695337499683555 329428024306043006249525333)
                    ·
                      refine ⟨3860484659836441479486625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 329428024306043006249525333 3860484659836441479486625)
                      ·
                        rfl

theorem cell23_7518267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 8].length) (baseStart_7518267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518267 prefixEnd_7518267 := by exact prefixLift 7518267
  have htrace : WordTrace (prefixWord ++ tailWord_7518267) baseStart_7518267 baseEnd_7518267 := by
    simpa [prefixWord, tailWord_7518267, baseEnd_7518267] using wordTrace_append hprefix tailTrace_7518267
  have hstable : (prefixWord ++ tailWord_7518267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518267).length < 2 ^ (prefixWord ++ tailWord_7518267).sum := by decide
  have hdescent : baseEnd_7518267 < baseStart_7518267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518281 : List Nat := [1, 2, 1, 1, 2, 2, 6, 3, 5]
def baseStart_7518281 : Nat := 118140960795 + 7518281 * 2 ^ 59
def prefixEnd_7518281 : Nat := 4983230072969 + 3 ^ 40 * 7518281 * 2
def baseEnd_7518281 : Nat := 428943538729511602745729

theorem tailTrace_7518281 : CollatzResearch.WordTrace tailWord_7518281 prefixEnd_7518281 428943538729511602745729 := by
  unfold tailWord_7518281
  simp only [CollatzResearch.WordTrace]
  refine ⟨274214235675559432013842697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182809490450372954675895131 274214235675559432013842697)
  ·
    refine ⟨205660676756669574010382023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274214235675559432013842697 205660676756669574010382023)
    ·
      refine ⟨308491015135004361015573035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205660676756669574010382023 308491015135004361015573035)
      ·
        refine ⟨462736522702506541523359553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308491015135004361015573035 462736522702506541523359553)
        ·
          refine ⟨347052392026879906142519665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462736522702506541523359553 347052392026879906142519665)
          ·
            refine ⟨260289294020159929606889749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347052392026879906142519665 260289294020159929606889749)
            ·
              refine ⟨12201060657194996700322957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 260289294020159929606889749 12201060657194996700322957)
              ·
                refine ⟨4575397746448123762621109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12201060657194996700322957 4575397746448123762621109)
                ·
                  refine ⟨428943538729511602745729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4575397746448123762621109 428943538729511602745729)
                  ·
                    rfl

theorem cell23_7518281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 5].length) (baseStart_7518281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518281 prefixEnd_7518281 := by exact prefixLift 7518281
  have htrace : WordTrace (prefixWord ++ tailWord_7518281) baseStart_7518281 baseEnd_7518281 := by
    simpa [prefixWord, tailWord_7518281, baseEnd_7518281] using wordTrace_append hprefix tailTrace_7518281
  have hstable : (prefixWord ++ tailWord_7518281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518281).length < 2 ^ (prefixWord ++ tailWord_7518281).sum := by decide
  have hdescent : baseEnd_7518281 < baseStart_7518281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518382 : List Nat := [4, 1, 4, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_7518382 : Nat := 118140960795 + 7518382 * 2 ^ 59
def prefixEnd_7518382 : Nat := 4983230072969 + 3 ^ 40 * 7518382 * 2
def baseEnd_7518382 : Nat := 3860543710111708529548597

theorem tailTrace_7518382 : CollatzResearch.WordTrace tailWord_7518382 prefixEnd_7518382 3860543710111708529548597 := by
  unfold tailWord_7518382
  simp only [CollatzResearch.WordTrace]
  refine ⟨34277239931024190782908675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182811946298795684175512933 34277239931024190782908675)
  ·
    refine ⟨51415859896536286174363013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34277239931024190782908675 51415859896536286174363013)
    ·
      refine ⟨9640473730600553657693065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51415859896536286174363013 9640473730600553657693065)
      ·
        refine ⟨7230355297950415243269799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9640473730600553657693065 7230355297950415243269799)
        ·
          refine ⟨10845532946925622864904699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7230355297950415243269799 10845532946925622864904699)
          ·
            refine ⟨16268299420388434297357049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10845532946925622864904699 16268299420388434297357049)
            ·
              refine ⟨12201224565291325723017787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16268299420388434297357049 12201224565291325723017787)
              ·
                refine ⟨18301836847936988584526681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12201224565291325723017787 18301836847936988584526681)
                ·
                  refine ⟨13726377635952741438395011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18301836847936988584526681 13726377635952741438395011)
                  ·
                    refine ⟨20589566453929112157592517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13726377635952741438395011 20589566453929112157592517)
                    ·
                      refine ⟨3860543710111708529548597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20589566453929112157592517 3860543710111708529548597)
                      ·
                        rfl

theorem cell23_7518382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_7518382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518382 prefixEnd_7518382 := by exact prefixLift 7518382
  have htrace : WordTrace (prefixWord ++ tailWord_7518382) baseStart_7518382 baseEnd_7518382 := by
    simpa [prefixWord, tailWord_7518382, baseEnd_7518382] using wordTrace_append hprefix tailTrace_7518382
  have hstable : (prefixWord ++ tailWord_7518382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518382).length < 2 ^ (prefixWord ++ tailWord_7518382).sum := by decide
  have hdescent : baseEnd_7518382 < baseStart_7518382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518385 : List Nat := [1, 2, 2, 5, 2, 1, 2, 1, 2, 2, 3]
def baseStart_7518385 : Nat := 118140960795 + 7518385 * 2 ^ 59
def prefixEnd_7518385 : Nat := 4983230072969 + 3 ^ 40 * 7518385 * 2
def baseEnd_7518385 : Nat := 3860545250553672017811083

theorem tailTrace_7518385 : CollatzResearch.WordTrace tailWord_7518385 prefixEnd_7518385 3860545250553672017811083 := by
  unfold tailWord_7518385
  simp only [CollatzResearch.WordTrace]
  refine ⟨274218028867182657775628609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182812019244788438517085739 274218028867182657775628609)
  ·
    refine ⟨205663521650386993331721457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274218028867182657775628609 205663521650386993331721457)
    ·
      refine ⟨154247641237790244998791093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205663521650386993331721457 154247641237790244998791093)
      ·
        refine ⟨14460716366042835468636665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154247641237790244998791093 14460716366042835468636665)
        ·
          refine ⟨10845537274532126601477499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14460716366042835468636665 10845537274532126601477499)
          ·
            refine ⟨16268305911798189902216249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10845537274532126601477499 16268305911798189902216249)
            ·
              refine ⟨12201229433848642426662187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16268305911798189902216249 12201229433848642426662187)
              ·
                refine ⟨18301844150772963639993281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12201229433848642426662187 18301844150772963639993281)
                ·
                  refine ⟨13726383113079722729994961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18301844150772963639993281 13726383113079722729994961)
                  ·
                    refine ⟨10294787334809792047496221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13726383113079722729994961 10294787334809792047496221)
                    ·
                      refine ⟨3860545250553672017811083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10294787334809792047496221 3860545250553672017811083)
                      ·
                        rfl

theorem cell23_7518385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_7518385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518385 prefixEnd_7518385 := by exact prefixLift 7518385
  have htrace : WordTrace (prefixWord ++ tailWord_7518385) baseStart_7518385 baseEnd_7518385 := by
    simpa [prefixWord, tailWord_7518385, baseEnd_7518385] using wordTrace_append hprefix tailTrace_7518385
  have hstable : (prefixWord ++ tailWord_7518385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518385).length < 2 ^ (prefixWord ++ tailWord_7518385).sum := by decide
  have hdescent : baseEnd_7518385 < baseStart_7518385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518402 : List Nat := [3, 5, 1, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_7518402 : Nat := 118140960795 + 7518402 * 2 ^ 59
def prefixEnd_7518402 : Nat := 4983230072969 + 3 ^ 40 * 7518402 * 2
def baseEnd_7518402 : Nat := 3860553979724798451298505

theorem tailTrace_7518402 : CollatzResearch.WordTrace tailWord_7518402 prefixEnd_7518402 3860553979724798451298505 := by
  unfold tailWord_7518402
  simp only [CollatzResearch.WordTrace]
  refine ⟨68554662227030267419749365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182812432605414046452664973 68554662227030267419749365)
  ·
    refine ⟨6426999583784087570601503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68554662227030267419749365 6426999583784087570601503)
    ·
      refine ⟨9640499375676131355902255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6426999583784087570601503 9640499375676131355902255)
      ·
        refine ⟨14460749063514197033853383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9640499375676131355902255 14460749063514197033853383)
        ·
          refine ⟨21691123595271295550780075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14460749063514197033853383 21691123595271295550780075)
          ·
            refine ⟨32536685392906943326170113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21691123595271295550780075 32536685392906943326170113)
            ·
              refine ⟨24402514044680207494627585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32536685392906943326170113 24402514044680207494627585)
              ·
                refine ⟨18301885533510155620970689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24402514044680207494627585 18301885533510155620970689)
                ·
                  refine ⟨13726414150132616715728017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18301885533510155620970689 13726414150132616715728017)
                  ·
                    refine ⟨10294810612599462536796013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13726414150132616715728017 10294810612599462536796013)
                    ·
                      refine ⟨3860553979724798451298505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10294810612599462536796013 3860553979724798451298505)
                      ·
                        rfl

theorem cell23_7518402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_7518402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518402 prefixEnd_7518402 := by exact prefixLift 7518402
  have htrace : WordTrace (prefixWord ++ tailWord_7518402) baseStart_7518402 baseEnd_7518402 := by
    simpa [prefixWord, tailWord_7518402, baseEnd_7518402] using wordTrace_append hprefix tailTrace_7518402
  have hstable : (prefixWord ++ tailWord_7518402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518402).length < 2 ^ (prefixWord ++ tailWord_7518402).sum := by decide
  have hdescent : baseEnd_7518402 < baseStart_7518402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518415 : List Nat := [1, 1, 2, 1, 1, 3, 5, 4, 1, 1, 3]
def baseStart_7518415 : Nat := 118140960795 + 7518415 * 2 ^ 59
def prefixEnd_7518415 : Nat := 4983230072969 + 3 ^ 40 * 7518415 * 2
def baseEnd_7518415 : Nat := 3860560654973306900435945

theorem tailTrace_7518415 : CollatzResearch.WordTrace tailWord_7518415 prefixEnd_7518415 3860560654973306900435945 := by
  unfold tailWord_7518415
  simp only [CollatzResearch.WordTrace]
  refine ⟨274219123057073972899220699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182812748704715981932813799 274219123057073972899220699)
  ·
    refine ⟨411328684585610959348831049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274219123057073972899220699 411328684585610959348831049)
    ·
      refine ⟨308496513439208219511623287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411328684585610959348831049 308496513439208219511623287)
      ·
        refine ⟨462744770158812329267434931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308496513439208219511623287 462744770158812329267434931)
        ·
          refine ⟨694117155238218493901152397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462744770158812329267434931 694117155238218493901152397)
          ·
            refine ⟨260293933214331935212932149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 694117155238218493901152397 260293933214331935212932149)
            ·
              refine ⟨24402556238843618926212389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 260293933214331935212932149 24402556238843618926212389)
              ·
                refine ⟨4575479294783178548664823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24402556238843618926212389 4575479294783178548664823)
                ·
                  refine ⟨6863218942174767822997235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4575479294783178548664823 6863218942174767822997235)
                  ·
                    refine ⟨10294828413262151734495853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6863218942174767822997235 10294828413262151734495853)
                    ·
                      refine ⟨3860560654973306900435945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10294828413262151734495853 3860560654973306900435945)
                      ·
                        rfl

theorem cell23_7518415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 1, 1, 3].length) (baseStart_7518415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518415 prefixEnd_7518415 := by exact prefixLift 7518415
  have htrace : WordTrace (prefixWord ++ tailWord_7518415) baseStart_7518415 baseEnd_7518415 := by
    simpa [prefixWord, tailWord_7518415, baseEnd_7518415] using wordTrace_append hprefix tailTrace_7518415
  have hstable : (prefixWord ++ tailWord_7518415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518415).length < 2 ^ (prefixWord ++ tailWord_7518415).sum := by decide
  have hdescent : baseEnd_7518415 < baseStart_7518415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518431 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 6, 4]
def baseStart_7518431 : Nat := 118140960795 + 7518431 * 2 ^ 59
def prefixEnd_7518431 : Nat := 4983230072969 + 3 ^ 40 * 7518431 * 2
def baseEnd_7518431 : Nat := 1286856290221259612611957

theorem tailTrace_7518431 : CollatzResearch.WordTrace tailWord_7518431 prefixEnd_7518431 1286856290221259612611957 := by
  unfold tailWord_7518431
  simp only [CollatzResearch.WordTrace]
  refine ⟨274219706625016007631803147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182813137750010671754535431 274219706625016007631803147)
  ·
    refine ⟨411329559937524011447704721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274219706625016007631803147 411329559937524011447704721)
    ·
      refine ⟨308497169953143008585778541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411329559937524011447704721 308497169953143008585778541)
      ·
        refine ⟨115686438732428628219666953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308497169953143008585778541 115686438732428628219666953)
        ·
          refine ⟨86764829049321471164750215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115686438732428628219666953 86764829049321471164750215)
          ·
            refine ⟨130147243573982206747125323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86764829049321471164750215 130147243573982206747125323)
            ·
              refine ⟨195220865360973310120687985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130147243573982206747125323 195220865360973310120687985)
              ·
                refine ⟨146415649020729982590515989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195220865360973310120687985 146415649020729982590515989)
                ·
                  refine ⟨6863233547846717933930437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146415649020729982590515989 6863233547846717933930437)
                  ·
                    refine ⟨1286856290221259612611957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6863233547846717933930437 1286856290221259612611957)
                    ·
                      rfl

theorem cell23_7518431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 4].length) (baseStart_7518431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518431 prefixEnd_7518431 := by exact prefixLift 7518431
  have htrace : WordTrace (prefixWord ++ tailWord_7518431) baseStart_7518431 baseEnd_7518431 := by
    simpa [prefixWord, tailWord_7518431, baseEnd_7518431] using wordTrace_append hprefix tailTrace_7518431
  have hstable : (prefixWord ++ tailWord_7518431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518431).length < 2 ^ (prefixWord ++ tailWord_7518431).sum := by decide
  have hdescent : baseEnd_7518431 < baseStart_7518431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518451 : List Nat := [1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 4]
def baseStart_7518451 : Nat := 118140960795 + 7518451 * 2 ^ 59
def prefixEnd_7518451 : Nat := 4983230072969 + 3 ^ 40 * 7518451 * 2
def baseEnd_7518451 : Nat := 3860579140276868759585779

theorem tailTrace_7518451 : CollatzResearch.WordTrace tailWord_7518451 prefixEnd_7518451 3860579140276868759585779 := by
  unfold tailWord_7518451
  simp only [CollatzResearch.WordTrace]
  refine ⟨274220436084943551047531207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182813624056629034031687471 274220436084943551047531207)
  ·
    refine ⟨411330654127415326571296811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274220436084943551047531207 411330654127415326571296811)
    ·
      refine ⟨616995981191122989856945217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411330654127415326571296811 616995981191122989856945217)
      ·
        refine ⟨462746985893342242392708913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616995981191122989856945217 462746985893342242392708913)
        ·
          refine ⟨347060239420006681794531685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462746985893342242392708913 347060239420006681794531685)
          ·
            refine ⟨65073794891251252836474691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 347060239420006681794531685 65073794891251252836474691)
            ·
              refine ⟨97610692336876879254712037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65073794891251252836474691 97610692336876879254712037)
              ·
                refine ⟨18302004813164414860258507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97610692336876879254712037 18302004813164414860258507)
                ·
                  refine ⟨27453007219746622290387761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18302004813164414860258507 27453007219746622290387761)
                  ·
                    refine ⟨20589755414809966717790821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27453007219746622290387761 20589755414809966717790821)
                    ·
                      refine ⟨3860579140276868759585779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20589755414809966717790821 3860579140276868759585779)
                      ·
                        rfl

theorem cell23_7518451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 4].length) (baseStart_7518451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518451 prefixEnd_7518451 := by exact prefixLift 7518451
  have htrace : WordTrace (prefixWord ++ tailWord_7518451) baseStart_7518451 baseEnd_7518451 := by
    simpa [prefixWord, tailWord_7518451, baseEnd_7518451] using wordTrace_append hprefix tailTrace_7518451
  have hstable : (prefixWord ++ tailWord_7518451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518451).length < 2 ^ (prefixWord ++ tailWord_7518451).sum := by decide
  have hdescent : baseEnd_7518451 < baseStart_7518451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518472 : List Nat := [2, 1, 3, 2, 3, 2, 2, 1, 3, 2, 2]
def baseStart_7518472 : Nat := 118140960795 + 7518472 * 2 ^ 59
def prefixEnd_7518472 : Nat := 4983230072969 + 3 ^ 40 * 7518472 * 2
def baseEnd_7518472 : Nat := 3860589923370613177423183

theorem tailTrace_7518472 : CollatzResearch.WordTrace tailWord_7518472 prefixEnd_7518472 3860589923370613177423183 := by
  unfold tailWord_7518472
  simp only [CollatzResearch.WordTrace]
  refine ⟨137110601008933735817022835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182814134678578314422697113 137110601008933735817022835)
  ·
    refine ⟨205665901513400603725534253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137110601008933735817022835 205665901513400603725534253)
    ·
      refine ⟨77124713067525226397075345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205665901513400603725534253 77124713067525226397075345)
      ·
        refine ⟨57843534800643919797806509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77124713067525226397075345 57843534800643919797806509)
        ·
          refine ⟨21691325550241469924177441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57843534800643919797806509 21691325550241469924177441)
          ·
            refine ⟨16268494162681102443133081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21691325550241469924177441 16268494162681102443133081)
            ·
              refine ⟨12201370622010826832349811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16268494162681102443133081 12201370622010826832349811)
              ·
                refine ⟨18302055933016240248524717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12201370622010826832349811 18302055933016240248524717)
                ·
                  refine ⟨6863270974881090093196769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18302055933016240248524717 6863270974881090093196769)
                  ·
                    refine ⟨5147453231160817569897577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6863270974881090093196769 5147453231160817569897577)
                    ·
                      refine ⟨3860589923370613177423183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147453231160817569897577 3860589923370613177423183)
                      ·
                        rfl

theorem cell23_7518472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_7518472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518472 prefixEnd_7518472 := by exact prefixLift 7518472
  have htrace : WordTrace (prefixWord ++ tailWord_7518472) baseStart_7518472 baseEnd_7518472 := by
    simpa [prefixWord, tailWord_7518472, baseEnd_7518472] using wordTrace_append hprefix tailTrace_7518472
  have hstable : (prefixWord ++ tailWord_7518472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518472).length < 2 ^ (prefixWord ++ tailWord_7518472).sum := by decide
  have hdescent : baseEnd_7518472 < baseStart_7518472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518515 : List Nat := [1, 1, 1, 2, 5, 1, 1, 5, 1, 3, 2]
def baseStart_7518515 : Nat := 118140960795 + 7518515 * 2 ^ 59
def prefixEnd_7518515 : Nat := 4983230072969 + 3 ^ 40 * 7518515 * 2
def baseEnd_7518515 : Nat := 3860612003038756509185485

theorem tailTrace_7518515 : CollatzResearch.WordTrace tailWord_7518515 prefixEnd_7518515 3860612003038756509185485 := by
  unfold tailWord_7518515
  simp only [CollatzResearch.WordTrace]
  refine ⟨274222770356711689977860999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182815180237807793318573999 274222770356711689977860999)
  ·
    refine ⟨411334155535067534966791499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274222770356711689977860999 411334155535067534966791499)
    ·
      refine ⟨617001233302601302450187249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411334155535067534966791499 617001233302601302450187249)
      ·
        refine ⟨462750924976950976837640437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617001233302601302450187249 462750924976950976837640437)
        ·
          refine ⟨43382899216589154078528791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 462750924976950976837640437 43382899216589154078528791)
          ·
            refine ⟨65074348824883731117793187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43382899216589154078528791 65074348824883731117793187)
            ·
              refine ⟨97611523237325596676689781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65074348824883731117793187 97611523237325596676689781)
              ·
                refine ⟨9151080303499274688439667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97611523237325596676689781 9151080303499274688439667)
                ·
                  refine ⟨13726620455248912032659501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9151080303499274688439667 13726620455248912032659501)
                  ·
                    refine ⟨5147482670718342012247313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13726620455248912032659501 5147482670718342012247313)
                    ·
                      refine ⟨3860612003038756509185485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147482670718342012247313 3860612003038756509185485)
                      ·
                        rfl

theorem cell23_7518515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 3, 2].length) (baseStart_7518515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518515 prefixEnd_7518515 := by exact prefixLift 7518515
  have htrace : WordTrace (prefixWord ++ tailWord_7518515) baseStart_7518515 baseEnd_7518515 := by
    simpa [prefixWord, tailWord_7518515, baseEnd_7518515] using wordTrace_append hprefix tailTrace_7518515
  have hstable : (prefixWord ++ tailWord_7518515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518515).length < 2 ^ (prefixWord ++ tailWord_7518515).sum := by decide
  have hdescent : baseEnd_7518515 < baseStart_7518515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518528 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 5, 4, 2]
def baseStart_7518528 : Nat := 118140960795 + 7518528 * 2 ^ 59
def prefixEnd_7518528 : Nat := 4983230072969 + 3 ^ 40 * 7518528 * 2
def baseEnd_7518528 : Nat := 3860618678287264958322925

theorem tailTrace_7518528 : CollatzResearch.WordTrace tailWord_7518528 prefixEnd_7518528 3860618678287264958322925 := by
  unfold tailWord_7518528
  simp only [CollatzResearch.WordTrace]
  refine ⟨137111622252832296599042119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182815496337109728798722825 137111622252832296599042119)
  ·
    refine ⟨205667433379248444898563179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137111622252832296599042119 205667433379248444898563179)
    ·
      refine ⟨308501150068872667347844769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205667433379248444898563179 308501150068872667347844769)
      ·
        refine ⟨231375862551654500510883577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308501150068872667347844769 231375862551654500510883577)
        ·
          refine ⟨173531896913740875383162683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231375862551654500510883577 173531896913740875383162683)
          ·
            refine ⟨260297845370611313074744025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173531896913740875383162683 260297845370611313074744025)
            ·
              refine ⟨195223384027958484806058019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260297845370611313074744025 195223384027958484806058019)
              ·
                refine ⟨292835076041937727209087029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195223384027958484806058019 292835076041937727209087029)
                ·
                  refine ⟨27453288378931661925851909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 292835076041937727209087029 27453288378931661925851909)
                  ·
                    refine ⟨5147491571049686611097233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27453288378931661925851909 5147491571049686611097233)
                    ·
                      refine ⟨3860618678287264958322925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147491571049686611097233 3860618678287264958322925)
                      ·
                        rfl

theorem cell23_7518528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5, 4, 2].length) (baseStart_7518528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518528 prefixEnd_7518528 := by exact prefixLift 7518528
  have htrace : WordTrace (prefixWord ++ tailWord_7518528) baseStart_7518528 baseEnd_7518528 := by
    simpa [prefixWord, tailWord_7518528, baseEnd_7518528] using wordTrace_append hprefix tailTrace_7518528
  have hstable : (prefixWord ++ tailWord_7518528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518528).length < 2 ^ (prefixWord ++ tailWord_7518528).sum := by decide
  have hdescent : baseEnd_7518528 < baseStart_7518528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518548 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_7518548 : Nat := 118140960795 + 7518548 * 2 ^ 59
def prefixEnd_7518548 : Nat := 4983230072969 + 3 ^ 40 * 7518548 * 2
def baseEnd_7518548 : Nat := 3860628947900354880072833

theorem tailTrace_7518548 : CollatzResearch.WordTrace tailWord_7518548 prefixEnd_7518548 3860628947900354880072833 := by
  unfold tailWord_7518548
  simp only [CollatzResearch.WordTrace]
  refine ⟨137111986982796068306906149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182815982643728091075874865 137111986982796068306906149)
  ·
    refine ⟨25708497559274262807544903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137111986982796068306906149 25708497559274262807544903)
    ·
      refine ⟨38562746338911394211317355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25708497559274262807544903 38562746338911394211317355)
      ·
        refine ⟨57844119508367091316976033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38562746338911394211317355 57844119508367091316976033)
        ·
          refine ⟨43383089631275318487732025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57844119508367091316976033 43383089631275318487732025)
          ·
            refine ⟨32537317223456488865799019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43383089631275318487732025 32537317223456488865799019)
            ·
              refine ⟨48805975835184733298698529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32537317223456488865799019 48805975835184733298698529)
              ·
                refine ⟨36604481876388549974023897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48805975835184733298698529 36604481876388549974023897)
                ·
                  refine ⟨27453361407291412480517923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36604481876388549974023897 27453361407291412480517923)
                  ·
                    refine ⟨41180042110937118720776885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27453361407291412480517923 41180042110937118720776885)
                    ·
                      refine ⟨3860628947900354880072833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41180042110937118720776885 3860628947900354880072833)
                      ·
                        rfl

theorem cell23_7518548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_7518548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518548 prefixEnd_7518548 := by exact prefixLift 7518548
  have htrace : WordTrace (prefixWord ++ tailWord_7518548) baseStart_7518548 baseEnd_7518548 := by
    simpa [prefixWord, tailWord_7518548, baseEnd_7518548] using wordTrace_append hprefix tailTrace_7518548
  have hstable : (prefixWord ++ tailWord_7518548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518548).length < 2 ^ (prefixWord ++ tailWord_7518548).sum := by decide
  have hdescent : baseEnd_7518548 < baseStart_7518548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518549 : List Nat := [1, 3, 2, 2, 4, 2, 1, 2, 1, 3, 2]
def baseStart_7518549 : Nat := 118140960795 + 7518549 * 2 ^ 59
def prefixEnd_7518549 : Nat := 4983230072969 + 3 ^ 40 * 7518549 * 2
def baseEnd_7518549 : Nat := 3860629461381009376160329

theorem tailTrace_7518549 : CollatzResearch.WordTrace tailWord_7518549 prefixEnd_7518549 3860629461381009376160329 := by
  unfold tailWord_7518549
  simp only [CollatzResearch.WordTrace]
  refine ⟨274224010438588513784598701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182816006959059009189732467 274224010438588513784598701)
  ·
    refine ⟨102834003914470692669224513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274224010438588513784598701 102834003914470692669224513)
    ·
      refine ⟨77125502935853019501918385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102834003914470692669224513 77125502935853019501918385)
      ·
        refine ⟨57844127201889764626438789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77125502935853019501918385 57844127201889764626438789)
        ·
          refine ⟨10845773850354330867457273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57844127201889764626438789 10845773850354330867457273)
          ·
            refine ⟨8134330387765748150592955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10845773850354330867457273 8134330387765748150592955)
            ·
              refine ⟨12201495581648622225889433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8134330387765748150592955 12201495581648622225889433)
              ·
                refine ⟨9151121686236466669417075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12201495581648622225889433 9151121686236466669417075)
                ·
                  refine ⟨13726682529354700004125613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9151121686236466669417075 13726682529354700004125613)
                  ·
                    refine ⟨5147505948508012501547105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13726682529354700004125613 5147505948508012501547105)
                    ·
                      refine ⟨3860629461381009376160329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147505948508012501547105 3860629461381009376160329)
                      ·
                        rfl

theorem cell23_7518549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_7518549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518549 prefixEnd_7518549 := by exact prefixLift 7518549
  have htrace : WordTrace (prefixWord ++ tailWord_7518549) baseStart_7518549 baseEnd_7518549 := by
    simpa [prefixWord, tailWord_7518549, baseEnd_7518549] using wordTrace_append hprefix tailTrace_7518549
  have hstable : (prefixWord ++ tailWord_7518549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518549).length < 2 ^ (prefixWord ++ tailWord_7518549).sum := by decide
  have hdescent : baseEnd_7518549 < baseStart_7518549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518551 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 9]
def baseStart_7518551 : Nat := 118140960795 + 7518551 * 2 ^ 59
def prefixEnd_7518551 : Nat := 4983230072969 + 3 ^ 40 * 7518551 * 2
def baseEnd_7518551 : Nat := 428958943149146485370591

theorem tailTrace_7518551 : CollatzResearch.WordTrace tailWord_7518551 prefixEnd_7518551 428958943149146485370591 := by
  unfold tailWord_7518551
  simp only [CollatzResearch.WordTrace]
  refine ⟨274224083384581268126171507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182816055589720845417447671 274224083384581268126171507)
  ·
    refine ⟨411336125076871902189257261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274224083384581268126171507 411336125076871902189257261)
    ·
      refine ⟨154251046903826963320971473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411336125076871902189257261 154251046903826963320971473)
      ·
        refine ⟨115688285177870222490728605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154251046903826963320971473 115688285177870222490728605)
        ·
          refine ⟨43383106941701333434023227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115688285177870222490728605 43383106941701333434023227)
          ·
            refine ⟨65074660412552000151034841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43383106941701333434023227 65074660412552000151034841)
            ·
              refine ⟨48805995309414000113276131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65074660412552000151034841 48805995309414000113276131)
              ·
                refine ⟨73208992964121000169914197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48805995309414000113276131 73208992964121000169914197)
                ·
                  refine ⟨428958943149146485370591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73208992964121000169914197 428958943149146485370591)
                  ·
                    rfl

theorem cell23_7518551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 9].length) (baseStart_7518551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518551 prefixEnd_7518551 := by exact prefixLift 7518551
  have htrace : WordTrace (prefixWord ++ tailWord_7518551) baseStart_7518551 baseEnd_7518551 := by
    simpa [prefixWord, tailWord_7518551, baseEnd_7518551] using wordTrace_append hprefix tailTrace_7518551
  have hstable : (prefixWord ++ tailWord_7518551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518551).length < 2 ^ (prefixWord ++ tailWord_7518551).sum := by decide
  have hdescent : baseEnd_7518551 < baseStart_7518551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518562 : List Nat := [3, 3, 2, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_7518562 : Nat := 118140960795 + 7518562 * 2 ^ 59
def prefixEnd_7518562 : Nat := 4983230072969 + 3 ^ 40 * 7518562 * 2
def baseEnd_7518562 : Nat := 3860636136629517825297769

theorem tailTrace_7518562 : CollatzResearch.WordTrace tailWord_7518562 prefixEnd_7518562 3860636136629517825297769 := by
  unfold tailWord_7518562
  simp only [CollatzResearch.WordTrace]
  refine ⟨68556121146885354251205485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182816323058360944669881293 68556121146885354251205485)
  ·
    refine ⟨25708545430082007844202057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68556121146885354251205485 25708545430082007844202057)
    ·
      refine ⟨19281409072561505883151543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25708545430082007844202057 19281409072561505883151543)
      ·
        refine ⟨28922113608842258824727315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19281409072561505883151543 28922113608842258824727315)
        ·
          refine ⟨43383170413263388237090973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28922113608842258824727315 43383170413263388237090973)
          ·
            refine ⟨16268688904973770588909115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43383170413263388237090973 16268688904973770588909115)
            ·
              refine ⟨24403033357460655883363673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16268688904973770588909115 24403033357460655883363673)
              ·
                refine ⟨18302275018095491912522755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24403033357460655883363673 18302275018095491912522755)
                ·
                  refine ⟨27453412527143237868784133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18302275018095491912522755 27453412527143237868784133)
                  ·
                    refine ⟨5147514848839357100397025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27453412527143237868784133 5147514848839357100397025)
                    ·
                      refine ⟨3860636136629517825297769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147514848839357100397025 3860636136629517825297769)
                      ·
                        rfl

theorem cell23_7518562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_7518562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518562 prefixEnd_7518562 := by exact prefixLift 7518562
  have htrace : WordTrace (prefixWord ++ tailWord_7518562) baseStart_7518562 baseEnd_7518562 := by
    simpa [prefixWord, tailWord_7518562, baseEnd_7518562] using wordTrace_append hprefix tailTrace_7518562
  have hstable : (prefixWord ++ tailWord_7518562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518562).length < 2 ^ (prefixWord ++ tailWord_7518562).sum := by decide
  have hdescent : baseEnd_7518562 < baseStart_7518562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518595 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 3]
def baseStart_7518595 : Nat := 118140960795 + 7518595 * 2 ^ 59
def prefixEnd_7518595 : Nat := 4983230072969 + 3 ^ 40 * 7518595 * 2
def baseEnd_7518595 : Nat := 3860653081491116196185117

theorem tailTrace_7518595 : CollatzResearch.WordTrace tailWord_7518595 prefixEnd_7518595 3860653081491116196185117 := by
  unfold tailWord_7518595
  simp only [CollatzResearch.WordTrace]
  refine ⟨274225688196421863640773239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182817125464281242427182159 274225688196421863640773239)
  ·
    refine ⟨411338532294632795461159859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274225688196421863640773239 411338532294632795461159859)
    ·
      refine ⟨617007798441949193191739789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411338532294632795461159859 617007798441949193191739789)
      ·
        refine ⟨231377924415730947446902421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 617007798441949193191739789 231377924415730947446902421)
        ·
          refine ⟨10845840206987388161573551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 231377924415730947446902421 10845840206987388161573551)
          ·
            refine ⟨16268760310481082242360327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10845840206987388161573551 16268760310481082242360327)
            ·
              refine ⟨24403140465721623363540491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16268760310481082242360327 24403140465721623363540491)
              ·
                refine ⟨36604710698582435045310737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24403140465721623363540491 36604710698582435045310737)
                ·
                  refine ⟨27453533023936826283983053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36604710698582435045310737 27453533023936826283983053)
                  ·
                    refine ⟨10295074883976309856493645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27453533023936826283983053 10295074883976309856493645)
                    ·
                      refine ⟨3860653081491116196185117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10295074883976309856493645 3860653081491116196185117)
                      ·
                        rfl

theorem cell23_7518595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_7518595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518595 prefixEnd_7518595 := by exact prefixLift 7518595
  have htrace : WordTrace (prefixWord ++ tailWord_7518595) baseStart_7518595 baseEnd_7518595 := by
    simpa [prefixWord, tailWord_7518595, baseEnd_7518595] using wordTrace_append hprefix tailTrace_7518595
  have hstable : (prefixWord ++ tailWord_7518595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518595).length < 2 ^ (prefixWord ++ tailWord_7518595).sum := by decide
  have hdescent : baseEnd_7518595 < baseStart_7518595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518652 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 2, 4, 2]
def baseStart_7518652 : Nat := 118140960795 + 7518652 * 2 ^ 59
def prefixEnd_7518652 : Nat := 4983230072969 + 3 ^ 40 * 7518652 * 2
def baseEnd_7518652 : Nat := 3860682349888422473172355

theorem tailTrace_7518652 : CollatzResearch.WordTrace tailWord_7518652 prefixEnd_7518652 3860682349888422473172355 := by
  unfold tailWord_7518652
  simp only [CollatzResearch.WordTrace]
  refine ⟨137113883578607681187799105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182818511438143574917065473 137113883578607681187799105)
  ·
    refine ⟨102835412683955760890849329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137113883578607681187799105 102835412683955760890849329)
    ·
      refine ⟨77126559512966820668136997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102835412683955760890849329 77126559512966820668136997)
      ·
        refine ⟨14461229908681278875275687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77126559512966820668136997 14461229908681278875275687)
        ·
          refine ⟨21691844863021918312913531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14461229908681278875275687 21691844863021918312913531)
          ·
            refine ⟨32537767294532877469370297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21691844863021918312913531 32537767294532877469370297)
            ·
              refine ⟨24403325470899658102027723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32537767294532877469370297 24403325470899658102027723)
              ·
                refine ⟨36604988206349487153041585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24403325470899658102027723 36604988206349487153041585)
                ·
                  refine ⟨27453741154762115364781189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36604988206349487153041585 27453741154762115364781189)
                  ·
                    refine ⟨5147576466517896630896473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27453741154762115364781189 5147576466517896630896473)
                    ·
                      refine ⟨3860682349888422473172355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147576466517896630896473 3860682349888422473172355)
                      ·
                        rfl

theorem cell23_7518652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_7518652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518652 prefixEnd_7518652 := by exact prefixLift 7518652
  have htrace : WordTrace (prefixWord ++ tailWord_7518652) baseStart_7518652 baseEnd_7518652 := by
    simpa [prefixWord, tailWord_7518652, baseEnd_7518652] using wordTrace_append hprefix tailTrace_7518652
  have hstable : (prefixWord ++ tailWord_7518652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518652).length < 2 ^ (prefixWord ++ tailWord_7518652).sum := by decide
  have hdescent : baseEnd_7518652 < baseStart_7518652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518725 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 2, 6, 2]
def baseStart_7518725 : Nat := 118140960795 + 7518725 * 2 ^ 59
def prefixEnd_7518725 : Nat := 4983230072969 + 3 ^ 40 * 7518725 * 2
def baseEnd_7518725 : Nat := 3860719833976200687559519

theorem tailTrace_7518725 : CollatzResearch.WordTrace tailWord_7518725 prefixEnd_7518725 3860719833976200687559519 := by
  unfold tailWord_7518725
  simp only [CollatzResearch.WordTrace]
  refine ⟨274230429685950895843005629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182820286457300597228670419 274230429685950895843005629)
  ·
    refine ⟨102836411132231585941127111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274230429685950895843005629 102836411132231585941127111)
    ·
      refine ⟨154254616698347378911690667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102836411132231585941127111 154254616698347378911690667)
      ·
        refine ⟨231381925047521068367536001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154254616698347378911690667 231381925047521068367536001)
        ·
          refine ⟨173536443785640801275652001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231381925047521068367536001 173536443785640801275652001)
          ·
            refine ⟨130152332839230600956739001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173536443785640801275652001 130152332839230600956739001)
            ·
              refine ⟨97614249629422950717554251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130152332839230600956739001 97614249629422950717554251)
              ·
                refine ⟨146421374444134426076331377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97614249629422950717554251 146421374444134426076331377)
                ·
                  refine ⟨109816030833100819557248533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146421374444134426076331377 109816030833100819557248533)
                  ·
                    refine ⟨5147626445301600916746025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109816030833100819557248533 5147626445301600916746025)
                    ·
                      refine ⟨3860719833976200687559519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147626445301600916746025 3860719833976200687559519)
                      ·
                        rfl

theorem cell23_7518725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 6, 2].length) (baseStart_7518725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518725 prefixEnd_7518725 := by exact prefixLift 7518725
  have htrace : WordTrace (prefixWord ++ tailWord_7518725) baseStart_7518725 baseEnd_7518725 := by
    simpa [prefixWord, tailWord_7518725, baseEnd_7518725] using wordTrace_append hprefix tailTrace_7518725
  have hstable : (prefixWord ++ tailWord_7518725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518725).length < 2 ^ (prefixWord ++ tailWord_7518725).sum := by decide
  have hdescent : baseEnd_7518725 < baseStart_7518725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518748 : List Nat := [2, 2, 3, 1, 2, 13]
def baseStart_7518748 : Nat := 118140960795 + 7518748 * 2 ^ 59
def prefixEnd_7518748 : Nat := 4983230072969 + 3 ^ 40 * 7518748 * 2
def baseEnd_7518748 : Nat := 15887784543338494228691

theorem tailTrace_7518748 : CollatzResearch.WordTrace tailWord_7518748 prefixEnd_7518748 15887784543338494228691 := by
  unfold tailWord_7518748
  simp only [CollatzResearch.WordTrace]
  refine ⟨137115634282433785385546449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182820845709911713847395265 137115634282433785385546449)
  ·
    refine ⟨102836725711825339039159837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137115634282433785385546449 102836725711825339039159837)
    ·
      refine ⟨38563772141934502139684939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102836725711825339039159837 38563772141934502139684939)
      ·
        refine ⟨57845658212901753209527409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38563772141934502139684939 57845658212901753209527409)
        ·
          refine ⟨43384243659676314907145557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57845658212901753209527409 43384243659676314907145557)
          ·
            refine ⟨15887784543338494228691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 43384243659676314907145557 15887784543338494228691)
            ·
              rfl

theorem cell23_7518748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 13].length) (baseStart_7518748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518748 prefixEnd_7518748 := by exact prefixLift 7518748
  have htrace : WordTrace (prefixWord ++ tailWord_7518748) baseStart_7518748 baseEnd_7518748 := by
    simpa [prefixWord, tailWord_7518748, baseEnd_7518748] using wordTrace_append hprefix tailTrace_7518748
  have hstable : (prefixWord ++ tailWord_7518748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518748).length < 2 ^ (prefixWord ++ tailWord_7518748).sum := by decide
  have hdescent : baseEnd_7518748 < baseStart_7518748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518762 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_7518762 : Nat := 118140960795 + 7518762 * 2 ^ 59
def prefixEnd_7518762 : Nat := 4983230072969 + 3 ^ 40 * 7518762 * 2
def baseEnd_7518762 : Nat := 3860738832760417042796849

theorem tailTrace_7518762 : CollatzResearch.WordTrace tailWord_7518762 prefixEnd_7518762 3860738832760417042796849 := by
  unfold tailWord_7518762
  simp only [CollatzResearch.WordTrace]
  refine ⟨68557944796704212790525635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182821186124544567441401693 68557944796704212790525635)
  ·
    refine ⟨102836917195056319185788453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68557944796704212790525635 102836917195056319185788453)
    ·
      refine ⟨19281921974073059847335335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102836917195056319185788453 19281921974073059847335335)
      ·
        refine ⟨28922882961109589771003003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19281921974073059847335335 28922882961109589771003003)
        ·
          refine ⟨43384324441664384656504505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28922882961109589771003003 43384324441664384656504505)
          ·
            refine ⟨32538243331248288492378379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43384324441664384656504505 32538243331248288492378379)
            ·
              refine ⟨48807364996872432738567569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32538243331248288492378379 48807364996872432738567569)
              ·
                refine ⟨36605523747654324553925677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48807364996872432738567569 36605523747654324553925677)
                ·
                  refine ⟨13727071405370371707722129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36605523747654324553925677 13727071405370371707722129)
                  ·
                    refine ⟨10295303554027778780791597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13727071405370371707722129 10295303554027778780791597)
                    ·
                      refine ⟨3860738832760417042796849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10295303554027778780791597 3860738832760417042796849)
                      ·
                        rfl

theorem cell23_7518762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_7518762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518762 prefixEnd_7518762 := by exact prefixLift 7518762
  have htrace : WordTrace (prefixWord ++ tailWord_7518762) baseStart_7518762 baseEnd_7518762 := by
    simpa [prefixWord, tailWord_7518762, baseEnd_7518762] using wordTrace_append hprefix tailTrace_7518762
  have hstable : (prefixWord ++ tailWord_7518762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518762).length < 2 ^ (prefixWord ++ tailWord_7518762).sum := by decide
  have hdescent : baseEnd_7518762 < baseStart_7518762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518768 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 6]
def baseStart_7518768 : Nat := 118140960795 + 7518768 * 2 ^ 59
def prefixEnd_7518768 : Nat := 4983230072969 + 3 ^ 40 * 7518768 * 2
def baseEnd_7518768 : Nat := 3860741913644344019321821

theorem tailTrace_7518768 : CollatzResearch.WordTrace tailWord_7518768 prefixEnd_7518768 3860741913644344019321821 := by
  unfold tailWord_7518768
  simp only [CollatzResearch.WordTrace]
  refine ⟨137115999012397557093410479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182821332016530076124547305 137115999012397557093410479)
  ·
    refine ⟨205673998518596335640115719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137115999012397557093410479 205673998518596335640115719)
    ·
      refine ⟨308510997777894503460173579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205673998518596335640115719 308510997777894503460173579)
      ·
        refine ⟨462766496666841755190260369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308510997777894503460173579 462766496666841755190260369)
        ·
          refine ⟨347074872500131316392695277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462766496666841755190260369 347074872500131316392695277)
          ·
            refine ⟨130153077187549243647260729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347074872500131316392695277 130153077187549243647260729)
            ·
              refine ⟨97614807890661932735445547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130153077187549243647260729 97614807890661932735445547)
              ·
                refine ⟨146422211835992899103168321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97614807890661932735445547 146422211835992899103168321)
                ·
                  refine ⟨109816658876994674327376241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146422211835992899103168321 109816658876994674327376241)
                  ·
                    refine ⟨82362494157746005745532181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109816658876994674327376241 82362494157746005745532181)
                    ·
                      refine ⟨3860741913644344019321821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82362494157746005745532181 3860741913644344019321821)
                      ·
                        rfl

theorem cell23_7518768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_7518768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518768 prefixEnd_7518768 := by exact prefixLift 7518768
  have htrace : WordTrace (prefixWord ++ tailWord_7518768) baseStart_7518768 baseEnd_7518768 := by
    simpa [prefixWord, tailWord_7518768, baseEnd_7518768] using wordTrace_append hprefix tailTrace_7518768
  have hstable : (prefixWord ++ tailWord_7518768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518768).length < 2 ^ (prefixWord ++ tailWord_7518768).sum := by decide
  have hdescent : baseEnd_7518768 < baseStart_7518768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518826 : List Nat := [3, 1, 3, 2, 1, 1, 5, 1, 2, 1, 3]
def baseStart_7518826 : Nat := 118140960795 + 7518826 * 2 ^ 59
def prefixEnd_7518826 : Nat := 4983230072969 + 3 ^ 40 * 7518826 * 2
def baseEnd_7518826 : Nat := 3860771695522304792396555

theorem tailTrace_7518826 : CollatzResearch.WordTrace tailWord_7518826 prefixEnd_7518826 3860771695522304792396555 := by
  unfold tailWord_7518826
  simp only [CollatzResearch.WordTrace]
  refine ⟨68558528364646247523108083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182822742305723326728288221 68558528364646247523108083)
  ·
    refine ⟨102837792546969371284662125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68558528364646247523108083 102837792546969371284662125)
    ·
      refine ⟨38564172205113514231748297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102837792546969371284662125 38564172205113514231748297)
      ·
        refine ⟨28923129153835135673811223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38564172205113514231748297 28923129153835135673811223)
        ·
          refine ⟨43384693730752703510716835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28923129153835135673811223 43384693730752703510716835)
          ·
            refine ⟨65077040596129055266075253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43384693730752703510716835 65077040596129055266075253)
            ·
              refine ⟨6100972555887098931194555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65077040596129055266075253 6100972555887098931194555)
              ·
                refine ⟨9151458833830648396791833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6100972555887098931194555 9151458833830648396791833)
                ·
                  refine ⟨6863594125372986297593875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9151458833830648396791833 6863594125372986297593875)
                  ·
                    refine ⟨10295391188059479446390813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6863594125372986297593875 10295391188059479446390813)
                    ·
                      refine ⟨3860771695522304792396555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10295391188059479446390813 3860771695522304792396555)
                      ·
                        rfl

theorem cell23_7518826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_7518826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518826 prefixEnd_7518826 := by exact prefixLift 7518826
  have htrace : WordTrace (prefixWord ++ tailWord_7518826) baseStart_7518826 baseEnd_7518826 := by
    simpa [prefixWord, tailWord_7518826, baseEnd_7518826] using wordTrace_append hprefix tailTrace_7518826
  have hstable : (prefixWord ++ tailWord_7518826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518826).length < 2 ^ (prefixWord ++ tailWord_7518826).sum := by decide
  have hdescent : baseEnd_7518826 < baseStart_7518826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518849 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 6, 2, 2]
def baseStart_7518849 : Nat := 118140960795 + 7518849 * 2 ^ 59
def prefixEnd_7518849 : Nat := 4983230072969 + 3 ^ 40 * 7518849 * 2
def baseEnd_7518849 : Nat := 3860783505577358202408949

theorem tailTrace_7518849 : CollatzResearch.WordTrace tailWord_7518849 prefixEnd_7518849 3860783505577358202408949 := by
  unfold tailWord_7518849
  simp only [CollatzResearch.WordTrace]
  refine ⟨274234952337501665020519601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182823301558334443347013067 274234952337501665020519601)
  ·
    refine ⟨205676214253126248765389701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274234952337501665020519601 205676214253126248765389701)
    ·
      refine ⟨38564290172461171643510569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205676214253126248765389701 38564290172461171643510569)
      ·
        refine ⟨28923217629345878732632927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38564290172461171643510569 28923217629345878732632927)
        ·
          refine ⟨43384826444018818098949391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28923217629345878732632927 43384826444018818098949391)
          ·
            refine ⟨65077239666028227148424087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43384826444018818098949391 65077239666028227148424087)
            ·
              refine ⟨97615859499042340722636131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65077239666028227148424087 97615859499042340722636131)
              ·
                refine ⟨146423789248563511083954197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97615859499042340722636131 146423789248563511083954197)
                ·
                  refine ⟨6863615121026414582060353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146423789248563511083954197 6863615121026414582060353)
                  ·
                    refine ⟨5147711340769810936545265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6863615121026414582060353 5147711340769810936545265)
                    ·
                      refine ⟨3860783505577358202408949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147711340769810936545265 3860783505577358202408949)
                      ·
                        rfl

theorem cell23_7518849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_7518849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518849 prefixEnd_7518849 := by exact prefixLift 7518849
  have htrace : WordTrace (prefixWord ++ tailWord_7518849) baseStart_7518849 baseEnd_7518849 := by
    simpa [prefixWord, tailWord_7518849, baseEnd_7518849] using wordTrace_append hprefix tailTrace_7518849
  have hstable : (prefixWord ++ tailWord_7518849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518849).length < 2 ^ (prefixWord ++ tailWord_7518849).sum := by decide
  have hdescent : baseEnd_7518849 < baseStart_7518849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518852 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_7518852 : Nat := 118140960795 + 7518852 * 2 ^ 59
def prefixEnd_7518852 : Nat := 4983230072969 + 3 ^ 40 * 7518852 * 2
def baseEnd_7518852 : Nat := 3860785046019321690671435

theorem tailTrace_7518852 : CollatzResearch.WordTrace tailWord_7518852 prefixEnd_7518852 3860785046019321690671435 := by
  unfold tailWord_7518852
  simp only [CollatzResearch.WordTrace]
  refine ⟨137117530878245398266439405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182823374504327197688585873 137117530878245398266439405)
  ·
    refine ⟨51419074079342024349914777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137117530878245398266439405 51419074079342024349914777)
    ·
      refine ⟨38564305559506518262436083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51419074079342024349914777 38564305559506518262436083)
      ·
        refine ⟨57846458339259777393654125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38564305559506518262436083 57846458339259777393654125)
        ·
          refine ⟨21692421877222416522620297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57846458339259777393654125 21692421877222416522620297)
          ·
            refine ⟨16269316407916812391965223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21692421877222416522620297 16269316407916812391965223)
            ·
              refine ⟨24403974611875218587947835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16269316407916812391965223 24403974611875218587947835)
              ·
                refine ⟨36605961917812827881921753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24403974611875218587947835 36605961917812827881921753)
                ·
                  refine ⟨27454471438359620911441315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36605961917812827881921753 27454471438359620911441315)
                  ·
                    refine ⟨41181707157539431367161973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27454471438359620911441315 41181707157539431367161973)
                    ·
                      refine ⟨3860785046019321690671435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41181707157539431367161973 3860785046019321690671435)
                      ·
                        rfl

theorem cell23_7518852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_7518852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518852 prefixEnd_7518852 := by exact prefixLift 7518852
  have htrace : WordTrace (prefixWord ++ tailWord_7518852) baseStart_7518852 baseEnd_7518852 := by
    simpa [prefixWord, tailWord_7518852, baseEnd_7518852] using wordTrace_append hprefix tailTrace_7518852
  have hstable : (prefixWord ++ tailWord_7518852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518852).length < 2 ^ (prefixWord ++ tailWord_7518852).sum := by decide
  have hdescent : baseEnd_7518852 < baseStart_7518852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518866 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_7518866 : Nat := 118140960795 + 7518866 * 2 ^ 59
def prefixEnd_7518866 : Nat := 4983230072969 + 3 ^ 40 * 7518866 * 2
def baseEnd_7518866 : Nat := 3860792234748484635896371

theorem tailTrace_7518866 : CollatzResearch.WordTrace tailWord_7518866 prefixEnd_7518866 3860792234748484635896371 := by
  unfold tailWord_7518866
  simp only [CollatzResearch.WordTrace]
  refine ⟨68558893094610019230972113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182823714918960051282592301 68558893094610019230972113)
  ·
    refine ⟨51419169820957514423229085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68558893094610019230972113 51419169820957514423229085)
    ·
      refine ⟨19282188682859067908710907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51419169820957514423229085 19282188682859067908710907)
      ·
        refine ⟨28923283024288601863066361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19282188682859067908710907 28923283024288601863066361)
        ·
          refine ⟨21692462268216451397299771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28923283024288601863066361 21692462268216451397299771)
          ·
            refine ⟨32538693402324677095949657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21692462268216451397299771 32538693402324677095949657)
            ·
              refine ⟨24404020051743507821962243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32538693402324677095949657 24404020051743507821962243)
              ·
                refine ⟨36606030077615261732943365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24404020051743507821962243 36606030077615261732943365)
                ·
                  refine ⟨6863630639552861574926881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36606030077615261732943365 6863630639552861574926881)
                  ·
                    refine ⟨5147722979664646181195161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6863630639552861574926881 5147722979664646181195161)
                    ·
                      refine ⟨3860792234748484635896371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147722979664646181195161 3860792234748484635896371)
                      ·
                        rfl

theorem cell23_7518866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_7518866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518866 prefixEnd_7518866 := by exact prefixLift 7518866
  have htrace : WordTrace (prefixWord ++ tailWord_7518866) baseStart_7518866 baseEnd_7518866 := by
    simpa [prefixWord, tailWord_7518866, baseEnd_7518866] using wordTrace_append hprefix tailTrace_7518866
  have hstable : (prefixWord ++ tailWord_7518866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518866).length < 2 ^ (prefixWord ++ tailWord_7518866).sum := by decide
  have hdescent : baseEnd_7518866 < baseStart_7518866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518885 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 6, 5]
def baseStart_7518885 : Nat := 118140960795 + 7518885 * 2 ^ 59
def prefixEnd_7518885 : Nat := 4983230072969 + 3 ^ 40 * 7518885 * 2
def baseEnd_7518885 : Nat := 1286933996960306687186261

theorem tailTrace_7518885 : CollatzResearch.WordTrace tailWord_7518885 prefixEnd_7518885 1286933996960306687186261 := by
  unfold tailWord_7518885
  simp only [CollatzResearch.WordTrace]
  refine ⟨274236265365371243168830109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182824176910247495445886739 274236265365371243168830109)
  ·
    refine ⟨102838599512014216188311291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274236265365371243168830109 102838599512014216188311291)
    ·
      refine ⟨154257899268021324282466937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102838599512014216188311291 154257899268021324282466937)
      ·
        refine ⟨115693424451015993211850203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154257899268021324282466937 115693424451015993211850203)
        ·
          refine ⟨173540136676523989817775305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115693424451015993211850203 173540136676523989817775305)
          ·
            refine ⟨130155102507392992363331479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173540136676523989817775305 130155102507392992363331479)
            ·
              refine ⟨195232653761089488544997219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130155102507392992363331479 195232653761089488544997219)
              ·
                refine ⟨292848980641634232817495829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195232653761089488544997219 292848980641634232817495829)
                ·
                  refine ⟨13727295967576604663320117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 292848980641634232817495829 13727295967576604663320117)
                  ·
                    refine ⟨1286933996960306687186261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13727295967576604663320117 1286933996960306687186261)
                    ·
                      rfl

theorem cell23_7518885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_7518885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518885 prefixEnd_7518885 := by exact prefixLift 7518885
  have htrace : WordTrace (prefixWord ++ tailWord_7518885) baseStart_7518885 baseEnd_7518885 := by
    simpa [prefixWord, tailWord_7518885, baseEnd_7518885] using wordTrace_append hprefix tailTrace_7518885
  have hstable : (prefixWord ++ tailWord_7518885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518885).length < 2 ^ (prefixWord ++ tailWord_7518885).sum := by decide
  have hdescent : baseEnd_7518885 < baseStart_7518885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518949 : List Nat := [1, 3, 1, 4, 1, 3, 1, 2, 3, 4]
def baseStart_7518949 : Nat := 118140960795 + 7518949 * 2 ^ 59
def prefixEnd_7518949 : Nat := 4983230072969 + 3 ^ 40 * 7518949 * 2
def baseEnd_7518949 : Nat := 1286944951214269270386163

theorem tailTrace_7518949 : CollatzResearch.WordTrace tailWord_7518949 prefixEnd_7518949 1286944951214269270386163 := by
  unfold tailWord_7518949
  simp only [CollatzResearch.WordTrace]
  refine ⟨274238599637139382099159901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182825733091426254732773267 274238599637139382099159901)
  ·
    refine ⟨102839474863927268287184963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274238599637139382099159901 102839474863927268287184963)
    ·
      refine ⟨154259212295890902430777445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102839474863927268287184963 154259212295890902430777445)
      ·
        refine ⟨28923602305479544205770771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154259212295890902430777445 28923602305479544205770771)
        ·
          refine ⟨43385403458219316308656157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28923602305479544205770771 43385403458219316308656157)
          ·
            refine ⟨16269526296832243615746059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43385403458219316308656157 16269526296832243615746059)
            ·
              refine ⟨24404289445248365423619089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16269526296832243615746059 24404289445248365423619089)
              ·
                refine ⟨18303217083936274067714317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24404289445248365423619089 18303217083936274067714317)
                ·
                  refine ⟨6863706406476102775392869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18303217083936274067714317 6863706406476102775392869)
                  ·
                    refine ⟨1286944951214269270386163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6863706406476102775392869 1286944951214269270386163)
                    ·
                      rfl

theorem cell23_7518949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_7518949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518949 prefixEnd_7518949 := by exact prefixLift 7518949
  have htrace : WordTrace (prefixWord ++ tailWord_7518949) baseStart_7518949 baseEnd_7518949 := by
    simpa [prefixWord, tailWord_7518949, baseEnd_7518949] using wordTrace_append hprefix tailTrace_7518949
  have hstable : (prefixWord ++ tailWord_7518949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518949).length < 2 ^ (prefixWord ++ tailWord_7518949).sum := by decide
  have hdescent : baseEnd_7518949 < baseStart_7518949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518959 : List Nat := [1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 3]
def baseStart_7518959 : Nat := 118140960795 + 7518959 * 2 ^ 59
def prefixEnd_7518959 : Nat := 4983230072969 + 3 ^ 40 * 7518959 * 2
def baseEnd_7518959 : Nat := 3860839988449352772033443

theorem tailTrace_7518959 : CollatzResearch.WordTrace tailWord_7518959 prefixEnd_7518959 3860839988449352772033443 := by
  unfold tailWord_7518959
  simp only [CollatzResearch.WordTrace]
  refine ⟨274238964367103153807023931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182825976244735435871349287 274238964367103153807023931)
  ·
    refine ⟨411358446550654730710535897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274238964367103153807023931 411358446550654730710535897)
    ·
      refine ⟨308518834912991048032901923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411358446550654730710535897 308518834912991048032901923)
      ·
        refine ⟨462778252369486572049352885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308518834912991048032901923 462778252369486572049352885)
        ·
          refine ⟨43385461159639366129626833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 462778252369486572049352885 43385461159639366129626833)
          ·
            refine ⟨32539095869729524597220125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43385461159639366129626833 32539095869729524597220125)
            ·
              refine ⟨12202160951148571723957547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32539095869729524597220125 12202160951148571723957547)
              ·
                refine ⟨18303241426722857585936321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12202160951148571723957547 18303241426722857585936321)
                ·
                  refine ⟨13727431070042143189452241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18303241426722857585936321 13727431070042143189452241)
                  ·
                    refine ⟨10295573302531607392089181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13727431070042143189452241 10295573302531607392089181)
                    ·
                      refine ⟨3860839988449352772033443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10295573302531607392089181 3860839988449352772033443)
                      ·
                        rfl

theorem cell23_7518959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 3].length) (baseStart_7518959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518959 prefixEnd_7518959 := by exact prefixLift 7518959
  have htrace : WordTrace (prefixWord ++ tailWord_7518959) baseStart_7518959 baseEnd_7518959 := by
    simpa [prefixWord, tailWord_7518959, baseEnd_7518959] using wordTrace_append hprefix tailTrace_7518959
  have hstable : (prefixWord ++ tailWord_7518959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518959).length < 2 ^ (prefixWord ++ tailWord_7518959).sum := by decide
  have hdescent : baseEnd_7518959 < baseStart_7518959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519009 : List Nat := [1, 2, 3, 2, 1, 2, 4, 2, 1, 5]
def baseStart_7519009 : Nat := 118140960795 + 7519009 * 2 ^ 59
def prefixEnd_7519009 : Nat := 4983230072969 + 3 ^ 40 * 7519009 * 2
def baseEnd_7519009 : Nat := 1286955220827359192136071

theorem tailTrace_7519009 : CollatzResearch.WordTrace tailWord_7519009 prefixEnd_7519009 1286955220827359192136071 := by
  unfold tailWord_7519009
  simp only [CollatzResearch.WordTrace]
  refine ⟨274240788016922012346344081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182827192011281341564229387 274240788016922012346344081)
  ·
    refine ⟨205680591012691509259758061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274240788016922012346344081 205680591012691509259758061)
    ·
      refine ⟨77130221629759315972409273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205680591012691509259758061 77130221629759315972409273)
      ·
        refine ⟨57847666222319486979306955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77130221629759315972409273 57847666222319486979306955)
        ·
          refine ⟨86771499333479230468960433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57847666222319486979306955 86771499333479230468960433)
          ·
            refine ⟨65078624500109422851720325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86771499333479230468960433 65078624500109422851720325)
            ·
              refine ⟨12202242093770516784697561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65078624500109422851720325 12202242093770516784697561)
              ·
                refine ⟨9151681570327887588523171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12202242093770516784697561 9151681570327887588523171)
                ·
                  refine ⟨13727522355491831382784757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9151681570327887588523171 13727522355491831382784757)
                  ·
                    refine ⟨1286955220827359192136071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13727522355491831382784757 1286955220827359192136071)
                    ·
                      rfl

theorem cell23_7519009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_7519009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519009 prefixEnd_7519009 := by exact prefixLift 7519009
  have htrace : WordTrace (prefixWord ++ tailWord_7519009) baseStart_7519009 baseEnd_7519009 := by
    simpa [prefixWord, tailWord_7519009, baseEnd_7519009] using wordTrace_append hprefix tailTrace_7519009
  have hstable : (prefixWord ++ tailWord_7519009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519009).length < 2 ^ (prefixWord ++ tailWord_7519009).sum := by decide
  have hdescent : baseEnd_7519009 < baseStart_7519009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519016 : List Nat := [2, 1, 5, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_7519016 : Nat := 118140960795 + 7519016 * 2 ^ 59
def prefixEnd_7519016 : Nat := 4983230072969 + 3 ^ 40 * 7519016 * 2
def baseEnd_7519016 : Nat := 3860869256846659049020681

theorem tailTrace_7519016 : CollatzResearch.WordTrace tailWord_7519016 prefixEnd_7519016 3860869256846659049020681 := by
  unfold tailWord_7519016
  simp only [CollatzResearch.WordTrace]
  refine ⟨137120521663948326270924451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182827362218597768361232601 137120521663948326270924451)
  ·
    refine ⟨205680782495922489406386677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137120521663948326270924451 205680782495922489406386677)
    ·
      refine ⟨19282573358992733381848751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205680782495922489406386677 19282573358992733381848751)
      ·
        refine ⟨28923860038489100072773127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19282573358992733381848751 28923860038489100072773127)
        ·
          refine ⟨43385790057733650109159691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28923860038489100072773127 43385790057733650109159691)
          ·
            refine ⟨65078685086600475163739537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43385790057733650109159691 65078685086600475163739537)
            ·
              refine ⟨48809013814950356372804653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65078685086600475163739537 48809013814950356372804653)
              ·
                refine ⟨18303380180606383639801745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48809013814950356372804653 18303380180606383639801745)
                ·
                  refine ⟨13727535135454787729851309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18303380180606383639801745 13727535135454787729851309)
                  ·
                    refine ⟨5147825675795545398694241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13727535135454787729851309 5147825675795545398694241)
                    ·
                      refine ⟨3860869256846659049020681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147825675795545398694241 3860869256846659049020681)
                      ·
                        rfl

theorem cell23_7519016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_7519016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519016 prefixEnd_7519016 := by exact prefixLift 7519016
  have htrace : WordTrace (prefixWord ++ tailWord_7519016) baseStart_7519016 baseEnd_7519016 := by
    simpa [prefixWord, tailWord_7519016, baseEnd_7519016] using wordTrace_append hprefix tailTrace_7519016
  have hstable : (prefixWord ++ tailWord_7519016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519016).length < 2 ^ (prefixWord ++ tailWord_7519016).sum := by decide
  have hdescent : baseEnd_7519016 < baseStart_7519016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519039 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 4, 4]
def baseStart_7519039 : Nat := 118140960795 + 7519039 * 2 ^ 59
def prefixEnd_7519039 : Nat := 4983230072969 + 3 ^ 40 * 7519039 * 2
def baseEnd_7519039 : Nat := 1286960355633904153011025

theorem tailTrace_7519039 : CollatzResearch.WordTrace tailWord_7519039 prefixEnd_7519039 1286960355633904153011025 := by
  unfold tailWord_7519039
  simp only [CollatzResearch.WordTrace]
  refine ⟨274241882206813327469936171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182827921471208884979957447 274241882206813327469936171)
  ·
    refine ⟨411362823310219991204904257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274241882206813327469936171 411362823310219991204904257)
    ·
      refine ⟨308522117482664993403678193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411362823310219991204904257 308522117482664993403678193)
      ·
        refine ⟨231391588111998745052758645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308522117482664993403678193 231391588111998745052758645)
        ·
          refine ⟨21692961385499882348696123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 231391588111998745052758645 21692961385499882348696123)
          ·
            refine ⟨32539442078249823523044185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21692961385499882348696123 32539442078249823523044185)
            ·
              refine ⟨24404581558687367642283139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32539442078249823523044185 24404581558687367642283139)
              ·
                refine ⟨36606872338031051463424709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24404581558687367642283139 36606872338031051463424709)
                ·
                  refine ⟨6863788563380822149392133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36606872338031051463424709 6863788563380822149392133)
                  ·
                    refine ⟨1286960355633904153011025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6863788563380822149392133 1286960355633904153011025)
                    ·
                      rfl

theorem cell23_7519039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 4].length) (baseStart_7519039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519039 prefixEnd_7519039 := by exact prefixLift 7519039
  have htrace : WordTrace (prefixWord ++ tailWord_7519039) baseStart_7519039 baseEnd_7519039 := by
    simpa [prefixWord, tailWord_7519039, baseEnd_7519039] using wordTrace_append hprefix tailTrace_7519039
  have hstable : (prefixWord ++ tailWord_7519039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519039).length < 2 ^ (prefixWord ++ tailWord_7519039).sum := by decide
  have hdescent : baseEnd_7519039 < baseStart_7519039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519052 : List Nat := [2, 2, 1, 3, 3, 1, 1, 10]
def baseStart_7519052 : Nat := 118140960795 + 7519052 * 2 ^ 59
def prefixEnd_7519052 : Nat := 4983230072969 + 3 ^ 40 * 7519052 * 2
def baseEnd_7519052 : Nat := 142995842301860033635945

theorem tailTrace_7519052 : CollatzResearch.WordTrace tailWord_7519052 prefixEnd_7519052 142995842301860033635945 := by
  unfold tailWord_7519052
  simp only [CollatzResearch.WordTrace]
  refine ⟨137121178177883115345079705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182828237570510820460106273 137121178177883115345079705)
  ·
    refine ⟨102840883633412336508809779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137121178177883115345079705 102840883633412336508809779)
    ·
      refine ⟨154261325450118504763214669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102840883633412336508809779 154261325450118504763214669)
      ·
        refine ⟨57847997043794439286205501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154261325450118504763214669 57847997043794439286205501)
        ·
          refine ⟨21692998891422914732327063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57847997043794439286205501 21692998891422914732327063)
          ·
            refine ⟨32539498337134372098490595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21692998891422914732327063 32539498337134372098490595)
            ·
              refine ⟨48809247505701558147735893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32539498337134372098490595 48809247505701558147735893)
              ·
                refine ⟨142995842301860033635945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48809247505701558147735893 142995842301860033635945)
                ·
                  rfl

theorem cell23_7519052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 10].length) (baseStart_7519052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519052 prefixEnd_7519052 := by exact prefixLift 7519052
  have htrace : WordTrace (prefixWord ++ tailWord_7519052) baseStart_7519052 baseEnd_7519052 := by
    simpa [prefixWord, tailWord_7519052, baseEnd_7519052] using wordTrace_append hprefix tailTrace_7519052
  have hstable : (prefixWord ++ tailWord_7519052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519052).length < 2 ^ (prefixWord ++ tailWord_7519052).sum := by decide
  have hdescent : baseEnd_7519052 < baseStart_7519052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519056 : List Nat := [2, 1, 1, 1, 1, 4, 6, 1, 2, 4]
def baseStart_7519056 : Nat := 118140960795 + 7519056 * 2 ^ 59
def prefixEnd_7519056 : Nat := 4983230072969 + 3 ^ 40 * 7519056 * 2
def baseEnd_7519056 : Nat := 1286963265357612964173499

theorem tailTrace_7519056 : CollatzResearch.WordTrace tailWord_7519056 prefixEnd_7519056 1286963265357612964173499 := by
  unfold tailWord_7519056
  simp only [CollatzResearch.WordTrace]
  refine ⟨137121251123875869686652511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182828334831834492915536681 137121251123875869686652511)
  ·
    refine ⟨205681876685813804529978767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137121251123875869686652511 205681876685813804529978767)
    ·
      refine ⟨308522815028720706794968151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205681876685813804529978767 308522815028720706794968151)
      ·
        refine ⟨462784222543081060192452227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308522815028720706794968151 462784222543081060192452227)
        ·
          refine ⟨694176333814621590288678341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462784222543081060192452227 694176333814621590288678341)
          ·
            refine ⟨130158062590241548179127189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 694176333814621590288678341 130158062590241548179127189)
            ·
              refine ⟨6101159183917572570896587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130158062590241548179127189 6101159183917572570896587)
              ·
                refine ⟨9151738775876358856344881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6101159183917572570896587 9151738775876358856344881)
                ·
                  refine ⟨6863804081907269142258661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9151738775876358856344881 6863804081907269142258661)
                  ·
                    refine ⟨1286963265357612964173499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6863804081907269142258661 1286963265357612964173499)
                    ·
                      rfl

theorem cell23_7519056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 2, 4].length) (baseStart_7519056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519056 prefixEnd_7519056 := by exact prefixLift 7519056
  have htrace : WordTrace (prefixWord ++ tailWord_7519056) baseStart_7519056 baseEnd_7519056 := by
    simpa [prefixWord, tailWord_7519056, baseEnd_7519056] using wordTrace_append hprefix tailTrace_7519056
  have hstable : (prefixWord ++ tailWord_7519056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519056).length < 2 ^ (prefixWord ++ tailWord_7519056).sum := by decide
  have hdescent : baseEnd_7519056 < baseStart_7519056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519066 : List Nat := [3, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3]
def baseStart_7519066 : Nat := 118140960795 + 7519066 * 2 ^ 59
def prefixEnd_7519066 : Nat := 4983230072969 + 3 ^ 40 * 7519066 * 2
def baseEnd_7519066 : Nat := 3860894930879383853395451

theorem tailTrace_7519066 : CollatzResearch.WordTrace tailWord_7519066 prefixEnd_7519066 3860894930879383853395451 := by
  unfold tailWord_7519066
  simp only [CollatzResearch.WordTrace]
  refine ⟨68560716744428877770292263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182828577985143674054112701 68560716744428877770292263)
  ·
    refine ⟨102841075116643316655438395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68560716744428877770292263 102841075116643316655438395)
    ·
      refine ⟨154261612674964974983157593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102841075116643316655438395 154261612674964974983157593)
      ·
        refine ⟨115696209506223731237368195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154261612674964974983157593 115696209506223731237368195)
        ·
          refine ⟨173544314259335596856052293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115696209506223731237368195 173544314259335596856052293)
          ·
            refine ⟨32539558923625424410509805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173544314259335596856052293 32539558923625424410509805)
            ·
              refine ⟨12202334596359534153941177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32539558923625424410509805 12202334596359534153941177)
              ·
                refine ⟨9151750947269650615455883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12202334596359534153941177 9151750947269650615455883)
                ·
                  refine ⟨13727626420904475923183825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9151750947269650615455883 13727626420904475923183825)
                  ·
                    refine ⟨10295719815678356942387869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13727626420904475923183825 10295719815678356942387869)
                    ·
                      refine ⟨3860894930879383853395451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10295719815678356942387869 3860894930879383853395451)
                      ·
                        rfl

theorem cell23_7519066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_7519066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519066 prefixEnd_7519066 := by exact prefixLift 7519066
  have htrace : WordTrace (prefixWord ++ tailWord_7519066) baseStart_7519066 baseEnd_7519066 := by
    simpa [prefixWord, tailWord_7519066, baseEnd_7519066] using wordTrace_append hprefix tailTrace_7519066
  have hstable : (prefixWord ++ tailWord_7519066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519066).length < 2 ^ (prefixWord ++ tailWord_7519066).sum := by decide
  have hdescent : baseEnd_7519066 < baseStart_7519066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519079 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_7519079 : Nat := 118140960795 + 7519079 * 2 ^ 59
def prefixEnd_7519079 : Nat := 4983230072969 + 3 ^ 40 * 7519079 * 2
def baseEnd_7519079 : Nat := 3860901606127892302532891

theorem tailTrace_7519079 : CollatzResearch.WordTrace tailWord_7519079 prefixEnd_7519079 3860901606127892302532891 := by
  unfold tailWord_7519079
  simp only [CollatzResearch.WordTrace]
  refine ⟨274243341126668414301392291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182828894084445609534261527 274243341126668414301392291)
  ·
    refine ⟨411365011690002621452088437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274243341126668414301392291 411365011690002621452088437)
    ·
      refine ⟨38565469845937745761133291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 411365011690002621452088437 38565469845937745761133291)
      ·
        refine ⟨57848204768906618641699937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38565469845937745761133291 57848204768906618641699937)
        ·
          refine ⟨43386153576679963981274953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57848204768906618641699937 43386153576679963981274953)
          ·
            refine ⟨32539615182509972985956215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43386153576679963981274953 32539615182509972985956215)
            ·
              refine ⟨48809422773764959478934323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32539615182509972985956215 48809422773764959478934323)
              ·
                refine ⟨73214134160647439218401485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48809422773764959478934323 73214134160647439218401485)
                ·
                  refine ⟨27455300310242789706900557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73214134160647439218401485 27455300310242789706900557)
                  ·
                    refine ⟨10295737616341046140087709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27455300310242789706900557 10295737616341046140087709)
                    ·
                      refine ⟨3860901606127892302532891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10295737616341046140087709 3860901606127892302532891)
                      ·
                        rfl

theorem cell23_7519079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_7519079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519079 prefixEnd_7519079 := by exact prefixLift 7519079
  have htrace : WordTrace (prefixWord ++ tailWord_7519079) baseStart_7519079 baseEnd_7519079 := by
    simpa [prefixWord, tailWord_7519079, baseEnd_7519079] using wordTrace_append hprefix tailTrace_7519079
  have hstable : (prefixWord ++ tailWord_7519079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519079).length < 2 ^ (prefixWord ++ tailWord_7519079).sum := by decide
  have hdescent : baseEnd_7519079 < baseStart_7519079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519097 : List Nat := [1, 2, 1, 3, 2, 5, 2, 2, 1, 2, 2]
def baseStart_7519097 : Nat := 118140960795 + 7519097 * 2 ^ 59
def prefixEnd_7519097 : Nat := 4983230072969 + 3 ^ 40 * 7519097 * 2
def baseEnd_7519097 : Nat := 3860910848779673232107809

theorem tailTrace_7519097 : CollatzResearch.WordTrace tailWord_7519097 prefixEnd_7519097 3860910848779673232107809 := by
  unfold tailWord_7519097
  simp only [CollatzResearch.WordTrace]
  refine ⟨274243997640603203375547545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182829331760402135583698363 274243997640603203375547545)
  ·
    refine ⟨205682998230452402531660659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274243997640603203375547545 205682998230452402531660659)
    ·
      refine ⟨308524497345678603797490989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205682998230452402531660659 308524497345678603797490989)
      ·
        refine ⟨115696686504629476424059121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308524497345678603797490989 115696686504629476424059121)
        ·
          refine ⟨86772514878472107318044341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115696686504629476424059121 86772514878472107318044341)
          ·
            refine ⟨8134923269856760061066657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86772514878472107318044341 8134923269856760061066657)
            ·
              refine ⟨6101192452392570045799993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8134923269856760061066657 6101192452392570045799993)
              ·
                refine ⟨4575894339294427534349995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6101192452392570045799993 4575894339294427534349995)
                ·
                  refine ⟨6863841508941641301524993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4575894339294427534349995 6863841508941641301524993)
                  ·
                    refine ⟨5147881131706230976143745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6863841508941641301524993 5147881131706230976143745)
                    ·
                      refine ⟨3860910848779673232107809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147881131706230976143745 3860910848779673232107809)
                      ·
                        rfl

theorem cell23_7519097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_7519097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519097 prefixEnd_7519097 := by exact prefixLift 7519097
  have htrace : WordTrace (prefixWord ++ tailWord_7519097) baseStart_7519097 baseEnd_7519097 := by
    simpa [prefixWord, tailWord_7519097, baseEnd_7519097] using wordTrace_append hprefix tailTrace_7519097
  have hstable : (prefixWord ++ tailWord_7519097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519097).length < 2 ^ (prefixWord ++ tailWord_7519097).sum := by decide
  have hdescent : baseEnd_7519097 < baseStart_7519097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519136 : List Nat := [2, 1, 1, 4, 1, 1, 4, 2, 1, 4, 2]
def baseStart_7519136 : Nat := 118140960795 + 7519136 * 2 ^ 59
def prefixEnd_7519136 : Nat := 4983230072969 + 3 ^ 40 * 7519136 * 2
def baseEnd_7519136 : Nat := 3860930874525198579520129

theorem tailTrace_7519136 : CollatzResearch.WordTrace tailWord_7519136 prefixEnd_7519136 3860930874525198579520129 := by
  unfold tailWord_7519136
  simp only [CollatzResearch.WordTrace]
  refine ⟨137122710043730956518108631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182830280058307942024144841 137122710043730956518108631)
  ·
    refine ⟨205684065065596434777162947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137122710043730956518108631 205684065065596434777162947)
    ·
      refine ⟨308526097598394652165744421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205684065065596434777162947 308526097598394652165744421)
      ·
        refine ⟨57848643299698997281077079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 308526097598394652165744421 57848643299698997281077079)
        ·
          refine ⟨86772964949548495921615619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57848643299698997281077079 86772964949548495921615619)
          ·
            refine ⟨130159447424322743882423429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86772964949548495921615619 130159447424322743882423429)
            ·
              refine ⟨24404896392060514477954393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130159447424322743882423429 24404896392060514477954393)
              ·
                refine ⟨18303672294045385858465795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24404896392060514477954393 18303672294045385858465795)
                ·
                  refine ⟨27455508441068078787698693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18303672294045385858465795 27455508441068078787698693)
                  ·
                    refine ⟨5147907832700264772693505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27455508441068078787698693 5147907832700264772693505)
                    ·
                      refine ⟨3860930874525198579520129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147907832700264772693505 3860930874525198579520129)
                      ·
                        rfl

theorem cell23_7519136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_7519136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519136 prefixEnd_7519136 := by exact prefixLift 7519136
  have htrace : WordTrace (prefixWord ++ tailWord_7519136) baseStart_7519136 baseEnd_7519136 := by
    simpa [prefixWord, tailWord_7519136, baseEnd_7519136] using wordTrace_append hprefix tailTrace_7519136
  have hstable : (prefixWord ++ tailWord_7519136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519136).length < 2 ^ (prefixWord ++ tailWord_7519136).sum := by decide
  have hdescent : baseEnd_7519136 < baseStart_7519136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519193 : List Nat := [1, 2, 1, 2, 5, 3, 1, 3, 5]
def baseStart_7519193 : Nat := 118140960795 + 7519193 * 2 ^ 59
def prefixEnd_7519193 : Nat := 4983230072969 + 3 ^ 40 * 7519193 * 2
def baseEnd_7519193 : Nat := 428995571435833872945263

theorem tailTrace_7519193 : CollatzResearch.WordTrace tailWord_7519193 prefixEnd_7519193 428995571435833872945263 := by
  unfold tailWord_7519193
  simp only [CollatzResearch.WordTrace]
  refine ⟨274247499048255411771042233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182831666032170274514028155 274247499048255411771042233)
  ·
    refine ⟨205685624286191558828281675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274247499048255411771042233 205685624286191558828281675)
    ·
      refine ⟨308528436429287338242422513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205685624286191558828281675 308528436429287338242422513)
      ·
        refine ⟨231396327321965503681816885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308528436429287338242422513 231396327321965503681816885)
        ·
          refine ⟨21693405686434265970170333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 231396327321965503681816885 21693405686434265970170333)
          ·
            refine ⟨8135027132412849738813875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21693405686434265970170333 8135027132412849738813875)
            ·
              refine ⟨12202540698619274608220813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8135027132412849738813875 12202540698619274608220813)
              ·
                refine ⟨4575952761982227978082805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12202540698619274608220813 4575952761982227978082805)
                ·
                  refine ⟨428995571435833872945263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4575952761982227978082805 428995571435833872945263)
                  ·
                    rfl

theorem cell23_7519193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 5].length) (baseStart_7519193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519193 prefixEnd_7519193 := by exact prefixLift 7519193
  have htrace : WordTrace (prefixWord ++ tailWord_7519193) baseStart_7519193 baseEnd_7519193 := by
    simpa [prefixWord, tailWord_7519193, baseEnd_7519193] using wordTrace_append hprefix tailTrace_7519193
  have hstable : (prefixWord ++ tailWord_7519193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519193).length < 2 ^ (prefixWord ++ tailWord_7519193).sum := by decide
  have hdescent : baseEnd_7519193 < baseStart_7519193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519221 : List Nat := [1, 3, 5, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_7519221 : Nat := 118140960795 + 7519221 * 2 ^ 59
def prefixEnd_7519221 : Nat := 4983230072969 + 3 ^ 40 * 7519221 * 2
def baseEnd_7519221 : Nat := 3860974520380830746957239

theorem tailTrace_7519221 : CollatzResearch.WordTrace tailWord_7519221 prefixEnd_7519221 3860974520380830746957239 := by
  unfold tailWord_7519221
  simp only [CollatzResearch.WordTrace]
  refine ⟨274248520292153972553061517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182832346861435981702041011 274248520292153972553061517)
  ·
    refine ⟨102843195109557739707398069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274248520292153972553061517 102843195109557739707398069)
    ·
      refine ⟨9641549541521038097568569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102843195109557739707398069 9641549541521038097568569)
      ·
        refine ⟨7231162156140778573176427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9641549541521038097568569 7231162156140778573176427)
        ·
          refine ⟨10846743234211167859764641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7231162156140778573176427 10846743234211167859764641)
          ·
            refine ⟨8135057425658375894823481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10846743234211167859764641 8135057425658375894823481)
            ·
              refine ⟨6101293069243781921117611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8135057425658375894823481 6101293069243781921117611)
              ·
                refine ⟨9151939603865672881676417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6101293069243781921117611 9151939603865672881676417)
                ·
                  refine ⟨6863954702899254661257313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9151939603865672881676417 6863954702899254661257313)
                  ·
                    refine ⟨5147966027174440995942985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6863954702899254661257313 5147966027174440995942985)
                    ·
                      refine ⟨3860974520380830746957239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147966027174440995942985 3860974520380830746957239)
                      ·
                        rfl

theorem cell23_7519221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_7519221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519221 prefixEnd_7519221 := by exact prefixLift 7519221
  have htrace : WordTrace (prefixWord ++ tailWord_7519221) baseStart_7519221 baseEnd_7519221 := by
    simpa [prefixWord, tailWord_7519221, baseEnd_7519221] using wordTrace_append hprefix tailTrace_7519221
  have hstable : (prefixWord ++ tailWord_7519221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519221).length < 2 ^ (prefixWord ++ tailWord_7519221).sum := by decide
  have hdescent : baseEnd_7519221 < baseStart_7519221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519226 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2]
def baseStart_7519226 : Nat := 118140960795 + 7519226 * 2 ^ 59
def prefixEnd_7519226 : Nat := 4983230072969 + 3 ^ 40 * 7519226 * 2
def baseEnd_7519226 : Nat := 3860977087784103227394715

theorem tailTrace_7519226 : CollatzResearch.WordTrace tailWord_7519226 prefixEnd_7519226 3860977087784103227394715 := by
  unfold tailWord_7519226
  simp only [CollatzResearch.WordTrace]
  refine ⟨68562175664283964601748383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182832468438090572271329021 68562175664283964601748383)
  ·
    refine ⟨102843263496425946902622575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68562175664283964601748383 102843263496425946902622575)
    ·
      refine ⟨154264895244638920353933863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102843263496425946902622575 154264895244638920353933863)
      ·
        refine ⟨231397342866958380530900795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154264895244638920353933863 231397342866958380530900795)
        ·
          refine ⟨347096014300437570796351193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231397342866958380530900795 347096014300437570796351193)
          ·
            refine ⟨260322010725328178097263395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347096014300437570796351193 260322010725328178097263395)
            ·
              refine ⟨390483016087992267145895093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260322010725328178097263395 390483016087992267145895093)
              ·
                refine ⟨36607782758249275044927665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 390483016087992267145895093 36607782758249275044927665)
                ·
                  refine ⟨27455837068686956283695749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36607782758249275044927665 27455837068686956283695749)
                  ·
                    refine ⟨5147969450378804303192953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27455837068686956283695749 5147969450378804303192953)
                    ·
                      refine ⟨3860977087784103227394715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147969450378804303192953 3860977087784103227394715)
                      ·
                        rfl

theorem cell23_7519226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2].length) (baseStart_7519226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519226 prefixEnd_7519226 := by exact prefixLift 7519226
  have htrace : WordTrace (prefixWord ++ tailWord_7519226) baseStart_7519226 baseEnd_7519226 := by
    simpa [prefixWord, tailWord_7519226, baseEnd_7519226] using wordTrace_append hprefix tailTrace_7519226
  have hstable : (prefixWord ++ tailWord_7519226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519226).length < 2 ^ (prefixWord ++ tailWord_7519226).sum := by decide
  have hdescent : baseEnd_7519226 < baseStart_7519226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519259 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 3]
def baseStart_7519259 : Nat := 118140960795 + 7519259 * 2 ^ 59
def prefixEnd_7519259 : Nat := 4983230072969 + 3 ^ 40 * 7519259 * 2
def baseEnd_7519259 : Nat := 3860994032645701598282063

theorem tailTrace_7519259 : CollatzResearch.WordTrace tailWord_7519259 prefixEnd_7519259 3860994032645701598282063 := by
  unfold tailWord_7519259
  simp only [CollatzResearch.WordTrace]
  refine ⟨274249906266016305042944831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182833270844010870028629887 274249906266016305042944831)
  ·
    refine ⟨411374859399024457564417247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274249906266016305042944831 411374859399024457564417247)
    ·
      refine ⟨617062289098536686346625871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411374859399024457564417247 617062289098536686346625871)
      ·
        refine ⟨925593433647805029519938807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617062289098536686346625871 925593433647805029519938807)
        ·
          refine ⟨1388390150471707544279908211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925593433647805029519938807 1388390150471707544279908211)
          ·
            refine ⟨2082585225707561316419862317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388390150471707544279908211 2082585225707561316419862317)
            ·
              refine ⟨780969459640335493657448369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2082585225707561316419862317 780969459640335493657448369)
              ·
                refine ⟨585727094730251620243086277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780969459640335493657448369 585727094730251620243086277)
                ·
                  refine ⟨109823830261922178795578677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 585727094730251620243086277 109823830261922178795578677)
                  ·
                    refine ⟨10295984087055204262085501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109823830261922178795578677 10295984087055204262085501)
                    ·
                      refine ⟨3860994032645701598282063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10295984087055204262085501 3860994032645701598282063)
                      ·
                        rfl

theorem cell23_7519259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 3].length) (baseStart_7519259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519259 prefixEnd_7519259 := by exact prefixLift 7519259
  have htrace : WordTrace (prefixWord ++ tailWord_7519259) baseStart_7519259 baseEnd_7519259 := by
    simpa [prefixWord, tailWord_7519259, baseEnd_7519259] using wordTrace_append hprefix tailTrace_7519259
  have hstable : (prefixWord ++ tailWord_7519259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519259).length < 2 ^ (prefixWord ++ tailWord_7519259).sum := by decide
  have hdescent : baseEnd_7519259 < baseStart_7519259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519266 : List Nat := [3, 3, 1, 1, 1, 3, 1, 4, 6]
def baseStart_7519266 : Nat := 118140960795 + 7519266 * 2 ^ 59
def prefixEnd_7519266 : Nat := 4983230072969 + 3 ^ 40 * 7519266 * 2
def baseEnd_7519266 : Nat := 428999736334475896766059

theorem tailTrace_7519266 : CollatzResearch.WordTrace tailWord_7519266 prefixEnd_7519266 428999736334475896766059 := by
  unfold tailWord_7519266
  simp only [CollatzResearch.WordTrace]
  refine ⟨68562540394247736309612413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182833441051327296825633101 68562540394247736309612413)
  ·
    refine ⟨25710952647842901116104655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68562540394247736309612413 25710952647842901116104655)
    ·
      refine ⟨38566428971764351674156983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25710952647842901116104655 38566428971764351674156983)
      ·
        refine ⟨57849643457646527511235475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38566428971764351674156983 57849643457646527511235475)
        ·
          refine ⟨86774465186469791266853213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57849643457646527511235475 86774465186469791266853213)
          ·
            refine ⟨32540424444926171725069955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86774465186469791266853213 32540424444926171725069955)
            ·
              refine ⟨48810636667389257587604933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32540424444926171725069955 48810636667389257587604933)
              ·
                refine ⟨9151994375135485797675925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48810636667389257587604933 9151994375135485797675925)
                ·
                  refine ⟨428999736334475896766059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9151994375135485797675925 428999736334475896766059)
                  ·
                    rfl

theorem cell23_7519266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_7519266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519266 prefixEnd_7519266 := by exact prefixLift 7519266
  have htrace : WordTrace (prefixWord ++ tailWord_7519266) baseStart_7519266 baseEnd_7519266 := by
    simpa [prefixWord, tailWord_7519266, baseEnd_7519266] using wordTrace_append hprefix tailTrace_7519266
  have hstable : (prefixWord ++ tailWord_7519266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519266).length < 2 ^ (prefixWord ++ tailWord_7519266).sum := by decide
  have hdescent : baseEnd_7519266 < baseStart_7519266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519269 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 1, 2, 6]
def baseStart_7519269 : Nat := 118140960795 + 7519269 * 2 ^ 59
def prefixEnd_7519269 : Nat := 4983230072969 + 3 ^ 40 * 7519269 * 2
def baseEnd_7519269 : Nat := 3860999167452246559157017

theorem tailTrace_7519269 : CollatzResearch.WordTrace tailWord_7519269 prefixEnd_7519269 3860999167452246559157017 := by
  unfold tailWord_7519269
  simp only [CollatzResearch.WordTrace]
  refine ⟨274250270995980076750808861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182833513997320051167205907 274250270995980076750808861)
  ·
    refine ⟨102843851623492528781553323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274250270995980076750808861 102843851623492528781553323)
    ·
      refine ⟨154265777435238793172329985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102843851623492528781553323 154265777435238793172329985)
      ·
        refine ⟨115699333076429094879247489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154265777435238793172329985 115699333076429094879247489)
        ·
          refine ⟨86774499807321821159435617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115699333076429094879247489 86774499807321821159435617)
          ·
            refine ⟨65080874855491365869576713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86774499807321821159435617 65080874855491365869576713)
            ·
              refine ⟨48810656141618524402182535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65080874855491365869576713 48810656141618524402182535)
              ·
                refine ⟨73215984212427786603273803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48810656141618524402182535 73215984212427786603273803)
                ·
                  refine ⟨109823976318641679904910705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73215984212427786603273803 109823976318641679904910705)
                  ·
                    refine ⟨82367982238981259928683029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109823976318641679904910705 82367982238981259928683029)
                    ·
                      refine ⟨3860999167452246559157017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82367982238981259928683029 3860999167452246559157017)
                      ·
                        rfl

theorem cell23_7519269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_7519269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519269 prefixEnd_7519269 := by exact prefixLift 7519269
  have htrace : WordTrace (prefixWord ++ tailWord_7519269) baseStart_7519269 baseEnd_7519269 := by
    simpa [prefixWord, tailWord_7519269, baseEnd_7519269] using wordTrace_append hprefix tailTrace_7519269
  have hstable : (prefixWord ++ tailWord_7519269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519269).length < 2 ^ (prefixWord ++ tailWord_7519269).sum := by decide
  have hdescent : baseEnd_7519269 < baseStart_7519269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519293 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 5, 1, 3]
def baseStart_7519293 : Nat := 118140960795 + 7519293 * 2 ^ 59
def prefixEnd_7519293 : Nat := 4983230072969 + 3 ^ 40 * 7519293 * 2
def baseEnd_7519293 : Nat := 3861011490987954465256907

theorem tailTrace_7519293 : CollatzResearch.WordTrace tailWord_7519293 prefixEnd_7519293 3861011490987954465256907 := by
  unfold tailWord_7519293
  simp only [CollatzResearch.WordTrace]
  refine ⟨274251146347893128849682533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182834097565262085899788355 274251146347893128849682533)
  ·
    refine ⟨51422089940229961659315475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274251146347893128849682533 51422089940229961659315475)
    ·
      refine ⟨77133134910344942488973213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51422089940229961659315475 77133134910344942488973213)
      ·
        refine ⟨28924925591379353433364955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77133134910344942488973213 28924925591379353433364955)
        ·
          refine ⟨43387388387069030150047433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28924925591379353433364955 43387388387069030150047433)
          ·
            refine ⟨32540541290301772612535575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43387388387069030150047433 32540541290301772612535575)
            ·
              refine ⟨48810811935452658918803363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32540541290301772612535575 48810811935452658918803363)
              ·
                refine ⟨73216217903178988378205045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48810811935452658918803363 73216217903178988378205045)
                ·
                  refine ⟨6864020428423030160456723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73216217903178988378205045 6864020428423030160456723)
                  ·
                    refine ⟨10296030642634545240685085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6864020428423030160456723 10296030642634545240685085)
                    ·
                      refine ⟨3861011490987954465256907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10296030642634545240685085 3861011490987954465256907)
                      ·
                        rfl

theorem cell23_7519293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_7519293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519293 prefixEnd_7519293 := by exact prefixLift 7519293
  have htrace : WordTrace (prefixWord ++ tailWord_7519293) baseStart_7519293 baseEnd_7519293 := by
    simpa [prefixWord, tailWord_7519293, baseEnd_7519293] using wordTrace_append hprefix tailTrace_7519293
  have hstable : (prefixWord ++ tailWord_7519293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519293).length < 2 ^ (prefixWord ++ tailWord_7519293).sum := by decide
  have hdescent : baseEnd_7519293 < baseStart_7519293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519296 : List Nat := [2, 1, 1, 2, 2, 3, 2, 4, 1, 5]
def baseStart_7519296 : Nat := 118140960795 + 7519296 * 2 ^ 59
def prefixEnd_7519296 : Nat := 4983230072969 + 3 ^ 40 * 7519296 * 2
def baseEnd_7519296 : Nat := 1287004343809972651173131

theorem tailTrace_7519296 : CollatzResearch.WordTrace tailWord_7519296 prefixEnd_7519296 1287004343809972651173131 := by
  unfold tailWord_7519296
  simp only [CollatzResearch.WordTrace]
  refine ⟨137125627883441130181020871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182834170511254840241361161 137125627883441130181020871)
  ·
    refine ⟨205688441825161695271531307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137125627883441130181020871 205688441825161695271531307)
    ·
      refine ⟨308532662737742542907296961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205688441825161695271531307 308532662737742542907296961)
      ·
        refine ⟨231399497053306907180472721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308532662737742542907296961 231399497053306907180472721)
        ·
          refine ⟨173549622789980180385354541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231399497053306907180472721 173549622789980180385354541)
          ·
            refine ⟨65081108546242567644507953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173549622789980180385354541 65081108546242567644507953)
            ·
              refine ⟨48810831409681925733380965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65081108546242567644507953 48810831409681925733380965)
              ·
                refine ⟨9152030889315361075008931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48810831409681925733380965 9152030889315361075008931)
                ·
                  refine ⟨13728046333973041612513397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9152030889315361075008931 13728046333973041612513397)
                  ·
                    refine ⟨1287004343809972651173131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13728046333973041612513397 1287004343809972651173131)
                    ·
                      rfl

theorem cell23_7519296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 1, 5].length) (baseStart_7519296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519296 prefixEnd_7519296 := by exact prefixLift 7519296
  have htrace : WordTrace (prefixWord ++ tailWord_7519296) baseStart_7519296 baseEnd_7519296 := by
    simpa [prefixWord, tailWord_7519296, baseEnd_7519296] using wordTrace_append hprefix tailTrace_7519296
  have hstable : (prefixWord ++ tailWord_7519296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519296).length < 2 ^ (prefixWord ++ tailWord_7519296).sum := by decide
  have hdescent : baseEnd_7519296 < baseStart_7519296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519297 : List Nat := [1, 2, 5, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_7519297 : Nat := 118140960795 + 7519297 * 2 ^ 59
def prefixEnd_7519297 : Nat := 4983230072969 + 3 ^ 40 * 7519297 * 2
def baseEnd_7519297 : Nat := 3861013544910572449606889

theorem tailTrace_7519297 : CollatzResearch.WordTrace tailWord_7519297 prefixEnd_7519297 3861013544910572449606889 := by
  unfold tailWord_7519297
  simp only [CollatzResearch.WordTrace]
  refine ⟨274251292239878637532828145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182834194826585758355218763 274251292239878637532828145)
  ·
    refine ⟨205688469179908978149621109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274251292239878637532828145 205688469179908978149621109)
    ·
      refine ⟨19283293985616466701526979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205688469179908978149621109 19283293985616466701526979)
      ·
        refine ⟨28924940978424700052290469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19283293985616466701526979 28924940978424700052290469)
        ·
          refine ⟨5423426433454631259804463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28924940978424700052290469 5423426433454631259804463)
          ·
            refine ⟨8135139650181946889706695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5423426433454631259804463 8135139650181946889706695)
            ·
              refine ⟨12202709475272920334560043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8135139650181946889706695 12202709475272920334560043)
              ·
                refine ⟨18304064212909380501840065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12202709475272920334560043 18304064212909380501840065)
                ·
                  refine ⟨13728048159682035376380049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18304064212909380501840065 13728048159682035376380049)
                  ·
                    refine ⟨10296036119761526532285037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13728048159682035376380049 10296036119761526532285037)
                    ·
                      refine ⟨3861013544910572449606889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10296036119761526532285037 3861013544910572449606889)
                      ·
                        rfl

theorem cell23_7519297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_7519297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519297 prefixEnd_7519297 := by exact prefixLift 7519297
  have htrace : WordTrace (prefixWord ++ tailWord_7519297) baseStart_7519297 baseEnd_7519297 := by
    simpa [prefixWord, tailWord_7519297, baseEnd_7519297] using wordTrace_append hprefix tailTrace_7519297
  have hstable : (prefixWord ++ tailWord_7519297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519297).length < 2 ^ (prefixWord ++ tailWord_7519297).sum := by decide
  have hdescent : baseEnd_7519297 < baseStart_7519297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519303 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 1, 5, 2]
def baseStart_7519303 : Nat := 118140960795 + 7519303 * 2 ^ 59
def prefixEnd_7519303 : Nat := 4983230072969 + 3 ^ 40 * 7519303 * 2
def baseEnd_7519303 : Nat := 3861016625794499426131861

theorem tailTrace_7519303 : CollatzResearch.WordTrace tailWord_7519303 prefixEnd_7519303 3861016625794499426131861 := by
  unfold tailWord_7519303
  simp only [CollatzResearch.WordTrace]
  refine ⟨274251511077856900557546563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182834340718571267038364375 274251511077856900557546563)
  ·
    refine ⟨411377266616785350836319845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274251511077856900557546563 411377266616785350836319845)
    ·
      refine ⟨77133237490647253281809971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 411377266616785350836319845 77133237490647253281809971)
      ·
        refine ⟨115699856235970879922714957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77133237490647253281809971 115699856235970879922714957)
        ·
          refine ⟨43387446088489079971018109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115699856235970879922714957 43387446088489079971018109)
          ·
            refine ⟨16270292283183404989131791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43387446088489079971018109 16270292283183404989131791)
            ·
              refine ⟨24405438424775107483697687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16270292283183404989131791 24405438424775107483697687)
              ·
                refine ⟨36608157637162661225546531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24405438424775107483697687 36608157637162661225546531)
                ·
                  refine ⟨54912236455743991838319797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36608157637162661225546531 54912236455743991838319797)
                  ·
                    refine ⟨5148022167725999234842481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54912236455743991838319797 5148022167725999234842481)
                    ·
                      refine ⟨3861016625794499426131861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5148022167725999234842481 3861016625794499426131861)
                      ·
                        rfl

theorem cell23_7519303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_7519303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519303 prefixEnd_7519303 := by exact prefixLift 7519303
  have htrace : WordTrace (prefixWord ++ tailWord_7519303) baseStart_7519303 baseEnd_7519303 := by
    simpa [prefixWord, tailWord_7519303, baseEnd_7519303] using wordTrace_append hprefix tailTrace_7519303
  have hstable : (prefixWord ++ tailWord_7519303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519303).length < 2 ^ (prefixWord ++ tailWord_7519303).sum := by decide
  have hdescent : baseEnd_7519303 < baseStart_7519303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519313 : List Nat := [1, 2, 2, 1, 3, 1, 6, 1, 1, 5]
def baseStart_7519313 : Nat := 118140960795 + 7519313 * 2 ^ 59
def prefixEnd_7519313 : Nat := 4983230072969 + 3 ^ 40 * 7519313 * 2
def baseEnd_7519313 : Nat := 1287007253533681462335605

theorem tailTrace_7519313 : CollatzResearch.WordTrace tailWord_7519313 prefixEnd_7519313 1287007253533681462335605 := by
  unfold tailWord_7519313
  simp only [CollatzResearch.WordTrace]
  refine ⟨274251875807820672265410593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182834583871880448176940395 274251875807820672265410593)
  ·
    refine ⟨205688906855865504199057945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274251875807820672265410593 205688906855865504199057945)
    ·
      refine ⟨154266680141899128149293459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205688906855865504199057945 154266680141899128149293459)
      ·
        refine ⟨231400020212848692223940189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154266680141899128149293459 231400020212848692223940189)
        ·
          refine ⟨86775007579818259583977571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231400020212848692223940189 86775007579818259583977571)
          ·
            refine ⟨130162511369727389375966357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86775007579818259583977571 130162511369727389375966357)
            ·
              refine ⟨6101367720455971376998423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130162511369727389375966357 6101367720455971376998423)
              ·
                refine ⟨9152051580683957065497635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6101367720455971376998423 9152051580683957065497635)
                ·
                  refine ⟨13728077371025935598246453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9152051580683957065497635 13728077371025935598246453)
                  ·
                    refine ⟨1287007253533681462335605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13728077371025935598246453 1287007253533681462335605)
                    ·
                      rfl

theorem cell23_7519313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 1, 5].length) (baseStart_7519313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519313 prefixEnd_7519313 := by exact prefixLift 7519313
  have htrace : WordTrace (prefixWord ++ tailWord_7519313) baseStart_7519313 baseEnd_7519313 := by
    simpa [prefixWord, tailWord_7519313, baseEnd_7519313] using wordTrace_append hprefix tailTrace_7519313
  have hstable : (prefixWord ++ tailWord_7519313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519313).length < 2 ^ (prefixWord ++ tailWord_7519313).sum := by decide
  have hdescent : baseEnd_7519313 < baseStart_7519313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519346 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_7519346 : Nat := 118140960795 + 7519346 * 2 ^ 59
def prefixEnd_7519346 : Nat := 4983230072969 + 3 ^ 40 * 7519346 * 2
def baseEnd_7519346 : Nat := 3861038705462642757894163

theorem tailTrace_7519346 : CollatzResearch.WordTrace tailWord_7519346 prefixEnd_7519346 3861038705462642757894163 := by
  unfold tailWord_7519346
  simp only [CollatzResearch.WordTrace]
  refine ⟨68563269854175279725340473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182835386277800745934241261 68563269854175279725340473)
  ·
    refine ⟨51422452390631459794005355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68563269854175279725340473 51422452390631459794005355)
    ·
      refine ⟨77133678585947189691008033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51422452390631459794005355 77133678585947189691008033)
      ·
        refine ⟨57850258939460392268256025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77133678585947189691008033 57850258939460392268256025)
        ·
          refine ⟨43387694204595294201192019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57850258939460392268256025 43387694204595294201192019)
          ·
            refine ⟨65081541306892941301788029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43387694204595294201192019 65081541306892941301788029)
            ·
              refine ⟨24405577990084852988170511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65081541306892941301788029 24405577990084852988170511)
              ·
                refine ⟨36608366985127279482255767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24405577990084852988170511 36608366985127279482255767)
                ·
                  refine ⟨54912550477690919223383651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36608366985127279482255767 54912550477690919223383651)
                  ·
                    refine ⟨82368825716536378835075477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54912550477690919223383651 82368825716536378835075477)
                    ·
                      refine ⟨3861038705462642757894163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82368825716536378835075477 3861038705462642757894163)
                      ·
                        rfl

theorem cell23_7519346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_7519346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519346 prefixEnd_7519346 := by exact prefixLift 7519346
  have htrace : WordTrace (prefixWord ++ tailWord_7519346) baseStart_7519346 baseEnd_7519346 := by
    simpa [prefixWord, tailWord_7519346, baseEnd_7519346] using wordTrace_append hprefix tailTrace_7519346
  have hstable : (prefixWord ++ tailWord_7519346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519346).length < 2 ^ (prefixWord ++ tailWord_7519346).sum := by decide
  have hdescent : baseEnd_7519346 < baseStart_7519346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519350 : List Nat := [5, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_7519350 : Nat := 118140960795 + 7519350 * 2 ^ 59
def prefixEnd_7519350 : Nat := 4983230072969 + 3 ^ 40 * 7519350 * 2
def baseEnd_7519350 : Nat := 3861040759385260742244145

theorem tailTrace_7519350 : CollatzResearch.WordTrace tailWord_7519350 prefixEnd_7519350 3861040759385260742244145 := by
  unfold tailWord_7519350
  simp only [CollatzResearch.WordTrace]
  refine ⟨17140826581792914224031719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182835483539124418389671669 17140826581792914224031719)
  ·
    refine ⟨25711239872689371336047579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17140826581792914224031719 25711239872689371336047579)
    ·
      refine ⟨38566859809034057004071369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25711239872689371336047579 38566859809034057004071369)
      ·
        refine ⟨28925144856775542753053527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38566859809034057004071369 28925144856775542753053527)
        ·
          refine ⟨43387717285163314129580291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28925144856775542753053527 43387717285163314129580291)
          ·
            refine ⟨65081575927744971194370437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43387717285163314129580291 65081575927744971194370437)
            ·
              refine ⟨12202795486452182098944457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65081575927744971194370437 12202795486452182098944457)
              ·
                refine ⟨9152096614839136574208343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12202795486452182098944457 9152096614839136574208343)
                ·
                  refine ⟨13728144922258704861312515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9152096614839136574208343 13728144922258704861312515)
                  ·
                    refine ⟨20592217383388057291968773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13728144922258704861312515 20592217383388057291968773)
                    ·
                      refine ⟨3861040759385260742244145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20592217383388057291968773 3861040759385260742244145)
                      ·
                        rfl

theorem cell23_7519350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_7519350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519350 prefixEnd_7519350 := by exact prefixLift 7519350
  have htrace : WordTrace (prefixWord ++ tailWord_7519350) baseStart_7519350 baseEnd_7519350 := by
    simpa [prefixWord, tailWord_7519350, baseEnd_7519350] using wordTrace_append hprefix tailTrace_7519350
  have hstable : (prefixWord ++ tailWord_7519350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519350).length < 2 ^ (prefixWord ++ tailWord_7519350).sum := by decide
  have hdescent : baseEnd_7519350 < baseStart_7519350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519359 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 6]
def baseStart_7519359 : Nat := 118140960795 + 7519359 * 2 ^ 59
def prefixEnd_7519359 : Nat := 4983230072969 + 3 ^ 40 * 7519359 * 2
def baseEnd_7519359 : Nat := 3861045380711151207031603

theorem tailTrace_7519359 : CollatzResearch.WordTrace tailWord_7519359 prefixEnd_7519359 3861045380711151207031603 := by
  unfold tailWord_7519359
  simp only [CollatzResearch.WordTrace]
  refine ⟨274253553565654022121585131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182835702377102681414390087 274253553565654022121585131)
  ·
    refine ⟨411380330348481033182377697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274253553565654022121585131 411380330348481033182377697)
    ·
      refine ⟨308535247761360774886783273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411380330348481033182377697 308535247761360774886783273)
      ·
        refine ⟨231401435821020581165087455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308535247761360774886783273 231401435821020581165087455)
        ·
          refine ⟨347102153731530871747631183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231401435821020581165087455 347102153731530871747631183)
          ·
            refine ⟨520653230597296307621446775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347102153731530871747631183 520653230597296307621446775)
            ·
              refine ⟨780979845895944461432170163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520653230597296307621446775 780979845895944461432170163)
              ·
                refine ⟨1171469768843916692148255245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780979845895944461432170163 1171469768843916692148255245)
                ·
                  refine ⟨439301163316468759555595717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1171469768843916692148255245 439301163316468759555595717)
                  ·
                    refine ⟨82368968121837892416674197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 439301163316468759555595717 82368968121837892416674197)
                    ·
                      refine ⟨3861045380711151207031603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82368968121837892416674197 3861045380711151207031603)
                      ·
                        rfl

theorem cell23_7519359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_7519359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519359 prefixEnd_7519359 := by exact prefixLift 7519359
  have htrace : WordTrace (prefixWord ++ tailWord_7519359) baseStart_7519359 baseEnd_7519359 := by
    simpa [prefixWord, tailWord_7519359, baseEnd_7519359] using wordTrace_append hprefix tailTrace_7519359
  have hstable : (prefixWord ++ tailWord_7519359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519359).length < 2 ^ (prefixWord ++ tailWord_7519359).sum := by decide
  have hdescent : baseEnd_7519359 < baseStart_7519359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519394 : List Nat := [3, 3, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_7519394 : Nat := 118140960795 + 7519394 * 2 ^ 59
def prefixEnd_7519394 : Nat := 4983230072969 + 3 ^ 40 * 7519394 * 2
def baseEnd_7519394 : Nat := 1287021117511352856697981

theorem tailTrace_7519394 : CollatzResearch.WordTrace tailWord_7519394 prefixEnd_7519394 1287021117511352856697981 := by
  unfold tailWord_7519394
  simp only [CollatzResearch.WordTrace]
  refine ⟨68563707530131805774777309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182836553413684815399406157 68563707530131805774777309)
  ·
    refine ⟨25711390323799427165541491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68563707530131805774777309 25711390323799427165541491)
    ·
      refine ⟨38567085485699140748312237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25711390323799427165541491 38567085485699140748312237)
      ·
        refine ⟨14462657057137177780617089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38567085485699140748312237 14462657057137177780617089)
        ·
          refine ⟨10846992792852883335462817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14462657057137177780617089 10846992792852883335462817)
          ·
            refine ⟨8135244594639662501597113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10846992792852883335462817 8135244594639662501597113)
            ·
              refine ⟨6101433445979746876197835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8135244594639662501597113 6101433445979746876197835)
              ·
                refine ⟨9152150168969620314296753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6101433445979746876197835 9152150168969620314296753)
                ·
                  refine ⟨6864112626727215235722565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9152150168969620314296753 6864112626727215235722565)
                  ·
                    refine ⟨1287021117511352856697981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6864112626727215235722565 1287021117511352856697981)
                    ·
                      rfl

theorem cell23_7519394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_7519394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519394 prefixEnd_7519394 := by exact prefixLift 7519394
  have htrace : WordTrace (prefixWord ++ tailWord_7519394) baseStart_7519394 baseEnd_7519394 := by
    simpa [prefixWord, tailWord_7519394, baseEnd_7519394] using wordTrace_append hprefix tailTrace_7519394
  have hstable : (prefixWord ++ tailWord_7519394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519394).length < 2 ^ (prefixWord ++ tailWord_7519394).sum := by decide
  have hdescent : baseEnd_7519394 < baseStart_7519394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519410 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2]
def baseStart_7519410 : Nat := 118140960795 + 7519410 * 2 ^ 59
def prefixEnd_7519410 : Nat := 4983230072969 + 3 ^ 40 * 7519410 * 2
def baseEnd_7519410 : Nat := 3861071568224530507493869

theorem tailTrace_7519410 : CollatzResearch.WordTrace tailWord_7519410 prefixEnd_7519410 3861071568224530507493869 := by
  unfold tailWord_7519410
  simp only [CollatzResearch.WordTrace]
  refine ⟨68563853422117314457922921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182836942458979505221127789 68563853422117314457922921)
  ·
    refine ⟨51422890066587985843442191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68563853422117314457922921 51422890066587985843442191)
    ·
      refine ⟨77134335099881978765163287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51422890066587985843442191 77134335099881978765163287)
      ·
        refine ⟨115701502649822968147744931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77134335099881978765163287 115701502649822968147744931)
        ·
          refine ⟨173552253974734452221617397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115701502649822968147744931 173552253974734452221617397)
          ·
            refine ⟨16270523810131354895776631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173552253974734452221617397 16270523810131354895776631)
            ·
              refine ⟨24405785715197032343664947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16270523810131354895776631 24405785715197032343664947)
              ·
                refine ⟨36608678572795548515497421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24405785715197032343664947 36608678572795548515497421)
                ·
                  refine ⟨13728254464798330693311533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36608678572795548515497421 13728254464798330693311533)
                  ·
                    refine ⟨5148095424299374009991825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13728254464798330693311533 5148095424299374009991825)
                    ·
                      refine ⟨3861071568224530507493869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5148095424299374009991825 3861071568224530507493869)
                      ·
                        rfl

theorem cell23_7519410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_7519410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519410 prefixEnd_7519410 := by exact prefixLift 7519410
  have htrace : WordTrace (prefixWord ++ tailWord_7519410) baseStart_7519410 baseEnd_7519410 := by
    simpa [prefixWord, tailWord_7519410, baseEnd_7519410] using wordTrace_append hprefix tailTrace_7519410
  have hstable : (prefixWord ++ tailWord_7519410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519410).length < 2 ^ (prefixWord ++ tailWord_7519410).sum := by decide
  have hdescent : baseEnd_7519410 < baseStart_7519410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519423 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 3, 4, 2]
def baseStart_7519423 : Nat := 118140960795 + 7519423 * 2 ^ 59
def prefixEnd_7519423 : Nat := 4983230072969 + 3 ^ 40 * 7519423 * 2
def baseEnd_7519423 : Nat := 3861078243473038956631309

theorem tailTrace_7519423 : CollatzResearch.WordTrace tailWord_7519423 prefixEnd_7519423 3861078243473038956631309 := by
  unfold tailWord_7519423
  simp only [CollatzResearch.WordTrace]
  refine ⟨274255887837422161051914923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182837258558281440701276615 274255887837422161051914923)
  ·
    refine ⟨411383831756133241577872385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274255887837422161051914923 411383831756133241577872385)
    ·
      refine ⟨308537873817099931183404289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411383831756133241577872385 308537873817099931183404289)
      ·
        refine ⟨231403405362824948387553217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308537873817099931183404289 231403405362824948387553217)
        ·
          refine ⟨173552554022118711290664913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231403405362824948387553217 173552554022118711290664913)
          ·
            refine ⟨130164415516589033467998685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173552554022118711290664913 130164415516589033467998685)
            ·
              refine ⟨48811655818720887550499507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130164415516589033467998685 48811655818720887550499507)
              ·
                refine ⟨73217483728081331325749261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48811655818720887550499507 73217483728081331325749261)
                ·
                  refine ⟨27456556398030499247155973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73217483728081331325749261 27456556398030499247155973)
                  ·
                    refine ⟨5148104324630718608841745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27456556398030499247155973 5148104324630718608841745)
                    ·
                      refine ⟨3861078243473038956631309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5148104324630718608841745 3861078243473038956631309)
                      ·
                        rfl

theorem cell23_7519423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 4, 2].length) (baseStart_7519423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519423 prefixEnd_7519423 := by exact prefixLift 7519423
  have htrace : WordTrace (prefixWord ++ tailWord_7519423) baseStart_7519423 baseEnd_7519423 := by
    simpa [prefixWord, tailWord_7519423, baseEnd_7519423] using wordTrace_append hprefix tailTrace_7519423
  have hstable : (prefixWord ++ tailWord_7519423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519423).length < 2 ^ (prefixWord ++ tailWord_7519423).sum := by decide
  have hdescent : baseEnd_7519423 < baseStart_7519423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519457 : List Nat := [1, 2, 3, 1, 3, 2, 2, 3, 2, 2, 2]
def baseStart_7519457 : Nat := 118140960795 + 7519457 * 2 ^ 59
def prefixEnd_7519457 : Nat := 4983230072969 + 3 ^ 40 * 7519457 * 2
def baseEnd_7519457 : Nat := 3861095701815291823606153

theorem tailTrace_7519457 : CollatzResearch.WordTrace tailWord_7519457 prefixEnd_7519457 3861095701815291823606153 := by
  unfold tailWord_7519457
  simp only [CollatzResearch.WordTrace]
  refine ⟨274257127919298984858652625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182838085279532656572435083 274257127919298984858652625)
  ·
    refine ⟨205692845939474238643989469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274257127919298984858652625 205692845939474238643989469)
    ·
      refine ⟨77134817227302839491496051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205692845939474238643989469 77134817227302839491496051)
      ·
        refine ⟨115702225840954259237244077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77134817227302839491496051 115702225840954259237244077)
        ·
          refine ⟨43388334690357847213966529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115702225840954259237244077 43388334690357847213966529)
          ·
            refine ⟨32541251017768385410474897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43388334690357847213966529 32541251017768385410474897)
            ·
              refine ⟨24405938263326289057856173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32541251017768385410474897 24405938263326289057856173)
              ·
                refine ⟨9152226848747358396696065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24405938263326289057856173 9152226848747358396696065)
                ·
                  refine ⟨6864170136560518797522049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9152226848747358396696065 6864170136560518797522049)
                  ·
                    refine ⟨5148127602420389098141537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6864170136560518797522049 5148127602420389098141537)
                    ·
                      refine ⟨3861095701815291823606153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5148127602420389098141537 3861095701815291823606153)
                      ·
                        rfl

theorem cell23_7519457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_7519457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519457 prefixEnd_7519457 := by exact prefixLift 7519457
  have htrace : WordTrace (prefixWord ++ tailWord_7519457) baseStart_7519457 baseEnd_7519457 := by
    simpa [prefixWord, tailWord_7519457, baseEnd_7519457] using wordTrace_append hprefix tailTrace_7519457
  have hstable : (prefixWord ++ tailWord_7519457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519457).length < 2 ^ (prefixWord ++ tailWord_7519457).sum := by decide
  have hdescent : baseEnd_7519457 < baseStart_7519457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519530 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_7519530 : Nat := 118140960795 + 7519530 * 2 ^ 59
def prefixEnd_7519530 : Nat := 4983230072969 + 3 ^ 40 * 7519530 * 2
def baseEnd_7519530 : Nat := 3861133185903070037993317

theorem tailTrace_7519530 : CollatzResearch.WordTrace tailWord_7519530 prefixEnd_7519530 3861133185903070037993317 := by
  unfold tailWord_7519530
  simp only [CollatzResearch.WordTrace]
  refine ⟨68564947612008629581515011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182839860298689678884040029 68564947612008629581515011)
  ·
    refine ⟨102847421418012944372272517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68564947612008629581515011 102847421418012944372272517)
    ·
      refine ⟨19283891515877427069801097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102847421418012944372272517 19283891515877427069801097)
      ·
        refine ⟨14462918636908070302350823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19283891515877427069801097 14462918636908070302350823)
        ·
          refine ⟨21694377955362105453526235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14462918636908070302350823 21694377955362105453526235)
          ·
            refine ⟨32541566933043158180289353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21694377955362105453526235 32541566933043158180289353)
            ·
              refine ⟨24406175199782368635217015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32541566933043158180289353 24406175199782368635217015)
              ·
                refine ⟨36609262799673552952825523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24406175199782368635217015 36609262799673552952825523)
                ·
                  refine ⟨54913894199510329429238285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36609262799673552952825523 54913894199510329429238285)
                  ·
                    refine ⟨20592710324816373535964357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54913894199510329429238285 20592710324816373535964357)
                    ·
                      refine ⟨3861133185903070037993317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20592710324816373535964357 3861133185903070037993317)
                      ·
                        rfl

theorem cell23_7519530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_7519530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519530 prefixEnd_7519530 := by exact prefixLift 7519530
  have htrace : WordTrace (prefixWord ++ tailWord_7519530) baseStart_7519530 baseEnd_7519530 := by
    simpa [prefixWord, tailWord_7519530, baseEnd_7519530] using wordTrace_append hprefix tailTrace_7519530
  have hstable : (prefixWord ++ tailWord_7519530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519530).length < 2 ^ (prefixWord ++ tailWord_7519530).sum := by decide
  have hdescent : baseEnd_7519530 < baseStart_7519530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519536 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 10]
def baseStart_7519536 : Nat := 118140960795 + 7519536 * 2 ^ 59
def prefixEnd_7519536 : Nat := 4983230072969 + 3 ^ 40 * 7519536 * 2
def baseEnd_7519536 : Nat := 429015140754110779390921

theorem tailTrace_7519536 : CollatzResearch.WordTrace tailWord_7519536 prefixEnd_7519536 429015140754110779390921 := by
  unfold tailWord_7519536
  simp only [CollatzResearch.WordTrace]
  refine ⟨137130004643006390675389231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182840006190675187567185641 137130004643006390675389231)
  ·
    refine ⟨205695006964509586013083847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137130004643006390675389231 205695006964509586013083847)
    ·
      refine ⟨308542510446764379019625771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205695006964509586013083847 308542510446764379019625771)
      ·
        refine ⟨462813765670146568529438657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308542510446764379019625771 462813765670146568529438657)
        ·
          refine ⟨347110324252609926397078993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462813765670146568529438657 347110324252609926397078993)
          ·
            refine ⟨260332743189457444797809245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347110324252609926397078993 260332743189457444797809245)
            ·
              refine ⟨97624778696046541799178467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260332743189457444797809245 97624778696046541799178467)
              ·
                refine ⟨146437168044069812698767701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97624778696046541799178467 146437168044069812698767701)
                ·
                  refine ⟨429015140754110779390921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 146437168044069812698767701 429015140754110779390921)
                  ·
                    rfl

theorem cell23_7519536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 10].length) (baseStart_7519536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519536 prefixEnd_7519536 := by exact prefixLift 7519536
  have htrace : WordTrace (prefixWord ++ tailWord_7519536) baseStart_7519536 baseEnd_7519536 := by
    simpa [prefixWord, tailWord_7519536, baseEnd_7519536] using wordTrace_append hprefix tailTrace_7519536
  have hstable : (prefixWord ++ tailWord_7519536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519536).length < 2 ^ (prefixWord ++ tailWord_7519536).sum := by decide
  have hdescent : baseEnd_7519536 < baseStart_7519536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519581 : List Nat := [1, 4, 5, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_7519581 : Nat := 118140960795 + 7519581 * 2 ^ 59
def prefixEnd_7519581 : Nat := 4983230072969 + 3 ^ 40 * 7519581 * 2
def baseEnd_7519581 : Nat := 3861159373416449338455583

theorem tailTrace_7519581 : CollatzResearch.WordTrace tailWord_7519581 prefixEnd_7519581 3861159373416449338455583 := by
  unfold tailWord_7519581
  simp only [CollatzResearch.WordTrace]
  refine ⟨274261650570849754036166597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182841100380566502690777731 274261650570849754036166597)
  ·
    refine ⟨51424059482034328881781237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274261650570849754036166597 51424059482034328881781237)
    ·
      refine ⟨4821005576440718332666991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51424059482034328881781237 4821005576440718332666991)
      ·
        refine ⟨7231508364661077499000487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4821005576440718332666991 7231508364661077499000487)
        ·
          refine ⟨10847262546991616248500731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7231508364661077499000487 10847262546991616248500731)
          ·
            refine ⟨16270893820487424372751097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10847262546991616248500731 16270893820487424372751097)
            ·
              refine ⟨12203170365365568279563323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16270893820487424372751097 12203170365365568279563323)
              ·
                refine ⟨18304755548048352419344985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12203170365365568279563323 18304755548048352419344985)
                ·
                  refine ⟨13728566661036264314508739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18304755548048352419344985 13728566661036264314508739)
                  ·
                    refine ⟨20592849991554396471763109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13728566661036264314508739 20592849991554396471763109)
                    ·
                      refine ⟨3861159373416449338455583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20592849991554396471763109 3861159373416449338455583)
                      ·
                        rfl

theorem cell23_7519581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_7519581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519581 prefixEnd_7519581 := by exact prefixLift 7519581
  have htrace : WordTrace (prefixWord ++ tailWord_7519581) baseStart_7519581 baseEnd_7519581 := by
    simpa [prefixWord, tailWord_7519581, baseEnd_7519581] using wordTrace_append hprefix tailTrace_7519581
  have hstable : (prefixWord ++ tailWord_7519581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519581).length < 2 ^ (prefixWord ++ tailWord_7519581).sum := by decide
  have hdescent : baseEnd_7519581 < baseStart_7519581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519603 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 4]
def baseStart_7519603 : Nat := 118140960795 + 7519603 * 2 ^ 59
def prefixEnd_7519603 : Nat := 4983230072969 + 3 ^ 40 * 7519603 * 2
def baseEnd_7519603 : Nat := 3861170669990848252380481

theorem tailTrace_7519603 : CollatzResearch.WordTrace tailWord_7519603 prefixEnd_7519603 3861170669990848252380481 := by
  unfold tailWord_7519603
  simp only [CollatzResearch.WordTrace]
  refine ⟨274262452976770051793467463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182841635317846701195644975 274262452976770051793467463)
  ·
    refine ⟨411393679465155077690201195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274262452976770051793467463 411393679465155077690201195)
    ·
      refine ⟨617090519197732616535301793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411393679465155077690201195 617090519197732616535301793)
      ·
        refine ⟨462817889398299462401476345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617090519197732616535301793 462817889398299462401476345)
        ·
          refine ⟨347113417048724596801107259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462817889398299462401476345 347113417048724596801107259)
          ·
            refine ⟨520670125573086895201660889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347113417048724596801107259 520670125573086895201660889)
            ·
              refine ⟨390502594179815171401245667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520670125573086895201660889 390502594179815171401245667)
              ·
                refine ⟨585753891269722757101868501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390502594179815171401245667 585753891269722757101868501)
                ·
                  refine ⟨13728606826634127119575043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 585753891269722757101868501 13728606826634127119575043)
                  ·
                    refine ⟨20592910239951190679362565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13728606826634127119575043 20592910239951190679362565)
                    ·
                      refine ⟨3861170669990848252380481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20592910239951190679362565 3861170669990848252380481)
                      ·
                        rfl

theorem cell23_7519603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 4].length) (baseStart_7519603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519603 prefixEnd_7519603 := by exact prefixLift 7519603
  have htrace : WordTrace (prefixWord ++ tailWord_7519603) baseStart_7519603 baseEnd_7519603 := by
    simpa [prefixWord, tailWord_7519603, baseEnd_7519603] using wordTrace_append hprefix tailTrace_7519603
  have hstable : (prefixWord ++ tailWord_7519603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519603).length < 2 ^ (prefixWord ++ tailWord_7519603).sum := by decide
  have hdescent : baseEnd_7519603 < baseStart_7519603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519613 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 3, 6]
def baseStart_7519613 : Nat := 118140960795 + 7519613 * 2 ^ 59
def prefixEnd_7519613 : Nat := 4983230072969 + 3 ^ 40 * 7519613 * 2
def baseEnd_7519613 : Nat := 1287058601599131071085145

theorem tailTrace_7519613 : CollatzResearch.WordTrace tailWord_7519613 prefixEnd_7519613 1287058601599131071085145 := by
  unfold tailWord_7519613
  simp only [CollatzResearch.WordTrace]
  refine ⟨274262817706733823501331493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182841878471155882334220995 274262817706733823501331493)
  ·
    refine ⟨51424278320012591906499655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274262817706733823501331493 51424278320012591906499655)
    ·
      refine ⟨77136417480018887859749483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51424278320012591906499655 77136417480018887859749483)
      ·
        refine ⟨115704626220028331789624225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77136417480018887859749483 115704626220028331789624225)
        ·
          refine ⟨86778469665021248842218169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115704626220028331789624225 86778469665021248842218169)
          ·
            refine ⟨65083852248765936631663627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86778469665021248842218169 65083852248765936631663627)
            ·
              refine ⟨97625778373148904947495441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65083852248765936631663627 97625778373148904947495441)
              ·
                refine ⟨73219333779861678710621581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97625778373148904947495441 73219333779861678710621581)
                ·
                  refine ⟨27457250167448129516483093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73219333779861678710621581 27457250167448129516483093)
                  ·
                    refine ⟨1287058601599131071085145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27457250167448129516483093 1287058601599131071085145)
                    ·
                      rfl

theorem cell23_7519613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_7519613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519613 prefixEnd_7519613 := by exact prefixLift 7519613
  have htrace : WordTrace (prefixWord ++ tailWord_7519613) baseStart_7519613 baseEnd_7519613 := by
    simpa [prefixWord, tailWord_7519613, baseEnd_7519613] using wordTrace_append hprefix tailTrace_7519613
  have hstable : (prefixWord ++ tailWord_7519613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519613).length < 2 ^ (prefixWord ++ tailWord_7519613).sum := by decide
  have hdescent : baseEnd_7519613 < baseStart_7519613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519620 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_7519620 : Nat := 118140960795 + 7519620 * 2 ^ 59
def prefixEnd_7519620 : Nat := 4983230072969 + 3 ^ 40 * 7519620 * 2
def baseEnd_7519620 : Nat := 3861179399161974685867903

theorem tailTrace_7519620 : CollatzResearch.WordTrace tailWord_7519620 prefixEnd_7519620 3861179399161974685867903 := by
  unfold tailWord_7519620
  simp only [CollatzResearch.WordTrace]
  refine ⟨137131536508854231848418157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182842048678472309131224209 137131536508854231848418157)
  ·
    refine ⟨51424326190820336943156809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137131536508854231848418157 51424326190820336943156809)
    ·
      refine ⟨38568244643115252707367607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51424326190820336943156809 38568244643115252707367607)
      ·
        refine ⟨57852366964672879061051411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38568244643115252707367607 57852366964672879061051411)
        ·
          refine ⟨86778550447009318591577117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57852366964672879061051411 86778550447009318591577117)
          ·
            refine ⟨32541956417628494471841419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86778550447009318591577117 32541956417628494471841419)
            ·
              refine ⟨48812934626442741707762129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32541956417628494471841419 48812934626442741707762129)
              ·
                refine ⟨36609700969832056280821597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48812934626442741707762129 36609700969832056280821597)
                ·
                  refine ⟨13728637863687021105308099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36609700969832056280821597 13728637863687021105308099)
                  ·
                    refine ⟨20592956795530531657962149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13728637863687021105308099 20592956795530531657962149)
                    ·
                      refine ⟨3861179399161974685867903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20592956795530531657962149 3861179399161974685867903)
                      ·
                        rfl

theorem cell23_7519620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_7519620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519620 prefixEnd_7519620 := by exact prefixLift 7519620
  have htrace : WordTrace (prefixWord ++ tailWord_7519620) baseStart_7519620 baseEnd_7519620 := by
    simpa [prefixWord, tailWord_7519620, baseEnd_7519620] using wordTrace_append hprefix tailTrace_7519620
  have hstable : (prefixWord ++ tailWord_7519620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519620).length < 2 ^ (prefixWord ++ tailWord_7519620).sum := by decide
  have hdescent : baseEnd_7519620 < baseStart_7519620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519633 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 4]
def baseStart_7519633 : Nat := 118140960795 + 7519633 * 2 ^ 59
def prefixEnd_7519633 : Nat := 4983230072969 + 3 ^ 40 * 7519633 * 2
def baseEnd_7519633 : Nat := 3861186074410483135005343

theorem tailTrace_7519633 : CollatzResearch.WordTrace tailWord_7519633 prefixEnd_7519633 3861186074410483135005343 := by
  unfold tailWord_7519633
  simp only [CollatzResearch.WordTrace]
  refine ⟨274263547166661366917059553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182842364777774244611373035 274263547166661366917059553)
  ·
    refine ⟨205697660374996025187794665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274263547166661366917059553 205697660374996025187794665)
    ·
      refine ⟨154273245281247018890845999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205697660374996025187794665 154273245281247018890845999)
      ·
        refine ⟨231409867921870528336268999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154273245281247018890845999 231409867921870528336268999)
        ·
          refine ⟨347114801882805792504403499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231409867921870528336268999 347114801882805792504403499)
          ·
            refine ⟨520672202824208688756605249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347114801882805792504403499 520672202824208688756605249)
            ·
              refine ⟨390504152118156516567453937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520672202824208688756605249 390504152118156516567453937)
              ·
                refine ⟨292878114088617387425590453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390504152118156516567453937 292878114088617387425590453)
                ·
                  refine ⟨27457323195807880071149105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 292878114088617387425590453 27457323195807880071149105)
                  ·
                    refine ⟨20592992396855910053361829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27457323195807880071149105 20592992396855910053361829)
                    ·
                      refine ⟨3861186074410483135005343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20592992396855910053361829 3861186074410483135005343)
                      ·
                        rfl

theorem cell23_7519633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_7519633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519633 prefixEnd_7519633 := by exact prefixLift 7519633
  have htrace : WordTrace (prefixWord ++ tailWord_7519633) baseStart_7519633 baseEnd_7519633 := by
    simpa [prefixWord, tailWord_7519633, baseEnd_7519633] using wordTrace_append hprefix tailTrace_7519633
  have hstable : (prefixWord ++ tailWord_7519633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519633).length < 2 ^ (prefixWord ++ tailWord_7519633).sum := by decide
  have hdescent : baseEnd_7519633 < baseStart_7519633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519637 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 5, 2, 2]
def baseStart_7519637 : Nat := 118140960795 + 7519637 * 2 ^ 59
def prefixEnd_7519637 : Nat := 4983230072969 + 3 ^ 40 * 7519637 * 2
def baseEnd_7519637 : Nat := 3861188128333101119355325

theorem tailTrace_7519637 : CollatzResearch.WordTrace tailWord_7519637 prefixEnd_7519637 3861188128333101119355325 := by
  unfold tailWord_7519637
  simp only [CollatzResearch.WordTrace]
  refine ⟨274263693058646875600205165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182842462039097917066803443 274263693058646875600205165)
  ·
    refine ⟨102848884896992578350076937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274263693058646875600205165 102848884896992578350076937)
    ·
      refine ⟨77136663672744433762557703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102848884896992578350076937 77136663672744433762557703)
      ·
        refine ⟨115704995509116650643836555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77136663672744433762557703 115704995509116650643836555)
        ·
          refine ⟨173557493263674975965754833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115704995509116650643836555 173557493263674975965754833)
          ·
            refine ⟨130168119947756231974316125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173557493263674975965754833 130168119947756231974316125)
            ·
              refine ⟨48813044980408586990368547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130168119947756231974316125 48813044980408586990368547)
              ·
                refine ⟨73219567470612880485552821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48813044980408586990368547 73219567470612880485552821)
                ·
                  refine ⟨6864334450369957545520577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73219567470612880485552821 6864334450369957545520577)
                  ·
                    refine ⟨5148250837777468159140433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6864334450369957545520577 5148250837777468159140433)
                    ·
                      refine ⟨3861188128333101119355325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5148250837777468159140433 3861188128333101119355325)
                      ·
                        rfl

theorem cell23_7519637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_7519637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519637 prefixEnd_7519637 := by exact prefixLift 7519637
  have htrace : WordTrace (prefixWord ++ tailWord_7519637) baseStart_7519637 baseEnd_7519637 := by
    simpa [prefixWord, tailWord_7519637, baseEnd_7519637] using wordTrace_append hprefix tailTrace_7519637
  have hstable : (prefixWord ++ tailWord_7519637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519637).length < 2 ^ (prefixWord ++ tailWord_7519637).sum := by decide
  have hdescent : baseEnd_7519637 < baseStart_7519637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519684 : List Nat := [2, 3, 3, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_7519684 : Nat := 118140960795 + 7519684 * 2 ^ 59
def prefixEnd_7519684 : Nat := 4983230072969 + 3 ^ 40 * 7519684 * 2
def baseEnd_7519684 : Nat := 3861212261923862435467609

theorem tailTrace_7519684 : CollatzResearch.WordTrace tailWord_7519684 prefixEnd_7519684 3861212261923862435467609 := by
  unfold tailWord_7519684
  simp only [CollatzResearch.WordTrace]
  refine ⟨137132703644738301313583053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182843604859651068418110737 137132703644738301313583053)
  ·
    refine ⟨51424763866776862992593645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137132703644738301313583053 51424763866776862992593645)
    ·
      refine ⟨19284286450041323622222617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51424763866776862992593645 19284286450041323622222617)
      ·
        refine ⟨14463214837530992716666963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19284286450041323622222617 14463214837530992716666963)
        ·
          refine ⟨21694822256296489075000445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14463214837530992716666963 21694822256296489075000445)
          ·
            refine ⟨8135558346111183403125167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21694822256296489075000445 8135558346111183403125167)
            ·
              refine ⟨12203337519166775104687751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8135558346111183403125167 12203337519166775104687751)
              ·
                refine ⟨18305006278750162657031627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12203337519166775104687751 18305006278750162657031627)
                ·
                  refine ⟨27457509418125243985547441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18305006278750162657031627 27457509418125243985547441)
                  ·
                    refine ⟨20593132063593932989160581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27457509418125243985547441 20593132063593932989160581)
                    ·
                      refine ⟨3861212261923862435467609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20593132063593932989160581 3861212261923862435467609)
                      ·
                        rfl

theorem cell23_7519684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_7519684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519684 prefixEnd_7519684 := by exact prefixLift 7519684
  have htrace : WordTrace (prefixWord ++ tailWord_7519684) baseStart_7519684 baseEnd_7519684 := by
    simpa [prefixWord, tailWord_7519684, baseEnd_7519684] using wordTrace_append hprefix tailTrace_7519684
  have hstable : (prefixWord ++ tailWord_7519684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519684).length < 2 ^ (prefixWord ++ tailWord_7519684).sum := by decide
  have hdescent : baseEnd_7519684 < baseStart_7519684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519703 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 1, 8]
def baseStart_7519703 : Nat := 118140960795 + 7519703 * 2 ^ 59
def prefixEnd_7519703 : Nat := 4983230072969 + 3 ^ 40 * 7519703 * 2
def baseEnd_7519703 : Nat := 1287074006018765953710007

theorem tailTrace_7519703 : CollatzResearch.WordTrace tailWord_7519703 prefixEnd_7519703 1287074006018765953710007 := by
  unfold tailWord_7519703
  simp only [CollatzResearch.WordTrace]
  refine ⟨274266100276407768872107763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182844066850938512581405175 274266100276407768872107763)
  ·
    refine ⟨411399150414611653308161645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274266100276407768872107763 411399150414611653308161645)
    ·
      refine ⟨154274681405479369990560617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411399150414611653308161645 154274681405479369990560617)
      ·
        refine ⟨115706011054109527492920463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154274681405479369990560617 115706011054109527492920463)
        ·
          refine ⟨173559016581164291239380695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115706011054109527492920463 173559016581164291239380695)
          ·
            refine ⟨260338524871746436859071043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173559016581164291239380695 260338524871746436859071043)
            ·
              refine ⟨390507787307619655288606565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260338524871746436859071043 390507787307619655288606565)
              ·
                refine ⟨73220210120178685366613731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 390507787307619655288606565 73220210120178685366613731)
                ·
                  refine ⟨109830315180268028049920597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73220210120178685366613731 109830315180268028049920597)
                  ·
                    refine ⟨1287074006018765953710007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109830315180268028049920597 1287074006018765953710007)
                    ·
                      rfl

theorem cell23_7519703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_7519703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519703 prefixEnd_7519703 := by exact prefixLift 7519703
  have htrace : WordTrace (prefixWord ++ tailWord_7519703) baseStart_7519703 baseEnd_7519703 := by
    simpa [prefixWord, tailWord_7519703, baseEnd_7519703] using wordTrace_append hprefix tailTrace_7519703
  have hstable : (prefixWord ++ tailWord_7519703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519703).length < 2 ^ (prefixWord ++ tailWord_7519703).sum := by decide
  have hdescent : baseEnd_7519703 < baseStart_7519703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519723 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 6]
def baseStart_7519723 : Nat := 118140960795 + 7519723 * 2 ^ 59
def prefixEnd_7519723 : Nat := 4983230072969 + 3 ^ 40 * 7519723 * 2
def baseEnd_7519723 : Nat := 3861232287669387782879929

theorem tailTrace_7519723 : CollatzResearch.WordTrace tailWord_7519723 prefixEnd_7519723 3861232287669387782879929 := by
  unfold tailWord_7519723
  simp only [CollatzResearch.WordTrace]
  refine ⟨274266829736335312287835823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182844553157556874858557215 274266829736335312287835823)
  ·
    refine ⟨411400244604502968431753735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274266829736335312287835823 411400244604502968431753735)
    ·
      refine ⟨617100366906754452647630603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411400244604502968431753735 617100366906754452647630603)
      ·
        refine ⟨925650550360131678971445905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617100366906754452647630603 925650550360131678971445905)
        ·
          refine ⟨694237912770098759228584429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 925650550360131678971445905 694237912770098759228584429)
          ·
            refine ⟨260339217288787034710719161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 694237912770098759228584429 260339217288787034710719161)
            ·
              refine ⟨195254412966590276033039371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260339217288787034710719161 195254412966590276033039371)
              ·
                refine ⟨292881619449885414049559057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195254412966590276033039371 292881619449885414049559057)
                ·
                  refine ⟨219661214587414060537169293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292881619449885414049559057 219661214587414060537169293)
                  ·
                    refine ⟨82372955470280272701438485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 219661214587414060537169293 82372955470280272701438485)
                    ·
                      refine ⟨3861232287669387782879929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82372955470280272701438485 3861232287669387782879929)
                      ·
                        rfl

theorem cell23_7519723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 6].length) (baseStart_7519723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519723 prefixEnd_7519723 := by exact prefixLift 7519723
  have htrace : WordTrace (prefixWord ++ tailWord_7519723) baseStart_7519723 baseEnd_7519723 := by
    simpa [prefixWord, tailWord_7519723, baseEnd_7519723] using wordTrace_append hprefix tailTrace_7519723
  have hstable : (prefixWord ++ tailWord_7519723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519723).length < 2 ^ (prefixWord ++ tailWord_7519723).sum := by decide
  have hdescent : baseEnd_7519723 < baseStart_7519723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519740 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_7519740 : Nat := 118140960795 + 7519740 * 2 ^ 59
def prefixEnd_7519740 : Nat := 4983230072969 + 3 ^ 40 * 7519740 * 2
def baseEnd_7519740 : Nat := 3861241016840514216367351

theorem tailTrace_7519740 : CollatzResearch.WordTrace tailWord_7519740 prefixEnd_7519740 3861241016840514216367351 := by
  unfold tailWord_7519740
  simp only [CollatzResearch.WordTrace]
  refine ⟨137133724888636862095602337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182844966518182482794136449 137133724888636862095602337)
  ·
    refine ⟨102850293666477646571701753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137133724888636862095602337 102850293666477646571701753)
    ·
      refine ⟨77137720249858234928776315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102850293666477646571701753 77137720249858234928776315)
      ·
        refine ⟨115706580374787352393164473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77137720249858234928776315 115706580374787352393164473)
        ·
          refine ⟨86779935281090514294873355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115706580374787352393164473 86779935281090514294873355)
          ·
            refine ⟨130169902921635771442310033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86779935281090514294873355 130169902921635771442310033)
            ·
              refine ⟨97627427191226828581732525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130169902921635771442310033 97627427191226828581732525)
              ·
                refine ⟨36610285196710060718149697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97627427191226828581732525 36610285196710060718149697)
                ·
                  refine ⟨27457713897532545538612273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36610285196710060718149697 27457713897532545538612273)
                  ·
                    refine ⟨20593285423149409153959205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27457713897532545538612273 20593285423149409153959205)
                    ·
                      refine ⟨3861241016840514216367351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20593285423149409153959205 3861241016840514216367351)
                      ·
                        rfl

theorem cell23_7519740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_7519740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519740 prefixEnd_7519740 := by exact prefixLift 7519740
  have htrace : WordTrace (prefixWord ++ tailWord_7519740) baseStart_7519740 baseEnd_7519740 := by
    simpa [prefixWord, tailWord_7519740, baseEnd_7519740] using wordTrace_append hprefix tailTrace_7519740
  have hstable : (prefixWord ++ tailWord_7519740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519740).length < 2 ^ (prefixWord ++ tailWord_7519740).sum := by decide
  have hdescent : baseEnd_7519740 < baseStart_7519740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519748 : List Nat := [2, 3, 2, 3, 2, 2, 1, 2, 1, 3, 2]
def baseStart_7519748 : Nat := 118140960795 + 7519748 * 2 ^ 59
def prefixEnd_7519748 : Nat := 4983230072969 + 3 ^ 40 * 7519748 * 2
def baseEnd_7519748 : Nat := 3861245124685750185067315

theorem tailTrace_7519748 : CollatzResearch.WordTrace tailWord_7519748 prefixEnd_7519748 3861245124685750185067315 := by
  unfold tailWord_7519748
  simp only [CollatzResearch.WordTrace]
  refine ⟨137133870780622370778747949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182845161040829827704997265 137133870780622370778747949)
  ·
    refine ⟨51425201542733389042030481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137133870780622370778747949 51425201542733389042030481)
    ·
      refine ⟨38568901157050041781522861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51425201542733389042030481 38568901157050041781522861)
      ·
        refine ⟨14463337933893765668071073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38568901157050041781522861 14463337933893765668071073)
        ·
          refine ⟨10847503450420324251053305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14463337933893765668071073 10847503450420324251053305)
          ·
            refine ⟨8135627587815243188289979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10847503450420324251053305 8135627587815243188289979)
            ·
              refine ⟨12203441381722864782434969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8135627587815243188289979 12203441381722864782434969)
              ·
                refine ⟨9152581036292148586826227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12203441381722864782434969 9152581036292148586826227)
                ·
                  refine ⟨13728871554438222880239341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9152581036292148586826227 13728871554438222880239341)
                  ·
                    refine ⟨5148326832914333580089753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13728871554438222880239341 5148326832914333580089753)
                    ·
                      refine ⟨3861245124685750185067315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5148326832914333580089753 3861245124685750185067315)
                      ·
                        rfl

theorem cell23_7519748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_7519748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519748 prefixEnd_7519748 := by exact prefixLift 7519748
  have htrace : WordTrace (prefixWord ++ tailWord_7519748) baseStart_7519748 baseEnd_7519748 := by
    simpa [prefixWord, tailWord_7519748, baseEnd_7519748] using wordTrace_append hprefix tailTrace_7519748
  have hstable : (prefixWord ++ tailWord_7519748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519748).length < 2 ^ (prefixWord ++ tailWord_7519748).sum := by decide
  have hdescent : baseEnd_7519748 < baseStart_7519748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519844 : List Nat := [2, 3, 1, 1, 2, 4, 2, 1, 3, 4]
def baseStart_7519844 : Nat := 118140960795 + 7519844 * 2 ^ 59
def prefixEnd_7519844 : Nat := 4983230072969 + 3 ^ 40 * 7519844 * 2
def baseEnd_7519844 : Nat := 1287098139609527269822291

theorem tailTrace_7519844 : CollatzResearch.WordTrace tailWord_7519844 prefixEnd_7519844 1287098139609527269822291 := by
  unfold tailWord_7519844
  simp only [CollatzResearch.WordTrace]
  refine ⟨137135621484448474976495293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182847495312597966635327057 137135621484448474976495293)
  ·
    refine ⟨51425858056668178116185735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137135621484448474976495293 51425858056668178116185735)
    ·
      refine ⟨77138787085002267174278603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51425858056668178116185735 77138787085002267174278603)
      ·
        refine ⟨115708180627503400761417905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77138787085002267174278603 115708180627503400761417905)
        ·
          refine ⟨86781135470627550571063429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115708180627503400761417905 86781135470627550571063429)
          ·
            refine ⟨16271462900742665732074393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86781135470627550571063429 16271462900742665732074393)
            ·
              refine ⟨12203597175556999299055795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16271462900742665732074393 12203597175556999299055795)
              ·
                refine ⟨18305395763335498948583693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12203597175556999299055795 18305395763335498948583693)
                ·
                  refine ⟨6864523411250812105718885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18305395763335498948583693 6864523411250812105718885)
                  ·
                    refine ⟨1287098139609527269822291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6864523411250812105718885 1287098139609527269822291)
                    ·
                      rfl

theorem cell23_7519844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_7519844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519844 prefixEnd_7519844 := by exact prefixLift 7519844
  have htrace : WordTrace (prefixWord ++ tailWord_7519844) baseStart_7519844 baseEnd_7519844 := by
    simpa [prefixWord, tailWord_7519844, baseEnd_7519844] using wordTrace_append hprefix tailTrace_7519844
  have hstable : (prefixWord ++ tailWord_7519844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519844).length < 2 ^ (prefixWord ++ tailWord_7519844).sum := by decide
  have hdescent : baseEnd_7519844 < baseStart_7519844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519907 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 4]
def baseStart_7519907 : Nat := 118140960795 + 7519907 * 2 ^ 59
def prefixEnd_7519907 : Nat := 4983230072969 + 3 ^ 40 * 7519907 * 2
def baseEnd_7519907 : Nat := 3861326768109815062979083

theorem tailTrace_7519907 : CollatzResearch.WordTrace tailWord_7519907 prefixEnd_7519907 3861326768109815062979083 := by
  unfold tailWord_7519907
  simp only [CollatzResearch.WordTrace]
  refine ⟨274273540767668711712533975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182849027178445807808355983 274273540767668711712533975)
  ·
    refine ⟨411410311151503067568800963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274273540767668711712533975 411410311151503067568800963)
    ·
      refine ⟨617115466727254601353201445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411410311151503067568800963 617115466727254601353201445)
      ·
        refine ⟨115709150011360237753725271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 617115466727254601353201445 115709150011360237753725271)
        ·
          refine ⟨173563725017040356630587907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115709150011360237753725271 173563725017040356630587907)
          ·
            refine ⟨260345587525560534945881861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173563725017040356630587907 260345587525560534945881861)
            ·
              refine ⟨48814797661042600302352849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260345587525560534945881861 48814797661042600302352849)
              ·
                refine ⟨36611098245781950226764637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48814797661042600302352849 36611098245781950226764637)
                ·
                  refine ⟨13729161842168231335036739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36611098245781950226764637 13729161842168231335036739)
                  ·
                    refine ⟨20593742763252347002555109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13729161842168231335036739 20593742763252347002555109)
                    ·
                      refine ⟨3861326768109815062979083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20593742763252347002555109 3861326768109815062979083)
                      ·
                        rfl

theorem cell23_7519907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_7519907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519907 prefixEnd_7519907 := by exact prefixLift 7519907
  have htrace : WordTrace (prefixWord ++ tailWord_7519907) baseStart_7519907 baseEnd_7519907 := by
    simpa [prefixWord, tailWord_7519907, baseEnd_7519907] using wordTrace_append hprefix tailTrace_7519907
  have hstable : (prefixWord ++ tailWord_7519907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519907).length < 2 ^ (prefixWord ++ tailWord_7519907).sum := by decide
  have hdescent : baseEnd_7519907 < baseStart_7519907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519934 : List Nat := [4, 2, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_7519934 : Nat := 118140960795 + 7519934 * 2 ^ 59
def prefixEnd_7519934 : Nat := 4983230072969 + 3 ^ 40 * 7519934 * 2
def baseEnd_7519934 : Nat := 1287113544029162152447153

theorem tailTrace_7519934 : CollatzResearch.WordTrace tailWord_7519934 prefixEnd_7519934 1287113544029162152447153 := by
  unfold tailWord_7519934
  simp only [CollatzResearch.WordTrace]
  refine ⟨34284315692321361915470857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182849683692380596882511237 34284315692321361915470857)
  ·
    refine ⟨25713236769241021436603143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34284315692321361915470857 25713236769241021436603143)
    ·
      refine ⟨38569855153861532154904715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25713236769241021436603143 38569855153861532154904715)
      ·
        refine ⟨57854782730792298232357073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38569855153861532154904715 57854782730792298232357073)
        ·
          refine ⟨43391087048094223674267805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57854782730792298232357073 43391087048094223674267805)
          ·
            refine ⟨16271657643035333877850427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43391087048094223674267805 16271657643035333877850427)
            ·
              refine ⟨24407486464553000816775641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16271657643035333877850427 24407486464553000816775641)
              ·
                refine ⟨18305614848414750612581731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24407486464553000816775641 18305614848414750612581731)
                ·
                  refine ⟨27458422272622125918872597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18305614848414750612581731 27458422272622125918872597)
                  ·
                    refine ⟨1287113544029162152447153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27458422272622125918872597 1287113544029162152447153)
                    ·
                      rfl

theorem cell23_7519934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_7519934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519934 prefixEnd_7519934 := by exact prefixLift 7519934
  have htrace : WordTrace (prefixWord ++ tailWord_7519934) baseStart_7519934 baseEnd_7519934 := by
    simpa [prefixWord, tailWord_7519934, baseEnd_7519934] using wordTrace_append hprefix tailTrace_7519934
  have hstable : (prefixWord ++ tailWord_7519934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519934).length < 2 ^ (prefixWord ++ tailWord_7519934).sum := by decide
  have hdescent : baseEnd_7519934 < baseStart_7519934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519971 : List Nat := [1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 4]
def baseStart_7519971 : Nat := 118140960795 + 7519971 * 2 ^ 59
def prefixEnd_7519971 : Nat := 4983230072969 + 3 ^ 40 * 7519971 * 2
def baseEnd_7519971 : Nat := 3861359630871702812578789

theorem tailTrace_7519971 : CollatzResearch.WordTrace tailWord_7519971 prefixEnd_7519971 3861359630871702812578789 := by
  unfold tailWord_7519971
  simp only [CollatzResearch.WordTrace]
  refine ⟨274275875039436850642863767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182850583359624567095242511 274275875039436850642863767)
  ·
    refine ⟨411413812559155275964295651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274275875039436850642863767 411413812559155275964295651)
    ·
      refine ⟨617120718838732913946443477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411413812559155275964295651 617120718838732913946443477)
      ·
        refine ⟨14463766847782802670619769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 617120718838732913946443477 14463766847782802670619769)
        ·
          refine ⟨10847825135837102002964827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14463766847782802670619769 10847825135837102002964827)
          ·
            refine ⟨16271737703755653004447241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10847825135837102002964827 16271737703755653004447241)
            ·
              refine ⟨12203803277816739753335431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16271737703755653004447241 12203803277816739753335431)
              ·
                refine ⟨18305704916725109630003147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12203803277816739753335431 18305704916725109630003147)
                ·
                  refine ⟨27458557375087664445004721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18305704916725109630003147 27458557375087664445004721)
                  ·
                    refine ⟨20593918031315748333753541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27458557375087664445004721 20593918031315748333753541)
                    ·
                      refine ⟨3861359630871702812578789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20593918031315748333753541 3861359630871702812578789)
                      ·
                        rfl

theorem cell23_7519971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_7519971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519971 prefixEnd_7519971 := by exact prefixLift 7519971
  have htrace : WordTrace (prefixWord ++ tailWord_7519971) baseStart_7519971 baseEnd_7519971 := by
    simpa [prefixWord, tailWord_7519971, baseEnd_7519971] using wordTrace_append hprefix tailTrace_7519971
  have hstable : (prefixWord ++ tailWord_7519971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519971).length < 2 ^ (prefixWord ++ tailWord_7519971).sum := by decide
  have hdescent : baseEnd_7519971 < baseStart_7519971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519975 : List Nat := [1, 1, 5, 4, 1, 1, 1, 2, 3, 2, 2]
def baseStart_7519975 : Nat := 118140960795 + 7519975 * 2 ^ 59
def prefixEnd_7519975 : Nat := 4983230072969 + 3 ^ 40 * 7519975 * 2
def baseEnd_7519975 : Nat := 3861361684794320796928771

theorem tailTrace_7519975 : CollatzResearch.WordTrace tailWord_7519975 prefixEnd_7519975 3861361684794320796928771 := by
  unfold tailWord_7519975
  simp only [CollatzResearch.WordTrace]
  refine ⟨274276020931422359326009379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182850680620948239550672919 274276020931422359326009379)
  ·
    refine ⟨411414031397133538989014069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274276020931422359326009379 411414031397133538989014069)
    ·
      refine ⟨38570065443481269280220069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 411414031397133538989014069 38570065443481269280220069)
      ·
        refine ⟨7231887270652737990041263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38570065443481269280220069 7231887270652737990041263)
        ·
          refine ⟨10847830905979106985061895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7231887270652737990041263 10847830905979106985061895)
          ·
            refine ⟨16271746358968660477592843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10847830905979106985061895 16271746358968660477592843)
            ·
              refine ⟨24407619538452990716389265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16271746358968660477592843 24407619538452990716389265)
              ·
                refine ⟨18305714653839743037291949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24407619538452990716389265 18305714653839743037291949)
                ·
                  refine ⟨6864642995189903638984481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18305714653839743037291949 6864642995189903638984481)
                  ·
                    refine ⟨5148482246392427729238361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6864642995189903638984481 5148482246392427729238361)
                    ·
                      refine ⟨3861361684794320796928771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5148482246392427729238361 3861361684794320796928771)
                      ·
                        rfl

theorem cell23_7519975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_7519975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519975 prefixEnd_7519975 := by exact prefixLift 7519975
  have htrace : WordTrace (prefixWord ++ tailWord_7519975) baseStart_7519975 baseEnd_7519975 := by
    simpa [prefixWord, tailWord_7519975, baseEnd_7519975] using wordTrace_append hprefix tailTrace_7519975
  have hstable : (prefixWord ++ tailWord_7519975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519975).length < 2 ^ (prefixWord ++ tailWord_7519975).sum := by decide
  have hdescent : baseEnd_7519975 < baseStart_7519975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519988 : List Nat := [2, 6, 1, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_7519988 : Nat := 118140960795 + 7519988 * 2 ^ 59
def prefixEnd_7519988 : Nat := 4983230072969 + 3 ^ 40 * 7519988 * 2
def baseEnd_7519988 : Nat := 3861368360042829246066211

theorem tailTrace_7519988 : CollatzResearch.WordTrace tailWord_7519988 prefixEnd_7519988 3861368360042829246066211 := by
  unfold tailWord_7519988
  simp only [CollatzResearch.WordTrace]
  refine ⟨137138247540187631273116309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182850996720250175030821745 137138247540187631273116309)
  ·
    refine ⟨6428355353446295215927327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 137138247540187631273116309 6428355353446295215927327)
    ·
      refine ⟨9642533030169442823890991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6428355353446295215927327 9642533030169442823890991)
      ·
        refine ⟨14463799545254164235836487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9642533030169442823890991 14463799545254164235836487)
        ·
          refine ⟨21695699317881246353754731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14463799545254164235836487 21695699317881246353754731)
          ·
            refine ⟨32543548976821869530632097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21695699317881246353754731 32543548976821869530632097)
            ·
              refine ⟨24407661732616402147974073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32543548976821869530632097 24407661732616402147974073)
              ·
                refine ⟨18305746299462301610980555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24407661732616402147974073 18305746299462301610980555)
                ·
                  refine ⟨27458619449193452416470833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18305746299462301610980555 27458619449193452416470833)
                  ·
                    refine ⟨20593964586895089312353125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27458619449193452416470833 20593964586895089312353125)
                    ·
                      refine ⟨3861368360042829246066211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20593964586895089312353125 3861368360042829246066211)
                      ·
                        rfl

theorem cell23_7519988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_7519988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519988 prefixEnd_7519988 := by exact prefixLift 7519988
  have htrace : WordTrace (prefixWord ++ tailWord_7519988) baseStart_7519988 baseEnd_7519988 := by
    simpa [prefixWord, tailWord_7519988, baseEnd_7519988] using wordTrace_append hprefix tailTrace_7519988
  have hstable : (prefixWord ++ tailWord_7519988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519988).length < 2 ^ (prefixWord ++ tailWord_7519988).sum := by decide
  have hdescent : baseEnd_7519988 < baseStart_7519988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7519997 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_7519997 : Nat := 118140960795 + 7519997 * 2 ^ 59
def prefixEnd_7519997 : Nat := 4983230072969 + 3 ^ 40 * 7519997 * 2
def baseEnd_7519997 : Nat := 3861372981368719710853669

theorem tailTrace_7519997 : CollatzResearch.WordTrace tailWord_7519997 prefixEnd_7519997 3861372981368719710853669 := by
  unfold tailWord_7519997
  simp only [CollatzResearch.WordTrace]
  refine ⟨274276823337342657083310245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182851215558228438055540163 274276823337342657083310245)
  ·
    refine ⟨51426904375751748203120671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274276823337342657083310245 51426904375751748203120671)
    ·
      refine ⟨77140356563627622304681007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51426904375751748203120671 77140356563627622304681007)
      ·
        refine ⟨115710534845441433457021511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77140356563627622304681007 115710534845441433457021511)
        ·
          refine ⟨173565802268162150185532267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115710534845441433457021511 173565802268162150185532267)
          ·
            refine ⟨260348703402243225278298401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173565802268162150185532267 260348703402243225278298401)
            ·
              refine ⟨195261527551682418958723801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260348703402243225278298401 195261527551682418958723801)
              ·
                refine ⟨146446145663761814219042851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195261527551682418958723801 146446145663761814219042851)
                ·
                  refine ⟨219669218495642721328564277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146446145663761814219042851 219669218495642721328564277)
                  ·
                    refine ⟨20593989233966505124552901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 219669218495642721328564277 20593989233966505124552901)
                    ·
                      refine ⟨3861372981368719710853669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20593989233966505124552901 3861372981368719710853669)
                      ·
                        rfl

theorem cell23_7519997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_7519997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7519997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7519997 prefixEnd_7519997 := by exact prefixLift 7519997
  have htrace : WordTrace (prefixWord ++ tailWord_7519997) baseStart_7519997 baseEnd_7519997 := by
    simpa [prefixWord, tailWord_7519997, baseEnd_7519997] using wordTrace_append hprefix tailTrace_7519997
  have hstable : (prefixWord ++ tailWord_7519997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7519997).length < 2 ^ (prefixWord ++ tailWord_7519997).sum := by decide
  have hdescent : baseEnd_7519997 < baseStart_7519997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7519997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520017 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 5]
def baseStart_7520017 : Nat := 118140960795 + 7520017 * 2 ^ 59
def prefixEnd_7520017 : Nat := 4983230072969 + 3 ^ 40 * 7520017 * 2
def baseEnd_7520017 : Nat := 3861383250981809632603577

theorem tailTrace_7520017 : CollatzResearch.WordTrace tailWord_7520017 prefixEnd_7520017 3861383250981809632603577 := by
  unfold tailWord_7520017
  simp only [CollatzResearch.WordTrace]
  refine ⟨274277552797270200499038305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182851701864846800332692203 274277552797270200499038305)
  ·
    refine ⟨205708164597952650374278729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274277552797270200499038305 205708164597952650374278729)
    ·
      refine ⟨154281123448464487780709047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205708164597952650374278729 154281123448464487780709047)
      ·
        refine ⟨231421685172696731671063571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154281123448464487780709047 231421685172696731671063571)
        ·
          refine ⟨347132527759045097506595357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231421685172696731671063571 347132527759045097506595357)
          ·
            refine ⟨130174697909641911564973259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347132527759045097506595357 130174697909641911564973259)
            ·
              refine ⟨195262046864462867347459889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130174697909641911564973259 195262046864462867347459889)
              ·
                refine ⟨146446535148347150510594917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195262046864462867347459889 146446535148347150510594917)
                ·
                  refine ⟨27458725340315090720736547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146446535148347150510594917 27458725340315090720736547)
                  ·
                    refine ⟨41188088010472636081104821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27458725340315090720736547 41188088010472636081104821)
                    ·
                      refine ⟨3861383250981809632603577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41188088010472636081104821 3861383250981809632603577)
                      ·
                        rfl

theorem cell23_7520017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_7520017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520017 prefixEnd_7520017 := by exact prefixLift 7520017
  have htrace : WordTrace (prefixWord ++ tailWord_7520017) baseStart_7520017 baseEnd_7520017 := by
    simpa [prefixWord, tailWord_7520017, baseEnd_7520017] using wordTrace_append hprefix tailTrace_7520017
  have hstable : (prefixWord ++ tailWord_7520017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520017).length < 2 ^ (prefixWord ++ tailWord_7520017).sum := by decide
  have hdescent : baseEnd_7520017 < baseStart_7520017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520034 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_7520034 : Nat := 118140960795 + 7520034 * 2 ^ 59
def prefixEnd_7520034 : Nat := 4983230072969 + 3 ^ 40 * 7520034 * 2
def baseEnd_7520034 : Nat := 3861391980152936066090999

theorem tailTrace_7520034 : CollatzResearch.WordTrace tailWord_7520034 prefixEnd_7520034 3861391980152936066090999 := by
  unfold tailWord_7520034
  simp only [CollatzResearch.WordTrace]
  refine ⟨68569543209552153100601789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182852115225472408268271437 68569543209552153100601789)
  ·
    refine ⟨25713578703582057412725671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68569543209552153100601789 25713578703582057412725671)
    ·
      refine ⟨38570368055373086119088507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25713578703582057412725671 38570368055373086119088507)
      ·
        refine ⟨57855552083059629178632761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38570368055373086119088507 57855552083059629178632761)
        ·
          refine ⟨43391664062294721883974571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57855552083059629178632761 43391664062294721883974571)
          ·
            refine ⟨65087496093442082825961857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43391664062294721883974571 65087496093442082825961857)
            ·
              refine ⟨48815622070081562119471393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65087496093442082825961857 48815622070081562119471393)
              ·
                refine ⟨36611716552561171589603545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48815622070081562119471393 36611716552561171589603545)
                ·
                  refine ⟨27458787414420878692202659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36611716552561171589603545 27458787414420878692202659)
                  ·
                    refine ⟨41188181121631318038303989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27458787414420878692202659 41188181121631318038303989)
                    ·
                      refine ⟨3861391980152936066090999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41188181121631318038303989 3861391980152936066090999)
                      ·
                        rfl

theorem cell23_7520034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_7520034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520034 prefixEnd_7520034 := by exact prefixLift 7520034
  have htrace : WordTrace (prefixWord ++ tailWord_7520034) baseStart_7520034 baseEnd_7520034 := by
    simpa [prefixWord, tailWord_7520034, baseEnd_7520034] using wordTrace_append hprefix tailTrace_7520034
  have hstable : (prefixWord ++ tailWord_7520034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520034).length < 2 ^ (prefixWord ++ tailWord_7520034).sum := by decide
  have hdescent : baseEnd_7520034 < baseStart_7520034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520082 : List Nat := [3, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2]
def baseStart_7520082 : Nat := 118140960795 + 7520082 * 2 ^ 59
def prefixEnd_7520082 : Nat := 4983230072969 + 3 ^ 40 * 7520082 * 2
def baseEnd_7520082 : Nat := 3861416627224351878290779

theorem tailTrace_7520082 : CollatzResearch.WordTrace tailWord_7520082 prefixEnd_7520082 3861416627224351878290779 := by
  unfold tailWord_7520082
  simp only [CollatzResearch.WordTrace]
  refine ⟨68569980885508679150038625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182853282361356477733436333 68569980885508679150038625)
  ·
    refine ⟨51427485664131509362528969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68569980885508679150038625 51427485664131509362528969)
    ·
      refine ⟨38570614248098632021896727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51427485664131509362528969 38570614248098632021896727)
      ·
        refine ⟨57855921372147948032845091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38570614248098632021896727 57855921372147948032845091)
        ·
          refine ⟨86783882058221922049267637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57855921372147948032845091 86783882058221922049267637)
          ·
            refine ⟨8135988942958305192118841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86783882058221922049267637 8135988942958305192118841)
            ·
              refine ⟨6101991707218728894089131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8135988942958305192118841 6101991707218728894089131)
              ·
                refine ⟨9152987560828093341133697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6101991707218728894089131 9152987560828093341133697)
                ·
                  refine ⟨6864740670621070005850273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9152987560828093341133697 6864740670621070005850273)
                  ·
                    refine ⟨5148555502965802504387705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6864740670621070005850273 5148555502965802504387705)
                    ·
                      refine ⟨3861416627224351878290779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5148555502965802504387705 3861416627224351878290779)
                      ·
                        rfl

theorem cell23_7520082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_7520082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520082 prefixEnd_7520082 := by exact prefixLift 7520082
  have htrace : WordTrace (prefixWord ++ tailWord_7520082) baseStart_7520082 baseEnd_7520082 := by
    simpa [prefixWord, tailWord_7520082, baseEnd_7520082] using wordTrace_append hprefix tailTrace_7520082
  have hstable : (prefixWord ++ tailWord_7520082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520082).length < 2 ^ (prefixWord ++ tailWord_7520082).sum := by decide
  have hdescent : baseEnd_7520082 < baseStart_7520082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520121 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 2, 4, 2]
def baseStart_7520121 : Nat := 118140960795 + 7520121 * 2 ^ 59
def prefixEnd_7520121 : Nat := 4983230072969 + 3 ^ 40 * 7520121 * 2
def baseEnd_7520121 : Nat := 3861436652969877225703099

theorem tailTrace_7520121 : CollatzResearch.WordTrace tailWord_7520121 prefixEnd_7520121 3861436652969877225703099 := by
  unfold tailWord_7520121
  simp only [CollatzResearch.WordTrace]
  refine ⟨274281345988893426260824217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182854230659262284173882811 274281345988893426260824217)
  ·
    refine ⟨205711009491670069695618163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274281345988893426260824217 205711009491670069695618163)
    ·
      refine ⟨308566514237505104543427245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205711009491670069695618163 308566514237505104543427245)
      ·
        refine ⟨115712442839064414203785217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308566514237505104543427245 115712442839064414203785217)
        ·
          refine ⟨86784332129298310652838913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115712442839064414203785217 86784332129298310652838913)
          ·
            refine ⟨65088249096973732989629185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86784332129298310652838913 65088249096973732989629185)
            ·
              refine ⟨48816186822730299742221889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65088249096973732989629185 48816186822730299742221889)
              ·
                refine ⟨36612140117047724806666417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48816186822730299742221889 36612140117047724806666417)
                ·
                  refine ⟨27459105087785793604999813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36612140117047724806666417 27459105087785793604999813)
                  ·
                    refine ⟨5148582203959836300937465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27459105087785793604999813 5148582203959836300937465)
                    ·
                      refine ⟨3861436652969877225703099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5148582203959836300937465 3861436652969877225703099)
                      ·
                        rfl

theorem cell23_7520121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_7520121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520121 prefixEnd_7520121 := by exact prefixLift 7520121
  have htrace : WordTrace (prefixWord ++ tailWord_7520121) baseStart_7520121 baseEnd_7520121 := by
    simpa [prefixWord, tailWord_7520121, baseEnd_7520121] using wordTrace_append hprefix tailTrace_7520121
  have hstable : (prefixWord ++ tailWord_7520121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520121).length < 2 ^ (prefixWord ++ tailWord_7520121).sum := by decide
  have hdescent : baseEnd_7520121 < baseStart_7520121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520124 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 5, 4, 3]
def baseStart_7520124 : Nat := 118140960795 + 7520124 * 2 ^ 59
def prefixEnd_7520124 : Nat := 4983230072969 + 3 ^ 40 * 7520124 * 2
def baseEnd_7520124 : Nat := 3861438193411840713965585

theorem tailTrace_7520124 : CollatzResearch.WordTrace tailWord_7520124 prefixEnd_7520124 3861438193411840713965585 := by
  unfold tailWord_7520124
  simp only [CollatzResearch.WordTrace]
  refine ⟨137140727703941278886591713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182854303605255038515455617 137140727703941278886591713)
  ·
    refine ⟨102855545777955959164943785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137140727703941278886591713 102855545777955959164943785)
    ·
      refine ⟨77141659333466969373707839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102855545777955959164943785 77141659333466969373707839)
      ·
        refine ⟨115712489000200454060561759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77141659333466969373707839 115712489000200454060561759)
        ·
          refine ⟨173568733500300681090842639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115712489000200454060561759 173568733500300681090842639)
          ·
            refine ⟨260353100250451021636263959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173568733500300681090842639 260353100250451021636263959)
            ·
              refine ⟨390529650375676532454395939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260353100250451021636263959 390529650375676532454395939)
              ·
                refine ⟨585794475563514798681593909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390529650375676532454395939 585794475563514798681593909)
                ·
                  refine ⟨54918232084079512376399429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 585794475563514798681593909 54918232084079512376399429)
                  ·
                    refine ⟨10297168515764908570574893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54918232084079512376399429 10297168515764908570574893)
                    ·
                      refine ⟨3861438193411840713965585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10297168515764908570574893 3861438193411840713965585)
                      ·
                        rfl

theorem cell23_7520124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_7520124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520124 prefixEnd_7520124 := by exact prefixLift 7520124
  have htrace : WordTrace (prefixWord ++ tailWord_7520124) baseStart_7520124 baseEnd_7520124 := by
    simpa [prefixWord, tailWord_7520124, baseEnd_7520124] using wordTrace_append hprefix tailTrace_7520124
  have hstable : (prefixWord ++ tailWord_7520124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520124).length < 2 ^ (prefixWord ++ tailWord_7520124).sum := by decide
  have hdescent : baseEnd_7520124 < baseStart_7520124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520148 : List Nat := [2, 4, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_7520148 : Nat := 118140960795 + 7520148 * 2 ^ 59
def prefixEnd_7520148 : Nat := 4983230072969 + 3 ^ 40 * 7520148 * 2
def baseEnd_7520148 : Nat := 1287150172315849540021825

theorem tailTrace_7520148 : CollatzResearch.WordTrace tailWord_7520148 prefixEnd_7520148 1287150172315849540021825 := by
  unfold tailWord_7520148
  simp only [CollatzResearch.WordTrace]
  refine ⟨137141165379897804936028549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182854887173197073248038065 137141165379897804936028549)
  ·
    refine ⟨25713968508730838425505353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137141165379897804936028549 25713968508730838425505353)
    ·
      refine ⟨19285476381548128819129015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25713968508730838425505353 19285476381548128819129015)
      ·
        refine ⟨28928214572322193228693523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19285476381548128819129015 28928214572322193228693523)
        ·
          refine ⟨43392321858483289843040285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28928214572322193228693523 43392321858483289843040285)
          ·
            refine ⟨16272120696931233691140107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43392321858483289843040285 16272120696931233691140107)
            ·
              refine ⟨24408181045396850536710161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16272120696931233691140107 24408181045396850536710161)
              ·
                refine ⟨18306135784047637902532621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24408181045396850536710161 18306135784047637902532621)
                ·
                  refine ⟨6864800919017864213449733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18306135784047637902532621 6864800919017864213449733)
                  ·
                    refine ⟨1287150172315849540021825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6864800919017864213449733 1287150172315849540021825)
                    ·
                      rfl

theorem cell23_7520148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_7520148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520148 prefixEnd_7520148 := by exact prefixLift 7520148
  have htrace : WordTrace (prefixWord ++ tailWord_7520148) baseStart_7520148 baseEnd_7520148 := by
    simpa [prefixWord, tailWord_7520148, baseEnd_7520148] using wordTrace_append hprefix tailTrace_7520148
  have hstable : (prefixWord ++ tailWord_7520148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520148).length < 2 ^ (prefixWord ++ tailWord_7520148).sum := by decide
  have hdescent : baseEnd_7520148 < baseStart_7520148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520238 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 4, 4]
def baseStart_7520238 : Nat := 118140960795 + 7520238 * 2 ^ 59
def prefixEnd_7520238 : Nat := 4983230072969 + 3 ^ 40 * 7520238 * 2
def baseEnd_7520238 : Nat := 1287165576735484422646687

theorem tailTrace_7520238 : CollatzResearch.WordTrace tailWord_7520238 prefixEnd_7520238 1287165576735484422646687 := by
  unfold tailWord_7520238
  simp only [CollatzResearch.WordTrace]
  refine ⟨34285701666183694405354171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182857075552979703495222245 34285701666183694405354171)
  ·
    refine ⟨51428552499275541608031257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34285701666183694405354171 51428552499275541608031257)
    ·
      refine ⟨38571414374456656206023443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51428552499275541608031257 38571414374456656206023443)
      ·
        refine ⟨57857121561684984309035165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38571414374456656206023443 57857121561684984309035165)
        ·
          refine ⟨21696420585631869115888187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57857121561684984309035165 21696420585631869115888187)
          ·
            refine ⟨32544630878447803673832281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21696420585631869115888187 32544630878447803673832281)
            ·
              refine ⟨24408473158835852755374211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32544630878447803673832281 24408473158835852755374211)
              ·
                refine ⟨36612709738253779133061317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24408473158835852755374211 36612709738253779133061317)
                ·
                  refine ⟨6864883075922583587448997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36612709738253779133061317 6864883075922583587448997)
                  ·
                    refine ⟨1287165576735484422646687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6864883075922583587448997 1287165576735484422646687)
                    ·
                      rfl

theorem cell23_7520238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_7520238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520238 prefixEnd_7520238 := by exact prefixLift 7520238
  have htrace : WordTrace (prefixWord ++ tailWord_7520238) baseStart_7520238 baseEnd_7520238 := by
    simpa [prefixWord, tailWord_7520238, baseEnd_7520238] using wordTrace_append hprefix tailTrace_7520238
  have hstable : (prefixWord ++ tailWord_7520238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520238).length < 2 ^ (prefixWord ++ tailWord_7520238).sum := by decide
  have hdescent : baseEnd_7520238 < baseStart_7520238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520296 : List Nat := [2, 1, 5, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_7520296 : Nat := 118140960795 + 7520296 * 2 ^ 59
def prefixEnd_7520296 : Nat := 4983230072969 + 3 ^ 40 * 7520296 * 2
def baseEnd_7520296 : Nat := 3861526512084414041014795

theorem tailTrace_7520296 : CollatzResearch.WordTrace tailWord_7520296 prefixEnd_7520296 3861526512084414041014795 := by
  unfold tailWord_7520296
  simp only [CollatzResearch.WordTrace]
  refine ⟨137143864381629715574222371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182858485842172954098963161 137143864381629715574222371)
  ·
    refine ⟨205715796572444573361333557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137143864381629715574222371 205715796572444573361333557)
    ·
      refine ⟨19285855928666678752625021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205715796572444573361333557 19285855928666678752625021)
      ·
        refine ⟨7232195973250004532234383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19285855928666678752625021 7232195973250004532234383)
        ·
          refine ⟨10848293959875006798351575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7232195973250004532234383 10848293959875006798351575)
          ·
            refine ⟨16272440939812510197527363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10848293959875006798351575 16272440939812510197527363)
            ·
              refine ⟨24408661409718765296291045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16272440939812510197527363 24408661409718765296291045)
              ·
                refine ⟨4576624014322268493054571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24408661409718765296291045 4576624014322268493054571)
                ·
                  refine ⟨6864936021483402739581857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4576624014322268493054571 6864936021483402739581857)
                  ·
                    refine ⟨5148702016112552054686393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6864936021483402739581857 5148702016112552054686393)
                    ·
                      refine ⟨3861526512084414041014795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5148702016112552054686393 3861526512084414041014795)
                      ·
                        rfl

theorem cell23_7520296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_7520296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520296 prefixEnd_7520296 := by exact prefixLift 7520296
  have htrace : WordTrace (prefixWord ++ tailWord_7520296) baseStart_7520296 baseEnd_7520296 := by
    simpa [prefixWord, tailWord_7520296, baseEnd_7520296] using wordTrace_append hprefix tailTrace_7520296
  have hstable : (prefixWord ++ tailWord_7520296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520296).length < 2 ^ (prefixWord ++ tailWord_7520296).sum := by decide
  have hdescent : baseEnd_7520296 < baseStart_7520296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520348 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_7520348 : Nat := 118140960795 + 7520348 * 2 ^ 59
def prefixEnd_7520348 : Nat := 4983230072969 + 3 ^ 40 * 7520348 * 2
def baseEnd_7520348 : Nat := 3861553213078447837564555

theorem tailTrace_7520348 : CollatzResearch.WordTrace tailWord_7520348 prefixEnd_7520348 3861553213078447837564555 := by
  unfold tailWord_7520348
  simp only [CollatzResearch.WordTrace]
  refine ⟨137144812679535522014668849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182859750239380696019558465 137144812679535522014668849)
  ·
    refine ⟨102858609509651641511001637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137144812679535522014668849 102858609509651641511001637)
    ·
      refine ⟨19285989283059682783312807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102858609509651641511001637 19285989283059682783312807)
      ·
        refine ⟨28928983924589524174969211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19285989283059682783312807 28928983924589524174969211)
        ·
          refine ⟨43393475886884286262453817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28928983924589524174969211 43393475886884286262453817)
          ·
            refine ⟨32545106915163214696840363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43393475886884286262453817 32545106915163214696840363)
            ·
              refine ⟨48817660372744822045260545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32545106915163214696840363 48817660372744822045260545)
              ·
                refine ⟨36613245279558616533945409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48817660372744822045260545 36613245279558616533945409)
                ·
                  refine ⟨27459933959668962400459057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36613245279558616533945409 27459933959668962400459057)
                  ·
                    refine ⟨20594950469751721800344293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27459933959668962400459057 20594950469751721800344293)
                    ·
                      refine ⟨3861553213078447837564555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20594950469751721800344293 3861553213078447837564555)
                      ·
                        rfl

theorem cell23_7520348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_7520348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520348 prefixEnd_7520348 := by exact prefixLift 7520348
  have htrace : WordTrace (prefixWord ++ tailWord_7520348) baseStart_7520348 baseEnd_7520348 := by
    simpa [prefixWord, tailWord_7520348, baseEnd_7520348] using wordTrace_append hprefix tailTrace_7520348
  have hstable : (prefixWord ++ tailWord_7520348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520348).length < 2 ^ (prefixWord ++ tailWord_7520348).sum := by decide
  have hdescent : baseEnd_7520348 < baseStart_7520348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520352 : List Nat := [2, 1, 1, 3, 2, 3, 3, 2, 2, 2, 2]
def baseStart_7520352 : Nat := 118140960795 + 7520352 * 2 ^ 59
def prefixEnd_7520352 : Nat := 4983230072969 + 3 ^ 40 * 7520352 * 2
def baseEnd_7520352 : Nat := 3861555267001065821914537

theorem tailTrace_7520352 : CollatzResearch.WordTrace tailWord_7520352 prefixEnd_7520352 3861555267001065821914537 := by
  unfold tailWord_7520352
  simp only [CollatzResearch.WordTrace]
  refine ⟨137144885625528276356241655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182859847500704368474988873 137144885625528276356241655)
  ·
    refine ⟨205717328438292414534362483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137144885625528276356241655 205717328438292414534362483)
    ·
      refine ⟨308575992657438621801543725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205717328438292414534362483 308575992657438621801543725)
      ·
        refine ⟨115715997246539483175578897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308575992657438621801543725 115715997246539483175578897)
        ·
          refine ⟨86786997934904612381684173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115715997246539483175578897 86786997934904612381684173)
          ·
            refine ⟨32545124225589229643131565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86786997934904612381684173 32545124225589229643131565)
            ·
              refine ⟨12204421584595961116174337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32545124225589229643131565 12204421584595961116174337)
              ·
                refine ⟨9153316188446970837130753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12204421584595961116174337 9153316188446970837130753)
                ·
                  refine ⟨6864987141335228127848065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9153316188446970837130753 6864987141335228127848065)
                  ·
                    refine ⟨5148740356001421095886049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6864987141335228127848065 5148740356001421095886049)
                    ·
                      refine ⟨3861555267001065821914537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5148740356001421095886049 3861555267001065821914537)
                      ·
                        rfl

theorem cell23_7520352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_7520352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520352 prefixEnd_7520352 := by exact prefixLift 7520352
  have htrace : WordTrace (prefixWord ++ tailWord_7520352) baseStart_7520352 baseEnd_7520352 := by
    simpa [prefixWord, tailWord_7520352, baseEnd_7520352] using wordTrace_append hprefix tailTrace_7520352
  have hstable : (prefixWord ++ tailWord_7520352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520352).length < 2 ^ (prefixWord ++ tailWord_7520352).sum := by decide
  have hdescent : baseEnd_7520352 < baseStart_7520352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520368 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 3]
def baseStart_7520368 : Nat := 118140960795 + 7520368 * 2 ^ 59
def prefixEnd_7520368 : Nat := 4983230072969 + 3 ^ 40 * 7520368 * 2
def baseEnd_7520368 : Nat := 3861563482691537759314463

theorem tailTrace_7520368 : CollatzResearch.WordTrace tailWord_7520368 prefixEnd_7520368 3861563482691537759314463 := by
  unfold tailWord_7520368
  simp only [CollatzResearch.WordTrace]
  refine ⟨137145177409499293722532879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182860236545999058296710505 137145177409499293722532879)
  ·
    refine ⟨205717766114248940583799319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137145177409499293722532879 205717766114248940583799319)
    ·
      refine ⟨308576649171373410875698979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205717766114248940583799319 308576649171373410875698979)
      ·
        refine ⟨462864973757060116313548469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308576649171373410875698979 462864973757060116313548469)
        ·
          refine ⟨43393591289724385904395169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 462864973757060116313548469 43393591289724385904395169)
          ·
            refine ⟨32545193467293289428296377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43393591289724385904395169 32545193467293289428296377)
            ·
              refine ⟨24408895100469967071222283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32545193467293289428296377 24408895100469967071222283)
              ·
                refine ⟨36613342650704950606833425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24408895100469967071222283 36613342650704950606833425)
                ·
                  refine ⟨27460006988028712955125069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36613342650704950606833425 27460006988028712955125069)
                  ·
                    refine ⟨10297502620510767358171901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27460006988028712955125069 10297502620510767358171901)
                    ·
                      refine ⟨3861563482691537759314463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10297502620510767358171901 3861563482691537759314463)
                      ·
                        rfl

theorem cell23_7520368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 3].length) (baseStart_7520368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520368 prefixEnd_7520368 := by exact prefixLift 7520368
  have htrace : WordTrace (prefixWord ++ tailWord_7520368) baseStart_7520368 baseEnd_7520368 := by
    simpa [prefixWord, tailWord_7520368, baseEnd_7520368] using wordTrace_append hprefix tailTrace_7520368
  have hstable : (prefixWord ++ tailWord_7520368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520368).length < 2 ^ (prefixWord ++ tailWord_7520368).sum := by decide
  have hdescent : baseEnd_7520368 < baseStart_7520368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520388 : List Nat := [2, 3, 2, 1, 2, 1, 2, 3, 2, 5]
def baseStart_7520388 : Nat := 118140960795 + 7520388 * 2 ^ 59
def prefixEnd_7520388 : Nat := 4983230072969 + 3 ^ 40 * 7520388 * 2
def baseEnd_7520388 : Nat := 1287191250768209227021457

theorem tailTrace_7520388 : CollatzResearch.WordTrace tailWord_7520388 prefixEnd_7520388 1287191250768209227021457 := by
  unfold tailWord_7520388
  simp only [CollatzResearch.WordTrace]
  refine ⟨137145542139463065430396909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182860722852617420573862545 137145542139463065430396909)
  ·
    refine ⟨51429578302298649536398841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137145542139463065430396909 51429578302298649536398841)
    ·
      refine ⟨38572183726723987152299131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51429578302298649536398841 38572183726723987152299131)
      ·
        refine ⟨57858275590085980728448697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38572183726723987152299131 57858275590085980728448697)
        ·
          refine ⟨43393706692564485546336523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57858275590085980728448697 43393706692564485546336523)
          ·
            refine ⟨65090560038846728319504785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43393706692564485546336523 65090560038846728319504785)
            ·
              refine ⟨48817920029135046239628589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65090560038846728319504785 48817920029135046239628589)
              ·
                refine ⟨18306720010925642339860721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48817920029135046239628589 18306720010925642339860721)
                ·
                  refine ⟨13730040008194231754895541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18306720010925642339860721 13730040008194231754895541)
                  ·
                    refine ⟨1287191250768209227021457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13730040008194231754895541 1287191250768209227021457)
                    ·
                      rfl

theorem cell23_7520388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_7520388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520388 prefixEnd_7520388 := by exact prefixLift 7520388
  have htrace : WordTrace (prefixWord ++ tailWord_7520388) baseStart_7520388 baseEnd_7520388 := by
    simpa [prefixWord, tailWord_7520388, baseEnd_7520388] using wordTrace_append hprefix tailTrace_7520388
  have hstable : (prefixWord ++ tailWord_7520388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520388).length < 2 ^ (prefixWord ++ tailWord_7520388).sum := by decide
  have hdescent : baseEnd_7520388 < baseStart_7520388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520392 : List Nat := [2, 1, 3, 4, 1, 3, 1, 3, 5]
def baseStart_7520392 : Nat := 118140960795 + 7520392 * 2 ^ 59
def prefixEnd_7520392 : Nat := 4983230072969 + 3 ^ 40 * 7520392 * 2
def baseEnd_7520392 : Nat := 429063978469693962823817

theorem tailTrace_7520392 : CollatzResearch.WordTrace tailWord_7520392 prefixEnd_7520392 429063978469693962823817 := by
  unfold tailWord_7520392
  simp only [CollatzResearch.WordTrace]
  refine ⟨137145615085455819771969715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182860820113941093029292953 137145615085455819771969715)
  ·
    refine ⟨205718422628183729657954573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137145615085455819771969715 205718422628183729657954573)
    ·
      refine ⟨77144408485568898621732965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205718422628183729657954573 77144408485568898621732965)
      ·
        refine ⟨14464576591044168491574931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77144408485568898621732965 14464576591044168491574931)
        ·
          refine ⟨21696864886566252737362397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14464576591044168491574931 21696864886566252737362397)
          ·
            refine ⟨8136324332462344776510899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21696864886566252737362397 8136324332462344776510899)
            ·
              refine ⟨12204486498693517164766349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8136324332462344776510899 12204486498693517164766349)
              ·
                refine ⟨4576682437010068936787381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12204486498693517164766349 4576682437010068936787381)
                ·
                  refine ⟨429063978469693962823817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4576682437010068936787381 429063978469693962823817)
                  ·
                    rfl

theorem cell23_7520392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 5].length) (baseStart_7520392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520392 prefixEnd_7520392 := by exact prefixLift 7520392
  have htrace : WordTrace (prefixWord ++ tailWord_7520392) baseStart_7520392 baseEnd_7520392 := by
    simpa [prefixWord, tailWord_7520392, baseEnd_7520392] using wordTrace_append hprefix tailTrace_7520392
  have hstable : (prefixWord ++ tailWord_7520392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520392).length < 2 ^ (prefixWord ++ tailWord_7520392).sum := by decide
  have hdescent : baseEnd_7520392 < baseStart_7520392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520469 : List Nat := [1, 3, 2, 4, 2, 1, 1, 4, 1, 4]
def baseStart_7520469 : Nat := 118140960795 + 7520469 * 2 ^ 59
def prefixEnd_7520469 : Nat := 4983230072969 + 3 ^ 40 * 7520469 * 2
def baseEnd_7520469 : Nat := 1287205114745880621383833

theorem tailTrace_7520469 : CollatzResearch.WordTrace tailWord_7520469 prefixEnd_7520469 1287205114745880621383833 := by
  unfold tailWord_7520469
  simp only [CollatzResearch.WordTrace]
  refine ⟨274294038591632681694492461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182862692394421787796328307 274294038591632681694492461)
  ·
    refine ⟨102860264471862255635434673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274294038591632681694492461 102860264471862255635434673)
    ·
      refine ⟨77145198353896691726576005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102860264471862255635434673 77145198353896691726576005)
      ·
        refine ⟨14464724691355629698733001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77145198353896691726576005 14464724691355629698733001)
        ·
          refine ⟨10848543518516722274049751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14464724691355629698733001 10848543518516722274049751)
          ·
            refine ⟨16272815277775083411074627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10848543518516722274049751 16272815277775083411074627)
            ·
              refine ⟨24409222916662625116611941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16272815277775083411074627 24409222916662625116611941)
              ·
                refine ⟨4576729296874242209364739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24409222916662625116611941 4576729296874242209364739)
                ·
                  refine ⟨6865093945311363314047109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4576729296874242209364739 6865093945311363314047109)
                  ·
                    refine ⟨1287205114745880621383833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6865093945311363314047109 1287205114745880621383833)
                    ·
                      rfl

theorem cell23_7520469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_7520469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520469 prefixEnd_7520469 := by exact prefixLift 7520469
  have htrace : WordTrace (prefixWord ++ tailWord_7520469) baseStart_7520469 baseEnd_7520469 := by
    simpa [prefixWord, tailWord_7520469, baseEnd_7520469] using wordTrace_append hprefix tailTrace_7520469
  have hstable : (prefixWord ++ tailWord_7520469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520469).length < 2 ^ (prefixWord ++ tailWord_7520469).sum := by decide
  have hdescent : baseEnd_7520469 < baseStart_7520469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520515 : List Nat := [1, 1, 1, 3, 2, 3, 3, 3, 1, 1, 4]
def baseStart_7520515 : Nat := 118140960795 + 7520515 * 2 ^ 59
def prefixEnd_7520515 : Nat := 4983230072969 + 3 ^ 40 * 7520515 * 2
def baseEnd_7520515 : Nat := 3861638964347748684176287

theorem tailTrace_7520515 : CollatzResearch.WordTrace tailWord_7520515 prefixEnd_7520515 3861638964347748684176287 := by
  unfold tailWord_7520515
  simp only [CollatzResearch.WordTrace]
  refine ⟨274295716349466031550666999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182863810899644021033777999 274295716349466031550666999)
  ·
    refine ⟨411443574524199047326000499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274295716349466031550666999 411443574524199047326000499)
    ·
      refine ⟨617165361786298570989000749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411443574524199047326000499 617165361786298570989000749)
      ·
        refine ⟨231437010669861964120875281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 617165361786298570989000749 231437010669861964120875281)
        ·
          refine ⟨173577758002396473090656461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231437010669861964120875281 173577758002396473090656461)
          ·
            refine ⟨65091659250898677408996173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173577758002396473090656461 65091659250898677408996173)
            ·
              refine ⟨24409372219087004028373565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65091659250898677408996173 24409372219087004028373565)
              ·
                refine ⟨9153514582157626510640087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24409372219087004028373565 9153514582157626510640087)
                ·
                  refine ⟨13730271873236439765960131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9153514582157626510640087 13730271873236439765960131)
                  ·
                    refine ⟨20595407809854659648940197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13730271873236439765960131 20595407809854659648940197)
                    ·
                      refine ⟨3861638964347748684176287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20595407809854659648940197 3861638964347748684176287)
                      ·
                        rfl

theorem cell23_7520515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 1, 4].length) (baseStart_7520515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520515 prefixEnd_7520515 := by exact prefixLift 7520515
  have htrace : WordTrace (prefixWord ++ tailWord_7520515) baseStart_7520515 baseEnd_7520515 := by
    simpa [prefixWord, tailWord_7520515, baseEnd_7520515] using wordTrace_append hprefix tailTrace_7520515
  have hstable : (prefixWord ++ tailWord_7520515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520515).length < 2 ^ (prefixWord ++ tailWord_7520515).sum := by decide
  have hdescent : baseEnd_7520515 < baseStart_7520515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520535 : List Nat := [1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 5]
def baseStart_7520535 : Nat := 118140960795 + 7520535 * 2 ^ 59
def prefixEnd_7520535 : Nat := 4983230072969 + 3 ^ 40 * 7520535 * 2
def baseEnd_7520535 : Nat := 3861649233960838605926195

theorem tailTrace_7520535 : CollatzResearch.WordTrace tailWord_7520535 prefixEnd_7520535 3861649233960838605926195 := by
  unfold tailWord_7520535
  simp only [CollatzResearch.WordTrace]
  refine ⟨274296445809393574966395059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182864297206262383310930039 274296445809393574966395059)
  ·
    refine ⟨411444668714090362449592589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274296445809393574966395059 411444668714090362449592589)
    ·
      refine ⟨154291750767783885918597221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411444668714090362449592589 154291750767783885918597221)
      ·
        refine ⟨28929703268959478609736979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154291750767783885918597221 28929703268959478609736979)
        ·
          refine ⟨43394554903439217914605469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28929703268959478609736979 43394554903439217914605469)
          ·
            refine ⟨16272958088789706717977051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43394554903439217914605469 16272958088789706717977051)
            ·
              refine ⟨24409437133184560076965577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16272958088789706717977051 24409437133184560076965577)
              ·
                refine ⟨18307077849888420057724183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24409437133184560076965577 18307077849888420057724183)
                ·
                  refine ⟨27460616774832630086586275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18307077849888420057724183 27460616774832630086586275)
                  ·
                    refine ⟨41190925162248945129879413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27460616774832630086586275 41190925162248945129879413)
                    ·
                      refine ⟨3861649233960838605926195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41190925162248945129879413 3861649233960838605926195)
                      ·
                        rfl

theorem cell23_7520535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_7520535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520535 prefixEnd_7520535 := by exact prefixLift 7520535
  have htrace : WordTrace (prefixWord ++ tailWord_7520535) baseStart_7520535 baseEnd_7520535 := by
    simpa [prefixWord, tailWord_7520535, baseEnd_7520535] using wordTrace_append hprefix tailTrace_7520535
  have hstable : (prefixWord ++ tailWord_7520535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520535).length < 2 ^ (prefixWord ++ tailWord_7520535).sum := by decide
  have hdescent : baseEnd_7520535 < baseStart_7520535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520545 : List Nat := [1, 2, 3, 2, 1, 1, 5, 1, 1, 2, 4]
def baseStart_7520545 : Nat := 118140960795 + 7520545 * 2 ^ 59
def prefixEnd_7520545 : Nat := 4983230072969 + 3 ^ 40 * 7520545 * 2
def baseEnd_7520545 : Nat := 3861654368767383566801149

theorem tailTrace_7520545 : CollatzResearch.WordTrace tailWord_7520545 prefixEnd_7520545 3861654368767383566801149 := by
  unfold tailWord_7520545
  simp only [CollatzResearch.WordTrace]
  refine ⟨274296810539357346674259089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182864540359571564449506059 274296810539357346674259089)
  ·
    refine ⟨205722607904518010005694317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274296810539357346674259089 205722607904518010005694317)
    ·
      refine ⟨77145977964194253752135369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205722607904518010005694317 77145977964194253752135369)
      ·
        refine ⟨57859483473145690314101527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77145977964194253752135369 57859483473145690314101527)
        ·
          refine ⟨86789225209718535471152291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57859483473145690314101527 86789225209718535471152291)
          ·
            refine ⟨130183837814577803206728437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86789225209718535471152291 130183837814577803206728437)
            ·
              refine ⟨12204734795116669050630791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130183837814577803206728437 12204734795116669050630791)
              ·
                refine ⟨18307102192675003575946187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12204734795116669050630791 18307102192675003575946187)
                ·
                  refine ⟨27460653289012505363919281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18307102192675003575946187 27460653289012505363919281)
                  ·
                    refine ⟨20595489966759379022939461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27460653289012505363919281 20595489966759379022939461)
                    ·
                      refine ⟨3861654368767383566801149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20595489966759379022939461 3861654368767383566801149)
                      ·
                        rfl

theorem cell23_7520545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_7520545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520545 prefixEnd_7520545 := by exact prefixLift 7520545
  have htrace : WordTrace (prefixWord ++ tailWord_7520545) baseStart_7520545 baseEnd_7520545 := by
    simpa [prefixWord, tailWord_7520545, baseEnd_7520545] using wordTrace_append hprefix tailTrace_7520545
  have hstable : (prefixWord ++ tailWord_7520545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520545).length < 2 ^ (prefixWord ++ tailWord_7520545).sum := by decide
  have hdescent : baseEnd_7520545 < baseStart_7520545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520565 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_7520565 : Nat := 118140960795 + 7520565 * 2 ^ 59
def prefixEnd_7520565 : Nat := 4983230072969 + 3 ^ 40 * 7520565 * 2
def baseEnd_7520565 : Nat := 3861664638380473488551057

theorem tailTrace_7520565 : CollatzResearch.WordTrace tailWord_7520565 prefixEnd_7520565 3861664638380473488551057 := by
  unfold tailWord_7520565
  simp only [CollatzResearch.WordTrace]
  refine ⟨274297539999284890089987149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182865026666189926726658099 274297539999284890089987149)
  ·
    refine ⟨102861577499731833783745181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274297539999284890089987149 102861577499731833783745181)
    ·
      refine ⟨38573091562399437668904443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102861577499731833783745181 38573091562399437668904443)
      ·
        refine ⟨57859637343599156503356665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38573091562399437668904443 57859637343599156503356665)
        ·
          refine ⟨43394728007699367377517499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57859637343599156503356665 43394728007699367377517499)
          ·
            refine ⟨65092092011549051066276249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43394728007699367377517499 65092092011549051066276249)
            ·
              refine ⟨48819069008661788299707187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65092092011549051066276249 48819069008661788299707187)
              ·
                refine ⟨73228603512992682449560781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48819069008661788299707187 73228603512992682449560781)
                ·
                  refine ⟨27460726317372255918585293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73228603512992682449560781 27460726317372255918585293)
                  ·
                    refine ⟨10297772369014595969469485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27460726317372255918585293 10297772369014595969469485)
                    ·
                      refine ⟨3861664638380473488551057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10297772369014595969469485 3861664638380473488551057)
                      ·
                        rfl

theorem cell23_7520565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_7520565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520565 prefixEnd_7520565 := by exact prefixLift 7520565
  have htrace : WordTrace (prefixWord ++ tailWord_7520565) baseStart_7520565 baseEnd_7520565 := by
    simpa [prefixWord, tailWord_7520565, baseEnd_7520565] using wordTrace_append hprefix tailTrace_7520565
  have hstable : (prefixWord ++ tailWord_7520565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520565).length < 2 ^ (prefixWord ++ tailWord_7520565).sum := by decide
  have hdescent : baseEnd_7520565 < baseStart_7520565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520626 : List Nat := [3, 2, 1, 2, 1, 4, 3, 1, 1, 3, 2]
def baseStart_7520626 : Nat := 118140960795 + 7520626 * 2 ^ 59
def prefixEnd_7520626 : Nat := 4983230072969 + 3 ^ 40 * 7520626 * 2
def baseEnd_7520626 : Nat := 3861695960700397749888277

theorem tailTrace_7520626 : CollatzResearch.WordTrace tailWord_7520626 prefixEnd_7520626 3861695960700397749888277 := by
  unfold tailWord_7520626
  simp only [CollatzResearch.WordTrace]
  refine ⟨68574941213015974376989433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182866509901375931671971821 68574941213015974376989433)
  ·
    refine ⟨51431205909761980782742075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68574941213015974376989433 51431205909761980782742075)
    ·
      refine ⟨77146808864642971174113113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51431205909761980782742075 77146808864642971174113113)
      ·
        refine ⟨57860106648482228380584835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77146808864642971174113113 57860106648482228380584835)
        ·
          refine ⟨86790159972723342570877253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57860106648482228380584835 86790159972723342570877253)
          ·
            refine ⟨16273154994885626732039485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86790159972723342570877253 16273154994885626732039485)
            ·
              refine ⟨6102433123082110024514807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16273154994885626732039485 6102433123082110024514807)
              ·
                refine ⟨9153649684623165036772211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6102433123082110024514807 9153649684623165036772211)
                ·
                  refine ⟨13730474526934747555158317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9153649684623165036772211 13730474526934747555158317)
                  ·
                    refine ⟨5148927947600530333184369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13730474526934747555158317 5148927947600530333184369)
                    ·
                      refine ⟨3861695960700397749888277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5148927947600530333184369 3861695960700397749888277)
                      ·
                        rfl

theorem cell23_7520626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_7520626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520626 prefixEnd_7520626 := by exact prefixLift 7520626
  have htrace : WordTrace (prefixWord ++ tailWord_7520626) baseStart_7520626 baseEnd_7520626 := by
    simpa [prefixWord, tailWord_7520626, baseEnd_7520626] using wordTrace_append hprefix tailTrace_7520626
  have hstable : (prefixWord ++ tailWord_7520626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520626).length < 2 ^ (prefixWord ++ tailWord_7520626).sum := by decide
  have hdescent : baseEnd_7520626 < baseStart_7520626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520675 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 1, 7]
def baseStart_7520675 : Nat := 118140960795 + 7520675 * 2 ^ 59
def prefixEnd_7520675 : Nat := 4983230072969 + 3 ^ 40 * 7520675 * 2
def baseEnd_7520675 : Nat := 1287240373750822686058517

theorem tailTrace_7520675 : CollatzResearch.WordTrace tailWord_7520675 prefixEnd_7520675 1287240373750822686058517 := by
  unfold tailWord_7520675
  simp only [CollatzResearch.WordTrace]
  refine ⟨274301552028886378876491479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182867701352590919250994319 274301552028886378876491479)
  ·
    refine ⟨411452328043329568314737219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274301552028886378876491479 411452328043329568314737219)
    ·
      refine ⟨617178492064994352472105829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411452328043329568314737219 617178492064994352472105829)
      ·
        refine ⟨115720967262186441088519843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 617178492064994352472105829 115720967262186441088519843)
        ·
          refine ⟨173581450893279661632779765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115720967262186441088519843 173581450893279661632779765)
          ·
            refine ⟨16273261021244968278073103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173581450893279661632779765 16273261021244968278073103)
            ·
              refine ⟨24409891531867452417109655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16273261021244968278073103 24409891531867452417109655)
              ·
                refine ⟨36614837297801178625664483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24409891531867452417109655 36614837297801178625664483)
                ·
                  refine ⟨54922255946701767938496725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36614837297801178625664483 54922255946701767938496725)
                  ·
                    refine ⟨1287240373750822686058517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54922255946701767938496725 1287240373750822686058517)
                    ·
                      rfl

theorem cell23_7520675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 7].length) (baseStart_7520675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520675 prefixEnd_7520675 := by exact prefixLift 7520675
  have htrace : WordTrace (prefixWord ++ tailWord_7520675) baseStart_7520675 baseEnd_7520675 := by
    simpa [prefixWord, tailWord_7520675, baseEnd_7520675] using wordTrace_append hprefix tailTrace_7520675
  have hstable : (prefixWord ++ tailWord_7520675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520675).length < 2 ^ (prefixWord ++ tailWord_7520675).sum := by decide
  have hdescent : baseEnd_7520675 < baseStart_7520675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520679 : List Nat := [1, 1, 6, 1, 1, 3, 2, 3, 5]
def baseStart_7520679 : Nat := 118140960795 + 7520679 * 2 ^ 59
def prefixEnd_7520679 : Nat := 4983230072969 + 3 ^ 40 * 7520679 * 2
def baseEnd_7520679 : Nat := 429080352797231782502837

theorem tailTrace_7520679 : CollatzResearch.WordTrace tailWord_7520679 prefixEnd_7520679 429080352797231782502837 := by
  unfold tailWord_7520679
  simp only [CollatzResearch.WordTrace]
  refine ⟨274301697920871887559637091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182867798613914591706424727 274301697920871887559637091)
  ·
    refine ⟨411452546881307831339455637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274301697920871887559637091 411452546881307831339455637)
    ·
      refine ⟨19286838135061304594036983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 411452546881307831339455637 19286838135061304594036983)
      ·
        refine ⟨28930257202591956891055475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19286838135061304594036983 28930257202591956891055475)
        ·
          refine ⟨43395385803887935336583213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28930257202591956891055475 43395385803887935336583213)
          ·
            refine ⟨16273269676457975751218705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43395385803887935336583213 16273269676457975751218705)
            ·
              refine ⟨12204952257343481813414029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16273269676457975751218705 12204952257343481813414029)
              ·
                refine ⟨4576857096503805680030261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12204952257343481813414029 4576857096503805680030261)
                ·
                  refine ⟨429080352797231782502837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4576857096503805680030261 429080352797231782502837)
                  ·
                    rfl

theorem cell23_7520679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 5].length) (baseStart_7520679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520679 prefixEnd_7520679 := by exact prefixLift 7520679
  have htrace : WordTrace (prefixWord ++ tailWord_7520679) baseStart_7520679 baseEnd_7520679 := by
    simpa [prefixWord, tailWord_7520679, baseEnd_7520679] using wordTrace_append hprefix tailTrace_7520679
  have hstable : (prefixWord ++ tailWord_7520679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520679).length < 2 ^ (prefixWord ++ tailWord_7520679).sum := by decide
  have hdescent : baseEnd_7520679 < baseStart_7520679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520735 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 8]
def baseStart_7520735 : Nat := 118140960795 + 7520735 * 2 ^ 59
def prefixEnd_7520735 : Nat := 4983230072969 + 3 ^ 40 * 7520735 * 2
def baseEnd_7520735 : Nat := 429083547787970869269475

theorem tailTrace_7520735 : CollatzResearch.WordTrace tailWord_7520735 prefixEnd_7520735 429083547787970869269475 := by
  unfold tailWord_7520735
  simp only [CollatzResearch.WordTrace]
  refine ⟨274303740408669009123675659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182869160272446006082450439 274303740408669009123675659)
  ·
    refine ⟨411455610613003513685513489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274303740408669009123675659 411455610613003513685513489)
    ·
      refine ⟨308591707959752635264135117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411455610613003513685513489 308591707959752635264135117)
      ·
        refine ⟨115721890484907238224050669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308591707959752635264135117 115721890484907238224050669)
        ·
          refine ⟨43395708931840214334019001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115721890484907238224050669 43395708931840214334019001)
          ·
            refine ⟨32546781698880160750514251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43395708931840214334019001 32546781698880160750514251)
            ·
              refine ⟨48820172548320241125771377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32546781698880160750514251 48820172548320241125771377)
              ·
                refine ⟨36615129411240180844328533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48820172548320241125771377 36615129411240180844328533)
                ·
                  refine ⟨429083547787970869269475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36615129411240180844328533 429083547787970869269475)
                  ·
                    rfl

theorem cell23_7520735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 8].length) (baseStart_7520735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520735 prefixEnd_7520735 := by exact prefixLift 7520735
  have htrace : WordTrace (prefixWord ++ tailWord_7520735) baseStart_7520735 baseEnd_7520735 := by
    simpa [prefixWord, tailWord_7520735, baseEnd_7520735] using wordTrace_append hprefix tailTrace_7520735
  have hstable : (prefixWord ++ tailWord_7520735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520735).length < 2 ^ (prefixWord ++ tailWord_7520735).sum := by decide
  have hdescent : baseEnd_7520735 < baseStart_7520735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520749 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_7520749 : Nat := 118140960795 + 7520749 * 2 ^ 59
def prefixEnd_7520749 : Nat := 4983230072969 + 3 ^ 40 * 7520749 * 2
def baseEnd_7520749 : Nat := 3861759118820900768650211

theorem tailTrace_7520749 : CollatzResearch.WordTrace tailWord_7520749 prefixEnd_7520749 3861759118820900768650211 := by
  unfold tailWord_7520749
  simp only [CollatzResearch.WordTrace]
  refine ⟨274304251030618289514685301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182869500687078859676456867 274304251030618289514685301)
  ·
    refine ⟨25716023534120464642001747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 274304251030618289514685301 25716023534120464642001747)
    ·
      refine ⟨38574035301180696963002621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25716023534120464642001747 38574035301180696963002621)
      ·
        refine ⟨14465263237942761361125983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38574035301180696963002621 14465263237942761361125983)
        ·
          refine ⟨21697894856914142041688975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14465263237942761361125983 21697894856914142041688975)
          ·
            refine ⟨32546842285371213062533463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21697894856914142041688975 32546842285371213062533463)
            ·
              refine ⟨48820263428056819593800195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32546842285371213062533463 48820263428056819593800195)
              ·
                refine ⟨73230395142085229390700293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48820263428056819593800195 73230395142085229390700293)
                ·
                  refine ⟨13730699089140980510756305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73230395142085229390700293 13730699089140980510756305)
                  ·
                    refine ⟨10298024316855735383067229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13730699089140980510756305 10298024316855735383067229)
                    ·
                      refine ⟨3861759118820900768650211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10298024316855735383067229 3861759118820900768650211)
                      ·
                        rfl

theorem cell23_7520749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_7520749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520749 prefixEnd_7520749 := by exact prefixLift 7520749
  have htrace : WordTrace (prefixWord ++ tailWord_7520749) baseStart_7520749 baseEnd_7520749 := by
    simpa [prefixWord, tailWord_7520749, baseEnd_7520749] using wordTrace_append hprefix tailTrace_7520749
  have hstable : (prefixWord ++ tailWord_7520749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520749).length < 2 ^ (prefixWord ++ tailWord_7520749).sum := by decide
  have hdescent : baseEnd_7520749 < baseStart_7520749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520769 : List Nat := [1, 2, 4, 1, 3, 1, 4, 1, 6]
def baseStart_7520769 : Nat := 118140960795 + 7520769 * 2 ^ 59
def prefixEnd_7520769 : Nat := 4983230072969 + 3 ^ 40 * 7520769 * 2
def baseEnd_7520769 : Nat := 429085487603776743377791

theorem tailTrace_7520769 : CollatzResearch.WordTrace tailWord_7520769 prefixEnd_7520769 429085487603776743377791 := by
  unfold tailWord_7520769
  simp only [CollatzResearch.WordTrace]
  refine ⟨274304980490545832930413361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182869986993697221953608907 274304980490545832930413361)
  ·
    refine ⟨205728735367909374697810021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274304980490545832930413361 205728735367909374697810021)
    ·
      refine ⟨38574137881483007755839379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205728735367909374697810021 38574137881483007755839379)
      ·
        refine ⟨57861206822224511633759069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38574137881483007755839379 57861206822224511633759069)
        ·
          refine ⟨21697952558334191862659651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57861206822224511633759069 21697952558334191862659651)
          ·
            refine ⟨32546928837501287793989477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21697952558334191862659651 32546928837501287793989477)
            ·
              refine ⟨6102549157031491461373027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32546928837501287793989477 6102549157031491461373027)
              ·
                refine ⟨9153823735547237192059541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6102549157031491461373027 9153823735547237192059541)
                ·
                  refine ⟨429085487603776743377791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9153823735547237192059541 429085487603776743377791)
                  ·
                    rfl

theorem cell23_7520769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 6].length) (baseStart_7520769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520769 prefixEnd_7520769 := by exact prefixLift 7520769
  have htrace : WordTrace (prefixWord ++ tailWord_7520769) baseStart_7520769 baseEnd_7520769 := by
    simpa [prefixWord, tailWord_7520769, baseEnd_7520769] using wordTrace_append hprefix tailTrace_7520769
  have hstable : (prefixWord ++ tailWord_7520769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520769).length < 2 ^ (prefixWord ++ tailWord_7520769).sum := by decide
  have hdescent : baseEnd_7520769 < baseStart_7520769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520807 : List Nat := [1, 1, 7, 2, 1, 2, 2, 2, 1, 4]
def baseStart_7520807 : Nat := 118140960795 + 7520807 * 2 ^ 59
def prefixEnd_7520807 : Nat := 4983230072969 + 3 ^ 40 * 7520807 * 2
def baseEnd_7520807 : Nat := 1287262966899620513908315

theorem tailTrace_7520807 : CollatzResearch.WordTrace tailWord_7520807 prefixEnd_7520807 1287262966899620513908315 := by
  unfold tailWord_7520807
  simp only [CollatzResearch.WordTrace]
  refine ⟨274306366464408165420296675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182870910976272110280197783 274306366464408165420296675)
  ·
    refine ⟨411459549696612248130445013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274306366464408165420296675 411459549696612248130445013)
    ·
      refine ⟨9643583196014349565557305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 411459549696612248130445013 9643583196014349565557305)
      ·
        refine ⟨7232687397010762174167979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9643583196014349565557305 7232687397010762174167979)
        ·
          refine ⟨10849031095516143261251969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7232687397010762174167979 10849031095516143261251969)
          ·
            refine ⟨8136773321637107445938977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10849031095516143261251969 8136773321637107445938977)
            ·
              refine ⟨6102579991227830584454233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8136773321637107445938977 6102579991227830584454233)
              ·
                refine ⟨4576934993420872938340675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6102579991227830584454233 4576934993420872938340675)
                ·
                  refine ⟨6865402490131309407511013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4576934993420872938340675 6865402490131309407511013)
                  ·
                    refine ⟨1287262966899620513908315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6865402490131309407511013 1287262966899620513908315)
                    ·
                      rfl

theorem cell23_7520807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_7520807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520807 prefixEnd_7520807 := by exact prefixLift 7520807
  have htrace : WordTrace (prefixWord ++ tailWord_7520807) baseStart_7520807 baseEnd_7520807 := by
    simpa [prefixWord, tailWord_7520807, baseEnd_7520807] using wordTrace_append hprefix tailTrace_7520807
  have hstable : (prefixWord ++ tailWord_7520807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520807).length < 2 ^ (prefixWord ++ tailWord_7520807).sum := by decide
  have hdescent : baseEnd_7520807 < baseStart_7520807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520812 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 4, 4]
def baseStart_7520812 : Nat := 118140960795 + 7520812 * 2 ^ 59
def prefixEnd_7520812 : Nat := 4983230072969 + 3 ^ 40 * 7520812 * 2
def baseEnd_7520812 : Nat := 1287263822700711340720807

theorem tailTrace_7520812 : CollatzResearch.WordTrace tailWord_7520812 prefixEnd_7520812 1287263822700711340720807 := by
  unfold tailWord_7520812
  simp only [CollatzResearch.WordTrace]
  refine ⟨137153274414695025637114345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182871032552926700849485793 137153274414695025637114345)
  ·
    refine ⟨102864955811021269227835759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137153274414695025637114345 102864955811021269227835759)
    ·
      refine ⟨154297433716531903841753639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102864955811021269227835759 154297433716531903841753639)
      ·
        refine ⟨231446150574797855762630459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154297433716531903841753639 231446150574797855762630459)
        ·
          refine ⟨347169225862196783643945689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231446150574797855762630459 347169225862196783643945689)
          ·
            refine ⟨260376919396647587732959267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347169225862196783643945689 260376919396647587732959267)
            ·
              refine ⟨390565379094971381599438901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260376919396647587732959267 390565379094971381599438901)
              ·
                refine ⟨36615504290153567024947397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 390565379094971381599438901 36615504290153567024947397)
                ·
                  refine ⟨6865407054403793817177637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36615504290153567024947397 6865407054403793817177637)
                  ·
                    refine ⟨1287263822700711340720807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6865407054403793817177637 1287263822700711340720807)
                    ·
                      rfl

theorem cell23_7520812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_7520812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520812 prefixEnd_7520812 := by exact prefixLift 7520812
  have htrace : WordTrace (prefixWord ++ tailWord_7520812) baseStart_7520812 baseEnd_7520812 := by
    simpa [prefixWord, tailWord_7520812, baseEnd_7520812] using wordTrace_append hprefix tailTrace_7520812
  have hstable : (prefixWord ++ tailWord_7520812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520812).length < 2 ^ (prefixWord ++ tailWord_7520812).sum := by decide
  have hdescent : baseEnd_7520812 < baseStart_7520812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520829 : List Nat := [1, 4, 1, 3, 2, 2, 2, 1, 1, 6]
def baseStart_7520829 : Nat := 118140960795 + 7520829 * 2 ^ 59
def prefixEnd_7520829 : Nat := 4983230072969 + 3 ^ 40 * 7520829 * 2
def baseEnd_7520829 : Nat := 1287266732424420151883281

theorem tailTrace_7520829 : CollatzResearch.WordTrace tailWord_7520829 prefixEnd_7520829 1287266732424420151883281 := by
  unfold tailWord_7520829
  simp only [CollatzResearch.WordTrace]
  refine ⟨274307168870328463177597541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182871445913552308785065027 274307168870328463177597541)
  ·
    refine ⟨51432594163186586845799539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274307168870328463177597541 51432594163186586845799539)
    ·
      refine ⟨77148891244779880268699309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51432594163186586845799539 77148891244779880268699309)
      ·
        refine ⟨28930834216792455100762241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77148891244779880268699309 28930834216792455100762241)
        ·
          refine ⟨21698125662594341325571681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28930834216792455100762241 21698125662594341325571681)
          ·
            refine ⟨16273594246945755994178761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21698125662594341325571681 16273594246945755994178761)
            ·
              refine ⟨12205195685209316995634071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16273594246945755994178761 12205195685209316995634071)
              ·
                refine ⟨18307793527813975493451107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12205195685209316995634071 18307793527813975493451107)
                ·
                  refine ⟨27461690291720963240176661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18307793527813975493451107 27461690291720963240176661)
                  ·
                    refine ⟨1287266732424420151883281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27461690291720963240176661 1287266732424420151883281)
                    ·
                      rfl

theorem cell23_7520829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_7520829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520829 prefixEnd_7520829 := by exact prefixLift 7520829
  have htrace : WordTrace (prefixWord ++ tailWord_7520829) baseStart_7520829 baseEnd_7520829 := by
    simpa [prefixWord, tailWord_7520829, baseEnd_7520829] using wordTrace_append hprefix tailTrace_7520829
  have hstable : (prefixWord ++ tailWord_7520829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520829).length < 2 ^ (prefixWord ++ tailWord_7520829).sum := by decide
  have hdescent : baseEnd_7520829 < baseStart_7520829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520832 : List Nat := [2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 4]
def baseStart_7520832 : Nat := 118140960795 + 7520832 * 2 ^ 59
def prefixEnd_7520832 : Nat := 4983230072969 + 3 ^ 40 * 7520832 * 2
def baseEnd_7520832 : Nat := 3861801737715223943912329

theorem tailTrace_7520832 : CollatzResearch.WordTrace tailWord_7520832 prefixEnd_7520832 3861801737715223943912329 := by
  unfold tailWord_7520832
  simp only [CollatzResearch.WordTrace]
  refine ⟨137153639144658797344978375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182871518859545063126637833 137153639144658797344978375)
  ·
    refine ⟨205730458716988196017467563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137153639144658797344978375 205730458716988196017467563)
    ·
      refine ⟨308595688075482294026201345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205730458716988196017467563 308595688075482294026201345)
      ·
        refine ⟨231446766056611720519651009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308595688075482294026201345 231446766056611720519651009)
        ·
          refine ⟨173585074542458790389738257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231446766056611720519651009 173585074542458790389738257)
          ·
            refine ⟨130188805906844092792303693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173585074542458790389738257 130188805906844092792303693)
            ·
              refine ⟨48820802215066534797113885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130188805906844092792303693 48820802215066534797113885)
              ·
                refine ⟨18307800830649950548917707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48820802215066534797113885 18307800830649950548917707)
                ·
                  refine ⟨27461701245974925823376561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18307800830649950548917707 27461701245974925823376561)
                  ·
                    refine ⟨20596275934481194367532421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27461701245974925823376561 20596275934481194367532421)
                    ·
                      refine ⟨3861801737715223943912329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20596275934481194367532421 3861801737715223943912329)
                      ·
                        rfl

theorem cell23_7520832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_7520832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520832 prefixEnd_7520832 := by exact prefixLift 7520832
  have htrace : WordTrace (prefixWord ++ tailWord_7520832) baseStart_7520832 baseEnd_7520832 := by
    simpa [prefixWord, tailWord_7520832, baseEnd_7520832] using wordTrace_append hprefix tailTrace_7520832
  have hstable : (prefixWord ++ tailWord_7520832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520832).length < 2 ^ (prefixWord ++ tailWord_7520832).sum := by decide
  have hdescent : baseEnd_7520832 < baseStart_7520832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520835 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 7]
def baseStart_7520835 : Nat := 118140960795 + 7520835 * 2 ^ 59
def prefixEnd_7520835 : Nat := 4983230072969 + 3 ^ 40 * 7520835 * 2
def baseEnd_7520835 : Nat := 3861803278157187432174815

theorem tailTrace_7520835 : CollatzResearch.WordTrace tailWord_7520835 prefixEnd_7520835 3861803278157187432174815 := by
  unfold tailWord_7520835
  simp only [CollatzResearch.WordTrace]
  refine ⟨274307387708306726202315959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182871591805537817468210639 274307387708306726202315959)
  ·
    refine ⟨411461081562460089303473939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274307387708306726202315959 411461081562460089303473939)
    ·
      refine ⟨617191622343690133955210909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411461081562460089303473939 617191622343690133955210909)
      ·
        refine ⟨231446858378883800233204091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 617191622343690133955210909 231446858378883800233204091)
        ·
          refine ⟨347170287568325700349806137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231446858378883800233204091 347170287568325700349806137)
          ·
            refine ⟨260377715676244275262354603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347170287568325700349806137 260377715676244275262354603)
            ·
              refine ⟨390566573514366412893531905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260377715676244275262354603 390566573514366412893531905)
              ·
                refine ⟨292924930135774809670148929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390566573514366412893531905 292924930135774809670148929)
                ·
                  refine ⟨219693697601831107252611697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292924930135774809670148929 219693697601831107252611697)
                  ·
                    refine ⟨164770273201373330439458773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 219693697601831107252611697 164770273201373330439458773)
                    ·
                      refine ⟨3861803278157187432174815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164770273201373330439458773 3861803278157187432174815)
                      ·
                        rfl

theorem cell23_7520835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_7520835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520835 prefixEnd_7520835 := by exact prefixLift 7520835
  have htrace : WordTrace (prefixWord ++ tailWord_7520835) baseStart_7520835 baseEnd_7520835 := by
    simpa [prefixWord, tailWord_7520835, baseEnd_7520835] using wordTrace_append hprefix tailTrace_7520835
  have hstable : (prefixWord ++ tailWord_7520835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520835).length < 2 ^ (prefixWord ++ tailWord_7520835).sum := by decide
  have hdescent : baseEnd_7520835 < baseStart_7520835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520839 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 3]
def baseStart_7520839 : Nat := 118140960795 + 7520839 * 2 ^ 59
def prefixEnd_7520839 : Nat := 4983230072969 + 3 ^ 40 * 7520839 * 2
def baseEnd_7520839 : Nat := 3861805332079805416524797

theorem tailTrace_7520839 : CollatzResearch.WordTrace tailWord_7520839 prefixEnd_7520839 3861805332079805416524797 := by
  unfold tailWord_7520839
  simp only [CollatzResearch.WordTrace]
  refine ⟨274307533600292234885461571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182871689066861489923641047 274307533600292234885461571)
  ·
    refine ⟨411461300400438352328192357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274307533600292234885461571 411461300400438352328192357)
    ·
      refine ⟨77148993825082191061536067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 411461300400438352328192357 77148993825082191061536067)
      ·
        refine ⟨115723490737623286592304101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77148993825082191061536067 115723490737623286592304101)
        ·
          refine ⟨21698154513304366236057019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115723490737623286592304101 21698154513304366236057019)
          ·
            refine ⟨32547231769956549354085529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21698154513304366236057019 32547231769956549354085529)
            ·
              refine ⟨24410423827467412015564147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32547231769956549354085529 24410423827467412015564147)
              ·
                refine ⟨36615635741201118023346221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24410423827467412015564147 36615635741201118023346221)
                ·
                  refine ⟨13730863402950419258754833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36615635741201118023346221 13730863402950419258754833)
                  ·
                    refine ⟨10298147552212814444066125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13730863402950419258754833 10298147552212814444066125)
                    ·
                      refine ⟨3861805332079805416524797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10298147552212814444066125 3861805332079805416524797)
                      ·
                        rfl

theorem cell23_7520839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_7520839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520839 prefixEnd_7520839 := by exact prefixLift 7520839
  have htrace : WordTrace (prefixWord ++ tailWord_7520839) baseStart_7520839 baseEnd_7520839 := by
    simpa [prefixWord, tailWord_7520839, baseEnd_7520839] using wordTrace_append hprefix tailTrace_7520839
  have hstable : (prefixWord ++ tailWord_7520839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520839).length < 2 ^ (prefixWord ++ tailWord_7520839).sum := by decide
  have hdescent : baseEnd_7520839 < baseStart_7520839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520853 : List Nat := [1, 3, 2, 2, 1, 1, 3, 5, 1, 2, 2]
def baseStart_7520853 : Nat := 118140960795 + 7520853 * 2 ^ 59
def prefixEnd_7520853 : Nat := 4983230072969 + 3 ^ 40 * 7520853 * 2
def baseEnd_7520853 : Nat := 3861812520808968361749733

theorem tailTrace_7520853 : CollatzResearch.WordTrace tailWord_7520853 prefixEnd_7520853 3861812520808968361749733 := by
  unfold tailWord_7520853
  simp only [CollatzResearch.WordTrace]
  refine ⟨274308044222241515276471213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182872029481494343517647475 274308044222241515276471213)
  ·
    refine ⟨102865516583340568228676705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274308044222241515276471213 102865516583340568228676705)
    ·
      refine ⟨77149137437505426171507529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102865516583340568228676705 77149137437505426171507529)
      ·
        refine ⟨57861853078129069628630647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77149137437505426171507529 57861853078129069628630647)
        ·
          refine ⟨86792779617193604442945971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57861853078129069628630647 86792779617193604442945971)
          ·
            refine ⟨130189169425790406664418957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86792779617193604442945971 130189169425790406664418957)
            ·
              refine ⟨48820938534671402499157109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130189169425790406664418957 48820938534671402499157109)
              ·
                refine ⟨4576962987625443984295979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48820938534671402499157109 4576962987625443984295979)
                ·
                  refine ⟨6865444481438165976443969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4576962987625443984295979 6865444481438165976443969)
                  ·
                    refine ⟨5149083361078624482332977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6865444481438165976443969 5149083361078624482332977)
                    ·
                      refine ⟨3861812520808968361749733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5149083361078624482332977 3861812520808968361749733)
                      ·
                        rfl

theorem cell23_7520853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_7520853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520853 prefixEnd_7520853 := by exact prefixLift 7520853
  have htrace : WordTrace (prefixWord ++ tailWord_7520853) baseStart_7520853 baseEnd_7520853 := by
    simpa [prefixWord, tailWord_7520853, baseEnd_7520853] using wordTrace_append hprefix tailTrace_7520853
  have hstable : (prefixWord ++ tailWord_7520853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520853).length < 2 ^ (prefixWord ++ tailWord_7520853).sum := by decide
  have hdescent : baseEnd_7520853 < baseStart_7520853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520856 : List Nat := [2, 1, 2, 2, 1, 2, 6, 1, 1, 2, 3]
def baseStart_7520856 : Nat := 118140960795 + 7520856 * 2 ^ 59
def prefixEnd_7520856 : Nat := 4983230072969 + 3 ^ 40 * 7520856 * 2
def baseEnd_7520856 : Nat := 3861814061250931850012219

theorem tailTrace_7520856 : CollatzResearch.WordTrace tailWord_7520856 prefixEnd_7520856 3861814061250931850012219 := by
  unfold tailWord_7520856
  simp only [CollatzResearch.WordTrace]
  refine ⟨137154076820615323394415211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182872102427487097859220281 137154076820615323394415211)
  ·
    refine ⟨205731115230922985091622817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137154076820615323394415211 205731115230922985091622817)
    ·
      refine ⟨154298336423192238818717113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205731115230922985091622817 154298336423192238818717113)
      ·
        refine ⟨115723752317394179114037835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154298336423192238818717113 115723752317394179114037835)
        ·
          refine ⟨173585628476091268671056753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115723752317394179114037835 173585628476091268671056753)
          ·
            refine ⟨130189221357068451503292565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173585628476091268671056753 130189221357068451503292565)
            ·
              refine ⟨6102619751112583664216839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130189221357068451503292565 6102619751112583664216839)
              ·
                refine ⟨9153929626668875496325259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6102619751112583664216839 9153929626668875496325259)
                ·
                  refine ⟨13730894440003313244487889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9153929626668875496325259 13730894440003313244487889)
                  ·
                    refine ⟨10298170830002484933365917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13730894440003313244487889 10298170830002484933365917)
                    ·
                      refine ⟨3861814061250931850012219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10298170830002484933365917 3861814061250931850012219)
                      ·
                        rfl

theorem cell23_7520856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_7520856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520856 prefixEnd_7520856 := by exact prefixLift 7520856
  have htrace : WordTrace (prefixWord ++ tailWord_7520856) baseStart_7520856 baseEnd_7520856 := by
    simpa [prefixWord, tailWord_7520856, baseEnd_7520856] using wordTrace_append hprefix tailTrace_7520856
  have hstable : (prefixWord ++ tailWord_7520856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520856).length < 2 ^ (prefixWord ++ tailWord_7520856).sum := by decide
  have hdescent : baseEnd_7520856 < baseStart_7520856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520879 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 5, 3, 2]
def baseStart_7520879 : Nat := 118140960795 + 7520879 * 2 ^ 59
def prefixEnd_7520879 : Nat := 4983230072969 + 3 ^ 40 * 7520879 * 2
def baseEnd_7520879 : Nat := 3861825871305985260024613

theorem tailTrace_7520879 : CollatzResearch.WordTrace tailWord_7520879 prefixEnd_7520879 3861825871305985260024613 := by
  unfold tailWord_7520879
  simp only [CollatzResearch.WordTrace]
  refine ⟨274308992520147321716917691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182872661680098214477945127 274308992520147321716917691)
  ·
    refine ⟨411463488780220982575376537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274308992520147321716917691 411463488780220982575376537)
    ·
      refine ⟨308597616585165736931532403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411463488780220982575376537 308597616585165736931532403)
      ·
        refine ⟨462896424877748605397298605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308597616585165736931532403 462896424877748605397298605)
        ·
          refine ⟨173586159329155727023986977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462896424877748605397298605 173586159329155727023986977)
          ·
            refine ⟨130189619496866795267990233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173586159329155727023986977 130189619496866795267990233)
            ·
              refine ⟨97642214622650096450992675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130189619496866795267990233 97642214622650096450992675)
              ·
                refine ⟨146463321933975144676489013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97642214622650096450992675 146463321933975144676489013)
                ·
                  refine ⟨13730936431310169813420845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146463321933975144676489013 13730936431310169813420845)
                  ·
                    refine ⟨5149101161741313680032817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13730936431310169813420845 5149101161741313680032817)
                    ·
                      refine ⟨3861825871305985260024613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5149101161741313680032817 3861825871305985260024613)
                      ·
                        rfl

theorem cell23_7520879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 3, 2].length) (baseStart_7520879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520879 prefixEnd_7520879 := by exact prefixLift 7520879
  have htrace : WordTrace (prefixWord ++ tailWord_7520879) baseStart_7520879 baseEnd_7520879 := by
    simpa [prefixWord, tailWord_7520879, baseEnd_7520879] using wordTrace_append hprefix tailTrace_7520879
  have hstable : (prefixWord ++ tailWord_7520879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520879).length < 2 ^ (prefixWord ++ tailWord_7520879).sum := by decide
  have hdescent : baseEnd_7520879 < baseStart_7520879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520892 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_7520892 : Nat := 118140960795 + 7520892 * 2 ^ 59
def prefixEnd_7520892 : Nat := 4983230072969 + 3 ^ 40 * 7520892 * 2
def baseEnd_7520892 : Nat := 3861832546554493709162053

theorem tailTrace_7520892 : CollatzResearch.WordTrace tailWord_7520892 prefixEnd_7520892 3861832546554493709162053 := by
  unfold tailWord_7520892
  simp only [CollatzResearch.WordTrace]
  refine ⟨137154733334550112468570465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182872977779400149958093953 137154733334550112468570465)
  ·
    refine ⟨102866050000912584351427849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137154733334550112468570465 102866050000912584351427849)
    ·
      refine ⟨77149537500684438263570887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102866050000912584351427849 77149537500684438263570887)
      ·
        refine ⟨115724306251026657395356331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77149537500684438263570887 115724306251026657395356331)
        ·
          refine ⟨173586459376539986093034497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115724306251026657395356331 173586459376539986093034497)
          ·
            refine ⟨130189844532404989569775873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173586459376539986093034497 130189844532404989569775873)
            ·
              refine ⟨97642383399303742177331905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130189844532404989569775873 97642383399303742177331905)
              ·
                refine ⟨73231787549477806632998929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97642383399303742177331905 73231787549477806632998929)
                ·
                  refine ⟨54923840662108354974749197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73231787549477806632998929 54923840662108354974749197)
                  ·
                    refine ⟨20596440248290633115530949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54923840662108354974749197 20596440248290633115530949)
                    ·
                      refine ⟨3861832546554493709162053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20596440248290633115530949 3861832546554493709162053)
                      ·
                        rfl

theorem cell23_7520892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_7520892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520892 prefixEnd_7520892 := by exact prefixLift 7520892
  have htrace : WordTrace (prefixWord ++ tailWord_7520892) baseStart_7520892 baseEnd_7520892 := by
    simpa [prefixWord, tailWord_7520892, baseEnd_7520892] using wordTrace_append hprefix tailTrace_7520892
  have hstable : (prefixWord ++ tailWord_7520892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520892).length < 2 ^ (prefixWord ++ tailWord_7520892).sum := by decide
  have hdescent : baseEnd_7520892 < baseStart_7520892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520896 : List Nat := [2, 1, 1, 2, 1, 5, 1, 4, 1, 3, 2]
def baseStart_7520896 : Nat := 118140960795 + 7520896 * 2 ^ 59
def prefixEnd_7520896 : Nat := 4983230072969 + 3 ^ 40 * 7520896 * 2
def baseEnd_7520896 : Nat := 3861834600477111693512035

theorem tailTrace_7520896 : CollatzResearch.WordTrace tailWord_7520896 prefixEnd_7520896 3861834600477111693512035 := by
  unfold tailWord_7520896
  simp only [CollatzResearch.WordTrace]
  refine ⟨137154806280542866810143271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182873075040723822413524361 137154806280542866810143271)
  ·
    refine ⟨205732209420814300215214907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137154806280542866810143271 205732209420814300215214907)
    ·
      refine ⟨308598314131221450322822361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205732209420814300215214907 308598314131221450322822361)
      ·
        refine ⟨231448735598416087742116771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308598314131221450322822361 231448735598416087742116771)
        ·
          refine ⟨347173103397624131613175157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231448735598416087742116771 347173103397624131613175157)
          ·
            refine ⟨32547478443527262338735171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 347173103397624131613175157 32547478443527262338735171)
            ·
              refine ⟨48821217665290893508102757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32547478443527262338735171 48821217665290893508102757)
              ·
                refine ⟨9153978312242042532769267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48821217665290893508102757 9153978312242042532769267)
                ·
                  refine ⟨13730967468363063799153901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9153978312242042532769267 13730967468363063799153901)
                  ·
                    refine ⟨5149112800636148924682713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13730967468363063799153901 5149112800636148924682713)
                    ·
                      refine ⟨3861834600477111693512035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5149112800636148924682713 3861834600477111693512035)
                      ·
                        rfl

theorem cell23_7520896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 1, 3, 2].length) (baseStart_7520896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520896 prefixEnd_7520896 := by exact prefixLift 7520896
  have htrace : WordTrace (prefixWord ++ tailWord_7520896) baseStart_7520896 baseEnd_7520896 := by
    simpa [prefixWord, tailWord_7520896, baseEnd_7520896] using wordTrace_append hprefix tailTrace_7520896
  have hstable : (prefixWord ++ tailWord_7520896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520896).length < 2 ^ (prefixWord ++ tailWord_7520896).sum := by decide
  have hdescent : baseEnd_7520896 < baseStart_7520896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520912 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 3]
def baseStart_7520912 : Nat := 118140960795 + 7520912 * 2 ^ 59
def prefixEnd_7520912 : Nat := 4983230072969 + 3 ^ 40 * 7520912 * 2
def baseEnd_7520912 : Nat := 3861842816167583630911961

theorem tailTrace_7520912 : CollatzResearch.WordTrace tailWord_7520912 prefixEnd_7520912 3861842816167583630911961 := by
  unfold tailWord_7520912
  simp only [CollatzResearch.WordTrace]
  refine ⟨137155098064513884176434495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182873464086018512235245993 137155098064513884176434495)
  ·
    refine ⟨205732647096770826264651743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137155098064513884176434495 205732647096770826264651743)
    ·
      refine ⟨308598970645156239396977615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205732647096770826264651743 308598970645156239396977615)
      ·
        refine ⟨462898455967734359095466423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308598970645156239396977615 462898455967734359095466423)
        ·
          refine ⟨694347683951601538643199635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462898455967734359095466423 694347683951601538643199635)
          ·
            refine ⟨1041521525927402307964799453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694347683951601538643199635 1041521525927402307964799453)
            ·
              refine ⟨390570572222775865486799795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1041521525927402307964799453 390570572222775865486799795)
              ·
                refine ⟨585855858334163798230199693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390570572222775865486799795 585855858334163798230199693)
                ·
                  refine ⟨219695946875311424336324885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585855858334163798230199693 219695946875311424336324885)
                  ·
                    refine ⟨10298247509780223015765229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 219695946875311424336324885 10298247509780223015765229)
                    ·
                      refine ⟨3861842816167583630911961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10298247509780223015765229 3861842816167583630911961)
                      ·
                        rfl

theorem cell23_7520912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 3].length) (baseStart_7520912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520912 prefixEnd_7520912 := by exact prefixLift 7520912
  have htrace : WordTrace (prefixWord ++ tailWord_7520912) baseStart_7520912 baseEnd_7520912 := by
    simpa [prefixWord, tailWord_7520912, baseEnd_7520912] using wordTrace_append hprefix tailTrace_7520912
  have hstable : (prefixWord ++ tailWord_7520912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520912).length < 2 ^ (prefixWord ++ tailWord_7520912).sum := by decide
  have hdescent : baseEnd_7520912 < baseStart_7520912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520943 : List Nat := [1, 1, 2, 1, 2, 6, 1, 3, 2, 2, 2]
def baseStart_7520943 : Nat := 118140960795 + 7520943 * 2 ^ 59
def prefixEnd_7520943 : Nat := 4983230072969 + 3 ^ 40 * 7520943 * 2
def baseEnd_7520943 : Nat := 3861858734067873009624319

theorem tailTrace_7520943 : CollatzResearch.WordTrace tailWord_7520943 prefixEnd_7520943 3861858734067873009624319 := by
  unfold tailWord_7520943
  simp only [CollatzResearch.WordTrace]
  refine ⟨274311326791915460647247483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182874217861276973764831655 274311326791915460647247483)
  ·
    refine ⟨411466990187873190970871225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274311326791915460647247483 411466990187873190970871225)
    ·
      refine ⟨308600242640904893228153419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411466990187873190970871225 308600242640904893228153419)
      ·
        refine ⟨462900363961357339842230129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308600242640904893228153419 462900363961357339842230129)
        ·
          refine ⟨347175272971018004881672597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462900363961357339842230129 347175272971018004881672597)
          ·
            refine ⟨16273840920516468978828403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 347175272971018004881672597 16273840920516468978828403)
            ·
              refine ⟨24410761380774703468242605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16273840920516468978828403 24410761380774703468242605)
              ·
                refine ⟨9154035517790513800590977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24410761380774703468242605 9154035517790513800590977)
                ·
                  refine ⟨6865526638342885350443233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9154035517790513800590977 6865526638342885350443233)
                  ·
                    refine ⟨5149144978757164012832425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6865526638342885350443233 5149144978757164012832425)
                    ·
                      refine ⟨3861858734067873009624319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5149144978757164012832425 3861858734067873009624319)
                      ·
                        rfl

theorem cell23_7520943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 2, 2].length) (baseStart_7520943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520943 prefixEnd_7520943 := by exact prefixLift 7520943
  have htrace : WordTrace (prefixWord ++ tailWord_7520943) baseStart_7520943 baseEnd_7520943 := by
    simpa [prefixWord, tailWord_7520943, baseEnd_7520943] using wordTrace_append hprefix tailTrace_7520943
  have hstable : (prefixWord ++ tailWord_7520943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520943).length < 2 ^ (prefixWord ++ tailWord_7520943).sum := by decide
  have hdescent : baseEnd_7520943 < baseStart_7520943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520969 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 6, 5, 2]
def baseStart_7520969 : Nat := 118140960795 + 7520969 * 2 ^ 59
def prefixEnd_7520969 : Nat := 4983230072969 + 3 ^ 40 * 7520969 * 2
def baseEnd_7520969 : Nat := 3861872084564889907899199

theorem tailTrace_7520969 : CollatzResearch.WordTrace tailWord_7520969 prefixEnd_7520969 3861872084564889907899199 := by
  unfold tailWord_7520969
  simp only [CollatzResearch.WordTrace]
  refine ⟨274312275089821267087693961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182874850059880844725129307 274312275089821267087693961)
  ·
    refine ⟨205734206317365950315770471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274312275089821267087693961 205734206317365950315770471)
    ·
      refine ⟨308601309476048925473655707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205734206317365950315770471 308601309476048925473655707)
      ·
        refine ⟨462901964214073388210483561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308601309476048925473655707 462901964214073388210483561)
        ·
          refine ⟨347176473160555041157862671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462901964214073388210483561 347176473160555041157862671)
          ·
            refine ⟨520764709740832561736794007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347176473160555041157862671 520764709740832561736794007)
            ·
              refine ⟨781147064611248842605191011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520764709740832561736794007 781147064611248842605191011)
              ·
                refine ⟨1171720596916873263907786517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 781147064611248842605191011 1171720596916873263907786517)
                ·
                  refine ⟨54924402980478434245677493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1171720596916873263907786517 54924402980478434245677493)
                  ·
                    refine ⟨5149162779419853210532265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54924402980478434245677493 5149162779419853210532265)
                    ·
                      refine ⟨3861872084564889907899199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5149162779419853210532265 3861872084564889907899199)
                      ·
                        rfl

theorem cell23_7520969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 5, 2].length) (baseStart_7520969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520969 prefixEnd_7520969 := by exact prefixLift 7520969
  have htrace : WordTrace (prefixWord ++ tailWord_7520969) baseStart_7520969 baseEnd_7520969 := by
    simpa [prefixWord, tailWord_7520969, baseEnd_7520969] using wordTrace_append hprefix tailTrace_7520969
  have hstable : (prefixWord ++ tailWord_7520969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520969).length < 2 ^ (prefixWord ++ tailWord_7520969).sum := by decide
  have hdescent : baseEnd_7520969 < baseStart_7520969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520983 : List Nat := [1, 1, 3, 2, 1, 6, 2, 2, 5]
def baseStart_7520983 : Nat := 118140960795 + 7520983 * 2 ^ 59
def prefixEnd_7520983 : Nat := 4983230072969 + 3 ^ 40 * 7520983 * 2
def baseEnd_7520983 : Nat := 429097697032672539236015

theorem tailTrace_7520983 : CollatzResearch.WordTrace tailWord_7520983 prefixEnd_7520983 429097697032672539236015 := by
  unfold tailWord_7520983
  simp only [CollatzResearch.WordTrace]
  refine ⟨274312785711770547478703603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182875190474513698319135735 274312785711770547478703603)
  ·
    refine ⟨411469178567655821218055405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274312785711770547478703603 411469178567655821218055405)
    ·
      refine ⟨154300941962870932956770777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411469178567655821218055405 154300941962870932956770777)
      ·
        refine ⟨115725706472153199717578083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154300941962870932956770777 115725706472153199717578083)
        ·
          refine ⟨173588559708229799576367125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115725706472153199717578083 173588559708229799576367125)
          ·
            refine ⟨8136963736323271855142209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 173588559708229799576367125 8136963736323271855142209)
            ·
              refine ⟨6102722802242453891356657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8136963736323271855142209 6102722802242453891356657)
              ·
                refine ⟨4577042101681840418517493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6102722802242453891356657 4577042101681840418517493)
                ·
                  refine ⟨429097697032672539236015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4577042101681840418517493 429097697032672539236015)
                  ·
                    rfl

theorem cell23_7520983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 5].length) (baseStart_7520983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520983 prefixEnd_7520983 := by exact prefixLift 7520983
  have htrace : WordTrace (prefixWord ++ tailWord_7520983) baseStart_7520983 baseEnd_7520983 := by
    simpa [prefixWord, tailWord_7520983, baseEnd_7520983] using wordTrace_append hprefix tailTrace_7520983
  have hstable : (prefixWord ++ tailWord_7520983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520983).length < 2 ^ (prefixWord ++ tailWord_7520983).sum := by decide
  have hdescent : baseEnd_7520983 < baseStart_7520983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7520992 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 2, 8]
def baseStart_7520992 : Nat := 118140960795 + 7520992 * 2 ^ 59
def prefixEnd_7520992 : Nat := 4983230072969 + 3 ^ 40 * 7520992 * 2
def baseEnd_7520992 : Nat := 1287294631539981105970531

theorem tailTrace_7520992 : CollatzResearch.WordTrace tailWord_7520992 prefixEnd_7520992 1287294631539981105970531 := by
  unfold tailWord_7520992
  simp only [CollatzResearch.WordTrace]
  refine ⟨137156556984368971007890615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182875409312491961343854153 137156556984368971007890615)
  ·
    refine ⟨205734835476553456511835923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137156556984368971007890615 205734835476553456511835923)
    ·
      refine ⟨308602253214830184767753885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205734835476553456511835923 308602253214830184767753885)
      ·
        refine ⟨115725844955561319287907707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308602253214830184767753885 115725844955561319287907707)
        ·
          refine ⟨173588767433341978931861561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115725844955561319287907707 173588767433341978931861561)
          ·
            refine ⟨130191575575006484198896171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173588767433341978931861561 130191575575006484198896171)
            ·
              refine ⟨195287363362509726298344257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130191575575006484198896171 195287363362509726298344257)
              ·
                refine ⟨146465522521882294723758193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195287363362509726298344257 146465522521882294723758193)
                ·
                  refine ⟨109849141891411721042818645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146465522521882294723758193 109849141891411721042818645)
                  ·
                    refine ⟨1287294631539981105970531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109849141891411721042818645 1287294631539981105970531)
                    ·
                      rfl

theorem cell23_7520992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 8].length) (baseStart_7520992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7520992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7520992 prefixEnd_7520992 := by exact prefixLift 7520992
  have htrace : WordTrace (prefixWord ++ tailWord_7520992) baseStart_7520992 baseEnd_7520992 := by
    simpa [prefixWord, tailWord_7520992, baseEnd_7520992] using wordTrace_append hprefix tailTrace_7520992
  have hstable : (prefixWord ++ tailWord_7520992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7520992).length < 2 ^ (prefixWord ++ tailWord_7520992).sum := by decide
  have hdescent : baseEnd_7520992 < baseStart_7520992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7520992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521094 : List Nat := [6, 1, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_7521094 : Nat := 118140960795 + 7521094 * 2 ^ 59
def prefixEnd_7521094 : Nat := 4983230072969 + 3 ^ 40 * 7521094 * 2
def baseEnd_7521094 : Nat := 1287312089882233972945375

theorem tailTrace_7521094 : CollatzResearch.WordTrace tailWord_7521094 prefixEnd_7521094 1287312089882233972945375 := by
  unfold tailWord_7521094
  simp only [CollatzResearch.WordTrace]
  refine ⟨8572401069199012919874823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 182877889476245608957329557 8572401069199012919874823)
  ·
    refine ⟨12858601603798519379812235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8572401069199012919874823 12858601603798519379812235)
    ·
      refine ⟨19287902405697779069718353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12858601603798519379812235 19287902405697779069718353)
      ·
        refine ⟨14465926804273334302288765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19287902405697779069718353 14465926804273334302288765)
        ·
          refine ⟨5424722551602500363358287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14465926804273334302288765 5424722551602500363358287)
          ·
            refine ⟨8137083827403750545037431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5424722551602500363358287 8137083827403750545037431)
            ·
              refine ⟨12205625741105625817556147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8137083827403750545037431 12205625741105625817556147)
              ·
                refine ⟨18308438611658438726334221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12205625741105625817556147 18308438611658438726334221)
                ·
                  refine ⟨6865664479371914522375333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18308438611658438726334221 6865664479371914522375333)
                  ·
                    refine ⟨1287312089882233972945375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6865664479371914522375333 1287312089882233972945375)
                    ·
                      rfl

theorem cell23_7521094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_7521094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521094 prefixEnd_7521094 := by exact prefixLift 7521094
  have htrace : WordTrace (prefixWord ++ tailWord_7521094) baseStart_7521094 baseEnd_7521094 := by
    simpa [prefixWord, tailWord_7521094, baseEnd_7521094] using wordTrace_append hprefix tailTrace_7521094
  have hstable : (prefixWord ++ tailWord_7521094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521094).length < 2 ^ (prefixWord ++ tailWord_7521094).sum := by decide
  have hdescent : baseEnd_7521094 < baseStart_7521094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521100 : List Nat := [2, 2, 1, 3, 3, 3, 1, 1, 3, 1, 3]
def baseStart_7521100 : Nat := 118140960795 + 7521100 * 2 ^ 59
def prefixEnd_7521100 : Nat := 4983230072969 + 3 ^ 40 * 7521100 * 2
def baseEnd_7521100 : Nat := 3861939350530628895361097

theorem tailTrace_7521100 : CollatzResearch.WordTrace tailWord_7521100 prefixEnd_7521100 3861939350530628895361097 := by
  unfold tailWord_7521100
  simp only [CollatzResearch.WordTrace]
  refine ⟨137158526526173338230356377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182878035368231117640475169 137158526526173338230356377)
  ·
    refine ⟨102868894894630003672767283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137158526526173338230356377 102868894894630003672767283)
    ·
      refine ⟨154303342341945005509150925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102868894894630003672767283 154303342341945005509150925)
      ·
        refine ⟨57863753378229377065931597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154303342341945005509150925 57863753378229377065931597)
        ·
          refine ⟨21698907516836016399724349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57863753378229377065931597 21698907516836016399724349)
          ·
            refine ⟨8137090318813506149896631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21698907516836016399724349 8137090318813506149896631)
            ·
              refine ⟨12205635478220259224844947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8137090318813506149896631 12205635478220259224844947)
              ·
                refine ⟨18308453217330388837267421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12205635478220259224844947 18308453217330388837267421)
                ·
                  refine ⟨6865669956498895813975283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18308453217330388837267421 6865669956498895813975283)
                  ·
                    refine ⟨10298504934748343720962925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6865669956498895813975283 10298504934748343720962925)
                    ·
                      refine ⟨3861939350530628895361097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10298504934748343720962925 3861939350530628895361097)
                      ·
                        rfl

theorem cell23_7521100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_7521100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521100 prefixEnd_7521100 := by exact prefixLift 7521100
  have htrace : WordTrace (prefixWord ++ tailWord_7521100) baseStart_7521100 baseEnd_7521100 := by
    simpa [prefixWord, tailWord_7521100, baseEnd_7521100] using wordTrace_append hprefix tailTrace_7521100
  have hstable : (prefixWord ++ tailWord_7521100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521100).length < 2 ^ (prefixWord ++ tailWord_7521100).sum := by decide
  have hdescent : baseEnd_7521100 < baseStart_7521100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521106 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_7521106 : Nat := 118140960795 + 7521106 * 2 ^ 59
def prefixEnd_7521106 : Nat := 4983230072969 + 3 ^ 40 * 7521106 * 2
def baseEnd_7521106 : Nat := 3861942431414555871886069

theorem tailTrace_7521106 : CollatzResearch.WordTrace tailWord_7521106 prefixEnd_7521106 3861942431414555871886069 := by
  unfold tailWord_7521106
  simp only [CollatzResearch.WordTrace]
  refine ⟨68579317972581234871357793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182878181260216626323620781 68579317972581234871357793)
  ·
    refine ⟨51434488479435926153518345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68579317972581234871357793 51434488479435926153518345)
    ·
      refine ⟨38575866359576944615138759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51434488479435926153518345 38575866359576944615138759)
      ·
        refine ⟨57863799539365416922708139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38575866359576944615138759 57863799539365416922708139)
        ·
          refine ⟨86795699309048125384062209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57863799539365416922708139 86795699309048125384062209)
          ·
            refine ⟨65096774481786094038046657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86795699309048125384062209 65096774481786094038046657)
            ·
              refine ⟨48822580861339570528534993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65096774481786094038046657 48822580861339570528534993)
              ·
                refine ⟨36616935646004677896401245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48822580861339570528534993 36616935646004677896401245)
                ·
                  refine ⟨13731350867251754211150467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36616935646004677896401245 13731350867251754211150467)
                  ·
                    refine ⟨20597026300877631316725701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13731350867251754211150467 20597026300877631316725701)
                    ·
                      refine ⟨3861942431414555871886069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20597026300877631316725701 3861942431414555871886069)
                      ·
                        rfl

theorem cell23_7521106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_7521106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521106 prefixEnd_7521106 := by exact prefixLift 7521106
  have htrace : WordTrace (prefixWord ++ tailWord_7521106) baseStart_7521106 baseEnd_7521106 := by
    simpa [prefixWord, tailWord_7521106, baseEnd_7521106] using wordTrace_append hprefix tailTrace_7521106
  have hstable : (prefixWord ++ tailWord_7521106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521106).length < 2 ^ (prefixWord ++ tailWord_7521106).sum := by decide
  have hdescent : baseEnd_7521106 < baseStart_7521106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521119 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 6]
def baseStart_7521119 : Nat := 118140960795 + 7521119 * 2 ^ 59
def prefixEnd_7521119 : Nat := 4983230072969 + 3 ^ 40 * 7521119 * 2
def baseEnd_7521119 : Nat := 3861949106663064321023509

theorem tailTrace_7521119 : CollatzResearch.WordTrace tailWord_7521119 prefixEnd_7521119 3861949106663064321023509 := by
  unfold tailWord_7521119
  simp only [CollatzResearch.WordTrace]
  refine ⟨274317746039277842705654411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182878497359518561803769607 274317746039277842705654411)
  ·
    refine ⟨411476619058916764058481617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274317746039277842705654411 411476619058916764058481617)
    ·
      refine ⟨308607464294187573043861213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411476619058916764058481617 308607464294187573043861213)
      ·
        refine ⟨115727799110320339891447955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308607464294187573043861213 115727799110320339891447955)
        ·
          refine ⟨173591698665480509837171933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115727799110320339891447955 173591698665480509837171933)
          ·
            refine ⟨65096886999555191188939475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173591698665480509837171933 65096886999555191188939475)
            ·
              refine ⟨97645330499332786783409213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65096886999555191188939475 97645330499332786783409213)
              ·
                refine ⟨36616998937249795043778455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97645330499332786783409213 36616998937249795043778455)
                ·
                  refine ⟨54925498405874692565667683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36616998937249795043778455 54925498405874692565667683)
                  ·
                    refine ⟨82388247608812038848501525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54925498405874692565667683 82388247608812038848501525)
                    ·
                      refine ⟨3861949106663064321023509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82388247608812038848501525 3861949106663064321023509)
                      ·
                        rfl

theorem cell23_7521119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_7521119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521119 prefixEnd_7521119 := by exact prefixLift 7521119
  have htrace : WordTrace (prefixWord ++ tailWord_7521119) baseStart_7521119 baseEnd_7521119 := by
    simpa [prefixWord, tailWord_7521119, baseEnd_7521119] using wordTrace_append hprefix tailTrace_7521119
  have hstable : (prefixWord ++ tailWord_7521119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521119).length < 2 ^ (prefixWord ++ tailWord_7521119).sum := by decide
  have hdescent : baseEnd_7521119 < baseStart_7521119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521123 : List Nat := [1, 1, 1, 5, 3, 1, 3, 2, 1, 1, 4]
def baseStart_7521123 : Nat := 118140960795 + 7521123 * 2 ^ 59
def prefixEnd_7521123 : Nat := 4983230072969 + 3 ^ 40 * 7521123 * 2
def baseEnd_7521123 : Nat := 3861951160585682305373491

theorem tailTrace_7521123 : CollatzResearch.WordTrace tailWord_7521123 prefixEnd_7521123 3861951160585682305373491 := by
  unfold tailWord_7521123
  simp only [CollatzResearch.WordTrace]
  refine ⟨274317891931263351388800023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182878594620842234259200015 274317891931263351388800023)
  ·
    refine ⟨411476837896895027083200035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274317891931263351388800023 411476837896895027083200035)
    ·
      refine ⟨617215256845342540624800053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411476837896895027083200035 617215256845342540624800053)
      ·
        refine ⟨57863930329250863183575005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 617215256845342540624800053 57863930329250863183575005)
        ·
          refine ⟨21698973873469073693840627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57863930329250863183575005 21698973873469073693840627)
          ·
            refine ⟨32548460810203610540760941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21698973873469073693840627 32548460810203610540760941)
            ·
              refine ⟨12205672803826353952785353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32548460810203610540760941 12205672803826353952785353)
              ·
                refine ⟨9154254602869765464589015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12205672803826353952785353 9154254602869765464589015)
                ·
                  refine ⟨13731381904304648196883523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9154254602869765464589015 13731381904304648196883523)
                  ·
                    refine ⟨20597072856456972295325285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13731381904304648196883523 20597072856456972295325285)
                    ·
                      refine ⟨3861951160585682305373491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20597072856456972295325285 3861951160585682305373491)
                      ·
                        rfl

theorem cell23_7521123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_7521123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521123 prefixEnd_7521123 := by exact prefixLift 7521123
  have htrace : WordTrace (prefixWord ++ tailWord_7521123) baseStart_7521123 baseEnd_7521123 := by
    simpa [prefixWord, tailWord_7521123, baseEnd_7521123] using wordTrace_append hprefix tailTrace_7521123
  have hstable : (prefixWord ++ tailWord_7521123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521123).length < 2 ^ (prefixWord ++ tailWord_7521123).sum := by decide
  have hdescent : baseEnd_7521123 < baseStart_7521123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521156 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_7521156 : Nat := 118140960795 + 7521156 * 2 ^ 59
def prefixEnd_7521156 : Nat := 4983230072969 + 3 ^ 40 * 7521156 * 2
def baseEnd_7521156 : Nat := 3861968105447280676260839

theorem tailTrace_7521156 : CollatzResearch.WordTrace tailWord_7521156 prefixEnd_7521156 3861968105447280676260839 := by
  unfold tailWord_7521156
  simp only [CollatzResearch.WordTrace]
  refine ⟨137159547770071899012375661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182879397026762532016500881 137159547770071899012375661)
  ·
    refine ⟨51434830413776962129640873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137159547770071899012375661 51434830413776962129640873)
    ·
      refine ⟨38576122810332721597230655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51434830413776962129640873 38576122810332721597230655)
      ·
        refine ⟨57864184215499082395845983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38576122810332721597230655 57864184215499082395845983)
        ·
          refine ⟨86796276323248623593768975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57864184215499082395845983 86796276323248623593768975)
          ·
            refine ⟨130194414484872935390653463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86796276323248623593768975 130194414484872935390653463)
            ·
              refine ⟨195291621727309403085980195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130194414484872935390653463 195291621727309403085980195)
              ·
                refine ⟨292937432590964104628970293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195291621727309403085980195 292937432590964104628970293)
                ·
                  refine ⟨27462884305402884808965965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 292937432590964104628970293 27462884305402884808965965)
                  ·
                    refine ⟨10298581614526081803362237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27462884305402884808965965 10298581614526081803362237)
                    ·
                      refine ⟨3861968105447280676260839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10298581614526081803362237 3861968105447280676260839)
                      ·
                        rfl

theorem cell23_7521156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_7521156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521156 prefixEnd_7521156 := by exact prefixLift 7521156
  have htrace : WordTrace (prefixWord ++ tailWord_7521156) baseStart_7521156 baseEnd_7521156 := by
    simpa [prefixWord, tailWord_7521156, baseEnd_7521156] using wordTrace_append hprefix tailTrace_7521156
  have hstable : (prefixWord ++ tailWord_7521156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521156).length < 2 ^ (prefixWord ++ tailWord_7521156).sum := by decide
  have hdescent : baseEnd_7521156 < baseStart_7521156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521157 : List Nat := [1, 3, 1, 1, 3, 4, 1, 4, 1, 2, 2]
def baseStart_7521157 : Nat := 118140960795 + 7521157 * 2 ^ 59
def prefixEnd_7521157 : Nat := 4983230072969 + 3 ^ 40 * 7521157 * 2
def baseEnd_7521157 : Nat := 3861968618927935172348335

theorem tailTrace_7521157 : CollatzResearch.WordTrace tailWord_7521157 prefixEnd_7521157 3861968618927935172348335 := by
  unfold tailWord_7521157
  simp only [CollatzResearch.WordTrace]
  refine ⟨274319132013140175195537725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182879421342093450130358483 274319132013140175195537725)
  ·
    refine ⟨102869674504927565698326647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274319132013140175195537725 102869674504927565698326647)
    ·
      refine ⟨154304511757391348547489971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102869674504927565698326647 154304511757391348547489971)
      ·
        refine ⟨231456767636087022821234957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154304511757391348547489971 231456767636087022821234957)
        ·
          refine ⟨86796287863532633557963109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231456767636087022821234957 86796287863532633557963109)
          ·
            refine ⟨16274303974412368792118083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86796287863532633557963109 16274303974412368792118083)
            ·
              refine ⟨24411455961618553188177125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16274303974412368792118083 24411455961618553188177125)
              ·
                refine ⟨4577147992803478722783211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24411455961618553188177125 4577147992803478722783211)
                ·
                  refine ⟨6865721989205218084174817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577147992803478722783211 6865721989205218084174817)
                  ·
                    refine ⟨5149291491903913563131113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6865721989205218084174817 5149291491903913563131113)
                    ·
                      refine ⟨3861968618927935172348335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5149291491903913563131113 3861968618927935172348335)
                      ·
                        rfl

theorem cell23_7521157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 1, 2, 2].length) (baseStart_7521157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521157 prefixEnd_7521157 := by exact prefixLift 7521157
  have htrace : WordTrace (prefixWord ++ tailWord_7521157) baseStart_7521157 baseEnd_7521157 := by
    simpa [prefixWord, tailWord_7521157, baseEnd_7521157] using wordTrace_append hprefix tailTrace_7521157
  have hstable : (prefixWord ++ tailWord_7521157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521157).length < 2 ^ (prefixWord ++ tailWord_7521157).sum := by decide
  have hdescent : baseEnd_7521157 < baseStart_7521157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521169 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 5]
def baseStart_7521169 : Nat := 118140960795 + 7521169 * 2 ^ 59
def prefixEnd_7521169 : Nat := 4983230072969 + 3 ^ 40 * 7521169 * 2
def baseEnd_7521169 : Nat := 3861974780695789125398279

theorem tailTrace_7521169 : CollatzResearch.WordTrace tailWord_7521169 prefixEnd_7521169 3861974780695789125398279 := by
  unfold tailWord_7521169
  simp only [CollatzResearch.WordTrace]
  refine ⟨274319569689096701244974561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182879713126064467496649707 274319569689096701244974561)
  ·
    refine ⟨205739677266822525933730921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274319569689096701244974561 205739677266822525933730921)
    ·
      refine ⟨154304757950116894450298191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205739677266822525933730921 154304757950116894450298191)
      ·
        refine ⟨231457136925175341675447287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154304757950116894450298191 231457136925175341675447287)
        ·
          refine ⟨347185705387763012513170931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231457136925175341675447287 347185705387763012513170931)
          ·
            refine ⟨520778558081644518769756397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347185705387763012513170931 520778558081644518769756397)
            ·
              refine ⟨195291959280616694538658649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 520778558081644518769756397 195291959280616694538658649)
              ·
                refine ⟨146468969460462520903993987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195291959280616694538658649 146468969460462520903993987)
                ·
                  refine ⟨219703454190693781355990981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146468969460462520903993987 219703454190693781355990981)
                  ·
                    refine ⟨41194397660755084004248309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 219703454190693781355990981 41194397660755084004248309)
                    ·
                      refine ⟨3861974780695789125398279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41194397660755084004248309 3861974780695789125398279)
                      ·
                        rfl

theorem cell23_7521169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_7521169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521169 prefixEnd_7521169 := by exact prefixLift 7521169
  have htrace : WordTrace (prefixWord ++ tailWord_7521169) baseStart_7521169 baseEnd_7521169 := by
    simpa [prefixWord, tailWord_7521169, baseEnd_7521169] using wordTrace_append hprefix tailTrace_7521169
  have hstable : (prefixWord ++ tailWord_7521169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521169).length < 2 ^ (prefixWord ++ tailWord_7521169).sum := by decide
  have hdescent : baseEnd_7521169 < baseStart_7521169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521170 : List Nat := [3, 2, 3, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_7521170 : Nat := 118140960795 + 7521170 * 2 ^ 59
def prefixEnd_7521170 : Nat := 4983230072969 + 3 ^ 40 * 7521170 * 2
def baseEnd_7521170 : Nat := 3861975294176443621485775

theorem tailTrace_7521170 : CollatzResearch.WordTrace tailWord_7521170 prefixEnd_7521170 3861975294176443621485775 := by
  unfold tailWord_7521170
  simp only [CollatzResearch.WordTrace]
  refine ⟨68579901540523269603940241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182879737441395385610507309 68579901540523269603940241)
  ·
    refine ⟨51434926155392452202955181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68579901540523269603940241 51434926155392452202955181)
    ·
      refine ⟨19288097308272169576108193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51434926155392452202955181 19288097308272169576108193)
      ·
        refine ⟨14466072981204127182081145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19288097308272169576108193 14466072981204127182081145)
        ·
          refine ⟨10849554735903095386560859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14466072981204127182081145 10849554735903095386560859)
          ·
            refine ⟨16274332103854643079841289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10849554735903095386560859 16274332103854643079841289)
            ·
              refine ⟨12205749077890982309880967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16274332103854643079841289 12205749077890982309880967)
              ·
                refine ⟨18308623616836473464821451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12205749077890982309880967 18308623616836473464821451)
                ·
                  refine ⟨27462935425254710197232177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18308623616836473464821451 27462935425254710197232177)
                  ·
                    refine ⟨20597201568941032647924133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27462935425254710197232177 20597201568941032647924133)
                    ·
                      refine ⟨3861975294176443621485775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20597201568941032647924133 3861975294176443621485775)
                      ·
                        rfl

theorem cell23_7521170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_7521170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521170 prefixEnd_7521170 := by exact prefixLift 7521170
  have htrace : WordTrace (prefixWord ++ tailWord_7521170) baseStart_7521170 baseEnd_7521170 := by
    simpa [prefixWord, tailWord_7521170, baseEnd_7521170] using wordTrace_append hprefix tailTrace_7521170
  have hstable : (prefixWord ++ tailWord_7521170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521170).length < 2 ^ (prefixWord ++ tailWord_7521170).sum := by decide
  have hdescent : baseEnd_7521170 < baseStart_7521170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521173 : List Nat := [1, 3, 2, 1, 1, 5, 2, 1, 1, 3, 3]
def baseStart_7521173 : Nat := 118140960795 + 7521173 * 2 ^ 59
def prefixEnd_7521173 : Nat := 4983230072969 + 3 ^ 40 * 7521173 * 2
def baseEnd_7521173 : Nat := 3861976834618407109748261

theorem tailTrace_7521173 : CollatzResearch.WordTrace tailWord_7521173 prefixEnd_7521173 3861976834618407109748261 := by
  unfold tailWord_7521173
  simp only [CollatzResearch.WordTrace]
  refine ⟨274319715581082209928120173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182879810387388139952080115 274319715581082209928120173)
  ·
    refine ⟨102869893342905828723045065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274319715581082209928120173 102869893342905828723045065)
    ·
      refine ⟨77152420007179371542283799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102869893342905828723045065 77152420007179371542283799)
      ·
        refine ⟨115728630010769057313425699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77152420007179371542283799 115728630010769057313425699)
        ·
          refine ⟨173592945016153585970138549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115728630010769057313425699 173592945016153585970138549)
          ·
            refine ⟨16274338595264398684700489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173592945016153585970138549 16274338595264398684700489)
            ·
              refine ⟨12205753946448299013525367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16274338595264398684700489 12205753946448299013525367)
              ·
                refine ⟨18308630919672448520288051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12205753946448299013525367 18308630919672448520288051)
                ·
                  refine ⟨27462946379508672780432077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18308630919672448520288051 27462946379508672780432077)
                  ·
                    refine ⟨10298604892315752292662029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27462946379508672780432077 10298604892315752292662029)
                    ·
                      refine ⟨3861976834618407109748261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10298604892315752292662029 3861976834618407109748261)
                      ·
                        rfl

theorem cell23_7521173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_7521173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521173 prefixEnd_7521173 := by exact prefixLift 7521173
  have htrace : WordTrace (prefixWord ++ tailWord_7521173) baseStart_7521173 baseEnd_7521173 := by
    simpa [prefixWord, tailWord_7521173, baseEnd_7521173] using wordTrace_append hprefix tailTrace_7521173
  have hstable : (prefixWord ++ tailWord_7521173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521173).length < 2 ^ (prefixWord ++ tailWord_7521173).sum := by decide
  have hdescent : baseEnd_7521173 < baseStart_7521173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521174 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_7521174 : Nat := 118140960795 + 7521174 * 2 ^ 59
def prefixEnd_7521174 : Nat := 4983230072969 + 3 ^ 40 * 7521174 * 2
def baseEnd_7521174 : Nat := 3861977348099061605835757

theorem tailTrace_7521174 : CollatzResearch.WordTrace tailWord_7521174 prefixEnd_7521174 3861977348099061605835757 := by
  unfold tailWord_7521174
  simp only [CollatzResearch.WordTrace]
  refine ⟨17144984503379911693681661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182879834702719058065937717 17144984503379911693681661)
  ·
    refine ⟨6429369188767466885130623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17144984503379911693681661 6429369188767466885130623)
    ·
      refine ⟨9644053783151200327695935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6429369188767466885130623 9644053783151200327695935)
      ·
        refine ⟨14466080674726800491543903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9644053783151200327695935 14466080674726800491543903)
        ·
          refine ⟨21699121012090200737315855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14466080674726800491543903 21699121012090200737315855)
          ·
            refine ⟨32548681518135301105973783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21699121012090200737315855 32548681518135301105973783)
            ·
              refine ⟨48823022277202951658960675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32548681518135301105973783 48823022277202951658960675)
              ·
                refine ⟨73234533415804427488441013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48823022277202951658960675 73234533415804427488441013)
                ·
                  refine ⟨6865737507731665077041345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73234533415804427488441013 6865737507731665077041345)
                  ·
                    refine ⟨5149303130798748807781009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6865737507731665077041345 5149303130798748807781009)
                    ·
                      refine ⟨3861977348099061605835757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5149303130798748807781009 3861977348099061605835757)
                      ·
                        rfl

theorem cell23_7521174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_7521174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521174 prefixEnd_7521174 := by exact prefixLift 7521174
  have htrace : WordTrace (prefixWord ++ tailWord_7521174) baseStart_7521174 baseEnd_7521174 := by
    simpa [prefixWord, tailWord_7521174, baseEnd_7521174] using wordTrace_append hprefix tailTrace_7521174
  have hstable : (prefixWord ++ tailWord_7521174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521174).length < 2 ^ (prefixWord ++ tailWord_7521174).sum := by decide
  have hdescent : baseEnd_7521174 < baseStart_7521174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521219 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 11]
def baseStart_7521219 : Nat := 118140960795 + 7521219 * 2 ^ 59
def prefixEnd_7521219 : Nat := 4983230072969 + 3 ^ 40 * 7521219 * 2
def baseEnd_7521219 : Nat := 429111161636501547752561

theorem tailTrace_7521219 : CollatzResearch.WordTrace tailWord_7521219 prefixEnd_7521219 429111161636501547752561 := by
  unfold tailWord_7521219
  simp only [CollatzResearch.WordTrace]
  refine ⟨274321393338915559784294711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182880928892610373189529807 274321393338915559784294711)
  ·
    refine ⟨411482090008373339676442067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274321393338915559784294711 411482090008373339676442067)
    ·
      refine ⟨617223135012560009514663101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411482090008373339676442067 617223135012560009514663101)
      ·
        refine ⟨231458675629710003567998663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 617223135012560009514663101 231458675629710003567998663)
        ·
          refine ⟨347188013444565005351997995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231458675629710003567998663 347188013444565005351997995)
          ·
            refine ⟨520782020166847508027996993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347188013444565005351997995 520782020166847508027996993)
            ·
              refine ⟨390586515125135631020997745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520782020166847508027996993 390586515125135631020997745)
              ·
                refine ⟨292939886343851723265748309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390586515125135631020997745 292939886343851723265748309)
                ·
                  refine ⟨429111161636501547752561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 292939886343851723265748309 429111161636501547752561)
                  ·
                    rfl

theorem cell23_7521219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 11].length) (baseStart_7521219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521219 prefixEnd_7521219 := by exact prefixLift 7521219
  have htrace : WordTrace (prefixWord ++ tailWord_7521219) baseStart_7521219 baseEnd_7521219 := by
    simpa [prefixWord, tailWord_7521219, baseEnd_7521219] using wordTrace_append hprefix tailTrace_7521219
  have hstable : (prefixWord ++ tailWord_7521219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521219).length < 2 ^ (prefixWord ++ tailWord_7521219).sum := by decide
  have hdescent : baseEnd_7521219 < baseStart_7521219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521230 : List Nat := [4, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2]
def baseStart_7521230 : Nat := 118140960795 + 7521230 * 2 ^ 59
def prefixEnd_7521230 : Nat := 4983230072969 + 3 ^ 40 * 7521230 * 2
def baseEnd_7521230 : Nat := 3862006103015713386735499

theorem tailTrace_7521230 : CollatzResearch.WordTrace tailWord_7521230 prefixEnd_7521230 3862006103015713386735499 := by
  unfold tailWord_7521230
  simp only [CollatzResearch.WordTrace]
  refine ⟨34290224317734463582868143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182881196361250472441963429 34290224317734463582868143)
  ·
    refine ⟨51435336476601695374302215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34290224317734463582868143 51435336476601695374302215)
    ·
      refine ⟨77153004714902543061453323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51435336476601695374302215 77153004714902543061453323)
      ·
        refine ⟨115729507072353814592179985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77153004714902543061453323 115729507072353814592179985)
        ·
          refine ⟨86797130304265360944134989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115729507072353814592179985 86797130304265360944134989)
          ·
            refine ⟨32548923864099510354050621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86797130304265360944134989 32548923864099510354050621)
            ·
              refine ⟨12205846449037316382768983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32548923864099510354050621 12205846449037316382768983)
              ·
                refine ⟨18308769673555974574153475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12205846449037316382768983 18308769673555974574153475)
                ·
                  refine ⟨27463154510333961861230213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18308769673555974574153475 27463154510333961861230213)
                  ·
                    refine ⟨5149341470687617848980665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27463154510333961861230213 5149341470687617848980665)
                    ·
                      refine ⟨3862006103015713386735499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5149341470687617848980665 3862006103015713386735499)
                      ·
                        rfl

theorem cell23_7521230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_7521230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521230 prefixEnd_7521230 := by exact prefixLift 7521230
  have htrace : WordTrace (prefixWord ++ tailWord_7521230) baseStart_7521230 baseEnd_7521230 := by
    simpa [prefixWord, tailWord_7521230, baseEnd_7521230] using wordTrace_append hprefix tailTrace_7521230
  have hstable : (prefixWord ++ tailWord_7521230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521230).length < 2 ^ (prefixWord ++ tailWord_7521230).sum := by decide
  have hdescent : baseEnd_7521230 < baseStart_7521230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521250 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_7521250 : Nat := 118140960795 + 7521250 * 2 ^ 59
def prefixEnd_7521250 : Nat := 4983230072969 + 3 ^ 40 * 7521250 * 2
def baseEnd_7521250 : Nat := 3862016372628803308485407

theorem tailTrace_7521250 : CollatzResearch.WordTrace tailWord_7521250 prefixEnd_7521250 3862016372628803308485407 := by
  unfold tailWord_7521250
  simp only [CollatzResearch.WordTrace]
  refine ⟨68580631000450813019668301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182881682667868834719115469 68580631000450813019668301)
  ·
    refine ⟨25717736625169054882375613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68580631000450813019668301 25717736625169054882375613)
    ·
      refine ⟨9644151234438395580890855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25717736625169054882375613 9644151234438395580890855)
      ·
        refine ⟨14466226851657593371336283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9644151234438395580890855 14466226851657593371336283)
        ·
          refine ⟨21699340277486390057004425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14466226851657593371336283 21699340277486390057004425)
          ·
            refine ⟨16274505208114792542753319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21699340277486390057004425 16274505208114792542753319)
            ·
              refine ⟨24411757812172188814129979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16274505208114792542753319 24411757812172188814129979)
              ·
                refine ⟨36617636718258283221194969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24411757812172188814129979 36617636718258283221194969)
                ·
                  refine ⟨27463227538693712415896227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36617636718258283221194969 27463227538693712415896227)
                  ·
                    refine ⟨41194841308040568623844341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27463227538693712415896227 41194841308040568623844341)
                    ·
                      refine ⟨3862016372628803308485407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41194841308040568623844341 3862016372628803308485407)
                      ·
                        rfl

theorem cell23_7521250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_7521250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521250 prefixEnd_7521250 := by exact prefixLift 7521250
  have htrace : WordTrace (prefixWord ++ tailWord_7521250) baseStart_7521250 baseEnd_7521250 := by
    simpa [prefixWord, tailWord_7521250, baseEnd_7521250] using wordTrace_append hprefix tailTrace_7521250
  have hstable : (prefixWord ++ tailWord_7521250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521250).length < 2 ^ (prefixWord ++ tailWord_7521250).sum := by decide
  have hdescent : baseEnd_7521250 < baseStart_7521250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521270 : List Nat := [5, 1, 1, 1, 3, 3, 1, 1, 7]
def baseStart_7521270 : Nat := 118140960795 + 7521270 * 2 ^ 59
def prefixEnd_7521270 : Nat := 4983230072969 + 3 ^ 40 * 7521270 * 2
def baseEnd_7521270 : Nat := 429114071360210358915035

theorem tailTrace_7521270 : CollatzResearch.WordTrace tailWord_7521270 prefixEnd_7521270 429114071360210358915035 := by
  unfold tailWord_7521270
  simp only [CollatzResearch.WordTrace]
  refine ⟨17145203341358174718400079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182882168974487196996267509 17145203341358174718400079)
  ·
    refine ⟨25717805012037262077600119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17145203341358174718400079 25717805012037262077600119)
    ·
      refine ⟨38576707518055893116400179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25717805012037262077600119 38576707518055893116400179)
      ·
        refine ⟨57865061277083839674600269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38576707518055893116400179 57865061277083839674600269)
        ·
          refine ⟨21699397978906439877975101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57865061277083839674600269 21699397978906439877975101)
          ·
            refine ⟨8137274242089914954240663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21699397978906439877975101 8137274242089914954240663)
            ·
              refine ⟨12205911363134872431360995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8137274242089914954240663 12205911363134872431360995)
              ·
                refine ⟨18308867044702308647041493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12205911363134872431360995 18308867044702308647041493)
                ·
                  refine ⟨429114071360210358915035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18308867044702308647041493 429114071360210358915035)
                  ·
                    rfl

theorem cell23_7521270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_7521270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521270 prefixEnd_7521270 := by exact prefixLift 7521270
  have htrace : WordTrace (prefixWord ++ tailWord_7521270) baseStart_7521270 baseEnd_7521270 := by
    simpa [prefixWord, tailWord_7521270, baseEnd_7521270] using wordTrace_append hprefix tailTrace_7521270
  have hstable : (prefixWord ++ tailWord_7521270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521270).length < 2 ^ (prefixWord ++ tailWord_7521270).sum := by decide
  have hdescent : baseEnd_7521270 < baseStart_7521270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521273 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 2, 5, 2]
def baseStart_7521273 : Nat := 118140960795 + 7521273 * 2 ^ 59
def prefixEnd_7521273 : Nat := 4983230072969 + 3 ^ 40 * 7521273 * 2
def baseEnd_7521273 : Nat := 3862028182683856718497801

theorem tailTrace_7521273 : CollatzResearch.WordTrace tailWord_7521273 prefixEnd_7521273 3862028182683856718497801 := by
  unfold tailWord_7521273
  simp only [CollatzResearch.WordTrace]
  refine ⟨274323362880719927006760473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182882241920479951337840315 274323362880719927006760473)
  ·
    refine ⟨205742522160539945255070355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274323362880719927006760473 205742522160539945255070355)
    ·
      refine ⟨308613783240809917882605533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205742522160539945255070355 308613783240809917882605533)
      ·
        refine ⟨115730168715303719205977075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308613783240809917882605533 115730168715303719205977075)
        ·
          refine ⟨173595253072955578808965613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115730168715303719205977075 173595253072955578808965613)
          ·
            refine ⟨65098219902358342053362105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173595253072955578808965613 65098219902358342053362105)
            ·
              refine ⟨48823664926768756540021579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65098219902358342053362105 48823664926768756540021579)
              ·
                refine ⟨73235497390153134810032369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48823664926768756540021579 73235497390153134810032369)
                ·
                  refine ⟨54926623042614851107524277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73235497390153134810032369 54926623042614851107524277)
                  ·
                    refine ⟨5149370910245142291330401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54926623042614851107524277 5149370910245142291330401)
                    ·
                      refine ⟨3862028182683856718497801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5149370910245142291330401 3862028182683856718497801)
                      ·
                        rfl

theorem cell23_7521273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_7521273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521273 prefixEnd_7521273 := by exact prefixLift 7521273
  have htrace : WordTrace (prefixWord ++ tailWord_7521273) baseStart_7521273 baseEnd_7521273 := by
    simpa [prefixWord, tailWord_7521273, baseEnd_7521273] using wordTrace_append hprefix tailTrace_7521273
  have hstable : (prefixWord ++ tailWord_7521273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521273).length < 2 ^ (prefixWord ++ tailWord_7521273).sum := by decide
  have hdescent : baseEnd_7521273 < baseStart_7521273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521276 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_7521276 : Nat := 118140960795 + 7521276 * 2 ^ 59
def prefixEnd_7521276 : Nat := 4983230072969 + 3 ^ 40 * 7521276 * 2
def baseEnd_7521276 : Nat := 3862029723125820206760287

theorem tailTrace_7521276 : CollatzResearch.WordTrace tailWord_7521276 prefixEnd_7521276 3862029723125820206760287 := by
  unfold tailWord_7521276
  simp only [CollatzResearch.WordTrace]
  refine ⟨137161736149854529259559841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182882314866472705679413121 137161736149854529259559841)
  ·
    refine ⟨102871302112390896944669881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137161736149854529259559841 102871302112390896944669881)
    ·
      refine ⟨77153476584293172708502411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102871302112390896944669881 77153476584293172708502411)
      ·
        refine ⟨115730214876439759062753617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77153476584293172708502411 115730214876439759062753617)
        ·
          refine ⟨86797661157329819297065213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115730214876439759062753617 86797661157329819297065213)
          ·
            refine ⟨32549122933998682236399455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86797661157329819297065213 32549122933998682236399455)
            ·
              refine ⟨48823684400998023354599183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32549122933998682236399455 48823684400998023354599183)
              ·
                refine ⟨73235526601497035031898775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48823684400998023354599183 73235526601497035031898775)
                ·
                  refine ⟨109853289902245552547848163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73235526601497035031898775 109853289902245552547848163)
                  ·
                    refine ⟨164779934853368328821772245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109853289902245552547848163 164779934853368328821772245)
                    ·
                      refine ⟨3862029723125820206760287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164779934853368328821772245 3862029723125820206760287)
                      ·
                        rfl

theorem cell23_7521276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_7521276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521276 prefixEnd_7521276 := by exact prefixLift 7521276
  have htrace : WordTrace (prefixWord ++ tailWord_7521276) baseStart_7521276 baseEnd_7521276 := by
    simpa [prefixWord, tailWord_7521276, baseEnd_7521276] using wordTrace_append hprefix tailTrace_7521276
  have hstable : (prefixWord ++ tailWord_7521276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521276).length < 2 ^ (prefixWord ++ tailWord_7521276).sum := by decide
  have hdescent : baseEnd_7521276 < baseStart_7521276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521323 : List Nat := [1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 3]
def baseStart_7521323 : Nat := 118140960795 + 7521323 * 2 ^ 59
def prefixEnd_7521323 : Nat := 4983230072969 + 3 ^ 40 * 7521323 * 2
def baseEnd_7521323 : Nat := 3862053856716581522872571

theorem tailTrace_7521323 : CollatzResearch.WordTrace tailWord_7521323 prefixEnd_7521323 3862053856716581522872571 := by
  unfold tailWord_7521323
  simp only [CollatzResearch.WordTrace]
  refine ⟨274325186530538785546080623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182883457687025857030720415 274325186530538785546080623)
  ·
    refine ⟨411487779795808178319120935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274325186530538785546080623 411487779795808178319120935)
    ·
      refine ⟨617231669693712267478681403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411487779795808178319120935 617231669693712267478681403)
      ·
        refine ⟨925847504540568401218022105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617231669693712267478681403 925847504540568401218022105)
        ·
          refine ⟨694385628405426300913516579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 925847504540568401218022105 694385628405426300913516579)
          ·
            refine ⟨1041578442608139451370274869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694385628405426300913516579 1041578442608139451370274869)
            ·
              refine ⟨97647978994513073565963269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1041578442608139451370274869 97647978994513073565963269)
              ·
                refine ⟨18308996061471201293618113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97647978994513073565963269 18308996061471201293618113)
                ·
                  refine ⟨13731747046103400970213585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18308996061471201293618113 13731747046103400970213585)
                  ·
                    refine ⟨10298810284577550727660189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13731747046103400970213585 10298810284577550727660189)
                    ·
                      refine ⟨3862053856716581522872571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10298810284577550727660189 3862053856716581522872571)
                      ·
                        rfl

theorem cell23_7521323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 3].length) (baseStart_7521323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521323 prefixEnd_7521323 := by exact prefixLift 7521323
  have htrace : WordTrace (prefixWord ++ tailWord_7521323) baseStart_7521323 baseEnd_7521323 := by
    simpa [prefixWord, tailWord_7521323, baseEnd_7521323] using wordTrace_append hprefix tailTrace_7521323
  have hstable : (prefixWord ++ tailWord_7521323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521323).length < 2 ^ (prefixWord ++ tailWord_7521323).sum := by decide
  have hdescent : baseEnd_7521323 < baseStart_7521323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521357 : List Nat := [1, 6, 1, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_7521357 : Nat := 118140960795 + 7521357 * 2 ^ 59
def prefixEnd_7521357 : Nat := 4983230072969 + 3 ^ 40 * 7521357 * 2
def baseEnd_7521357 : Nat := 3862071315058834389847415

theorem tailTrace_7521357 : CollatzResearch.WordTrace tailWord_7521357 prefixEnd_7521357 3862071315058834389847415 := by
  unfold tailWord_7521357
  simp only [CollatzResearch.WordTrace]
  refine ⟨274326426612415609352818325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182884284408277072901878883 274326426612415609352818325)
  ·
    refine ⟨12859051247456981688413359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 274326426612415609352818325 12859051247456981688413359)
    ·
      refine ⟨19288576871185472532620039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12859051247456981688413359 19288576871185472532620039)
      ·
        refine ⟨28932865306778208798930059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19288576871185472532620039 28932865306778208798930059)
        ·
          refine ⟨43399297960167313198395089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28932865306778208798930059 43399297960167313198395089)
          ·
            refine ⟨32549473470125484898796317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43399297960167313198395089 32549473470125484898796317)
            ·
              refine ⟨12206052551297056837048619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32549473470125484898796317 12206052551297056837048619)
              ·
                refine ⟨18309078826945585255572929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12206052551297056837048619 18309078826945585255572929)
                ·
                  refine ⟨13731809120209188941679697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18309078826945585255572929 13731809120209188941679697)
                  ·
                    refine ⟨10298856840156891706259773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13731809120209188941679697 10298856840156891706259773)
                    ·
                      refine ⟨3862071315058834389847415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10298856840156891706259773 3862071315058834389847415)
                      ·
                        rfl

theorem cell23_7521357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_7521357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521357 prefixEnd_7521357 := by exact prefixLift 7521357
  have htrace : WordTrace (prefixWord ++ tailWord_7521357) baseStart_7521357 baseEnd_7521357 := by
    simpa [prefixWord, tailWord_7521357, baseEnd_7521357] using wordTrace_append hprefix tailTrace_7521357
  have hstable : (prefixWord ++ tailWord_7521357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521357).length < 2 ^ (prefixWord ++ tailWord_7521357).sum := by decide
  have hdescent : baseEnd_7521357 < baseStart_7521357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521380 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 4, 3, 2]
def baseStart_7521380 : Nat := 118140960795 + 7521380 * 2 ^ 59
def prefixEnd_7521380 : Nat := 4983230072969 + 3 ^ 40 * 7521380 * 2
def baseEnd_7521380 : Nat := 3862083125113887799859809

theorem tailTrace_7521380 : CollatzResearch.WordTrace tailWord_7521380 prefixEnd_7521380 3862083125113887799859809 := by
  unfold tailWord_7521380
  simp only [CollatzResearch.WordTrace]
  refine ⟨137163632745666142140452797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182884843660888189520603729 137163632745666142140452797)
  ·
    refine ⟨51436362279624803302669799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137163632745666142140452797 51436362279624803302669799)
    ·
      refine ⟨77154543419437204954004699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51436362279624803302669799 77154543419437204954004699)
      ·
        refine ⟨115731815129155807431007049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77154543419437204954004699 115731815129155807431007049)
        ·
          refine ⟨86798861346866855573255287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115731815129155807431007049 86798861346866855573255287)
          ·
            refine ⟨130198292020300283359882931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86798861346866855573255287 130198292020300283359882931)
            ·
              refine ⟨195297438030450425039824397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130198292020300283359882931 195297438030450425039824397)
              ·
                refine ⟨73236539261418909389934149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195297438030450425039824397 73236539261418909389934149)
                ·
                  refine ⟨13731851111516045510612653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73236539261418909389934149 13731851111516045510612653)
                  ·
                    refine ⟨5149444166818517066479745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13731851111516045510612653 5149444166818517066479745)
                    ·
                      refine ⟨3862083125113887799859809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5149444166818517066479745 3862083125113887799859809)
                      ·
                        rfl

theorem cell23_7521380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_7521380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521380 prefixEnd_7521380 := by exact prefixLift 7521380
  have htrace : WordTrace (prefixWord ++ tailWord_7521380) baseStart_7521380 baseEnd_7521380 := by
    simpa [prefixWord, tailWord_7521380, baseEnd_7521380] using wordTrace_append hprefix tailTrace_7521380
  have hstable : (prefixWord ++ tailWord_7521380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521380).length < 2 ^ (prefixWord ++ tailWord_7521380).sum := by decide
  have hdescent : baseEnd_7521380 < baseStart_7521380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521393 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 3, 1, 4]
def baseStart_7521393 : Nat := 118140960795 + 7521393 * 2 ^ 59
def prefixEnd_7521393 : Nat := 4983230072969 + 3 ^ 40 * 7521393 * 2
def baseEnd_7521393 : Nat := 3862089800362396248997249

theorem tailTrace_7521393 : CollatzResearch.WordTrace tailWord_7521393 prefixEnd_7521393 3862089800362396248997249 := by
  unfold tailWord_7521393
  simp only [CollatzResearch.WordTrace]
  refine ⟨274327739640285187501128833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182885159760190125000752555 274327739640285187501128833)
  ·
    refine ⟨205745804730213890625846625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274327739640285187501128833 205745804730213890625846625)
    ·
      refine ⟨154309353547660417969384969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205745804730213890625846625 154309353547660417969384969)
      ·
        refine ⟨115732015160745313477038727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154309353547660417969384969 115732015160745313477038727)
        ·
          refine ⟨173598022741117970215558091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115732015160745313477038727 173598022741117970215558091)
          ·
            refine ⟨260397034111676955323337137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173598022741117970215558091 260397034111676955323337137)
            ·
              refine ⟨195297775583757716492502853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260397034111676955323337137 195297775583757716492502853)
              ·
                refine ⟨36618332921954571842344285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195297775583757716492502853 36618332921954571842344285)
                ·
                  refine ⟨13731874845732964440879107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36618332921954571842344285 13731874845732964440879107)
                  ·
                    refine ⟨20597812268599446661318661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13731874845732964440879107 20597812268599446661318661)
                    ·
                      refine ⟨3862089800362396248997249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20597812268599446661318661 3862089800362396248997249)
                      ·
                        rfl

theorem cell23_7521393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_7521393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521393 prefixEnd_7521393 := by exact prefixLift 7521393
  have htrace : WordTrace (prefixWord ++ tailWord_7521393) baseStart_7521393 baseEnd_7521393 := by
    simpa [prefixWord, tailWord_7521393, baseEnd_7521393] using wordTrace_append hprefix tailTrace_7521393
  have hstable : (prefixWord ++ tailWord_7521393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521393).length < 2 ^ (prefixWord ++ tailWord_7521393).sum := by decide
  have hdescent : baseEnd_7521393 < baseStart_7521393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521438 : List Nat := [4, 3, 1, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_7521438 : Nat := 118140960795 + 7521438 * 2 ^ 59
def prefixEnd_7521438 : Nat := 4983230072969 + 3 ^ 40 * 7521438 * 2
def baseEnd_7521438 : Nat := 3862112906991848572934543

theorem tailTrace_7521438 : CollatzResearch.WordTrace tailWord_7521438 prefixEnd_7521438 3862112906991848572934543 := by
  unfold tailWord_7521438
  simp only [CollatzResearch.WordTrace]
  refine ⟨34291172615640270023314621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182886253950081440124344645 34291172615640270023314621)
  ·
    refine ⟨12859189730865101258742983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34291172615640270023314621 12859189730865101258742983)
    ·
      refine ⟨19288784596297651888114475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12859189730865101258742983 19288784596297651888114475)
      ·
        refine ⟨28933176894446477832171713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19288784596297651888114475 28933176894446477832171713)
        ·
          refine ⟨21699882670834858374128785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28933176894446477832171713 21699882670834858374128785)
          ·
            refine ⟨16274912003126143780596589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21699882670834858374128785 16274912003126143780596589)
            ·
              refine ⟨6103092001172303917723721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16274912003126143780596589 6103092001172303917723721)
              ·
                refine ⟨4577319000879227938292791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6103092001172303917723721 4577319000879227938292791)
                ·
                  refine ⟨6865978501318841907439187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577319000879227938292791 6865978501318841907439187)
                  ·
                    refine ⟨10298967751978262861158781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6865978501318841907439187 10298967751978262861158781)
                    ·
                      refine ⟨3862112906991848572934543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10298967751978262861158781 3862112906991848572934543)
                      ·
                        rfl

theorem cell23_7521438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_7521438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521438 prefixEnd_7521438 := by exact prefixLift 7521438
  have htrace : WordTrace (prefixWord ++ tailWord_7521438) baseStart_7521438 baseEnd_7521438 := by
    simpa [prefixWord, tailWord_7521438, baseEnd_7521438] using wordTrace_append hprefix tailTrace_7521438
  have hstable : (prefixWord ++ tailWord_7521438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521438).length < 2 ^ (prefixWord ++ tailWord_7521438).sum := by decide
  have hdescent : baseEnd_7521438 < baseStart_7521438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521444 : List Nat := [2, 3, 1, 2, 3, 1, 3, 1, 3, 2, 2]
def baseStart_7521444 : Nat := 118140960795 + 7521444 * 2 ^ 59
def prefixEnd_7521444 : Nat := 4983230072969 + 3 ^ 40 * 7521444 * 2
def baseEnd_7521444 : Nat := 3862115987875775549459515

theorem tailTrace_7521444 : CollatzResearch.WordTrace tailWord_7521444 prefixEnd_7521444 3862115987875775549459515 := by
  unfold tailWord_7521444
  simp only [CollatzResearch.WordTrace]
  refine ⟨137164799881550211605617693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182886399842066948807490257 137164799881550211605617693)
  ·
    refine ⟨51436799955581329352106635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137164799881550211605617693 51436799955581329352106635)
    ·
      refine ⟨77155199933371994028159953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51436799955581329352106635 77155199933371994028159953)
      ·
        refine ⟨57866399950028995521119965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77155199933371994028159953 57866399950028995521119965)
        ·
          refine ⟨21699899981260873320419987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57866399950028995521119965 21699899981260873320419987)
          ·
            refine ⟨32549849971891309980629981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21699899981260873320419987 32549849971891309980629981)
            ·
              refine ⟨12206193739459241242736243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32549849971891309980629981 12206193739459241242736243)
              ·
                refine ⟨18309290609188861864104365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12206193739459241242736243 18309290609188861864104365)
                ·
                  refine ⟨6865983978445823199039137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18309290609188861864104365 6865983978445823199039137)
                  ·
                    refine ⟨5149487983834367399279353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6865983978445823199039137 5149487983834367399279353)
                    ·
                      refine ⟨3862115987875775549459515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5149487983834367399279353 3862115987875775549459515)
                      ·
                        rfl

theorem cell23_7521444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_7521444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521444 prefixEnd_7521444 := by exact prefixLift 7521444
  have htrace : WordTrace (prefixWord ++ tailWord_7521444) baseStart_7521444 baseEnd_7521444 := by
    simpa [prefixWord, tailWord_7521444, baseEnd_7521444] using wordTrace_append hprefix tailTrace_7521444
  have hstable : (prefixWord ++ tailWord_7521444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521444).length < 2 ^ (prefixWord ++ tailWord_7521444).sum := by decide
  have hdescent : baseEnd_7521444 < baseStart_7521444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521450 : List Nat := [3, 1, 5, 1, 1, 1, 1, 10]
def baseStart_7521450 : Nat := 118140960795 + 7521450 * 2 ^ 59
def prefixEnd_7521450 : Nat := 4983230072969 + 3 ^ 40 * 7521450 * 2
def baseEnd_7521450 : Nat := 143041446991100093554981

theorem tailTrace_7521450 : CollatzResearch.WordTrace tailWord_7521450 prefixEnd_7521450 143041446991100093554981 := by
  unfold tailWord_7521450
  simp only [CollatzResearch.WordTrace]
  refine ⟨68582454650269671558988451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182886545734052457490635869 68582454650269671558988451)
  ·
    refine ⟨102873681975404507338482677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68582454650269671558988451 102873681975404507338482677)
    ·
      refine ⟨9644407685194172562982751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102873681975404507338482677 9644407685194172562982751)
      ·
        refine ⟨14466611527791258844474127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9644407685194172562982751 14466611527791258844474127)
        ·
          refine ⟨21699917291686888266711191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14466611527791258844474127 21699917291686888266711191)
          ·
            refine ⟨32549875937530332400066787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21699917291686888266711191 32549875937530332400066787)
            ·
              refine ⟨48824813906295498600100181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32549875937530332400066787 48824813906295498600100181)
              ·
                refine ⟨143041446991100093554981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48824813906295498600100181 143041446991100093554981)
                ·
                  rfl

theorem cell23_7521450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 10].length) (baseStart_7521450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521450 prefixEnd_7521450 := by exact prefixLift 7521450
  have htrace : WordTrace (prefixWord ++ tailWord_7521450) baseStart_7521450 baseEnd_7521450 := by
    simpa [prefixWord, tailWord_7521450, baseEnd_7521450] using wordTrace_append hprefix tailTrace_7521450
  have hstable : (prefixWord ++ tailWord_7521450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521450).length < 2 ^ (prefixWord ++ tailWord_7521450).sum := by decide
  have hdescent : baseEnd_7521450 < baseStart_7521450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521503 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 5]
def baseStart_7521503 : Nat := 118140960795 + 7521503 * 2 ^ 59
def prefixEnd_7521503 : Nat := 4983230072969 + 3 ^ 40 * 7521503 * 2
def baseEnd_7521503 : Nat := 3862146283234390818621743

theorem tailTrace_7521503 : CollatzResearch.WordTrace tailWord_7521503 prefixEnd_7521503 3862146283234390818621743 := by
  unfold tailWord_7521503
  simp only [CollatzResearch.WordTrace]
  refine ⟨274331751669886676287633163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182887834446591117525088775 274331751669886676287633163)
  ·
    refine ⟨411497627504830014431449745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274331751669886676287633163 411497627504830014431449745)
    ·
      refine ⟨308623220628622510823587309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411497627504830014431449745 308623220628622510823587309)
      ·
        refine ⟨115733707735733441558845241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308623220628622510823587309 115733707735733441558845241)
        ·
          refine ⟨86800280801800081169133931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115733707735733441558845241 86800280801800081169133931)
          ·
            refine ⟨130200421202700121753700897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86800280801800081169133931 130200421202700121753700897)
            ·
              refine ⟨97650315902025091315275673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130200421202700121753700897 97650315902025091315275673)
              ·
                refine ⟨73237736926518818486456755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97650315902025091315275673 73237736926518818486456755)
                ·
                  refine ⟨109856605389778227729685133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73237736926518818486456755 109856605389778227729685133)
                  ·
                    refine ⟨41196227021166835398631925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109856605389778227729685133 41196227021166835398631925)
                    ·
                      refine ⟨3862146283234390818621743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41196227021166835398631925 3862146283234390818621743)
                      ·
                        rfl

theorem cell23_7521503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_7521503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521503 prefixEnd_7521503 := by exact prefixLift 7521503
  have htrace : WordTrace (prefixWord ++ tailWord_7521503) baseStart_7521503 baseEnd_7521503 := by
    simpa [prefixWord, tailWord_7521503, baseEnd_7521503] using wordTrace_append hprefix tailTrace_7521503
  have hstable : (prefixWord ++ tailWord_7521503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521503).length < 2 ^ (prefixWord ++ tailWord_7521503).sum := by decide
  have hdescent : baseEnd_7521503 < baseStart_7521503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521523 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 9]
def baseStart_7521523 : Nat := 118140960795 + 7521523 * 2 ^ 59
def prefixEnd_7521523 : Nat := 4983230072969 + 3 ^ 40 * 7521523 * 2
def baseEnd_7521523 : Nat := 429128505871942304485739

theorem tailTrace_7521523 : CollatzResearch.WordTrace tailWord_7521523 prefixEnd_7521523 429128505871942304485739 := by
  unfold tailWord_7521523
  simp only [CollatzResearch.WordTrace]
  refine ⟨274332481129814219703361223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182888320753209479802240815 274332481129814219703361223)
  ·
    refine ⟨411498721694721329555041835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274332481129814219703361223 411498721694721329555041835)
    ·
      refine ⟨617248082542081994332562753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411498721694721329555041835 617248082542081994332562753)
      ·
        refine ⟨462936061906561495749422065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617248082542081994332562753 462936061906561495749422065)
        ·
          refine ⟨347202046429921121812066549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462936061906561495749422065 347202046429921121812066549)
          ·
            refine ⟨32550191852805105169881239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 347202046429921121812066549 32550191852805105169881239)
            ·
              refine ⟨48825287779207657754821859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32550191852805105169881239 48825287779207657754821859)
              ·
                refine ⟨73237931668811486632232789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48825287779207657754821859 73237931668811486632232789)
                ·
                  refine ⟨429128505871942304485739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73237931668811486632232789 429128505871942304485739)
                  ·
                    rfl

theorem cell23_7521523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 9].length) (baseStart_7521523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521523 prefixEnd_7521523 := by exact prefixLift 7521523
  have htrace : WordTrace (prefixWord ++ tailWord_7521523) baseStart_7521523 baseEnd_7521523 := by
    simpa [prefixWord, tailWord_7521523, baseEnd_7521523] using wordTrace_append hprefix tailTrace_7521523
  have hstable : (prefixWord ++ tailWord_7521523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521523).length < 2 ^ (prefixWord ++ tailWord_7521523).sum := by decide
  have hdescent : baseEnd_7521523 < baseStart_7521523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521533 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_7521533 : Nat := 118140960795 + 7521533 * 2 ^ 59
def prefixEnd_7521533 : Nat := 4983230072969 + 3 ^ 40 * 7521533 * 2
def baseEnd_7521533 : Nat := 3862161687654025701246605

theorem tailTrace_7521533 : CollatzResearch.WordTrace tailWord_7521533 prefixEnd_7521533 3862161687654025701246605 := by
  unfold tailWord_7521533
  simp only [CollatzResearch.WordTrace]
  refine ⟨274332845859777991411225253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182888563906518660940816835 274332845859777991411225253)
  ·
    refine ⟨51437408598708373389604735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274332845859777991411225253 51437408598708373389604735)
    ·
      refine ⟨77156112898062560084407103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51437408598708373389604735 77156112898062560084407103)
      ·
        refine ⟨115734169347093840126610655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77156112898062560084407103 115734169347093840126610655)
        ·
          refine ⟨173601254020640760189915983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115734169347093840126610655 173601254020640760189915983)
          ·
            refine ⟨260401881030961140284873975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173601254020640760189915983 260401881030961140284873975)
            ·
              refine ⟨390602821546441710427310963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260401881030961140284873975 390602821546441710427310963)
              ·
                refine ⟨585904232319662565640966445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390602821546441710427310963 585904232319662565640966445)
                ·
                  refine ⟨219714087119873462115362417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585904232319662565640966445 219714087119873462115362417)
                  ·
                    refine ⟨164785565339905096586521813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 219714087119873462115362417 164785565339905096586521813)
                    ·
                      refine ⟨3862161687654025701246605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164785565339905096586521813 3862161687654025701246605)
                      ·
                        rfl

theorem cell23_7521533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_7521533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521533 prefixEnd_7521533 := by exact prefixLift 7521533
  have htrace : WordTrace (prefixWord ++ tailWord_7521533) baseStart_7521533 baseEnd_7521533 := by
    simpa [prefixWord, tailWord_7521533, baseEnd_7521533] using wordTrace_append hprefix tailTrace_7521533
  have hstable : (prefixWord ++ tailWord_7521533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521533).length < 2 ^ (prefixWord ++ tailWord_7521533).sum := by decide
  have hdescent : baseEnd_7521533 < baseStart_7521533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521534 : List Nat := [4, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_7521534 : Nat := 118140960795 + 7521534 * 2 ^ 59
def prefixEnd_7521534 : Nat := 4983230072969 + 3 ^ 40 * 7521534 * 2
def baseEnd_7521534 : Nat := 3862162201134680197334101

theorem tailTrace_7521534 : CollatzResearch.WordTrace tailWord_7521534 prefixEnd_7521534 3862162201134680197334101 := by
  unfold tailWord_7521534
  simp only [CollatzResearch.WordTrace]
  refine ⟨34291610291596796072751457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182888588221849579054674437 34291610291596796072751457)
  ·
    refine ⟨25718707718697597054563593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34291610291596796072751457 25718707718697597054563593)
    ·
      refine ⟨19289030789023197790922695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25718707718697597054563593 19289030789023197790922695)
      ·
        refine ⟨28933546183534796686384043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19289030789023197790922695 28933546183534796686384043)
        ·
          refine ⟨43400319275302195029576065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28933546183534796686384043 43400319275302195029576065)
          ·
            refine ⟨32550239456476646272182049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43400319275302195029576065 32550239456476646272182049)
            ·
              refine ⟨24412679592357484704136537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32550239456476646272182049 24412679592357484704136537)
              ·
                refine ⟨18309509694268113528102403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24412679592357484704136537 18309509694268113528102403)
                ·
                  refine ⟨27464264541402170292153605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18309509694268113528102403 27464264541402170292153605)
                  ·
                    refine ⟨5149549601512906929778801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27464264541402170292153605 5149549601512906929778801)
                    ·
                      refine ⟨3862162201134680197334101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5149549601512906929778801 3862162201134680197334101)
                      ·
                        rfl

theorem cell23_7521534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_7521534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521534 prefixEnd_7521534 := by exact prefixLift 7521534
  have htrace : WordTrace (prefixWord ++ tailWord_7521534) baseStart_7521534 baseEnd_7521534 := by
    simpa [prefixWord, tailWord_7521534, baseEnd_7521534] using wordTrace_append hprefix tailTrace_7521534
  have hstable : (prefixWord ++ tailWord_7521534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521534).length < 2 ^ (prefixWord ++ tailWord_7521534).sum := by decide
  have hdescent : baseEnd_7521534 < baseStart_7521534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521563 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 7]
def baseStart_7521563 : Nat := 118140960795 + 7521563 * 2 ^ 59
def prefixEnd_7521563 : Nat := 4983230072969 + 3 ^ 40 * 7521563 * 2
def baseEnd_7521563 : Nat := 3862177092073660583871467

theorem tailTrace_7521563 : CollatzResearch.WordTrace tailWord_7521563 prefixEnd_7521563 3862177092073660583871467 := by
  unfold tailWord_7521563
  simp only [CollatzResearch.WordTrace]
  refine ⟨274333940049669306534817343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182889293366446204356544895 274333940049669306534817343)
  ·
    refine ⟨411500910074503959802226015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274333940049669306534817343 411500910074503959802226015)
    ·
      refine ⟨617251365111755939703339023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411500910074503959802226015 617251365111755939703339023)
      ·
        refine ⟨925877047667633909555008535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617251365111755939703339023 925877047667633909555008535)
        ·
          refine ⟨1388815571501450864332512803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925877047667633909555008535 1388815571501450864332512803)
          ·
            refine ⟨2083223357252176296498769205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388815571501450864332512803 2083223357252176296498769205)
            ·
              refine ⟨195302189742391527796759613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2083223357252176296498769205 195302189742391527796759613)
              ·
                refine ⟨73238321153396822923784855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195302189742391527796759613 73238321153396822923784855)
                ·
                  refine ⟨109857481730095234385677283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73238321153396822923784855 109857481730095234385677283)
                  ·
                    refine ⟨164786222595142851578515925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109857481730095234385677283 164786222595142851578515925)
                    ·
                      refine ⟨3862177092073660583871467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164786222595142851578515925 3862177092073660583871467)
                      ·
                        rfl

theorem cell23_7521563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 7].length) (baseStart_7521563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521563 prefixEnd_7521563 := by exact prefixLift 7521563
  have htrace : WordTrace (prefixWord ++ tailWord_7521563) baseStart_7521563 baseEnd_7521563 := by
    simpa [prefixWord, tailWord_7521563, baseEnd_7521563] using wordTrace_append hprefix tailTrace_7521563
  have hstable : (prefixWord ++ tailWord_7521563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521563).length < 2 ^ (prefixWord ++ tailWord_7521563).sum := by decide
  have hdescent : baseEnd_7521563 < baseStart_7521563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521568 : List Nat := [2, 1, 1, 5, 3, 1, 3, 1, 2, 2, 2]
def baseStart_7521568 : Nat := 118140960795 + 7521568 * 2 ^ 59
def prefixEnd_7521568 : Nat := 4983230072969 + 3 ^ 40 * 7521568 * 2
def baseEnd_7521568 : Nat := 3862179659476933064308945

theorem tailTrace_7521568 : CollatzResearch.WordTrace tailWord_7521568 prefixEnd_7521568 3862179659476933064308945 := by
  unfold tailWord_7521568
  simp only [CollatzResearch.WordTrace]
  refine ⟨137167061207325596194374679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182889414943100794925832905 137167061207325596194374679)
  ·
    refine ⟨205750591810988394291562019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137167061207325596194374679 205750591810988394291562019)
    ·
      refine ⟨308625887716482591437343029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205750591810988394291562019 308625887716482591437343029)
      ·
        refine ⟨28933676973420242947250909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 308625887716482591437343029 28933676973420242947250909)
        ·
          refine ⟨10850128865032591105219091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28933676973420242947250909 10850128865032591105219091)
          ·
            refine ⟨16275193297548886657828637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10850128865032591105219091 16275193297548886657828637)
            ·
              refine ⟨6103197486580832496685739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16275193297548886657828637 6103197486580832496685739)
              ·
                refine ⟨9154796229871248745028609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6103197486580832496685739 9154796229871248745028609)
                ·
                  refine ⟨6866097172403436558771457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9154796229871248745028609 6866097172403436558771457)
                  ·
                    refine ⟨5149572879302577419078593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6866097172403436558771457 5149572879302577419078593)
                    ·
                      refine ⟨3862179659476933064308945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5149572879302577419078593 3862179659476933064308945)
                      ·
                        rfl

theorem cell23_7521568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_7521568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521568 prefixEnd_7521568 := by exact prefixLift 7521568
  have htrace : WordTrace (prefixWord ++ tailWord_7521568) baseStart_7521568 baseEnd_7521568 := by
    simpa [prefixWord, tailWord_7521568, baseEnd_7521568] using wordTrace_append hprefix tailTrace_7521568
  have hstable : (prefixWord ++ tailWord_7521568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521568).length < 2 ^ (prefixWord ++ tailWord_7521568).sum := by decide
  have hdescent : baseEnd_7521568 < baseStart_7521568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521583 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 1, 10]
def baseStart_7521583 : Nat := 118140960795 + 7521583 * 2 ^ 59
def prefixEnd_7521583 : Nat := 4983230072969 + 3 ^ 40 * 7521583 * 2
def baseEnd_7521583 : Nat := 1287395787228916835207125

theorem tailTrace_7521583 : CollatzResearch.WordTrace tailWord_7521583 prefixEnd_7521583 1287395787228916835207125 := by
  unfold tailWord_7521583
  simp only [CollatzResearch.WordTrace]
  refine ⟨274334669509596849950545403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182889779673064566633696935 274334669509596849950545403)
  ·
    refine ⟨411502004264395274925818105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274334669509596849950545403 411502004264395274925818105)
    ·
      refine ⟨308626503198296456194363579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411502004264395274925818105 308626503198296456194363579)
      ·
        refine ⟨462939754797444684291545369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308626503198296456194363579 462939754797444684291545369)
        ·
          refine ⟨347204816098083513218659027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462939754797444684291545369 347204816098083513218659027)
          ·
            refine ⟨520807224147125269827988541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347204816098083513218659027 520807224147125269827988541)
            ·
              refine ⟨195302709055171976185495703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 520807224147125269827988541 195302709055171976185495703)
              ·
                refine ⟨292954063582757964278243555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195302709055171976185495703 292954063582757964278243555)
                ·
                  refine ⟨439431095374136946417365333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292954063582757964278243555 439431095374136946417365333)
                  ·
                    refine ⟨1287395787228916835207125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 439431095374136946417365333 1287395787228916835207125)
                    ·
                      rfl

theorem cell23_7521583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 10].length) (baseStart_7521583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521583 prefixEnd_7521583 := by exact prefixLift 7521583
  have htrace : WordTrace (prefixWord ++ tailWord_7521583) baseStart_7521583 baseEnd_7521583 := by
    simpa [prefixWord, tailWord_7521583, baseEnd_7521583] using wordTrace_append hprefix tailTrace_7521583
  have hstable : (prefixWord ++ tailWord_7521583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521583).length < 2 ^ (prefixWord ++ tailWord_7521583).sum := by decide
  have hdescent : baseEnd_7521583 < baseStart_7521583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521604 : List Nat := [2, 3, 4, 1, 1, 2, 1, 2, 2, 5]
def baseStart_7521604 : Nat := 118140960795 + 7521604 * 2 ^ 59
def prefixEnd_7521604 : Nat := 4983230072969 + 3 ^ 40 * 7521604 * 2
def baseEnd_7521604 : Nat := 1287399381593498307819593

theorem tailTrace_7521604 : CollatzResearch.WordTrace tailWord_7521604 prefixEnd_7521604 1287399381593498307819593 := by
  unfold tailWord_7521604
  simp only [CollatzResearch.WordTrace]
  refine ⟨137167717721260385268529933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182890290295013847024706577 137167717721260385268529933)
  ·
    refine ⟨51437894145472644475698725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137167717721260385268529933 51437894145472644475698725)
    ·
      refine ⟨9644605152276120839193511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51437894145472644475698725 9644605152276120839193511)
      ·
        refine ⟨14466907728414181258790267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9644605152276120839193511 14466907728414181258790267)
        ·
          refine ⟨21700361592621271888185401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14466907728414181258790267 21700361592621271888185401)
          ·
            refine ⟨16275271194465953916139051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21700361592621271888185401 16275271194465953916139051)
            ·
              refine ⟨24412906791698930874208577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16275271194465953916139051 24412906791698930874208577)
              ·
                refine ⟨18309680093774198155656433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24412906791698930874208577 18309680093774198155656433)
                ·
                  refine ⟨13732260070330648616742325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18309680093774198155656433 13732260070330648616742325)
                  ·
                    refine ⟨1287399381593498307819593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13732260070330648616742325 1287399381593498307819593)
                    ·
                      rfl

theorem cell23_7521604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_7521604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521604 prefixEnd_7521604 := by exact prefixLift 7521604
  have htrace : WordTrace (prefixWord ++ tailWord_7521604) baseStart_7521604 baseEnd_7521604 := by
    simpa [prefixWord, tailWord_7521604, baseEnd_7521604] using wordTrace_append hprefix tailTrace_7521604
  have hstable : (prefixWord ++ tailWord_7521604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521604).length < 2 ^ (prefixWord ++ tailWord_7521604).sum := by decide
  have hdescent : baseEnd_7521604 < baseStart_7521604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521607 : List Nat := [1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_7521607 : Nat := 118140960795 + 7521607 * 2 ^ 59
def prefixEnd_7521607 : Nat := 4983230072969 + 3 ^ 40 * 7521607 * 2
def baseEnd_7521607 : Nat := 3862199685222458411721265

theorem tailTrace_7521607 : CollatzResearch.WordTrace tailWord_7521607 prefixEnd_7521607 3862199685222458411721265 := by
  unfold tailWord_7521607
  simp only [CollatzResearch.WordTrace]
  refine ⟨274335544861509902049419075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182890363241006601366279383 274335544861509902049419075)
  ·
    refine ⟨411503317292264853074128613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274335544861509902049419075 411503317292264853074128613)
    ·
      refine ⟨77156871992299659951399115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 411503317292264853074128613 77156871992299659951399115)
      ·
        refine ⟨115735307988449489927098673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77156871992299659951399115 115735307988449489927098673)
        ·
          refine ⟨86801480991337117445324005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115735307988449489927098673 86801480991337117445324005)
          ·
            refine ⟨16275277685875709520998251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86801480991337117445324005 16275277685875709520998251)
            ·
              refine ⟨24412916528813564281497377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16275277685875709520998251 24412916528813564281497377)
              ·
                refine ⟨18309687396610173211123033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24412916528813564281497377 18309687396610173211123033)
                ·
                  refine ⟨13732265547457629908342275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18309687396610173211123033 13732265547457629908342275)
                  ·
                    refine ⟨20598398321186444862513413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13732265547457629908342275 20598398321186444862513413)
                    ·
                      refine ⟨3862199685222458411721265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20598398321186444862513413 3862199685222458411721265)
                      ·
                        rfl

theorem cell23_7521607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_7521607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521607 prefixEnd_7521607 := by exact prefixLift 7521607
  have htrace : WordTrace (prefixWord ++ tailWord_7521607) baseStart_7521607 baseEnd_7521607 := by
    simpa [prefixWord, tailWord_7521607, baseEnd_7521607] using wordTrace_append hprefix tailTrace_7521607
  have hstable : (prefixWord ++ tailWord_7521607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521607).length < 2 ^ (prefixWord ++ tailWord_7521607).sum := by decide
  have hdescent : baseEnd_7521607 < baseStart_7521607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521644 : List Nat := [2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 3]
def baseStart_7521644 : Nat := 118140960795 + 7521644 * 2 ^ 59
def prefixEnd_7521644 : Nat := 4983230072969 + 3 ^ 40 * 7521644 * 2
def baseEnd_7521644 : Nat := 3862218684006674766958595

theorem tailTrace_7521644 : CollatzResearch.WordTrace tailWord_7521644 prefixEnd_7521644 3862218684006674766958595 := by
  unfold tailWord_7521644
  simp only [CollatzResearch.WordTrace]
  refine ⟨137168447181187928684257993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182891262908250571579010657 137168447181187928684257993)
  ·
    refine ⟨102876335385890946513193495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137168447181187928684257993 102876335385890946513193495)
    ·
      refine ⟨154314503078836419769790243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102876335385890946513193495 154314503078836419769790243)
      ·
        refine ⟨231471754618254629654685365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154314503078836419769790243 231471754618254629654685365)
        ·
          refine ⟨21700476995461371530126753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 231471754618254629654685365 21700476995461371530126753)
          ·
            refine ⟨16275357746596028647595065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21700476995461371530126753 16275357746596028647595065)
            ·
              refine ⟨12206518309947021485696299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16275357746596028647595065 12206518309947021485696299)
              ·
                refine ⟨18309777464920532228544449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12206518309947021485696299 18309777464920532228544449)
                ·
                  refine ⟨13732333098690399171408337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18309777464920532228544449 13732333098690399171408337)
                  ·
                    refine ⟨10299249824017799378556253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13732333098690399171408337 10299249824017799378556253)
                    ·
                      refine ⟨3862218684006674766958595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10299249824017799378556253 3862218684006674766958595)
                      ·
                        rfl

theorem cell23_7521644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_7521644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521644 prefixEnd_7521644 := by exact prefixLift 7521644
  have htrace : WordTrace (prefixWord ++ tailWord_7521644) baseStart_7521644 baseEnd_7521644 := by
    simpa [prefixWord, tailWord_7521644, baseEnd_7521644] using wordTrace_append hprefix tailTrace_7521644
  have hstable : (prefixWord ++ tailWord_7521644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521644).length < 2 ^ (prefixWord ++ tailWord_7521644).sum := by decide
  have hdescent : baseEnd_7521644 < baseStart_7521644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521668 : List Nat := [2, 3, 2, 1, 1, 5, 2, 2, 1, 4]
def baseStart_7521668 : Nat := 118140960795 + 7521668 * 2 ^ 59
def prefixEnd_7521668 : Nat := 4983230072969 + 3 ^ 40 * 7521668 * 2
def baseEnd_7521668 : Nat := 1287410335847460891019495

theorem tailTrace_7521668 : CollatzResearch.WordTrace tailWord_7521668 prefixEnd_7521668 1287410335847460891019495 := by
  unfold tailWord_7521668
  simp only [CollatzResearch.WordTrace]
  refine ⟨137168884857144454733694829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182891846476192606311593105 137168884857144454733694829)
  ·
    refine ⟨51438331821429170525135561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137168884857144454733694829 51438331821429170525135561)
    ·
      refine ⟨38578748866071877893851671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51438331821429170525135561 38578748866071877893851671)
      ·
        refine ⟨57868123299107816840777507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38578748866071877893851671 57868123299107816840777507)
        ·
          refine ⟨86802184948661725261166261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57868123299107816840777507 86802184948661725261166261)
          ·
            refine ⟨8137704838937036743234337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86802184948661725261166261 8137704838937036743234337)
            ·
              refine ⟨6103278629202777557425753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8137704838937036743234337 6103278629202777557425753)
              ·
                refine ⟨4577458971902083168069315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6103278629202777557425753 4577458971902083168069315)
                ·
                  refine ⟨6866188457853124752103973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577458971902083168069315 6866188457853124752103973)
                  ·
                    refine ⟨1287410335847460891019495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6866188457853124752103973 1287410335847460891019495)
                    ·
                      rfl

theorem cell23_7521668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_7521668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521668 prefixEnd_7521668 := by exact prefixLift 7521668
  have htrace : WordTrace (prefixWord ++ tailWord_7521668) baseStart_7521668 baseEnd_7521668 := by
    simpa [prefixWord, tailWord_7521668, baseEnd_7521668] using wordTrace_append hprefix tailTrace_7521668
  have hstable : (prefixWord ++ tailWord_7521668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521668).length < 2 ^ (prefixWord ++ tailWord_7521668).sum := by decide
  have hdescent : baseEnd_7521668 < baseStart_7521668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521754 : List Nat := [3, 1, 1, 2, 3, 4, 2, 7]
def baseStart_7521754 : Nat := 118140960795 + 7521754 * 2 ^ 59
def prefixEnd_7521754 : Nat := 4983230072969 + 3 ^ 40 * 7521754 * 2
def baseEnd_7521754 : Nat := 143047228402913679132707

theorem tailTrace_7521754 : CollatzResearch.WordTrace tailWord_7521754 prefixEnd_7521754 143047228402913679132707 := by
  unfold tailWord_7521754
  simp only [CollatzResearch.WordTrace]
  refine ⟨68585226597994336538755079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182893937594651564103346877 68585226597994336538755079)
  ·
    refine ⟨102877839896991504808132619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68585226597994336538755079 102877839896991504808132619)
    ·
      refine ⟨154316759845487257212198929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102877839896991504808132619 154316759845487257212198929)
      ·
        refine ⟨115737569884115442909149197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154316759845487257212198929 115737569884115442909149197)
        ·
          refine ⟨43401588706543291090930949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115737569884115442909149197 43401588706543291090930949)
          ·
            refine ⟨8137797882476867079549553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43401588706543291090930949 8137797882476867079549553)
            ·
              refine ⟨6103348411857650309662165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8137797882476867079549553 6103348411857650309662165)
              ·
                refine ⟨143047228402913679132707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6103348411857650309662165 143047228402913679132707)
                ·
                  rfl

theorem cell23_7521754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 7].length) (baseStart_7521754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521754 prefixEnd_7521754 := by exact prefixLift 7521754
  have htrace : WordTrace (prefixWord ++ tailWord_7521754) baseStart_7521754 baseEnd_7521754 := by
    simpa [prefixWord, tailWord_7521754, baseEnd_7521754] using wordTrace_append hprefix tailTrace_7521754
  have hstable : (prefixWord ++ tailWord_7521754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521754).length < 2 ^ (prefixWord ++ tailWord_7521754).sum := by decide
  have hdescent : baseEnd_7521754 < baseStart_7521754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521765 : List Nat := [1, 3, 1, 5, 1, 1, 3, 3, 1, 2, 2]
def baseStart_7521765 : Nat := 118140960795 + 7521765 * 2 ^ 59
def prefixEnd_7521765 : Nat := 4983230072969 + 3 ^ 40 * 7521765 * 2
def baseEnd_7521765 : Nat := 3862280815165868793545539

theorem tailTrace_7521765 : CollatzResearch.WordTrace tailWord_7521765 prefixEnd_7521765 3862280815165868793545539 := by
  unfold tailWord_7521765
  simp only [CollatzResearch.WordTrace]
  refine ⟨274341307594937495033670749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182894205063291663355780499 274341307594937495033670749)
  ·
    refine ⟨102877990348101560637626531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274341307594937495033670749 102877990348101560637626531)
    ·
      refine ⟨154316985522152340956439797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102877990348101560637626531 154316985522152340956439797)
      ·
        refine ⟨14467217392701781964666231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154316985522152340956439797 14467217392701781964666231)
        ·
          refine ⟨21700826089052672946999347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14467217392701781964666231 21700826089052672946999347)
          ·
            refine ⟨32551239133579009420499021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21700826089052672946999347 32551239133579009420499021)
            ·
              refine ⟨12206714675092128532687133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32551239133579009420499021 12206714675092128532687133)
              ·
                refine ⟨4577518003159548199757675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12206714675092128532687133 4577518003159548199757675)
                ·
                  refine ⟨6866277004739322299636513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577518003159548199757675 6866277004739322299636513)
                  ·
                    refine ⟨5149707753554491724727385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6866277004739322299636513 5149707753554491724727385)
                    ·
                      refine ⟨3862280815165868793545539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5149707753554491724727385 3862280815165868793545539)
                      ·
                        rfl

theorem cell23_7521765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_7521765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521765 prefixEnd_7521765 := by exact prefixLift 7521765
  have htrace : WordTrace (prefixWord ++ tailWord_7521765) baseStart_7521765 baseEnd_7521765 := by
    simpa [prefixWord, tailWord_7521765, baseEnd_7521765] using wordTrace_append hprefix tailTrace_7521765
  have hstable : (prefixWord ++ tailWord_7521765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521765).length < 2 ^ (prefixWord ++ tailWord_7521765).sum := by decide
  have hdescent : baseEnd_7521765 < baseStart_7521765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521782 : List Nat := [5, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2]
def baseStart_7521782 : Nat := 118140960795 + 7521782 * 2 ^ 59
def prefixEnd_7521782 : Nat := 4983230072969 + 3 ^ 40 * 7521782 * 2
def baseEnd_7521782 : Nat := 3862289544336995227032961

theorem tailTrace_7521782 : CollatzResearch.WordTrace tailWord_7521782 prefixEnd_7521782 3862289544336995227032961 := by
  unfold tailWord_7521782
  simp only [CollatzResearch.WordTrace]
  refine ⟨17146370477242244183564975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182894618423917271291359733 17146370477242244183564975)
  ·
    refine ⟨25719555715863366275347463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17146370477242244183564975 25719555715863366275347463)
    ·
      refine ⟨38579333573795049413021195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25719555715863366275347463 38579333573795049413021195)
      ·
        refine ⟨57869000360692574119531793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38579333573795049413021195 57869000360692574119531793)
        ·
          refine ⟨43401750270519430589648845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57869000360692574119531793 43401750270519430589648845)
          ·
            refine ⟨16275656351444786471118317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43401750270519430589648845 16275656351444786471118317)
            ·
              refine ⟨6103371131791794926669369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16275656351444786471118317 6103371131791794926669369)
              ·
                refine ⟨4577528348843846195002027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6103371131791794926669369 4577528348843846195002027)
                ·
                  refine ⟨6866292523265769292503041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577528348843846195002027 6866292523265769292503041)
                  ·
                    refine ⟨5149719392449326969377281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6866292523265769292503041 5149719392449326969377281)
                    ·
                      refine ⟨3862289544336995227032961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5149719392449326969377281 3862289544336995227032961)
                      ·
                        rfl

theorem cell23_7521782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_7521782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521782 prefixEnd_7521782 := by exact prefixLift 7521782
  have htrace : WordTrace (prefixWord ++ tailWord_7521782) baseStart_7521782 baseEnd_7521782 := by
    simpa [prefixWord, tailWord_7521782, baseEnd_7521782] using wordTrace_append hprefix tailTrace_7521782
  have hstable : (prefixWord ++ tailWord_7521782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521782).length < 2 ^ (prefixWord ++ tailWord_7521782).sum := by decide
  have hdescent : baseEnd_7521782 < baseStart_7521782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521821 : List Nat := [1, 4, 2, 2, 1, 1, 3, 2, 1, 4, 2]
def baseStart_7521821 : Nat := 118140960795 + 7521821 * 2 ^ 59
def prefixEnd_7521821 : Nat := 4983230072969 + 3 ^ 40 * 7521821 * 2
def baseEnd_7521821 : Nat := 3862309570082520574445281

theorem tailTrace_7521821 : CollatzResearch.WordTrace tailWord_7521821 prefixEnd_7521821 3862309570082520574445281 := by
  unfold tailWord_7521821
  simp only [CollatzResearch.WordTrace]
  refine ⟨274343350082734616597709317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182895566721823077731806211 274343350082734616597709317)
  ·
    refine ⟨51439378140512740612070497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274343350082734616597709317 51439378140512740612070497)
    ·
      refine ⟨38579533605384555459052873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51439378140512740612070497 38579533605384555459052873)
      ·
        refine ⟨28934650204038416594289655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38579533605384555459052873 28934650204038416594289655)
        ·
          refine ⟨43401975306057624891434483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28934650204038416594289655 43401975306057624891434483)
          ·
            refine ⟨65102962959086437337151725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43401975306057624891434483 65102962959086437337151725)
            ·
              refine ⟨24413611109657414001431897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65102962959086437337151725 24413611109657414001431897)
              ·
                refine ⟨18310208332243060501073923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24413611109657414001431897 18310208332243060501073923)
                ·
                  refine ⟨27465312498364590751610885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18310208332243060501073923 27465312498364590751610885)
                  ·
                    refine ⟨5149746093443360765927041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27465312498364590751610885 5149746093443360765927041)
                    ·
                      refine ⟨3862309570082520574445281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5149746093443360765927041 3862309570082520574445281)
                      ·
                        rfl

theorem cell23_7521821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_7521821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521821 prefixEnd_7521821 := by exact prefixLift 7521821
  have htrace : WordTrace (prefixWord ++ tailWord_7521821) baseStart_7521821 baseEnd_7521821 := by
    simpa [prefixWord, tailWord_7521821, baseEnd_7521821] using wordTrace_append hprefix tailTrace_7521821
  have hstable : (prefixWord ++ tailWord_7521821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521821).length < 2 ^ (prefixWord ++ tailWord_7521821).sum := by decide
  have hdescent : baseEnd_7521821 < baseStart_7521821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521824 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 5]
def baseStart_7521824 : Nat := 118140960795 + 7521824 * 2 ^ 59
def prefixEnd_7521824 : Nat := 4983230072969 + 3 ^ 40 * 7521824 * 2
def baseEnd_7521824 : Nat := 3862311110524484062707767

theorem tailTrace_7521824 : CollatzResearch.WordTrace tailWord_7521824 prefixEnd_7521824 3862311110524484062707767 := by
  unfold tailWord_7521824
  simp only [CollatzResearch.WordTrace]
  refine ⟨137171729750861874055034263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182895639667815832073379017 137171729750861874055034263)
  ·
    refine ⟨205757594626292811082551395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137171729750861874055034263 205757594626292811082551395)
    ·
      refine ⟨308636391939439216623827093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205757594626292811082551395 308636391939439216623827093)
      ·
        refine ⟨14467330872161213279241895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 308636391939439216623827093 14467330872161213279241895)
        ·
          refine ⟨21700996308241819918862843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14467330872161213279241895 21700996308241819918862843)
          ·
            refine ⟨32551494462362729878294265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21700996308241819918862843 32551494462362729878294265)
            ·
              refine ⟨24413620846772047408720699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32551494462362729878294265 24413620846772047408720699)
              ·
                refine ⟨36620431270158071113081049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24413620846772047408720699 36620431270158071113081049)
                ·
                  refine ⟨27465323452618553334810787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36620431270158071113081049 27465323452618553334810787)
                  ·
                    refine ⟨41197985178927830002216181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27465323452618553334810787 41197985178927830002216181)
                    ·
                      refine ⟨3862311110524484062707767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41197985178927830002216181 3862311110524484062707767)
                      ·
                        rfl

theorem cell23_7521824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_7521824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521824 prefixEnd_7521824 := by exact prefixLift 7521824
  have htrace : WordTrace (prefixWord ++ tailWord_7521824) baseStart_7521824 baseEnd_7521824 := by
    simpa [prefixWord, tailWord_7521824, baseEnd_7521824] using wordTrace_append hprefix tailTrace_7521824
  have hstable : (prefixWord ++ tailWord_7521824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521824).length < 2 ^ (prefixWord ++ tailWord_7521824).sum := by decide
  have hdescent : baseEnd_7521824 < baseStart_7521824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521834 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_7521834 : Nat := 118140960795 + 7521834 * 2 ^ 59
def prefixEnd_7521834 : Nat := 4983230072969 + 3 ^ 40 * 7521834 * 2
def baseEnd_7521834 : Nat := 3862316245331029023582721

theorem tailTrace_7521834 : CollatzResearch.WordTrace tailWord_7521834 prefixEnd_7521834 3862316245331029023582721 := by
  unfold tailWord_7521834
  simp only [CollatzResearch.WordTrace]
  refine ⟨68585956057921879954483139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182895882821125013211955037 68585956057921879954483139)
  ·
    refine ⟨102878934086882819931724709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68585956057921879954483139 102878934086882819931724709)
    ·
      refine ⟨19289800141290528737198383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102878934086882819931724709 19289800141290528737198383)
      ·
        refine ⟨28934700211935793105797575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19289800141290528737198383 28934700211935793105797575)
        ·
          refine ⟨43402050317903689658696363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28934700211935793105797575 43402050317903689658696363)
          ·
            refine ⟨65103075476855534488044545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43402050317903689658696363 65103075476855534488044545)
            ·
              refine ⟨48827306607641650866033409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65103075476855534488044545 48827306607641650866033409)
              ·
                refine ⟨36620479955731238149525057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48827306607641650866033409 36620479955731238149525057)
                ·
                  refine ⟨27465359966798428612143793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36620479955731238149525057 27465359966798428612143793)
                  ·
                    refine ⟨20599019975098821459107845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27465359966798428612143793 20599019975098821459107845)
                    ·
                      refine ⟨3862316245331029023582721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20599019975098821459107845 3862316245331029023582721)
                      ·
                        rfl

theorem cell23_7521834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_7521834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521834 prefixEnd_7521834 := by exact prefixLift 7521834
  have htrace : WordTrace (prefixWord ++ tailWord_7521834) baseStart_7521834 baseEnd_7521834 := by
    simpa [prefixWord, tailWord_7521834, baseEnd_7521834] using wordTrace_append hprefix tailTrace_7521834
  have hstable : (prefixWord ++ tailWord_7521834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521834).length < 2 ^ (prefixWord ++ tailWord_7521834).sum := by decide
  have hdescent : baseEnd_7521834 < baseStart_7521834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521874 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 1, 7]
def baseStart_7521874 : Nat := 118140960795 + 7521874 * 2 ^ 59
def prefixEnd_7521874 : Nat := 4983230072969 + 3 ^ 40 * 7521874 * 2
def baseEnd_7521874 : Nat := 1287445594852402955694179

theorem tailTrace_7521874 : CollatzResearch.WordTrace tailWord_7521874 prefixEnd_7521874 1287445594852402955694179 := by
  unfold tailWord_7521874
  simp only [CollatzResearch.WordTrace]
  refine ⟨68586320787885651662347169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182896855434361737766259117 68586320787885651662347169)
  ·
    refine ⟨51439740590914238746760377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68586320787885651662347169 51439740590914238746760377)
    ·
      refine ⟨38579805443185679060070283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51439740590914238746760377 38579805443185679060070283)
      ·
        refine ⟨57869708164778518590105425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38579805443185679060070283 57869708164778518590105425)
        ·
          refine ⟨43402281123583888942579069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57869708164778518590105425 43402281123583888942579069)
          ·
            refine ⟨16275855421343958353467151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43402281123583888942579069 16275855421343958353467151)
            ·
              refine ⟨24413783132015937530200727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16275855421343958353467151 24413783132015937530200727)
              ·
                refine ⟨36620674698023906295301091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24413783132015937530200727 36620674698023906295301091)
                ·
                  refine ⟨54931012047035859442951637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36620674698023906295301091 54931012047035859442951637)
                  ·
                    refine ⟨1287445594852402955694179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54931012047035859442951637 1287445594852402955694179)
                    ·
                      rfl

theorem cell23_7521874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_7521874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521874 prefixEnd_7521874 := by exact prefixLift 7521874
  have htrace : WordTrace (prefixWord ++ tailWord_7521874) baseStart_7521874 baseEnd_7521874 := by
    simpa [prefixWord, tailWord_7521874, baseEnd_7521874] using wordTrace_append hprefix tailTrace_7521874
  have hstable : (prefixWord ++ tailWord_7521874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521874).length < 2 ^ (prefixWord ++ tailWord_7521874).sum := by decide
  have hdescent : baseEnd_7521874 < baseStart_7521874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521897 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 2, 3, 5]
def baseStart_7521897 : Nat := 118140960795 + 7521897 * 2 ^ 59
def prefixEnd_7521897 : Nat := 4983230072969 + 3 ^ 40 * 7521897 * 2
def baseEnd_7521897 : Nat := 3862348594612262277094931

theorem tailTrace_7521897 : CollatzResearch.WordTrace tailWord_7521897 prefixEnd_7521897 3862348594612262277094931 := by
  unfold tailWord_7521897
  simp only [CollatzResearch.WordTrace]
  refine ⟨274346122030459281577475945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182897414686972854384983963 274346122030459281577475945)
  ·
    refine ⟨205759591522844461183106959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274346122030459281577475945 205759591522844461183106959)
    ·
      refine ⟨308639387284266691774660439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205759591522844461183106959 308639387284266691774660439)
      ·
        refine ⟨462959080926400037661990659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308639387284266691774660439 462959080926400037661990659)
        ·
          refine ⟨694438621389600056492985989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462959080926400037661990659 694438621389600056492985989)
          ·
            refine ⟨130207241510550010592434873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 694438621389600056492985989 130207241510550010592434873)
            ·
              refine ⟨97655431132912507944326155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130207241510550010592434873 97655431132912507944326155)
              ·
                refine ⟨146483146699368761916489233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97655431132912507944326155 146483146699368761916489233)
                ·
                  refine ⟨109862360024526571437366925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146483146699368761916489233 109862360024526571437366925)
                  ·
                    refine ⟨41198385009197464289012597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109862360024526571437366925 41198385009197464289012597)
                    ·
                      refine ⟨3862348594612262277094931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41198385009197464289012597 3862348594612262277094931)
                      ·
                        rfl

theorem cell23_7521897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_7521897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521897 prefixEnd_7521897 := by exact prefixLift 7521897
  have htrace : WordTrace (prefixWord ++ tailWord_7521897) baseStart_7521897 baseEnd_7521897 := by
    simpa [prefixWord, tailWord_7521897, baseEnd_7521897] using wordTrace_append hprefix tailTrace_7521897
  have hstable : (prefixWord ++ tailWord_7521897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521897).length < 2 ^ (prefixWord ++ tailWord_7521897).sum := by decide
  have hdescent : baseEnd_7521897 < baseStart_7521897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521914 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3]
def baseStart_7521914 : Nat := 118140960795 + 7521914 * 2 ^ 59
def prefixEnd_7521914 : Nat := 4983230072969 + 3 ^ 40 * 7521914 * 2
def baseEnd_7521914 : Nat := 3862357323783388710582353

theorem tailTrace_7521914 : CollatzResearch.WordTrace tailWord_7521914 prefixEnd_7521914 3862357323783388710582353 := by
  unfold tailWord_7521914
  simp only [CollatzResearch.WordTrace]
  refine ⟨68586685517849423370211199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182897828047598462320563197 68586685517849423370211199)
  ·
    refine ⟨102880028276774135055316799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68586685517849423370211199 102880028276774135055316799)
    ·
      refine ⟨154320042415161202582975199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102880028276774135055316799 154320042415161202582975199)
      ·
        refine ⟨231480063622741803874462799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154320042415161202582975199 231480063622741803874462799)
        ·
          refine ⟨347220095434112705811694199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231480063622741803874462799 347220095434112705811694199)
          ·
            refine ⟨520830143151169058717541299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347220095434112705811694199 520830143151169058717541299)
            ·
              refine ⟨781245214726753588076311949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520830143151169058717541299 781245214726753588076311949)
              ·
                refine ⟨292966955522532595528616981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 781245214726753588076311949 292966955522532595528616981)
                ·
                  refine ⟨13732826040118715415403921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 292966955522532595528616981 13732826040118715415403921)
                  ·
                    refine ⟨10299619530089036561552941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13732826040118715415403921 10299619530089036561552941)
                    ·
                      refine ⟨3862357323783388710582353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10299619530089036561552941 3862357323783388710582353)
                      ·
                        rfl

theorem cell23_7521914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_7521914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521914 prefixEnd_7521914 := by exact prefixLift 7521914
  have htrace : WordTrace (prefixWord ++ tailWord_7521914) baseStart_7521914 baseEnd_7521914 := by
    simpa [prefixWord, tailWord_7521914, baseEnd_7521914] using wordTrace_append hprefix tailTrace_7521914
  have hstable : (prefixWord ++ tailWord_7521914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521914).length < 2 ^ (prefixWord ++ tailWord_7521914).sum := by decide
  have hdescent : baseEnd_7521914 < baseStart_7521914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521921 : List Nat := [1, 2, 4, 2, 1, 2, 2, 2, 3, 4]
def baseStart_7521921 : Nat := 118140960795 + 7521921 * 2 ^ 59
def prefixEnd_7521921 : Nat := 4983230072969 + 3 ^ 40 * 7521921 * 2
def baseEnd_7521921 : Nat := 1287453639382656727731607

theorem tailTrace_7521921 : CollatzResearch.WordTrace tailWord_7521921 prefixEnd_7521921 1287453639382656727731607 := by
  unfold tailWord_7521921
  simp only [CollatzResearch.WordTrace]
  refine ⟨274346997382372333676349617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182897998254914889117566411 274346997382372333676349617)
  ·
    refine ⟨205760248036779250257262213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274346997382372333676349617 205760248036779250257262213)
    ·
      refine ⟨38580046506896109423236665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205760248036779250257262213 38580046506896109423236665)
      ·
        refine ⟨28935034880172082067427499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38580046506896109423236665 28935034880172082067427499)
        ·
          refine ⟨43402552320258123101141249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28935034880172082067427499 43402552320258123101141249)
          ·
            refine ⟨32551914240193592325855937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43402552320258123101141249 32551914240193592325855937)
            ·
              refine ⟨24413935680145194244391953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32551914240193592325855937 24413935680145194244391953)
              ·
                refine ⟨18310451760108895683293965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24413935680145194244391953 18310451760108895683293965)
                ·
                  refine ⟨6866419410040835881235237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18310451760108895683293965 6866419410040835881235237)
                  ·
                    refine ⟨1287453639382656727731607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6866419410040835881235237 1287453639382656727731607)
                    ·
                      rfl

theorem cell23_7521921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_7521921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521921 prefixEnd_7521921 := by exact prefixLift 7521921
  have htrace : WordTrace (prefixWord ++ tailWord_7521921) baseStart_7521921 baseEnd_7521921 := by
    simpa [prefixWord, tailWord_7521921, baseEnd_7521921] using wordTrace_append hprefix tailTrace_7521921
  have hstable : (prefixWord ++ tailWord_7521921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521921).length < 2 ^ (prefixWord ++ tailWord_7521921).sum := by decide
  have hdescent : baseEnd_7521921 < baseStart_7521921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521934 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 8]
def baseStart_7521934 : Nat := 118140960795 + 7521934 * 2 ^ 59
def prefixEnd_7521934 : Nat := 4983230072969 + 3 ^ 40 * 7521934 * 2
def baseEnd_7521934 : Nat := 429151954821830959148029

theorem tailTrace_7521934 : CollatzResearch.WordTrace tailWord_7521934 prefixEnd_7521934 429151954821830959148029 := by
  unfold tailWord_7521934
  simp only [CollatzResearch.WordTrace]
  refine ⟨34293433941415654612071607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182898314354216824597715237 34293433941415654612071607)
  ·
    refine ⟨51440150912123481918107411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34293433941415654612071607 51440150912123481918107411)
    ·
      refine ⟨77160226368185222877161117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51440150912123481918107411 77160226368185222877161117)
      ·
        refine ⟨28935084888069458578935419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77160226368185222877161117 28935084888069458578935419)
        ·
          refine ⟨43402627332104187868403129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28935084888069458578935419 43402627332104187868403129)
          ·
            refine ⟨32551970499078140901302347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43402627332104187868403129 32551970499078140901302347)
            ·
              refine ⟨48827955748617211351953521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32551970499078140901302347 48827955748617211351953521)
              ·
                refine ⟨36620966811462908513965141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48827955748617211351953521 36620966811462908513965141)
                ·
                  refine ⟨429151954821830959148029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36620966811462908513965141 429151954821830959148029)
                  ·
                    rfl

theorem cell23_7521934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_7521934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521934 prefixEnd_7521934 := by exact prefixLift 7521934
  have htrace : WordTrace (prefixWord ++ tailWord_7521934) baseStart_7521934 baseEnd_7521934 := by
    simpa [prefixWord, tailWord_7521934, baseEnd_7521934] using wordTrace_append hprefix tailTrace_7521934
  have hstable : (prefixWord ++ tailWord_7521934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521934).length < 2 ^ (prefixWord ++ tailWord_7521934).sum := by decide
  have hdescent : baseEnd_7521934 < baseStart_7521934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521937 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 8]
def baseStart_7521937 : Nat := 118140960795 + 7521937 * 2 ^ 59
def prefixEnd_7521937 : Nat := 4983230072969 + 3 ^ 40 * 7521937 * 2
def baseEnd_7521937 : Nat := 3862369133838442120594747

theorem tailTrace_7521937 : CollatzResearch.WordTrace tailWord_7521937 prefixEnd_7521937 3862369133838442120594747 := by
  unfold tailWord_7521937
  simp only [CollatzResearch.WordTrace]
  refine ⟨274347580950314368408932065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182898387300209578939288043 274347580950314368408932065)
  ·
    refine ⟨205760685712735776306699049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274347580950314368408932065 205760685712735776306699049)
    ·
      refine ⟨154320514284551832230024287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205760685712735776306699049 154320514284551832230024287)
      ·
        refine ⟨231480771426827748345036431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154320514284551832230024287 231480771426827748345036431)
        ·
          refine ⟨347221157140241622517554647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231480771426827748345036431 347221157140241622517554647)
          ·
            refine ⟨520831735710362433776331971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347221157140241622517554647 520831735710362433776331971)
            ·
              refine ⟨781247603565543650664497957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520831735710362433776331971 781247603565543650664497957)
              ·
                refine ⟨146483925668539434499593367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 781247603565543650664497957 146483925668539434499593367)
                ·
                  refine ⟨219725888502809151749390051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146483925668539434499593367 219725888502809151749390051)
                  ·
                    refine ⟨329588832754213727624085077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 219725888502809151749390051 329588832754213727624085077)
                    ·
                      refine ⟨3862369133838442120594747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 329588832754213727624085077 3862369133838442120594747)
                      ·
                        rfl

theorem cell23_7521937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_7521937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521937 prefixEnd_7521937 := by exact prefixLift 7521937
  have htrace : WordTrace (prefixWord ++ tailWord_7521937) baseStart_7521937 baseEnd_7521937 := by
    simpa [prefixWord, tailWord_7521937, baseEnd_7521937] using wordTrace_append hprefix tailTrace_7521937
  have hstable : (prefixWord ++ tailWord_7521937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521937).length < 2 ^ (prefixWord ++ tailWord_7521937).sum := by decide
  have hdescent : baseEnd_7521937 < baseStart_7521937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521948 : List Nat := [2, 2, 3, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_7521948 : Nat := 118140960795 + 7521948 * 2 ^ 59
def prefixEnd_7521948 : Nat := 4983230072969 + 3 ^ 40 * 7521948 * 2
def baseEnd_7521948 : Nat := 3862374782125641577557197

theorem tailTrace_7521948 : CollatzResearch.WordTrace tailWord_7521948 prefixEnd_7521948 3862374782125641577557197 := by
  unfold tailWord_7521948
  simp only [CollatzResearch.WordTrace]
  refine ⟨137173991076637258643791249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182898654768849678191721665 137173991076637258643791249)
  ·
    refine ⟨102880493307477943982843437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137173991076637258643791249 102880493307477943982843437)
    ·
      refine ⟨38580184990304228993566289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102880493307477943982843437 38580184990304228993566289)
      ·
        refine ⟨28935138742728171745174717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38580184990304228993566289 28935138742728171745174717)
        ·
          refine ⟨10850677028523064404440519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28935138742728171745174717 10850677028523064404440519)
          ·
            refine ⟨16276015542784596606660779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10850677028523064404440519 16276015542784596606660779)
            ·
              refine ⟨24414023314176894909991169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16276015542784596606660779 24414023314176894909991169)
              ·
                refine ⟨18310517485632671182493377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24414023314176894909991169 18310517485632671182493377)
                ·
                  refine ⟨13732888114224503386870033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18310517485632671182493377 13732888114224503386870033)
                  ·
                    refine ⟨10299666085668377540152525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13732888114224503386870033 10299666085668377540152525)
                    ·
                      refine ⟨3862374782125641577557197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10299666085668377540152525 3862374782125641577557197)
                      ·
                        rfl

theorem cell23_7521948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_7521948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521948 prefixEnd_7521948 := by exact prefixLift 7521948
  have htrace : WordTrace (prefixWord ++ tailWord_7521948) baseStart_7521948 baseEnd_7521948 := by
    simpa [prefixWord, tailWord_7521948, baseEnd_7521948] using wordTrace_append hprefix tailTrace_7521948
  have hstable : (prefixWord ++ tailWord_7521948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521948).length < 2 ^ (prefixWord ++ tailWord_7521948).sum := by decide
  have hdescent : baseEnd_7521948 < baseStart_7521948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521971 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 4, 3, 2]
def baseStart_7521971 : Nat := 118140960795 + 7521971 * 2 ^ 59
def prefixEnd_7521971 : Nat := 4983230072969 + 3 ^ 40 * 7521971 * 2
def baseEnd_7521971 : Nat := 3862386592180694987569591

theorem tailTrace_7521971 : CollatzResearch.WordTrace tailWord_7521971 prefixEnd_7521971 3862386592180694987569591 := by
  unfold tailWord_7521971
  simp only [CollatzResearch.WordTrace]
  refine ⟨274348821032191192215669767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182899214021460794810446511 274348821032191192215669767)
  ·
    refine ⟨411523231548286788323504651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274348821032191192215669767 411523231548286788323504651)
    ·
      refine ⟨617284847322430182485256977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411523231548286788323504651 617284847322430182485256977)
      ·
        refine ⟨462963635491822636863942733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617284847322430182485256977 462963635491822636863942733)
        ·
          refine ⟨173611363309433488823978525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462963635491822636863942733 173611363309433488823978525)
          ·
            refine ⟨65104261241037558308991947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173611363309433488823978525 65104261241037558308991947)
            ·
              refine ⟨97656391861556337463487921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65104261241037558308991947 97656391861556337463487921)
              ·
                refine ⟨73242293896167253097615941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97656391861556337463487921 73242293896167253097615941)
                ·
                  refine ⟨13732930105531359955802989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73242293896167253097615941 13732930105531359955802989)
                  ·
                    refine ⟨5149848789574259983426121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13732930105531359955802989 5149848789574259983426121)
                    ·
                      refine ⟨3862386592180694987569591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5149848789574259983426121 3862386592180694987569591)
                      ·
                        rfl

theorem cell23_7521971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 3, 2].length) (baseStart_7521971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521971 prefixEnd_7521971 := by exact prefixLift 7521971
  have htrace : WordTrace (prefixWord ++ tailWord_7521971) baseStart_7521971 baseEnd_7521971 := by
    simpa [prefixWord, tailWord_7521971, baseEnd_7521971] using wordTrace_append hprefix tailTrace_7521971
  have hstable : (prefixWord ++ tailWord_7521971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521971).length < 2 ^ (prefixWord ++ tailWord_7521971).sum := by decide
  have hdescent : baseEnd_7521971 < baseStart_7521971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7521998 : List Nat := [4, 1, 1, 1, 3, 1, 5, 1, 1, 5]
def baseStart_7521998 : Nat := 118140960795 + 7521998 * 2 ^ 59
def prefixEnd_7521998 : Nat := 4983230072969 + 3 ^ 40 * 7521998 * 2
def baseEnd_7521998 : Nat := 1287466818719455460643989

theorem tailTrace_7521998 : CollatzResearch.WordTrace tailWord_7521998 prefixEnd_7521998 1287466818719455460643989 := by
  unfold tailWord_7521998
  simp only [CollatzResearch.WordTrace]
  refine ⟨34293725725386671978362831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182899870535395583884601765 34293725725386671978362831)
  ·
    refine ⟨51440588588080007967544247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34293725725386671978362831 51440588588080007967544247)
    ·
      refine ⟨77160882882120011951316371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51440588588080007967544247 77160882882120011951316371)
      ·
        refine ⟨115741324323180017926974557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77160882882120011951316371 115741324323180017926974557)
        ·
          refine ⟨43402996621192506722615459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115741324323180017926974557 43402996621192506722615459)
          ·
            refine ⟨65104494931788760083923189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43402996621192506722615459 65104494931788760083923189)
            ·
              refine ⟨6103546399855196257867799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65104494931788760083923189 6103546399855196257867799)
              ·
                refine ⟨9155319599782794386801699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6103546399855196257867799 9155319599782794386801699)
                ·
                  refine ⟨13732979399674191580202549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9155319599782794386801699 13732979399674191580202549)
                  ·
                    refine ⟨1287466818719455460643989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13732979399674191580202549 1287466818719455460643989)
                    ·
                      rfl

theorem cell23_7521998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_7521998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7521998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7521998 prefixEnd_7521998 := by exact prefixLift 7521998
  have htrace : WordTrace (prefixWord ++ tailWord_7521998) baseStart_7521998 baseEnd_7521998 := by
    simpa [prefixWord, tailWord_7521998, baseEnd_7521998] using wordTrace_append hprefix tailTrace_7521998
  have hstable : (prefixWord ++ tailWord_7521998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7521998).length < 2 ^ (prefixWord ++ tailWord_7521998).sum := by decide
  have hdescent : baseEnd_7521998 < baseStart_7521998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7521998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522006 : List Nat := [5, 2, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_7522006 : Nat := 118140960795 + 7522006 * 2 ^ 59
def prefixEnd_7522006 : Nat := 4983230072969 + 3 ^ 40 * 7522006 * 2
def baseEnd_7522006 : Nat := 1287468188001200783543977

theorem tailTrace_7522006 : CollatzResearch.WordTrace tailWord_7522006 prefixEnd_7522006 1287468188001200783543977 := by
  unfold tailWord_7522006
  simp only [CollatzResearch.WordTrace]
  refine ⟨17146881099191524574574617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182900065058042928795462581 17146881099191524574574617)
  ·
    refine ⟨12860160824393643430930963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17146881099191524574574617 12860160824393643430930963)
    ·
      refine ⟨19290241236590465146396445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12860160824393643430930963 19290241236590465146396445)
      ·
        refine ⟨7233840463721424429898667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19290241236590465146396445 7233840463721424429898667)
        ·
          refine ⟨10850760695582136644848001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7233840463721424429898667 10850760695582136644848001)
          ·
            refine ⟨8138070521686602483636001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10850760695582136644848001 8138070521686602483636001)
            ·
              refine ⟨6103552891264951862727001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8138070521686602483636001 6103552891264951862727001)
              ·
                refine ⟨4577664668448713897045251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6103552891264951862727001 4577664668448713897045251)
                ·
                  refine ⟨6866497002673070845567877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577664668448713897045251 6866497002673070845567877)
                  ·
                    refine ⟨1287468188001200783543977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6866497002673070845567877 1287468188001200783543977)
                    ·
                      rfl

theorem cell23_7522006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_7522006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522006 prefixEnd_7522006 := by exact prefixLift 7522006
  have htrace : WordTrace (prefixWord ++ tailWord_7522006) baseStart_7522006 baseEnd_7522006 := by
    simpa [prefixWord, tailWord_7522006, baseEnd_7522006] using wordTrace_append hprefix tailTrace_7522006
  have hstable : (prefixWord ++ tailWord_7522006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522006).length < 2 ^ (prefixWord ++ tailWord_7522006).sum := by decide
  have hdescent : baseEnd_7522006 < baseStart_7522006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522021 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 5, 2, 3]
def baseStart_7522021 : Nat := 118140960795 + 7522021 * 2 ^ 59
def prefixEnd_7522021 : Nat := 4983230072969 + 3 ^ 40 * 7522021 * 2
def baseEnd_7522021 : Nat := 3862412266213419791944361

theorem tailTrace_7522021 : CollatzResearch.WordTrace tailWord_7522021 prefixEnd_7522021 3862412266213419791944361 := by
  unfold tailWord_7522021
  simp only [CollatzResearch.WordTrace]
  refine ⟨274350644682010050754989917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182900429788006700503326611 274350644682010050754989917)
  ·
    refine ⟨102881491755753769033121219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274350644682010050754989917 102881491755753769033121219)
    ·
      refine ⟨154322237633630653549681829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102881491755753769033121219 154322237633630653549681829)
      ·
        refine ⟨28935419556305747540565343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154322237633630653549681829 28935419556305747540565343)
        ·
          refine ⟨43403129334458621310848015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28935419556305747540565343 43403129334458621310848015)
          ·
            refine ⟨65104694001687931966272023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43403129334458621310848015 65104694001687931966272023)
            ·
              refine ⟨97657041002531897949408035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65104694001687931966272023 97657041002531897949408035)
              ·
                refine ⟨146485561503797846924112053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97657041002531897949408035 146485561503797846924112053)
                ·
                  refine ⟨13733021390981048149135505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146485561503797846924112053 13733021390981048149135505)
                  ·
                    refine ⟨10299766043235786111851629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13733021390981048149135505 10299766043235786111851629)
                    ·
                      refine ⟨3862412266213419791944361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10299766043235786111851629 3862412266213419791944361)
                      ·
                        rfl

theorem cell23_7522021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_7522021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522021 prefixEnd_7522021 := by exact prefixLift 7522021
  have htrace : WordTrace (prefixWord ++ tailWord_7522021) baseStart_7522021 baseEnd_7522021 := by
    simpa [prefixWord, tailWord_7522021, baseEnd_7522021] using wordTrace_append hprefix tailTrace_7522021
  have hstable : (prefixWord ++ tailWord_7522021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522021).length < 2 ^ (prefixWord ++ tailWord_7522021).sum := by decide
  have hdescent : baseEnd_7522021 < baseStart_7522021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522031 : List Nat := [1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 4]
def baseStart_7522031 : Nat := 118140960795 + 7522031 * 2 ^ 59
def prefixEnd_7522031 : Nat := 4983230072969 + 3 ^ 40 * 7522031 * 2
def baseEnd_7522031 : Nat := 3862417401019964752819315

theorem tailTrace_7522031 : CollatzResearch.WordTrace tailWord_7522031 prefixEnd_7522031 3862417401019964752819315 := by
  unfold tailWord_7522031
  simp only [CollatzResearch.WordTrace]
  refine ⟨274351009411973822462853947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182900672941315881641902631 274351009411973822462853947)
  ·
    refine ⟨411526514117960733694280921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274351009411973822462853947 411526514117960733694280921)
    ·
      refine ⟨308644885588470550270710691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411526514117960733694280921 308644885588470550270710691)
      ·
        refine ⟨462967328382705825406066037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308644885588470550270710691 462967328382705825406066037)
        ·
          refine ⟨43403187035878671131818691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 462967328382705825406066037 43403187035878671131818691)
          ·
            refine ⟨65104780553818006697728037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43403187035878671131818691 65104780553818006697728037)
            ·
              refine ⟨12207146353840876255824007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65104780553818006697728037 12207146353840876255824007)
              ·
                refine ⟨18310719530761314383736011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12207146353840876255824007 18310719530761314383736011)
                ·
                  refine ⟨27466079296141971575604017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18310719530761314383736011 27466079296141971575604017)
                  ·
                    refine ⟨20599559472106478681703013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27466079296141971575604017 20599559472106478681703013)
                    ·
                      refine ⟨3862417401019964752819315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20599559472106478681703013 3862417401019964752819315)
                      ·
                        rfl

theorem cell23_7522031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 4].length) (baseStart_7522031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522031 prefixEnd_7522031 := by exact prefixLift 7522031
  have htrace : WordTrace (prefixWord ++ tailWord_7522031) baseStart_7522031 baseEnd_7522031 := by
    simpa [prefixWord, tailWord_7522031, baseEnd_7522031] using wordTrace_append hprefix tailTrace_7522031
  have hstable : (prefixWord ++ tailWord_7522031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522031).length < 2 ^ (prefixWord ++ tailWord_7522031).sum := by decide
  have hdescent : baseEnd_7522031 < baseStart_7522031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522038 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_7522038 : Nat := 118140960795 + 7522038 * 2 ^ 59
def prefixEnd_7522038 : Nat := 4983230072969 + 3 ^ 40 * 7522038 * 2
def baseEnd_7522038 : Nat := 3862420995384546225431783

theorem tailTrace_7522038 : CollatzResearch.WordTrace tailWord_7522038 prefixEnd_7522038 3862420995384546225431783 := by
  unfold tailWord_7522038
  simp only [CollatzResearch.WordTrace]
  refine ⟨17146954045184278916147423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182900843148632308438905845 17146954045184278916147423)
  ·
    refine ⟨25720431067776418374221135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17146954045184278916147423 25720431067776418374221135)
    ·
      refine ⟨38580646601664627561331703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25720431067776418374221135 38580646601664627561331703)
      ·
        refine ⟨57870969902496941341997555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38580646601664627561331703 57870969902496941341997555)
        ·
          refine ⟨86806454853745412012996333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57870969902496941341997555 86806454853745412012996333)
          ·
            refine ⟨32552420570154529504873625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86806454853745412012996333 32552420570154529504873625)
            ·
              refine ⟨24414315427615897128655219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32552420570154529504873625 24414315427615897128655219)
              ·
                refine ⟨36621473141423845692982829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24414315427615897128655219 36621473141423845692982829)
                ·
                  refine ⟨13733052428033942134868561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36621473141423845692982829 13733052428033942134868561)
                  ·
                    refine ⟨10299789321025456601151421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13733052428033942134868561 10299789321025456601151421)
                    ·
                      refine ⟨3862420995384546225431783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10299789321025456601151421 3862420995384546225431783)
                      ·
                        rfl

theorem cell23_7522038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_7522038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522038 prefixEnd_7522038 := by exact prefixLift 7522038
  have htrace : WordTrace (prefixWord ++ tailWord_7522038) baseStart_7522038 baseEnd_7522038 := by
    simpa [prefixWord, tailWord_7522038, baseEnd_7522038] using wordTrace_append hprefix tailTrace_7522038
  have hstable : (prefixWord ++ tailWord_7522038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522038).length < 2 ^ (prefixWord ++ tailWord_7522038).sum := by decide
  have hdescent : baseEnd_7522038 < baseStart_7522038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522051 : List Nat := [1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 3]
def baseStart_7522051 : Nat := 118140960795 + 7522051 * 2 ^ 59
def prefixEnd_7522051 : Nat := 4983230072969 + 3 ^ 40 * 7522051 * 2
def baseEnd_7522051 : Nat := 3862427670633054674569223

theorem tailTrace_7522051 : CollatzResearch.WordTrace tailWord_7522051 prefixEnd_7522051 3862427670633054674569223 := by
  unfold tailWord_7522051
  simp only [CollatzResearch.WordTrace]
  refine ⟨274351738871901365878582007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182901159247934243919054671 274351738871901365878582007)
  ·
    refine ⟨411527608307852048817873011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274351738871901365878582007 411527608307852048817873011)
    ·
      refine ⟨617291412461778073226809517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411527608307852048817873011 617291412461778073226809517)
      ·
        refine ⟨231484279673166777460053569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 617291412461778073226809517 231484279673166777460053569)
        ·
          refine ⟨173613209754875083095040177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231484279673166777460053569 173613209754875083095040177)
          ·
            refine ⟨130209907316156312321280133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173613209754875083095040177 130209907316156312321280133)
            ·
              refine ⟨24414357621779308560240025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130209907316156312321280133 24414357621779308560240025)
              ·
                refine ⟨18310768216334481420180019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24414357621779308560240025 18310768216334481420180019)
                ·
                  refine ⟨27466152324501722130270029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18310768216334481420180019 27466152324501722130270029)
                  ·
                    refine ⟨10299807121688145798851261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27466152324501722130270029 10299807121688145798851261)
                    ·
                      refine ⟨3862427670633054674569223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10299807121688145798851261 3862427670633054674569223)
                      ·
                        rfl

theorem cell23_7522051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_7522051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522051 prefixEnd_7522051 := by exact prefixLift 7522051
  have htrace : WordTrace (prefixWord ++ tailWord_7522051) baseStart_7522051 baseEnd_7522051 := by
    simpa [prefixWord, tailWord_7522051, baseEnd_7522051] using wordTrace_append hprefix tailTrace_7522051
  have hstable : (prefixWord ++ tailWord_7522051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522051).length < 2 ^ (prefixWord ++ tailWord_7522051).sum := by decide
  have hdescent : baseEnd_7522051 < baseStart_7522051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522052 : List Nat := [2, 3, 2, 2, 1, 2, 1, 5, 1, 2, 2]
def baseStart_7522052 : Nat := 118140960795 + 7522052 * 2 ^ 59
def prefixEnd_7522052 : Nat := 4983230072969 + 3 ^ 40 * 7522052 * 2
def baseEnd_7522052 : Nat := 3862428184113709170656719

theorem tailTrace_7522052 : CollatzResearch.WordTrace tailWord_7522052 prefixEnd_7522052 3862428184113709170656719 := by
  unfold tailWord_7522052
  simp only [CollatzResearch.WordTrace]
  refine ⟨137175887672448871524684205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182901183563265162032912273 137175887672448871524684205)
  ·
    refine ⟨51440957877168326821756577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137175887672448871524684205 51440957877168326821756577)
    ·
      refine ⟨38580718407876245116317433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51440957877168326821756577 38580718407876245116317433)
      ·
        refine ⟨28935538805907183837238075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38580718407876245116317433 28935538805907183837238075)
        ·
          refine ⟨43403308208860775755857113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28935538805907183837238075 43403308208860775755857113)
          ·
            refine ⟨32552481156645581816892835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43403308208860775755857113 32552481156645581816892835)
            ·
              refine ⟨48828721734968372725339253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32552481156645581816892835 48828721734968372725339253)
              ·
                refine ⟨4577692662653284943000555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48828721734968372725339253 4577692662653284943000555)
                ·
                  refine ⟨6866538993979927414500833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577692662653284943000555 6866538993979927414500833)
                  ·
                    refine ⟨5149904245484945560875625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6866538993979927414500833 5149904245484945560875625)
                    ·
                      refine ⟨3862428184113709170656719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5149904245484945560875625 3862428184113709170656719)
                      ·
                        rfl

theorem cell23_7522052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_7522052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522052 prefixEnd_7522052 := by exact prefixLift 7522052
  have htrace : WordTrace (prefixWord ++ tailWord_7522052) baseStart_7522052 baseEnd_7522052 := by
    simpa [prefixWord, tailWord_7522052, baseEnd_7522052] using wordTrace_append hprefix tailTrace_7522052
  have hstable : (prefixWord ++ tailWord_7522052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522052).length < 2 ^ (prefixWord ++ tailWord_7522052).sum := by decide
  have hdescent : baseEnd_7522052 < baseStart_7522052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522055 : List Nat := [1, 1, 4, 4, 2, 1, 1, 3, 1, 2, 3]
def baseStart_7522055 : Nat := 118140960795 + 7522055 * 2 ^ 59
def prefixEnd_7522055 : Nat := 4983230072969 + 3 ^ 40 * 7522055 * 2
def baseEnd_7522055 : Nat := 3862429724555672658919205

theorem tailTrace_7522055 : CollatzResearch.WordTrace tailWord_7522055 prefixEnd_7522055 3862429724555672658919205 := by
  unfold tailWord_7522055
  simp only [CollatzResearch.WordTrace]
  refine ⟨274351884763886874561727619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182901256509257916374485079 274351884763886874561727619)
  ·
    refine ⟨411527827145830311842591429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274351884763886874561727619 411527827145830311842591429)
    ·
      refine ⟨77161467589843183470485893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 411527827145830311842591429 77161467589843183470485893)
      ·
        refine ⟨14467775173095596900716105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77161467589843183470485893 14467775173095596900716105)
        ·
          refine ⟨10850831379821697675537079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14467775173095596900716105 10850831379821697675537079)
          ·
            refine ⟨16276247069732546513305619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10850831379821697675537079 16276247069732546513305619)
            ·
              refine ⟨24414370604598819769958429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16276247069732546513305619 24414370604598819769958429)
              ·
                refine ⟨9155388976724557413734411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24414370604598819769958429 9155388976724557413734411)
                ·
                  refine ⟨13733083465086836120601617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9155388976724557413734411 13733083465086836120601617)
                  ·
                    refine ⟨10299812598815127090451213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13733083465086836120601617 10299812598815127090451213)
                    ·
                      refine ⟨3862429724555672658919205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10299812598815127090451213 3862429724555672658919205)
                      ·
                        rfl

theorem cell23_7522055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_7522055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522055 prefixEnd_7522055 := by exact prefixLift 7522055
  have htrace : WordTrace (prefixWord ++ tailWord_7522055) baseStart_7522055 baseEnd_7522055 := by
    simpa [prefixWord, tailWord_7522055, baseEnd_7522055] using wordTrace_append hprefix tailTrace_7522055
  have hstable : (prefixWord ++ tailWord_7522055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522055).length < 2 ^ (prefixWord ++ tailWord_7522055).sum := by decide
  have hdescent : baseEnd_7522055 < baseStart_7522055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522108 : List Nat := [2, 2, 2, 2, 1, 1, 2, 4, 1, 4, 2]
def baseStart_7522108 : Nat := 118140960795 + 7522108 * 2 ^ 59
def prefixEnd_7522108 : Nat := 4983230072969 + 3 ^ 40 * 7522108 * 2
def baseEnd_7522108 : Nat := 3862456939030360951556461

theorem tailTrace_7522108 : CollatzResearch.WordTrace tailWord_7522108 prefixEnd_7522108 3862456939030360951556461 := by
  unfold tailWord_7522108
  simp only [CollatzResearch.WordTrace]
  refine ⟨137176908916347432306703489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182902545221796576408937985 137176908916347432306703489)
  ·
    refine ⟨102882681687260574230027617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137176908916347432306703489 102882681687260574230027617)
    ·
      refine ⟨77162011265445430672520713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102882681687260574230027617 77162011265445430672520713)
      ·
        refine ⟨57871508449084073004390535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77162011265445430672520713 57871508449084073004390535)
        ·
          refine ⟨86807262673626109506585803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57871508449084073004390535 86807262673626109506585803)
          ·
            refine ⟨130210894010439164259878705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86807262673626109506585803 130210894010439164259878705)
            ·
              refine ⟨97658170507829373194909029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130210894010439164259878705 97658170507829373194909029)
              ·
                refine ⟨18310906970218007474045443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97658170507829373194909029 18310906970218007474045443)
                ·
                  refine ⟨27466360455327011211068165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18310906970218007474045443 27466360455327011211068165)
                  ·
                    refine ⟨5149942585373814602075281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27466360455327011211068165 5149942585373814602075281)
                    ·
                      refine ⟨3862456939030360951556461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5149942585373814602075281 3862456939030360951556461)
                      ·
                        rfl

theorem cell23_7522108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_7522108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522108 prefixEnd_7522108 := by exact prefixLift 7522108
  have htrace : WordTrace (prefixWord ++ tailWord_7522108) baseStart_7522108 baseEnd_7522108 := by
    simpa [prefixWord, tailWord_7522108, baseEnd_7522108] using wordTrace_append hprefix tailTrace_7522108
  have hstable : (prefixWord ++ tailWord_7522108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522108).length < 2 ^ (prefixWord ++ tailWord_7522108).sum := by decide
  have hdescent : baseEnd_7522108 < baseStart_7522108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522215 : List Nat := [1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_7522215 : Nat := 118140960795 + 7522215 * 2 ^ 59
def prefixEnd_7522215 : Nat := 4983230072969 + 3 ^ 40 * 7522215 * 2
def baseEnd_7522215 : Nat := 3862511881460392032918469

theorem tailTrace_7522215 : CollatzResearch.WordTrace tailWord_7522215 prefixEnd_7522215 3862511881460392032918469 := by
  unfold tailWord_7522215
  simp only [CollatzResearch.WordTrace]
  refine ⟨274357720443307221887552099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182905146962204814591701399 274357720443307221887552099)
  ·
    refine ⟨411536580664960832831328149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274357720443307221887552099 411536580664960832831328149)
    ·
      refine ⟨19290777218670039038968507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 411536580664960832831328149 19290777218670039038968507)
      ·
        refine ⟨28936165828005058558452761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19290777218670039038968507 28936165828005058558452761)
        ·
          refine ⟨21702124371003793918839571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28936165828005058558452761 21702124371003793918839571)
          ·
            refine ⟨32553186556505690878259357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21702124371003793918839571 32553186556505690878259357)
            ·
              refine ⟨12207444958689634079347259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32553186556505690878259357 12207444958689634079347259)
              ·
                refine ⟨18311167438034451119020889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12207444958689634079347259 18311167438034451119020889)
                ·
                  refine ⟨13733375578525838339265667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18311167438034451119020889 13733375578525838339265667)
                  ·
                    refine ⟨20600063367788757508898501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13733375578525838339265667 20600063367788757508898501)
                    ·
                      refine ⟨3862511881460392032918469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20600063367788757508898501 3862511881460392032918469)
                      ·
                        rfl

theorem cell23_7522215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_7522215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522215 prefixEnd_7522215 := by exact prefixLift 7522215
  have htrace : WordTrace (prefixWord ++ tailWord_7522215) baseStart_7522215 baseEnd_7522215 := by
    simpa [prefixWord, tailWord_7522215, baseEnd_7522215] using wordTrace_append hprefix tailTrace_7522215
  have hstable : (prefixWord ++ tailWord_7522215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522215).length < 2 ^ (prefixWord ++ tailWord_7522215).sum := by decide
  have hdescent : baseEnd_7522215 < baseStart_7522215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522238 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 8]
def baseStart_7522238 : Nat := 118140960795 + 7522238 * 2 ^ 59
def prefixEnd_7522238 : Nat := 4983230072969 + 3 ^ 40 * 7522238 * 2
def baseEnd_7522238 : Nat := 429169299057271715881207

theorem tailTrace_7522238 : CollatzResearch.WordTrace tailWord_7522238 prefixEnd_7522238 429169299057271715881207 := by
  unfold tailWord_7522238
  simp only [CollatzResearch.WordTrace]
  refine ⟨34294819915277987101954921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182905706214815931210426245 34294819915277987101954921)
  ·
    refine ⟨25721114936458490326466191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34294819915277987101954921 25721114936458490326466191)
    ·
      refine ⟨38581672404687735489699287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25721114936458490326466191 38581672404687735489699287)
      ·
        refine ⟨57872508607031603234548931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38581672404687735489699287 57872508607031603234548931)
        ·
          refine ⟨86808762910547404851823397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57872508607031603234548931 86808762910547404851823397)
          ·
            refine ⟨16276643045727638409716887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86808762910547404851823397 16276643045727638409716887)
            ·
              refine ⟨24414964568591457614575331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16276643045727638409716887 24414964568591457614575331)
              ·
                refine ⟨36622446852887186421862997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24414964568591457614575331 36622446852887186421862997)
                ·
                  refine ⟨429169299057271715881207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36622446852887186421862997 429169299057271715881207)
                  ·
                    rfl

theorem cell23_7522238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_7522238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522238 prefixEnd_7522238 := by exact prefixLift 7522238
  have htrace : WordTrace (prefixWord ++ tailWord_7522238) baseStart_7522238 baseEnd_7522238 := by
    simpa [prefixWord, tailWord_7522238, baseEnd_7522238] using wordTrace_append hprefix tailTrace_7522238
  have hstable : (prefixWord ++ tailWord_7522238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522238).length < 2 ^ (prefixWord ++ tailWord_7522238).sum := by decide
  have hdescent : baseEnd_7522238 < baseStart_7522238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522275 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 1, 5, 2]
def baseStart_7522275 : Nat := 118140960795 + 7522275 * 2 ^ 59
def prefixEnd_7522275 : Nat := 4983230072969 + 3 ^ 40 * 7522275 * 2
def baseEnd_7522275 : Nat := 3862542690299661798168193

theorem tailTrace_7522275 : CollatzResearch.WordTrace tailWord_7522275 prefixEnd_7522275 3862542690299661798168193 := by
  unfold tailWord_7522275
  simp only [CollatzResearch.WordTrace]
  refine ⟨274359908823089852134736279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182906605882059901423157519 274359908823089852134736279)
  ·
    refine ⟨411539863234634778202104419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274359908823089852134736279 411539863234634778202104419)
    ·
      refine ⟨617309794851952167303156629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411539863234634778202104419 617309794851952167303156629)
      ·
        refine ⟨28936396633685257842335467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 617309794851952167303156629 28936396633685257842335467)
        ·
          refine ⟨43404594950527886763503201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28936396633685257842335467 43404594950527886763503201)
          ·
            refine ⟨32553446212895915072627401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43404594950527886763503201 32553446212895915072627401)
            ·
              refine ⟨24415084659671936304470551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32553446212895915072627401 24415084659671936304470551)
              ·
                refine ⟨36622626989507904456705827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24415084659671936304470551 36622626989507904456705827)
                ·
                  refine ⟨54933940484261856685058741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36622626989507904456705827 54933940484261856685058741)
                  ·
                    refine ⟨5150056920399549064224257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54933940484261856685058741 5150056920399549064224257)
                    ·
                      refine ⟨3862542690299661798168193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5150056920399549064224257 3862542690299661798168193)
                      ·
                        rfl

theorem cell23_7522275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_7522275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522275 prefixEnd_7522275 := by exact prefixLift 7522275
  have htrace : WordTrace (prefixWord ++ tailWord_7522275) baseStart_7522275 baseEnd_7522275 := by
    simpa [prefixWord, tailWord_7522275, baseEnd_7522275] using wordTrace_append hprefix tailTrace_7522275
  have hstable : (prefixWord ++ tailWord_7522275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522275).length < 2 ^ (prefixWord ++ tailWord_7522275).sum := by decide
  have hdescent : baseEnd_7522275 < baseStart_7522275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522315 : List Nat := [1, 1, 1, 1, 6, 1, 3, 3, 2, 4]
def baseStart_7522315 : Nat := 118140960795 + 7522315 * 2 ^ 59
def prefixEnd_7522315 : Nat := 4983230072969 + 3 ^ 40 * 7522315 * 2
def baseEnd_7522315 : Nat := 1287521076508613880556003

theorem tailTrace_7522315 : CollatzResearch.WordTrace tailWord_7522315 prefixEnd_7522315 1287521076508613880556003 := by
  unfold tailWord_7522315
  simp only [CollatzResearch.WordTrace]
  refine ⟨274361367742944938966192399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182907578495296625977461599 274361367742944938966192399)
  ·
    refine ⟨411542051614417408449288599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274361367742944938966192399 411542051614417408449288599)
    ·
      refine ⟨617313077421626112673932899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411542051614417408449288599 617313077421626112673932899)
      ·
        refine ⟨925969616132439169010899349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617313077421626112673932899 925969616132439169010899349)
        ·
          refine ⟨43404825756208086047385907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 925969616132439169010899349 43404825756208086047385907)
          ·
            refine ⟨65107238634312129071078861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43404825756208086047385907 65107238634312129071078861)
            ·
              refine ⟨24415214487867048401654573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65107238634312129071078861 24415214487867048401654573)
              ·
                refine ⟨9155705432950143150620465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24415214487867048401654573 9155705432950143150620465)
                ·
                  refine ⟨6866779074712607362965349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9155705432950143150620465 6866779074712607362965349)
                  ·
                    refine ⟨1287521076508613880556003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6866779074712607362965349 1287521076508613880556003)
                    ·
                      rfl

theorem cell23_7522315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 4].length) (baseStart_7522315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522315 prefixEnd_7522315 := by exact prefixLift 7522315
  have htrace : WordTrace (prefixWord ++ tailWord_7522315) baseStart_7522315 baseEnd_7522315 := by
    simpa [prefixWord, tailWord_7522315, baseEnd_7522315] using wordTrace_append hprefix tailTrace_7522315
  have hstable : (prefixWord ++ tailWord_7522315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522315).length < 2 ^ (prefixWord ++ tailWord_7522315).sum := by decide
  have hdescent : baseEnd_7522315 < baseStart_7522315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522318 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_7522318 : Nat := 118140960795 + 7522318 * 2 ^ 59
def prefixEnd_7522318 : Nat := 4983230072969 + 3 ^ 40 * 7522318 * 2
def baseEnd_7522318 : Nat := 3862564769967805129930495

theorem tailTrace_7522318 : CollatzResearch.WordTrace tailWord_7522318 prefixEnd_7522318 3862564769967805129930495 := by
  unfold tailWord_7522318
  simp only [CollatzResearch.WordTrace]
  refine ⟨34295184645241758809818951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182907651441289380319034405 34295184645241758809818951)
  ·
    refine ⟨51442776967862638214728427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34295184645241758809818951 51442776967862638214728427)
    ·
      refine ⟨77164165451793957322092641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51442776967862638214728427 77164165451793957322092641)
      ·
        refine ⟨57873124088845467991569481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77164165451793957322092641 57873124088845467991569481)
        ·
          refine ⟨43404843066634100993677111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57873124088845467991569481 43404843066634100993677111)
          ·
            refine ⟨65107264599951151490515667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43404843066634100993677111 65107264599951151490515667)
            ·
              refine ⟨97660896899926727235773501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65107264599951151490515667 97660896899926727235773501)
              ·
                refine ⟨36622836337472522713415063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97660896899926727235773501 36622836337472522713415063)
                ·
                  refine ⟨54934254506208784070122595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36622836337472522713415063 54934254506208784070122595)
                  ·
                    refine ⟨82401381759313176105183893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54934254506208784070122595 82401381759313176105183893)
                    ·
                      refine ⟨3862564769967805129930495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82401381759313176105183893 3862564769967805129930495)
                      ·
                        rfl

theorem cell23_7522318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_7522318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522318 prefixEnd_7522318 := by exact prefixLift 7522318
  have htrace : WordTrace (prefixWord ++ tailWord_7522318) baseStart_7522318 baseEnd_7522318 := by
    simpa [prefixWord, tailWord_7522318, baseEnd_7522318] using wordTrace_append hprefix tailTrace_7522318
  have hstable : (prefixWord ++ tailWord_7522318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522318).length < 2 ^ (prefixWord ++ tailWord_7522318).sum := by decide
  have hdescent : baseEnd_7522318 < baseStart_7522318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522339 : List Nat := [1, 1, 1, 4, 3, 1, 2, 5, 1, 2, 2]
def baseStart_7522339 : Nat := 118140960795 + 7522339 * 2 ^ 59
def prefixEnd_7522339 : Nat := 4983230072969 + 3 ^ 40 * 7522339 * 2
def baseEnd_7522339 : Nat := 3862575553061549547767899

theorem tailTrace_7522339 : CollatzResearch.WordTrace tailWord_7522339 prefixEnd_7522339 3862575553061549547767899 := by
  unfold tailWord_7522339
  simp only [CollatzResearch.WordTrace]
  refine ⟨274362243094857991065066071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182908162063238660710044047 274362243094857991065066071)
  ·
    refine ⟨411543364642286986597599107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274362243094857991065066071 411543364642286986597599107)
    ·
      refine ⟨617315046963430479896398661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411543364642286986597599107 617315046963430479896398661)
      ·
        refine ⟨115746571305643214980574749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 617315046963430479896398661 115746571305643214980574749)
        ·
          refine ⟨43404964239616205617715531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115746571305643214980574749 43404964239616205617715531)
          ·
            refine ⟨65107446359424308426573297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43404964239616205617715531 65107446359424308426573297)
            ·
              refine ⟨48830584769568231319929973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65107446359424308426573297 48830584769568231319929973)
              ·
                refine ⟨4577867322147021686243435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48830584769568231319929973 4577867322147021686243435)
                ·
                  refine ⟨6866800983220532529365153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577867322147021686243435 6866800983220532529365153)
                  ·
                    refine ⟨5150100737415399397023865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6866800983220532529365153 5150100737415399397023865)
                    ·
                      refine ⟨3862575553061549547767899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5150100737415399397023865 3862575553061549547767899)
                      ·
                        rfl

theorem cell23_7522339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_7522339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522339 prefixEnd_7522339 := by exact prefixLift 7522339
  have htrace : WordTrace (prefixWord ++ tailWord_7522339) baseStart_7522339 baseEnd_7522339 := by
    simpa [prefixWord, tailWord_7522339, baseEnd_7522339] using wordTrace_append hprefix tailTrace_7522339
  have hstable : (prefixWord ++ tailWord_7522339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522339).length < 2 ^ (prefixWord ++ tailWord_7522339).sum := by decide
  have hdescent : baseEnd_7522339 < baseStart_7522339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522355 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 4, 1, 3]
def baseStart_7522355 : Nat := 118140960795 + 7522355 * 2 ^ 59
def prefixEnd_7522355 : Nat := 4983230072969 + 3 ^ 40 * 7522355 * 2
def baseEnd_7522355 : Nat := 3862583768752021485167825

theorem tailTrace_7522355 : CollatzResearch.WordTrace tailWord_7522355 prefixEnd_7522355 3862583768752021485167825 := by
  unfold tailWord_7522355
  simp only [CollatzResearch.WordTrace]
  refine ⟨274362826662800025797648519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182908551108533350531765679 274362826662800025797648519)
  ·
    refine ⟨411544239994200038696472779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274362826662800025797648519 411544239994200038696472779)
    ·
      refine ⟨617316359991300058044709169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411544239994200038696472779 617316359991300058044709169)
      ·
        refine ⟨462987269993475043533531877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617316359991300058044709169 462987269993475043533531877)
        ·
          refine ⟨86810113123776570662537227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 462987269993475043533531877 86810113123776570662537227)
          ·
            refine ⟨130215169685664855993805841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86810113123776570662537227 130215169685664855993805841)
            ·
              refine ⟨97661377264248641995354381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130215169685664855993805841 97661377264248641995354381)
              ·
                refine ⟨36623016474093240748257893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97661377264248641995354381 36623016474093240748257893)
                ·
                  refine ⟨6866815588892482640298355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36623016474093240748257893 6866815588892482640298355)
                  ·
                    refine ⟨10300223383338723960447533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6866815588892482640298355 10300223383338723960447533)
                    ·
                      refine ⟨3862583768752021485167825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10300223383338723960447533 3862583768752021485167825)
                      ·
                        rfl

theorem cell23_7522355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 1, 3].length) (baseStart_7522355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522355 prefixEnd_7522355 := by exact prefixLift 7522355
  have htrace : WordTrace (prefixWord ++ tailWord_7522355) baseStart_7522355 baseEnd_7522355 := by
    simpa [prefixWord, tailWord_7522355, baseEnd_7522355] using wordTrace_append hprefix tailTrace_7522355
  have hstable : (prefixWord ++ tailWord_7522355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522355).length < 2 ^ (prefixWord ++ tailWord_7522355).sum := by decide
  have hdescent : baseEnd_7522355 < baseStart_7522355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522378 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_7522378 : Nat := 118140960795 + 7522378 * 2 ^ 59
def prefixEnd_7522378 : Nat := 4983230072969 + 3 ^ 40 * 7522378 * 2
def baseEnd_7522378 : Nat := 3862595578807074895180219

theorem tailTrace_7522378 : CollatzResearch.WordTrace tailWord_7522378 prefixEnd_7522378 3862595578807074895180219 := by
  unfold tailWord_7522378
  simp only [CollatzResearch.WordTrace]
  refine ⟨68590916385429175181433947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182909110361144467150490525 68590916385429175181433947)
  ·
    refine ⟨102886374578143762772150921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68590916385429175181433947 102886374578143762772150921)
    ·
      refine ⟨77164780933607822079113191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102886374578143762772150921 77164780933607822079113191)
      ·
        refine ⟨115747171400411733118669787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77164780933607822079113191 115747171400411733118669787)
        ·
          refine ⟨173620757100617599678004681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115747171400411733118669787 173620757100617599678004681)
          ·
            refine ⟨130215567825463199758503511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173620757100617599678004681 130215567825463199758503511)
            ·
              refine ⟨195323351738194799637755267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130215567825463199758503511 195323351738194799637755267)
              ·
                refine ⟨292985027607292199456632901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195323351738194799637755267 292985027607292199456632901)
                ·
                  refine ⟨54934692676367287398118669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 292985027607292199456632901 54934692676367287398118669)
                  ·
                    refine ⟨20600509753637732774294501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54934692676367287398118669 20600509753637732774294501)
                    ·
                      refine ⟨3862595578807074895180219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20600509753637732774294501 3862595578807074895180219)
                      ·
                        rfl

theorem cell23_7522378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_7522378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522378 prefixEnd_7522378 := by exact prefixLift 7522378
  have htrace : WordTrace (prefixWord ++ tailWord_7522378) baseStart_7522378 baseEnd_7522378 := by
    simpa [prefixWord, tailWord_7522378, baseEnd_7522378] using wordTrace_append hprefix tailTrace_7522378
  have hstable : (prefixWord ++ tailWord_7522378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522378).length < 2 ^ (prefixWord ++ tailWord_7522378).sum := by decide
  have hdescent : baseEnd_7522378 < baseStart_7522378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522382 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2]
def baseStart_7522382 : Nat := 118140960795 + 7522382 * 2 ^ 59
def prefixEnd_7522382 : Nat := 4983230072969 + 3 ^ 40 * 7522382 * 2
def baseEnd_7522382 : Nat := 3862597632729692879530201

theorem tailTrace_7522382 : CollatzResearch.WordTrace tailWord_7522382 prefixEnd_7522382 3862597632729692879530201 := by
  unfold tailWord_7522382
  simp only [CollatzResearch.WordTrace]
  refine ⟨34295476429212776176110175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182909207622468139605920933 34295476429212776176110175)
  ·
    refine ⟨51443214643819164264165263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34295476429212776176110175 51443214643819164264165263)
    ·
      refine ⟨77164821965728746396247895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51443214643819164264165263 77164821965728746396247895)
      ·
        refine ⟨115747232948593119594371843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77164821965728746396247895 115747232948593119594371843)
        ·
          refine ⟨173620849422889679391557765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115747232948593119594371843 173620849422889679391557765)
          ·
            refine ⟨32553909266791814885917081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173620849422889679391557765 32553909266791814885917081)
            ·
              refine ⟨24415431950093861164437811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32553909266791814885917081 24415431950093861164437811)
              ·
                refine ⟨36623147925140791746656717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24415431950093861164437811 36623147925140791746656717)
                ·
                  refine ⟨13733680471927796904996269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36623147925140791746656717 13733680471927796904996269)
                  ·
                    refine ⟨5150130176972923839373601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13733680471927796904996269 5150130176972923839373601)
                    ·
                      refine ⟨3862597632729692879530201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5150130176972923839373601 3862597632729692879530201)
                      ·
                        rfl

theorem cell23_7522382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_7522382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522382 prefixEnd_7522382 := by exact prefixLift 7522382
  have htrace : WordTrace (prefixWord ++ tailWord_7522382) baseStart_7522382 baseEnd_7522382 := by
    simpa [prefixWord, tailWord_7522382, baseEnd_7522382] using wordTrace_append hprefix tailTrace_7522382
  have hstable : (prefixWord ++ tailWord_7522382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522382).length < 2 ^ (prefixWord ++ tailWord_7522382).sum := by decide
  have hdescent : baseEnd_7522382 < baseStart_7522382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522388 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_7522388 : Nat := 118140960795 + 7522388 * 2 ^ 59
def prefixEnd_7522388 : Nat := 4983230072969 + 3 ^ 40 * 7522388 * 2
def baseEnd_7522388 : Nat := 1287533571204539952018391

theorem tailTrace_7522388 : CollatzResearch.WordTrace tailWord_7522388 prefixEnd_7522388 1287533571204539952018391 := by
  unfold tailWord_7522388
  simp only [CollatzResearch.WordTrace]
  refine ⟨137182015135840236216799909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182909353514453648289066545 137182015135840236216799909)
  ·
    refine ⟨25721627837970044290649983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137182015135840236216799909 25721627837970044290649983)
    ·
      refine ⟨38582441756955066435974975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25721627837970044290649983 38582441756955066435974975)
      ·
        refine ⟨57873662635432599653962463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38582441756955066435974975 57873662635432599653962463)
        ·
          refine ⟨86810493953148899480943695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57873662635432599653962463 86810493953148899480943695)
          ·
            refine ⟨130215740929723349221415543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86810493953148899480943695 130215740929723349221415543)
            ·
              refine ⟨195323611394585023832123315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130215740929723349221415543 195323611394585023832123315)
              ·
                refine ⟨292985417091877535748184973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195323611394585023832123315 292985417091877535748184973)
                ·
                  refine ⟨109869531409454075905569365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292985417091877535748184973 109869531409454075905569365)
                  ·
                    refine ⟨1287533571204539952018391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109869531409454075905569365 1287533571204539952018391)
                    ·
                      rfl

theorem cell23_7522388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_7522388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522388 prefixEnd_7522388 := by exact prefixLift 7522388
  have htrace : WordTrace (prefixWord ++ tailWord_7522388) baseStart_7522388 baseEnd_7522388 := by
    simpa [prefixWord, tailWord_7522388, baseEnd_7522388] using wordTrace_append hprefix tailTrace_7522388
  have hstable : (prefixWord ++ tailWord_7522388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522388).length < 2 ^ (prefixWord ++ tailWord_7522388).sum := by decide
  have hdescent : baseEnd_7522388 < baseStart_7522388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522390 : List Nat := [5, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_7522390 : Nat := 118140960795 + 7522390 * 2 ^ 59
def prefixEnd_7522390 : Nat := 4983230072969 + 3 ^ 40 * 7522390 * 2
def baseEnd_7522390 : Nat := 3862601740574928848230165

theorem tailTrace_7522390 : CollatzResearch.WordTrace tailWord_7522390 prefixEnd_7522390 3862601740574928848230165 := by
  unfold tailWord_7522390
  simp only [CollatzResearch.WordTrace]
  refine ⟨17147756451104576673448289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182909402145115484516781749 17147756451104576673448289)
  ·
    refine ⟨12860817338328432505086217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17147756451104576673448289 12860817338328432505086217)
    ·
      refine ⟨9645613003746324378814663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12860817338328432505086217 9645613003746324378814663)
      ·
        refine ⟨14468419505619486568221995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9645613003746324378814663 14468419505619486568221995)
        ·
          refine ⟨21702629258429229852332993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14468419505619486568221995 21702629258429229852332993)
          ·
            refine ⟨16276971943821922389249745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21702629258429229852332993 16276971943821922389249745)
            ·
              refine ⟨12207728957866441791937309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16276971943821922389249745 12207728957866441791937309)
              ·
                refine ⟨4577898359199915671976491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12207728957866441791937309 4577898359199915671976491)
                ·
                  refine ⟨6866847538799873507964737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577898359199915671976491 6866847538799873507964737)
                  ·
                    refine ⟨5150135654099905130973553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6866847538799873507964737 5150135654099905130973553)
                    ·
                      refine ⟨3862601740574928848230165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5150135654099905130973553 3862601740574928848230165)
                      ·
                        rfl

theorem cell23_7522390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_7522390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522390 prefixEnd_7522390 := by exact prefixLift 7522390
  have htrace : WordTrace (prefixWord ++ tailWord_7522390) baseStart_7522390 baseEnd_7522390 := by
    simpa [prefixWord, tailWord_7522390, baseEnd_7522390] using wordTrace_append hprefix tailTrace_7522390
  have hstable : (prefixWord ++ tailWord_7522390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522390).length < 2 ^ (prefixWord ++ tailWord_7522390).sum := by decide
  have hdescent : baseEnd_7522390 < baseStart_7522390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522425 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 2, 2, 4]
def baseStart_7522425 : Nat := 118140960795 + 7522425 * 2 ^ 59
def prefixEnd_7522425 : Nat := 4983230072969 + 3 ^ 40 * 7522425 * 2
def baseEnd_7522425 : Nat := 3862619712397836211292503

theorem tailTrace_7522425 : CollatzResearch.WordTrace tailWord_7522425 prefixEnd_7522425 3862619712397836211292503 := by
  unfold tailWord_7522425
  simp only [CollatzResearch.WordTrace]
  refine ⟨274365379772546427752696729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182910253181697618501797819 274365379772546427752696729)
  ·
    refine ⟨205774034829409820814522547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274365379772546427752696729 205774034829409820814522547)
    ·
      refine ⟨308661052244114731221783821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205774034829409820814522547 308661052244114731221783821)
      ·
        refine ⟨115747894591543024208168933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308661052244114731221783821 115747894591543024208168933)
        ·
          refine ⟨21702730235914317039031675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115747894591543024208168933 21702730235914317039031675)
          ·
            refine ⟨32554095353871475558547513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21702730235914317039031675 32554095353871475558547513)
            ·
              refine ⟨24415571515403606668910635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32554095353871475558547513 24415571515403606668910635)
              ·
                refine ⟨36623357273105410003365953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24415571515403606668910635 36623357273105410003365953)
                ·
                  refine ⟨27467517954829057502524465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36623357273105410003365953 27467517954829057502524465)
                  ·
                    refine ⟨20600638466121793126893349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27467517954829057502524465 20600638466121793126893349)
                    ·
                      refine ⟨3862619712397836211292503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20600638466121793126893349 3862619712397836211292503)
                      ·
                        rfl

theorem cell23_7522425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_7522425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522425 prefixEnd_7522425 := by exact prefixLift 7522425
  have htrace : WordTrace (prefixWord ++ tailWord_7522425) baseStart_7522425 baseEnd_7522425 := by
    simpa [prefixWord, tailWord_7522425, baseEnd_7522425] using wordTrace_append hprefix tailTrace_7522425
  have hstable : (prefixWord ++ tailWord_7522425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522425).length < 2 ^ (prefixWord ++ tailWord_7522425).sum := by decide
  have hdescent : baseEnd_7522425 < baseStart_7522425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522429 : List Nat := [1, 4, 1, 1, 3, 4, 1, 1, 1, 4, 2]
def baseStart_7522429 : Nat := 118140960795 + 7522429 * 2 ^ 59
def prefixEnd_7522429 : Nat := 4983230072969 + 3 ^ 40 * 7522429 * 2
def baseEnd_7522429 : Nat := 3862621766320454195642485

theorem tailTrace_7522429 : CollatzResearch.WordTrace tailWord_7522429 prefixEnd_7522429 3862621766320454195642485 := by
  unfold tailWord_7522429
  simp only [CollatzResearch.WordTrace]
  refine ⟨274365525664531936435842341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182910350443021290957228227 274365525664531936435842341)
  ·
    refine ⟨51443536062099738081720439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274365525664531936435842341 51443536062099738081720439)
    ·
      refine ⟨77165304093149607122580659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51443536062099738081720439 77165304093149607122580659)
      ·
        refine ⟨115747956139724410683870989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77165304093149607122580659 115747956139724410683870989)
        ·
          refine ⟨43405483552396654006451621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115747956139724410683870989 43405483552396654006451621)
          ·
            refine ⟨8138528166074372626209679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43405483552396654006451621 8138528166074372626209679)
            ·
              refine ⟨12207792249111558939314519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8138528166074372626209679 12207792249111558939314519)
              ·
                refine ⟨18311688373667338408971779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12207792249111558939314519 18311688373667338408971779)
                ·
                  refine ⟨27467532560501007613457669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18311688373667338408971779 27467532560501007613457669)
                  ·
                    refine ⟨5150162355093938927523313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27467532560501007613457669 5150162355093938927523313)
                    ·
                      refine ⟨3862621766320454195642485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5150162355093938927523313 3862621766320454195642485)
                      ·
                        rfl

theorem cell23_7522429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_7522429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522429 prefixEnd_7522429 := by exact prefixLift 7522429
  have htrace : WordTrace (prefixWord ++ tailWord_7522429) baseStart_7522429 baseEnd_7522429 := by
    simpa [prefixWord, tailWord_7522429, baseEnd_7522429] using wordTrace_append hprefix tailTrace_7522429
  have hstable : (prefixWord ++ tailWord_7522429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522429).length < 2 ^ (prefixWord ++ tailWord_7522429).sum := by decide
  have hdescent : baseEnd_7522429 < baseStart_7522429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522448 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 1, 7]
def baseStart_7522448 : Nat := 118140960795 + 7522448 * 2 ^ 59
def prefixEnd_7522448 : Nat := 4983230072969 + 3 ^ 40 * 7522448 * 2
def baseEnd_7522448 : Nat := 1287543840817629873768299

theorem tailTrace_7522448 : CollatzResearch.WordTrace tailWord_7522448 prefixEnd_7522448 1287543840817629873768299 := by
  unfold tailWord_7522448
  simp only [CollatzResearch.WordTrace]
  refine ⟨137183109325731551340391999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182910812434308735120522665 137183109325731551340391999)
  ·
    refine ⟨205774663988597327010587999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137183109325731551340391999 205774663988597327010587999)
    ·
      refine ⟨308661995982895990515881999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205774663988597327010587999 308661995982895990515881999)
      ·
        refine ⟨462992993974343985773822999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308661995982895990515881999 462992993974343985773822999)
        ·
          refine ⟨694489490961515978660734499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462992993974343985773822999 694489490961515978660734499)
          ·
            refine ⟨1041734236442273967991101749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694489490961515978660734499 1041734236442273967991101749)
            ·
              refine ⟨97662584666463184499165789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1041734236442273967991101749 97662584666463184499165789)
              ·
                refine ⟨36623469249923694187187171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97662584666463184499165789 36623469249923694187187171)
                ·
                  refine ⟨54935203874885541280780757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36623469249923694187187171 54935203874885541280780757)
                  ·
                    refine ⟨1287543840817629873768299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54935203874885541280780757 1287543840817629873768299)
                    ·
                      rfl

theorem cell23_7522448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 1, 7].length) (baseStart_7522448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522448 prefixEnd_7522448 := by exact prefixLift 7522448
  have htrace : WordTrace (prefixWord ++ tailWord_7522448) baseStart_7522448 baseEnd_7522448 := by
    simpa [prefixWord, tailWord_7522448, baseEnd_7522448] using wordTrace_append hprefix tailTrace_7522448
  have hstable : (prefixWord ++ tailWord_7522448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522448).length < 2 ^ (prefixWord ++ tailWord_7522448).sum := by decide
  have hdescent : baseEnd_7522448 < baseStart_7522448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522465 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 4, 5]
def baseStart_7522465 : Nat := 118140960795 + 7522465 * 2 ^ 59
def prefixEnd_7522465 : Nat := 4983230072969 + 3 ^ 40 * 7522465 * 2
def baseEnd_7522465 : Nat := 1287546750541338684930773

theorem tailTrace_7522465 : CollatzResearch.WordTrace tailWord_7522465 prefixEnd_7522465 1287546750541338684930773 := by
  unfold tailWord_7522465
  simp only [CollatzResearch.WordTrace]
  refine ⟨274366838692401514584152849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182911225794934343056101899 274366838692401514584152849)
  ·
    refine ⟨205775129019301135938114637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274366838692401514584152849 205775129019301135938114637)
    ·
      refine ⟨77165673382237925976792989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205775129019301135938114637 77165673382237925976792989)
      ·
        refine ⟨28937127518339222241297371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77165673382237925976792989 28937127518339222241297371)
        ·
          refine ⟨43405691277508833361946057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28937127518339222241297371 43405691277508833361946057)
          ·
            refine ⟨32554268458131625021459543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43405691277508833361946057 32554268458131625021459543)
            ·
              refine ⟨48831402687197437532189315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32554268458131625021459543 48831402687197437532189315)
              ·
                refine ⟨73247104030796156298283973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48831402687197437532189315 73247104030796156298283973)
                ·
                  refine ⟨13733832005774279305928245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73247104030796156298283973 13733832005774279305928245)
                  ·
                    refine ⟨1287546750541338684930773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13733832005774279305928245 1287546750541338684930773)
                    ·
                      rfl

theorem cell23_7522465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_7522465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522465 prefixEnd_7522465 := by exact prefixLift 7522465
  have htrace : WordTrace (prefixWord ++ tailWord_7522465) baseStart_7522465 baseEnd_7522465 := by
    simpa [prefixWord, tailWord_7522465, baseEnd_7522465] using wordTrace_append hprefix tailTrace_7522465
  have hstable : (prefixWord ++ tailWord_7522465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522465).length < 2 ^ (prefixWord ++ tailWord_7522465).sum := by decide
  have hdescent : baseEnd_7522465 < baseStart_7522465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522495 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 5, 4]
def baseStart_7522495 : Nat := 118140960795 + 7522495 * 2 ^ 59
def prefixEnd_7522495 : Nat := 4983230072969 + 3 ^ 40 * 7522495 * 2
def baseEnd_7522495 : Nat := 1287551885347883645805727

theorem tailTrace_7522495 : CollatzResearch.WordTrace tailWord_7522495 prefixEnd_7522495 1287551885347883645805727 := by
  unfold tailWord_7522495
  simp only [CollatzResearch.WordTrace]
  refine ⟨274367932882292829707744939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182911955254861886471829959 274367932882292829707744939)
  ·
    refine ⟨411551899323439244561617409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274367932882292829707744939 411551899323439244561617409)
    ·
      refine ⟨308663924492579433421213057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411551899323439244561617409 308663924492579433421213057)
      ·
        refine ⟨231497943369434575065909793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308663924492579433421213057 231497943369434575065909793)
        ·
          refine ⟨173623457527075931299432345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231497943369434575065909793 173623457527075931299432345)
          ·
            refine ⟨130217593145306948474574259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173623457527075931299432345 130217593145306948474574259)
            ·
              refine ⟨195326389717960422711861389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130217593145306948474574259 195326389717960422711861389)
              ·
                refine ⟨73247396144235158516948021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195326389717960422711861389 73247396144235158516948021)
                ·
                  refine ⟨6866943388522046110963877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73247396144235158516948021 6866943388522046110963877)
                  ·
                    refine ⟨1287551885347883645805727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6866943388522046110963877 1287551885347883645805727)
                    ·
                      rfl

theorem cell23_7522495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 4].length) (baseStart_7522495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522495 prefixEnd_7522495 := by exact prefixLift 7522495
  have htrace : WordTrace (prefixWord ++ tailWord_7522495) baseStart_7522495 baseEnd_7522495 := by
    simpa [prefixWord, tailWord_7522495, baseEnd_7522495] using wordTrace_append hprefix tailTrace_7522495
  have hstable : (prefixWord ++ tailWord_7522495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522495).length < 2 ^ (prefixWord ++ tailWord_7522495).sum := by decide
  have hdescent : baseEnd_7522495 < baseStart_7522495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522522 : List Nat := [3, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3]
def baseStart_7522522 : Nat := 118140960795 + 7522522 * 2 ^ 59
def prefixEnd_7522522 : Nat := 4983230072969 + 3 ^ 40 * 7522522 * 2
def baseEnd_7522522 : Nat := 3862669520021322331779557

theorem tailTrace_7522522 : CollatzResearch.WordTrace tailWord_7522522 prefixEnd_7522522 3862669520021322331779557 := by
  unfold tailWord_7522522
  simp only [CollatzResearch.WordTrace]
  refine ⟨68592229413298753329744455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182912611768796675545985213 68592229413298753329744455)
  ·
    refine ⟨102888344119948129994616683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68592229413298753329744455 102888344119948129994616683)
    ·
      refine ⟨154332516179922194991925025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102888344119948129994616683 154332516179922194991925025)
      ·
        refine ⟨115749387134941646243943769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154332516179922194991925025 115749387134941646243943769)
        ·
          refine ⟨86812040351206234682957827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115749387134941646243943769 86812040351206234682957827)
          ·
            refine ⟨130218060526809352024436741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86812040351206234682957827 130218060526809352024436741)
            ·
              refine ⟨24415886348776753504581889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130218060526809352024436741 24415886348776753504581889)
              ·
                refine ⟨18311914761582565128436417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24415886348776753504581889 18311914761582565128436417)
                ·
                  refine ⟨13733936071186923846327313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18311914761582565128436417 13733936071186923846327313)
                  ·
                    refine ⟨10300452053390192884745485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13733936071186923846327313 10300452053390192884745485)
                    ·
                      refine ⟨3862669520021322331779557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10300452053390192884745485 3862669520021322331779557)
                      ·
                        rfl

theorem cell23_7522522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_7522522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522522 prefixEnd_7522522 := by exact prefixLift 7522522
  have htrace : WordTrace (prefixWord ++ tailWord_7522522) baseStart_7522522 baseEnd_7522522 := by
    simpa [prefixWord, tailWord_7522522, baseEnd_7522522] using wordTrace_append hprefix tailTrace_7522522
  have hstable : (prefixWord ++ tailWord_7522522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522522).length < 2 ^ (prefixWord ++ tailWord_7522522).sum := by decide
  have hdescent : baseEnd_7522522 < baseStart_7522522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522529 : List Nat := [1, 2, 3, 1, 3, 1, 3, 4, 1, 4]
def baseStart_7522529 : Nat := 118140960795 + 7522529 * 2 ^ 59
def prefixEnd_7522529 : Nat := 4983230072969 + 3 ^ 40 * 7522529 * 2
def baseEnd_7522529 : Nat := 1287557704795301268130675

theorem tailTrace_7522529 : CollatzResearch.WordTrace tailWord_7522529 prefixEnd_7522529 1287557704795301268130675 := by
  unfold tailWord_7522529
  simp only [CollatzResearch.WordTrace]
  refine ⟨274369172964169653514482641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182912781976113102342988427 274369172964169653514482641)
  ·
    refine ⟨205776879723127240135861981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274369172964169653514482641 205776879723127240135861981)
    ·
      refine ⟨77166329896172715050948243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205776879723127240135861981 77166329896172715050948243)
      ·
        refine ⟨115749494844259072576422365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77166329896172715050948243 115749494844259072576422365)
        ·
          refine ⟨43406060566597152216158387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115749494844259072576422365 43406060566597152216158387)
          ·
            refine ⟨65109090849895728324237581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43406060566597152216158387 65109090849895728324237581)
            ·
              refine ⟨24415909068710898121589093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65109090849895728324237581 24415909068710898121589093)
              ·
                refine ⟨4577982950383293397797955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24415909068710898121589093 4577982950383293397797955)
                ·
                  refine ⟨6866974425574940096696933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577982950383293397797955 6866974425574940096696933)
                  ·
                    refine ⟨1287557704795301268130675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6866974425574940096696933 1287557704795301268130675)
                    ·
                      rfl

theorem cell23_7522529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_7522529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522529 prefixEnd_7522529 := by exact prefixLift 7522529
  have htrace : WordTrace (prefixWord ++ tailWord_7522529) baseStart_7522529 baseEnd_7522529 := by
    simpa [prefixWord, tailWord_7522529, baseEnd_7522529] using wordTrace_append hprefix tailTrace_7522529
  have hstable : (prefixWord ++ tailWord_7522529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522529).length < 2 ^ (prefixWord ++ tailWord_7522529).sum := by decide
  have hdescent : baseEnd_7522529 < baseStart_7522529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522572 : List Nat := [2, 2, 1, 2, 2, 2, 3, 3, 1, 5]
def baseStart_7522572 : Nat := 118140960795 + 7522572 * 2 ^ 59
def prefixEnd_7522572 : Nat := 4983230072969 + 3 ^ 40 * 7522572 * 2
def baseEnd_7522572 : Nat := 1287565064684682378718109

theorem tailTrace_7522572 : CollatzResearch.WordTrace tailWord_7522572 prefixEnd_7522572 1287565064684682378718109 := by
  unfold tailWord_7522572
  simp only [CollatzResearch.WordTrace]
  refine ⟨137185370651506935929148985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182913827535342581238865313 137185370651506935929148985)
  ·
    refine ⟨102889027988630201946861739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137185370651506935929148985 102889027988630201946861739)
    ·
      refine ⟨154333541982945302920292609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102889027988630201946861739 154333541982945302920292609)
      ·
        refine ⟨115750156487208977190219457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154333541982945302920292609 115750156487208977190219457)
        ·
          refine ⟨86812617365406732892664593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115750156487208977190219457 86812617365406732892664593)
          ·
            refine ⟨65109463024055049669498445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86812617365406732892664593 65109463024055049669498445)
            ·
              refine ⟨24416048634020643626061917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65109463024055049669498445 24416048634020643626061917)
              ·
                refine ⟨9156018237757741359773219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24416048634020643626061917 9156018237757741359773219)
                ·
                  refine ⟨13734027356636612039659829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9156018237757741359773219 13734027356636612039659829)
                  ·
                    refine ⟨1287565064684682378718109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13734027356636612039659829 1287565064684682378718109)
                    ·
                      rfl

theorem cell23_7522572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_7522572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522572 prefixEnd_7522572 := by exact prefixLift 7522572
  have htrace : WordTrace (prefixWord ++ tailWord_7522572) baseStart_7522572 baseEnd_7522572 := by
    simpa [prefixWord, tailWord_7522572, baseEnd_7522572] using wordTrace_append hprefix tailTrace_7522572
  have hstable : (prefixWord ++ tailWord_7522572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522572).length < 2 ^ (prefixWord ++ tailWord_7522572).sum := by decide
  have hdescent : baseEnd_7522572 < baseStart_7522572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522586 : List Nat := [3, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3]
def baseStart_7522586 : Nat := 118140960795 + 7522586 * 2 ^ 59
def prefixEnd_7522586 : Nat := 4983230072969 + 3 ^ 40 * 7522586 * 2
def baseEnd_7522586 : Nat := 3862702382783210081379263

theorem tailTrace_7522586 : CollatzResearch.WordTrace tailWord_7522586 prefixEnd_7522586 3862702382783210081379263 := by
  unfold tailWord_7522586
  simp only [CollatzResearch.WordTrace]
  refine ⟨68592812981240788062326903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182914167949975434832871741 68592812981240788062326903)
  ·
    refine ⟨102889219471861182093490355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68592812981240788062326903 102889219471861182093490355)
    ·
      refine ⟨154333829207791773140235533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102889219471861182093490355 154333829207791773140235533)
      ·
        refine ⟨57875185952921914927588325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154333829207791773140235533 57875185952921914927588325)
        ·
          refine ⟨10851597366172859048922811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57875185952921914927588325 10851597366172859048922811)
          ·
            refine ⟨16277396049259288573384217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10851597366172859048922811 16277396049259288573384217)
            ·
              refine ⟨12208047036944466430038163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16277396049259288573384217 12208047036944466430038163)
              ·
                refine ⟨18312070555416699645057245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12208047036944466430038163 18312070555416699645057245)
                ·
                  refine ⟨6867026458281262366896467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18312070555416699645057245 6867026458281262366896467)
                  ·
                    refine ⟨10300539687421893550344701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6867026458281262366896467 10300539687421893550344701)
                    ·
                      refine ⟨3862702382783210081379263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10300539687421893550344701 3862702382783210081379263)
                      ·
                        rfl

theorem cell23_7522586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_7522586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522586 prefixEnd_7522586 := by exact prefixLift 7522586
  have htrace : WordTrace (prefixWord ++ tailWord_7522586) baseStart_7522586 baseEnd_7522586 := by
    simpa [prefixWord, tailWord_7522586, baseEnd_7522586] using wordTrace_append hprefix tailTrace_7522586
  have hstable : (prefixWord ++ tailWord_7522586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522586).length < 2 ^ (prefixWord ++ tailWord_7522586).sum := by decide
  have hdescent : baseEnd_7522586 < baseStart_7522586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522675 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 1, 8]
def baseStart_7522675 : Nat := 118140960795 + 7522675 * 2 ^ 59
def prefixEnd_7522675 : Nat := 4983230072969 + 3 ^ 40 * 7522675 * 2
def baseEnd_7522675 : Nat := 1287582694187153411055451

theorem tailTrace_7522675 : CollatzResearch.WordTrace tailWord_7522675 prefixEnd_7522675 1287582694187153411055451 := by
  unfold tailWord_7522675
  simp only [CollatzResearch.WordTrace]
  refine ⟨274374498021640720449297479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182916332014427146966198319 274374498021640720449297479)
  ·
    refine ⟨411561747032461080673946219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274374498021640720449297479 411561747032461080673946219)
    ·
      refine ⟨617342620548691621010919329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411561747032461080673946219 617342620548691621010919329)
      ·
        refine ⟨463006965411518715758189497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617342620548691621010919329 463006965411518715758189497)
        ·
          refine ⟨347255224058639036818642123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463006965411518715758189497 347255224058639036818642123)
          ·
            refine ⟨520882836087958555227963185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347255224058639036818642123 520882836087958555227963185)
            ·
              refine ⟨390662127065968916420972389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520882836087958555227963185 390662127065968916420972389)
              ·
                refine ⟨73249148824869171828932323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 390662127065968916420972389 73249148824869171828932323)
                ·
                  refine ⟨109873723237303757743398485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73249148824869171828932323 109873723237303757743398485)
                  ·
                    refine ⟨1287582694187153411055451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109873723237303757743398485 1287582694187153411055451)
                    ·
                      rfl

theorem cell23_7522675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 8].length) (baseStart_7522675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522675 prefixEnd_7522675 := by exact prefixLift 7522675
  have htrace : WordTrace (prefixWord ++ tailWord_7522675) baseStart_7522675 baseEnd_7522675 := by
    simpa [prefixWord, tailWord_7522675, baseEnd_7522675] using wordTrace_append hprefix tailTrace_7522675
  have hstable : (prefixWord ++ tailWord_7522675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522675).length < 2 ^ (prefixWord ++ tailWord_7522675).sum := by decide
  have hdescent : baseEnd_7522675 < baseStart_7522675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522692 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 2, 6]
def baseStart_7522692 : Nat := 118140960795 + 7522692 * 2 ^ 59
def prefixEnd_7522692 : Nat := 4983230072969 + 3 ^ 40 * 7522692 * 2
def baseEnd_7522692 : Nat := 1287585603910862222217925

theorem tailTrace_7522692 : CollatzResearch.WordTrace tailWord_7522692 prefixEnd_7522692 1287585603910862222217925 := by
  unfold tailWord_7522692
  simp only [CollatzResearch.WordTrace]
  refine ⟨137187559031289566176333165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182916745375052754901777553 137187559031289566176333165)
  ·
    refine ⟨51445334636733587316124937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137187559031289566176333165 51445334636733587316124937)
    ·
      refine ⟨38584000977550190487093703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51445334636733587316124937 38584000977550190487093703)
      ·
        refine ⟨57876001466325285730640555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38584000977550190487093703 57876001466325285730640555)
        ·
          refine ⟨86814002199487928595960833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57876001466325285730640555 86814002199487928595960833)
          ·
            refine ⟨65110501649615946446970625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86814002199487928595960833 65110501649615946446970625)
            ·
              refine ⟨48832876237211959835227969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65110501649615946446970625 48832876237211959835227969)
              ·
                refine ⟨36624657177908969876420977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48832876237211959835227969 36624657177908969876420977)
                ·
                  refine ⟨27468492883431727407315733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36624657177908969876420977 27468492883431727407315733)
                  ·
                    refine ⟨1287585603910862222217925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27468492883431727407315733 1287585603910862222217925)
                    ·
                      rfl

theorem cell23_7522692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_7522692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522692 prefixEnd_7522692 := by exact prefixLift 7522692
  have htrace : WordTrace (prefixWord ++ tailWord_7522692) baseStart_7522692 baseEnd_7522692 := by
    simpa [prefixWord, tailWord_7522692, baseEnd_7522692] using wordTrace_append hprefix tailTrace_7522692
  have hstable : (prefixWord ++ tailWord_7522692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522692).length < 2 ^ (prefixWord ++ tailWord_7522692).sum := by decide
  have hdescent : baseEnd_7522692 < baseStart_7522692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522732 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 3]
def baseStart_7522732 : Nat := 118140960795 + 7522732 * 2 ^ 59
def prefixEnd_7522732 : Nat := 4983230072969 + 3 ^ 40 * 7522732 * 2
def baseEnd_7522732 : Nat := 3862777350958766510153591

theorem tailTrace_7522732 : CollatzResearch.WordTrace tailWord_7522732 prefixEnd_7522732 3862777350958766510153591 := by
  unfold tailWord_7522732
  simp only [CollatzResearch.WordTrace]
  refine ⟨137188288491217109592061225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182917717988289479456081633 137188288491217109592061225)
  ·
    refine ⟨102891216368412832194045919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137188288491217109592061225 102891216368412832194045919)
    ·
      refine ⟨154336824552619248291068879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102891216368412832194045919 154336824552619248291068879)
      ·
        refine ⟨231505236828928872436603319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154336824552619248291068879 231505236828928872436603319)
        ·
          refine ⟨347257855243393308654904979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231505236828928872436603319 347257855243393308654904979)
          ·
            refine ⟨520886782865089962982357469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347257855243393308654904979 520886782865089962982357469)
            ·
              refine ⟨195332543574408736118384051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 520886782865089962982357469 195332543574408736118384051)
              ·
                refine ⟨292998815361613104177576077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195332543574408736118384051 292998815361613104177576077)
                ·
                  refine ⟨109874555760604914066591029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292998815361613104177576077 109874555760604914066591029)
                  ·
                    refine ⟨10300739602556710693742909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109874555760604914066591029 10300739602556710693742909)
                    ·
                      refine ⟨3862777350958766510153591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10300739602556710693742909 3862777350958766510153591)
                      ·
                        rfl

theorem cell23_7522732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_7522732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522732 prefixEnd_7522732 := by exact prefixLift 7522732
  have htrace : WordTrace (prefixWord ++ tailWord_7522732) baseStart_7522732 baseEnd_7522732 := by
    simpa [prefixWord, tailWord_7522732, baseEnd_7522732] using wordTrace_append hprefix tailTrace_7522732
  have hstable : (prefixWord ++ tailWord_7522732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522732).length < 2 ^ (prefixWord ++ tailWord_7522732).sum := by decide
  have hdescent : baseEnd_7522732 < baseStart_7522732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522749 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 2, 3, 3]
def baseStart_7522749 : Nat := 118140960795 + 7522749 * 2 ^ 59
def prefixEnd_7522749 : Nat := 4983230072969 + 3 ^ 40 * 7522749 * 2
def baseEnd_7522749 : Nat := 3862786080129892943641013

theorem tailTrace_7522749 : CollatzResearch.WordTrace tailWord_7522749 prefixEnd_7522749 3862786080129892943641013 := by
  unfold tailWord_7522749
  simp only [CollatzResearch.WordTrace]
  refine ⟨274377197023372631087491301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182918131348915087391660867 274377197023372631087491301)
  ·
    refine ⟨51445724441882368328904619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274377197023372631087491301 51445724441882368328904619)
    ·
      refine ⟨77168586662823552493356929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51445724441882368328904619 77168586662823552493356929)
      ·
        refine ⟨57876439997117664370017697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77168586662823552493356929 57876439997117664370017697)
        ·
          refine ⟨43407329997838248277513273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57876439997117664370017697 43407329997838248277513273)
          ·
            refine ⟨32555497498378686208134955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43407329997838248277513273 32555497498378686208134955)
            ·
              refine ⟨48833246247568029312202433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32555497498378686208134955 48833246247568029312202433)
              ·
                refine ⟨36624934685676021984151825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48833246247568029312202433 36624934685676021984151825)
                ·
                  refine ⟨27468701014257016488113869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36624934685676021984151825 27468701014257016488113869)
                  ·
                    refine ⟨10300762880346381183042701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27468701014257016488113869 10300762880346381183042701)
                    ·
                      refine ⟨3862786080129892943641013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10300762880346381183042701 3862786080129892943641013)
                      ·
                        rfl

theorem cell23_7522749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_7522749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522749 prefixEnd_7522749 := by exact prefixLift 7522749
  have htrace : WordTrace (prefixWord ++ tailWord_7522749) baseStart_7522749 baseEnd_7522749 := by
    simpa [prefixWord, tailWord_7522749, baseEnd_7522749] using wordTrace_append hprefix tailTrace_7522749
  have hstable : (prefixWord ++ tailWord_7522749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522749).length < 2 ^ (prefixWord ++ tailWord_7522749).sum := by decide
  have hdescent : baseEnd_7522749 < baseStart_7522749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522752 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 4, 5]
def baseStart_7522752 : Nat := 118140960795 + 7522752 * 2 ^ 59
def prefixEnd_7522752 : Nat := 4983230072969 + 3 ^ 40 * 7522752 * 2
def baseEnd_7522752 : Nat := 1287595873523952143967833

theorem tailTrace_7522752 : CollatzResearch.WordTrace tailWord_7522752 prefixEnd_7522752 1287595873523952143967833 := by
  unfold tailWord_7522752
  simp only [CollatzResearch.WordTrace]
  refine ⟨137188653221180881299925255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182918204294907841733233673 137188653221180881299925255)
  ·
    refine ⟨205782979831771321949887883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137188653221180881299925255 205782979831771321949887883)
    ·
      refine ⟨308674469747656982924831825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205782979831771321949887883 308674469747656982924831825)
      ·
        refine ⟨231505852310742737193623869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308674469747656982924831825 231505852310742737193623869)
        ·
          refine ⟨86814694616528526447608951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231505852310742737193623869 86814694616528526447608951)
          ·
            refine ⟨130222041924792789671413427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86814694616528526447608951 130222041924792789671413427)
            ·
              refine ⟨195333062887189184507120141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130222041924792789671413427 195333062887189184507120141)
              ·
                refine ⟨73249898582695944190170053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195333062887189184507120141 73249898582695944190170053)
                ·
                  refine ⟨13734355984255489535656885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73249898582695944190170053 13734355984255489535656885)
                  ·
                    refine ⟨1287595873523952143967833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13734355984255489535656885 1287595873523952143967833)
                    ·
                      rfl

theorem cell23_7522752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 4, 5].length) (baseStart_7522752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522752 prefixEnd_7522752 := by exact prefixLift 7522752
  have htrace : WordTrace (prefixWord ++ tailWord_7522752) baseStart_7522752 baseEnd_7522752 := by
    simpa [prefixWord, tailWord_7522752, baseEnd_7522752] using wordTrace_append hprefix tailTrace_7522752
  have hstable : (prefixWord ++ tailWord_7522752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522752).length < 2 ^ (prefixWord ++ tailWord_7522752).sum := by decide
  have hdescent : baseEnd_7522752 < baseStart_7522752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522756 : List Nat := [2, 3, 3, 2, 2, 1, 2, 1, 7]
def baseStart_7522756 : Nat := 118140960795 + 7522756 * 2 ^ 59
def prefixEnd_7522756 : Nat := 4983230072969 + 3 ^ 40 * 7522756 * 2
def baseEnd_7522756 : Nat := 429198852721608268472609

theorem tailTrace_7522756 : CollatzResearch.WordTrace tailWord_7522756 prefixEnd_7522756 429198852721608268472609 := by
  unfold tailWord_7522756
  simp only [CollatzResearch.WordTrace]
  refine ⟨137188726167173635641498061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182918301556231514188664081 137188726167173635641498061)
  ·
    refine ⟨51445772312690113365561773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137188726167173635641498061 51445772312690113365561773)
    ·
      refine ⟨19292164617258792512085665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51445772312690113365561773 19292164617258792512085665)
      ·
        refine ⟨14469123462944094384064249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19292164617258792512085665 14469123462944094384064249)
        ·
          refine ⟨10851842597208070788048187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14469123462944094384064249 10851842597208070788048187)
          ·
            refine ⟨16277763895812106182072281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10851842597208070788048187 16277763895812106182072281)
            ·
              refine ⟨12208322921859079636554211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16277763895812106182072281 12208322921859079636554211)
              ·
                refine ⟨18312484382788619454831317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12208322921859079636554211 18312484382788619454831317)
                ·
                  refine ⟨429198852721608268472609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18312484382788619454831317 429198852721608268472609)
                  ·
                    rfl

theorem cell23_7522756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_7522756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522756 prefixEnd_7522756 := by exact prefixLift 7522756
  have htrace : WordTrace (prefixWord ++ tailWord_7522756) baseStart_7522756 baseEnd_7522756 := by
    simpa [prefixWord, tailWord_7522756, baseEnd_7522756] using wordTrace_append hprefix tailTrace_7522756
  have hstable : (prefixWord ++ tailWord_7522756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522756).length < 2 ^ (prefixWord ++ tailWord_7522756).sum := by decide
  have hdescent : baseEnd_7522756 < baseStart_7522756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522762 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_7522762 : Nat := 118140960795 + 7522762 * 2 ^ 59
def prefixEnd_7522762 : Nat := 4983230072969 + 3 ^ 40 * 7522762 * 2
def baseEnd_7522762 : Nat := 3862792755378401392778453

theorem tailTrace_7522762 : CollatzResearch.WordTrace tailWord_7522762 prefixEnd_7522762 3862792755378401392778453 := by
  unfold tailWord_7522762
  simp only [CollatzResearch.WordTrace]
  refine ⟨68594417793081383576928635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182918447448217022871809693 68594417793081383576928635)
  ·
    refine ⟨102891626689622075365392953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68594417793081383576928635 102891626689622075365392953)
    ·
      refine ⟨77168720017216556524044715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102891626689622075365392953 77168720017216556524044715)
      ·
        refine ⟨115753080025824834786067073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77168720017216556524044715 115753080025824834786067073)
        ·
          refine ⟨86814810019368626089550305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115753080025824834786067073 86814810019368626089550305)
          ·
            refine ⟨65111107514526469567162729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86814810019368626089550305 65111107514526469567162729)
            ·
              refine ⟨48833330635894852175372047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65111107514526469567162729 48833330635894852175372047)
              ·
                refine ⟨73249995953842278263058071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48833330635894852175372047 73249995953842278263058071)
                ·
                  refine ⟨109874993930763417394587107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73249995953842278263058071 109874993930763417394587107)
                  ·
                    refine ⟨164812490896145126091880661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109874993930763417394587107 164812490896145126091880661)
                    ·
                      refine ⟨3862792755378401392778453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164812490896145126091880661 3862792755378401392778453)
                      ·
                        rfl

theorem cell23_7522762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_7522762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522762 prefixEnd_7522762 := by exact prefixLift 7522762
  have htrace : WordTrace (prefixWord ++ tailWord_7522762) baseStart_7522762 baseEnd_7522762 := by
    simpa [prefixWord, tailWord_7522762, baseEnd_7522762] using wordTrace_append hprefix tailTrace_7522762
  have hstable : (prefixWord ++ tailWord_7522762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522762).length < 2 ^ (prefixWord ++ tailWord_7522762).sum := by decide
  have hdescent : baseEnd_7522762 < baseStart_7522762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522806 : List Nat := [5, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_7522806 : Nat := 118140960795 + 7522806 * 2 ^ 59
def prefixEnd_7522806 : Nat := 4983230072969 + 3 ^ 40 * 7522806 * 2
def baseEnd_7522806 : Nat := 3862815348527199220628251

theorem tailTrace_7522806 : CollatzResearch.WordTrace tailWord_7522806 prefixEnd_7522806 3862815348527199220628251 := by
  unfold tailWord_7522806
  simp only [CollatzResearch.WordTrace]
  refine ⟨17148704749010383113894767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182919517322777419881544181 17148704749010383113894767)
  ·
    refine ⟨25723057123515574670842151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17148704749010383113894767 25723057123515574670842151)
    ·
      refine ⟨38584585685273362006263227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25723057123515574670842151 38584585685273362006263227)
      ·
        refine ⟨57876878527910043009394841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38584585685273362006263227 57876878527910043009394841)
        ·
          refine ⟨43407658895932532257046131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57876878527910043009394841 43407658895932532257046131)
          ·
            refine ⟨65111488343898798385569197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43407658895932532257046131 65111488343898798385569197)
            ·
              refine ⟨24416808128962049394588449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65111488343898798385569197 24416808128962049394588449)
              ·
                refine ⟨18312606096721537045941337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24416808128962049394588449 18312606096721537045941337)
                ·
                  refine ⟨13734454572541152784456003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18312606096721537045941337 13734454572541152784456003)
                  ·
                    refine ⟨20601681858811729176684005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13734454572541152784456003 20601681858811729176684005)
                    ·
                      refine ⟨3862815348527199220628251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20601681858811729176684005 3862815348527199220628251)
                      ·
                        rfl

theorem cell23_7522806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_7522806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522806 prefixEnd_7522806 := by exact prefixLift 7522806
  have htrace : WordTrace (prefixWord ++ tailWord_7522806) baseStart_7522806 baseEnd_7522806 := by
    simpa [prefixWord, tailWord_7522806, baseEnd_7522806] using wordTrace_append hprefix tailTrace_7522806
  have hstable : (prefixWord ++ tailWord_7522806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522806).length < 2 ^ (prefixWord ++ tailWord_7522806).sum := by decide
  have hdescent : baseEnd_7522806 < baseStart_7522806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522809 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 4, 2, 3]
def baseStart_7522809 : Nat := 118140960795 + 7522809 * 2 ^ 59
def prefixEnd_7522809 : Nat := 4983230072969 + 3 ^ 40 * 7522809 * 2
def baseEnd_7522809 : Nat := 3862816888969162708890737

theorem tailTrace_7522809 : CollatzResearch.WordTrace tailWord_7522809 prefixEnd_7522809 3862816888969162708890737 := by
  unfold tailWord_7522809
  simp only [CollatzResearch.WordTrace]
  refine ⟨274379385403155261334675481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182919590268770174223116987 274379385403155261334675481)
  ·
    refine ⟨205784539052366446001006611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274379385403155261334675481 205784539052366446001006611)
    ·
      refine ⟨308676808578549669001509917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205784539052366446001006611 308676808578549669001509917)
      ·
        refine ⟨115753803216956125875566219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308676808578549669001509917 115753803216956125875566219)
        ·
          refine ⟨173630704825434188813349329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115753803216956125875566219 173630704825434188813349329)
          ·
            refine ⟨130223028619075641610011997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173630704825434188813349329 130223028619075641610011997)
            ·
              refine ⟨48833635732153365603754499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130223028619075641610011997 48833635732153365603754499)
              ·
                refine ⟨73250453598230048405631749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48833635732153365603754499 73250453598230048405631749)
                ·
                  refine ⟨13734460049668134076055953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73250453598230048405631749 13734460049668134076055953)
                  ·
                    refine ⟨10300845037251100557041965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13734460049668134076055953 10300845037251100557041965)
                    ·
                      refine ⟨3862816888969162708890737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10300845037251100557041965 3862816888969162708890737)
                      ·
                        rfl

theorem cell23_7522809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_7522809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522809 prefixEnd_7522809 := by exact prefixLift 7522809
  have htrace : WordTrace (prefixWord ++ tailWord_7522809) baseStart_7522809 baseEnd_7522809 := by
    simpa [prefixWord, tailWord_7522809, baseEnd_7522809] using wordTrace_append hprefix tailTrace_7522809
  have hstable : (prefixWord ++ tailWord_7522809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522809).length < 2 ^ (prefixWord ++ tailWord_7522809).sum := by decide
  have hdescent : baseEnd_7522809 < baseStart_7522809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522859 : List Nat := [1, 1, 1, 1, 2, 1, 3, 7, 1, 5]
def baseStart_7522859 : Nat := 118140960795 + 7522859 * 2 ^ 59
def prefixEnd_7522859 : Nat := 4983230072969 + 3 ^ 40 * 7522859 * 2
def baseEnd_7522859 : Nat := 1287614187667295837755169

theorem tailTrace_7522859 : CollatzResearch.WordTrace tailWord_7522859 prefixEnd_7522859 1287614187667295837755169 := by
  unfold tailWord_7522859
  simp only [CollatzResearch.WordTrace]
  refine ⟨274381209052974119873995631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182920806035316079915997087 274381209052974119873995631)
  ·
    refine ⟨411571813579461179810993447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274381209052974119873995631 411571813579461179810993447)
    ·
      refine ⟨617357720369191769716490171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411571813579461179810993447 617357720369191769716490171)
      ·
        refine ⟨926036580553787654574735257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617357720369191769716490171 926036580553787654574735257)
        ·
          refine ⟨694527435415340740931051443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 926036580553787654574735257 694527435415340740931051443)
          ·
            refine ⟨1041791153123011111396577165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694527435415340740931051443 1041791153123011111396577165)
            ·
              refine ⟨390671682421129166773716437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1041791153123011111396577165 390671682421129166773716437)
              ·
                refine ⟨9156367556745214846258979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 390671682421129166773716437 9156367556745214846258979)
                ·
                  refine ⟨13734551335117822269388469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9156367556745214846258979 13734551335117822269388469)
                  ·
                    refine ⟨1287614187667295837755169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13734551335117822269388469 1287614187667295837755169)
                    ·
                      rfl

theorem cell23_7522859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 5].length) (baseStart_7522859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522859 prefixEnd_7522859 := by exact prefixLift 7522859
  have htrace : WordTrace (prefixWord ++ tailWord_7522859) baseStart_7522859 baseEnd_7522859 := by
    simpa [prefixWord, tailWord_7522859, baseEnd_7522859] using wordTrace_append hprefix tailTrace_7522859
  have hstable : (prefixWord ++ tailWord_7522859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522859).length < 2 ^ (prefixWord ++ tailWord_7522859).sum := by decide
  have hdescent : baseEnd_7522859 < baseStart_7522859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522879 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 4]
def baseStart_7522879 : Nat := 118140960795 + 7522879 * 2 ^ 59
def prefixEnd_7522879 : Nat := 4983230072969 + 3 ^ 40 * 7522879 * 2
def baseEnd_7522879 : Nat := 3862852832614977435015415

theorem tailTrace_7522879 : CollatzResearch.WordTrace tailWord_7522879 prefixEnd_7522879 3862852832614977435015415 := by
  unfold tailWord_7522879
  simp only [CollatzResearch.WordTrace]
  refine ⟨274381938512901663289723691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182921292341934442193149127 274381938512901663289723691)
  ·
    refine ⟨411572907769352494934585537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274381938512901663289723691 411572907769352494934585537)
    ·
      refine ⟨308679680827014371200939153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411572907769352494934585537 308679680827014371200939153)
      ·
        refine ⟨231509760620260778400704365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308679680827014371200939153 231509760620260778400704365)
        ·
          refine ⟨86816160232597791900264137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231509760620260778400704365 86816160232597791900264137)
          ·
            refine ⟨65112120174448343925198103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86816160232597791900264137 65112120174448343925198103)
            ·
              refine ⟨97668180261672515887797155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65112120174448343925198103 97668180261672515887797155)
              ·
                refine ⟨146502270392508773831695733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97668180261672515887797155 146502270392508773831695733)
                ·
                  refine ⟨13734587849297697546721475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146502270392508773831695733 13734587849297697546721475)
                  ·
                    refine ⟨20601881773946546320082213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13734587849297697546721475 20601881773946546320082213)
                    ·
                      refine ⟨3862852832614977435015415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20601881773946546320082213 3862852832614977435015415)
                      ·
                        rfl

theorem cell23_7522879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_7522879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522879 prefixEnd_7522879 := by exact prefixLift 7522879
  have htrace : WordTrace (prefixWord ++ tailWord_7522879) baseStart_7522879 baseEnd_7522879 := by
    simpa [prefixWord, tailWord_7522879, baseEnd_7522879] using wordTrace_append hprefix tailTrace_7522879
  have hstable : (prefixWord ++ tailWord_7522879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522879).length < 2 ^ (prefixWord ++ tailWord_7522879).sum := by decide
  have hdescent : baseEnd_7522879 < baseStart_7522879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522889 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 8, 4]
def baseStart_7522889 : Nat := 118140960795 + 7522889 * 2 ^ 59
def prefixEnd_7522889 : Nat := 4983230072969 + 3 ^ 40 * 7522889 * 2
def baseEnd_7522889 : Nat := 1287619322473840798630123

theorem tailTrace_7522889 : CollatzResearch.WordTrace tailWord_7522889 prefixEnd_7522889 1287619322473840798630123 := by
  unfold tailWord_7522889
  simp only [CollatzResearch.WordTrace]
  refine ⟨274382303242865434997587721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182921535495243623331725147 274382303242865434997587721)
  ·
    refine ⟨205786727432149076248190791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274382303242865434997587721 205786727432149076248190791)
    ·
      refine ⟨308680091148223614372286187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205786727432149076248190791 308680091148223614372286187)
      ·
        refine ⟨463020136722335421558429281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308680091148223614372286187 463020136722335421558429281)
        ·
          refine ⟨347265102541751566168821961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463020136722335421558429281 347265102541751566168821961)
          ·
            refine ⟨260448826906313674626616471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347265102541751566168821961 260448826906313674626616471)
            ·
              refine ⟨390673240359470511939924707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260448826906313674626616471 390673240359470511939924707)
              ·
                refine ⟨586009860539205767909887061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390673240359470511939924707 586009860539205767909887061)
                ·
                  refine ⟨6867303053193817592693989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 586009860539205767909887061 6867303053193817592693989)
                  ·
                    refine ⟨1287619322473840798630123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6867303053193817592693989 1287619322473840798630123)
                    ·
                      rfl

theorem cell23_7522889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 4].length) (baseStart_7522889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522889 prefixEnd_7522889 := by exact prefixLift 7522889
  have htrace : WordTrace (prefixWord ++ tailWord_7522889) baseStart_7522889 baseEnd_7522889 := by
    simpa [prefixWord, tailWord_7522889, baseEnd_7522889] using wordTrace_append hprefix tailTrace_7522889
  have hstable : (prefixWord ++ tailWord_7522889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522889).length < 2 ^ (prefixWord ++ tailWord_7522889).sum := by decide
  have hdescent : baseEnd_7522889 < baseStart_7522889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522900 : List Nat := [2, 4, 1, 1, 1, 5, 1, 1, 2, 3, 2]
def baseStart_7522900 : Nat := 118140960795 + 7522900 * 2 ^ 59
def prefixEnd_7522900 : Nat := 4983230072969 + 3 ^ 40 * 7522900 * 2
def baseEnd_7522900 : Nat := 3862863615708721852852819

theorem tailTrace_7522900 : CollatzResearch.WordTrace tailWord_7522900 prefixEnd_7522900 3862863615708721852852819 := by
  unfold tailWord_7522900
  simp only [CollatzResearch.WordTrace]
  refine ⟨137191352222912791938119077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182921802963883722584158769 137191352222912791938119077)
  ·
    refine ⟨25723378541796148488397327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137191352222912791938119077 25723378541796148488397327)
    ·
      refine ⟨38585067812694222732595991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25723378541796148488397327 38585067812694222732595991)
      ·
        refine ⟨57877601719041334098893987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38585067812694222732595991 57877601719041334098893987)
        ·
          refine ⟨86816402578562001148340981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57877601719041334098893987 86816402578562001148340981)
          ·
            refine ⟨8139037741740187607656967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86816402578562001148340981 8139037741740187607656967)
            ·
              refine ⟨12208556612610281411485451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8139037741740187607656967 12208556612610281411485451)
              ·
                refine ⟨18312834918915422117228177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12208556612610281411485451 18312834918915422117228177)
                ·
                  refine ⟨13734626189186566587921133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18312834918915422117228177 13734626189186566587921133)
                  ·
                    refine ⟨5150484820944962470470425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13734626189186566587921133 5150484820944962470470425)
                    ·
                      refine ⟨3862863615708721852852819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5150484820944962470470425 3862863615708721852852819)
                      ·
                        rfl

theorem cell23_7522900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_7522900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522900 prefixEnd_7522900 := by exact prefixLift 7522900
  have htrace : WordTrace (prefixWord ++ tailWord_7522900) baseStart_7522900 baseEnd_7522900 := by
    simpa [prefixWord, tailWord_7522900, baseEnd_7522900] using wordTrace_append hprefix tailTrace_7522900
  have hstable : (prefixWord ++ tailWord_7522900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522900).length < 2 ^ (prefixWord ++ tailWord_7522900).sum := by decide
  have hdescent : baseEnd_7522900 < baseStart_7522900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522913 : List Nat := [1, 2, 3, 1, 1, 4, 4, 1, 1, 1, 4]
def baseStart_7522913 : Nat := 118140960795 + 7522913 * 2 ^ 59
def prefixEnd_7522913 : Nat := 4983230072969 + 3 ^ 40 * 7522913 * 2
def baseEnd_7522913 : Nat := 3862870290957230301990259

theorem tailTrace_7522913 : CollatzResearch.WordTrace tailWord_7522913 prefixEnd_7522913 3862870290957230301990259 := by
  unfold tailWord_7522913
  simp only [CollatzResearch.WordTrace]
  refine ⟨274383178594778487096461393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182922119063185658064307595 274383178594778487096461393)
  ·
    refine ⟨205787383946083865322346045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274383178594778487096461393 205787383946083865322346045)
    ·
      refine ⟨77170268979781449495879767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205787383946083865322346045 77170268979781449495879767)
      ·
        refine ⟨115755403469672174243819651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77170268979781449495879767 115755403469672174243819651)
        ·
          refine ⟨173633105204508261365729477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115755403469672174243819651 173633105204508261365729477)
          ·
            refine ⟨32556207225845299006074277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173633105204508261365729477 32556207225845299006074277)
            ·
              refine ⟨6104288854845993563638927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32556207225845299006074277 6104288854845993563638927)
              ·
                refine ⟨9156433282268990345458391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6104288854845993563638927 9156433282268990345458391)
                ·
                  refine ⟨13734649923403485518187587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9156433282268990345458391 13734649923403485518187587)
                  ·
                    refine ⟨20601974885105228277281381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13734649923403485518187587 20601974885105228277281381)
                    ·
                      refine ⟨3862870290957230301990259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20601974885105228277281381 3862870290957230301990259)
                      ·
                        rfl

theorem cell23_7522913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_7522913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522913 prefixEnd_7522913 := by exact prefixLift 7522913
  have htrace : WordTrace (prefixWord ++ tailWord_7522913) baseStart_7522913 baseEnd_7522913 := by
    simpa [prefixWord, tailWord_7522913, baseEnd_7522913] using wordTrace_append hprefix tailTrace_7522913
  have hstable : (prefixWord ++ tailWord_7522913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522913).length < 2 ^ (prefixWord ++ tailWord_7522913).sum := by decide
  have hdescent : baseEnd_7522913 < baseStart_7522913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522929 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 2, 7, 3]
def baseStart_7522929 : Nat := 118140960795 + 7522929 * 2 ^ 59
def prefixEnd_7522929 : Nat := 4983230072969 + 3 ^ 40 * 7522929 * 2
def baseEnd_7522929 : Nat := 3862878506647702239390185

theorem tailTrace_7522929 : CollatzResearch.WordTrace tailWord_7522929 prefixEnd_7522929 3862878506647702239390185 := by
  unfold tailWord_7522929
  simp only [CollatzResearch.WordTrace]
  refine ⟨274383762162720521829043841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182922508108480347886029227 274383762162720521829043841)
  ·
    refine ⟨205787821622040391371782881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274383762162720521829043841 205787821622040391371782881)
    ·
      refine ⟨154340866216530293528837161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205787821622040391371782881 154340866216530293528837161)
      ·
        refine ⟨115755649662397720146627871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154340866216530293528837161 115755649662397720146627871)
        ·
          refine ⟨173633474493596580219941807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115755649662397720146627871 173633474493596580219941807)
          ·
            refine ⟨260450211740394870329912711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173633474493596580219941807 260450211740394870329912711)
            ·
              refine ⟨390675317610592305494869067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260450211740394870329912711 390675317610592305494869067)
              ·
                refine ⟨586012976415888458242303601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390675317610592305494869067 586012976415888458242303601)
                ·
                  refine ⟨439509732311916343681727701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586012976415888458242303601 439509732311916343681727701)
                  ·
                    refine ⟨10301009351060539305040493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 439509732311916343681727701 10301009351060539305040493)
                    ·
                      refine ⟨3862878506647702239390185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10301009351060539305040493 3862878506647702239390185)
                      ·
                        rfl

theorem cell23_7522929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_7522929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522929 prefixEnd_7522929 := by exact prefixLift 7522929
  have htrace : WordTrace (prefixWord ++ tailWord_7522929) baseStart_7522929 baseEnd_7522929 := by
    simpa [prefixWord, tailWord_7522929, baseEnd_7522929] using wordTrace_append hprefix tailTrace_7522929
  have hstable : (prefixWord ++ tailWord_7522929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522929).length < 2 ^ (prefixWord ++ tailWord_7522929).sum := by decide
  have hdescent : baseEnd_7522929 < baseStart_7522929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522933 : List Nat := [1, 3, 4, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_7522933 : Nat := 118140960795 + 7522933 * 2 ^ 59
def prefixEnd_7522933 : Nat := 4983230072969 + 3 ^ 40 * 7522933 * 2
def baseEnd_7522933 : Nat := 3862880560570320223740167

theorem tailTrace_7522933 : CollatzResearch.WordTrace tailWord_7522933 prefixEnd_7522933 3862880560570320223740167 := by
  unfold tailWord_7522933
  simp only [CollatzResearch.WordTrace]
  refine ⟨274383908054706030512189453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182922605369804020341459635 274383908054706030512189453)
  ·
    refine ⟨102893965520514761442071045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274383908054706030512189453 102893965520514761442071045)
    ·
      refine ⟨19292618535096517770388321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102893965520514761442071045 19292618535096517770388321)
      ·
        refine ⟨14469463901322388327791241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19292618535096517770388321 14469463901322388327791241)
        ·
          refine ⟨10852097925991791245843431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14469463901322388327791241 10852097925991791245843431)
          ·
            refine ⟨16278146888987686868765147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10852097925991791245843431 16278146888987686868765147)
            ·
              refine ⟨24417220333481530303147721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16278146888987686868765147 24417220333481530303147721)
              ·
                refine ⟨18312915250111147727360791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24417220333481530303147721 18312915250111147727360791)
                ·
                  refine ⟨27469372875166721591041187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18312915250111147727360791 27469372875166721591041187)
                  ·
                    refine ⟨41204059312750082386561781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27469372875166721591041187 41204059312750082386561781)
                    ·
                      refine ⟨3862880560570320223740167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41204059312750082386561781 3862880560570320223740167)
                      ·
                        rfl

theorem cell23_7522933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_7522933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522933 prefixEnd_7522933 := by exact prefixLift 7522933
  have htrace : WordTrace (prefixWord ++ tailWord_7522933) baseStart_7522933 baseEnd_7522933 := by
    simpa [prefixWord, tailWord_7522933, baseEnd_7522933] using wordTrace_append hprefix tailTrace_7522933
  have hstable : (prefixWord ++ tailWord_7522933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522933).length < 2 ^ (prefixWord ++ tailWord_7522933).sum := by decide
  have hdescent : baseEnd_7522933 < baseStart_7522933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522964 : List Nat := [2, 4, 2, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_7522964 : Nat := 118140960795 + 7522964 * 2 ^ 59
def prefixEnd_7522964 : Nat := 4983230072969 + 3 ^ 40 * 7522964 * 2
def baseEnd_7522964 : Nat := 3862896478470609602452525

theorem tailTrace_7522964 : CollatzResearch.WordTrace tailWord_7522964 prefixEnd_7522964 3862896478470609602452525 := by
  unfold tailWord_7522964
  simp only [CollatzResearch.WordTrace]
  refine ⟨137192519358796861403283973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182923359145062481871045297 137192519358796861403283973)
  ·
    refine ⟨25723597379774411513115745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137192519358796861403283973 25723597379774411513115745)
    ·
      refine ⟨19292698034830808634836809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25723597379774411513115745 19292698034830808634836809)
      ·
        refine ⟨14469523526123106476127607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19292698034830808634836809 14469523526123106476127607)
        ·
          refine ⟨21704285289184659714191411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14469523526123106476127607 21704285289184659714191411)
          ·
            refine ⟨32556427933776989571287117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21704285289184659714191411 32556427933776989571287117)
            ·
              refine ⟨12208660475166371089232669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32556427933776989571287117 12208660475166371089232669)
              ·
                refine ⟨4578247678187389158462251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12208660475166371089232669 4578247678187389158462251)
                ·
                  refine ⟨6867371517281083737693377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4578247678187389158462251 6867371517281083737693377)
                  ·
                    refine ⟨5150528637960812803270033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6867371517281083737693377 5150528637960812803270033)
                    ·
                      refine ⟨3862896478470609602452525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5150528637960812803270033 3862896478470609602452525)
                      ·
                        rfl

theorem cell23_7522964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_7522964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522964 prefixEnd_7522964 := by exact prefixLift 7522964
  have htrace : WordTrace (prefixWord ++ tailWord_7522964) baseStart_7522964 baseEnd_7522964 := by
    simpa [prefixWord, tailWord_7522964, baseEnd_7522964] using wordTrace_append hprefix tailTrace_7522964
  have hstable : (prefixWord ++ tailWord_7522964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522964).length < 2 ^ (prefixWord ++ tailWord_7522964).sum := by decide
  have hdescent : baseEnd_7522964 < baseStart_7522964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522979 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 2, 6]
def baseStart_7522979 : Nat := 118140960795 + 7522979 * 2 ^ 59
def prefixEnd_7522979 : Nat := 4983230072969 + 3 ^ 40 * 7522979 * 2
def baseEnd_7522979 : Nat := 1287634726893475681254985

theorem tailTrace_7522979 : CollatzResearch.WordTrace tailWord_7522979 prefixEnd_7522979 1287634726893475681254985 := by
  unfold tailWord_7522979
  simp only [CollatzResearch.WordTrace]
  refine ⟨274385585812539380368363991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182923723875026253578909327 274385585812539380368363991)
  ·
    refine ⟨411578378718809070552545987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274385585812539380368363991 411578378718809070552545987)
    ·
      refine ⟨617367568078213605828818981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411578378718809070552545987 617367568078213605828818981)
      ·
        refine ⟨115756419014665051092903559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 617367568078213605828818981 115756419014665051092903559)
        ·
          refine ⟨173634628521997576639355339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115756419014665051092903559 173634628521997576639355339)
          ·
            refine ⟨260451942782996364959033009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173634628521997576639355339 260451942782996364959033009)
            ·
              refine ⟨195338957087247273719274757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260451942782996364959033009 195338957087247273719274757)
              ·
                refine ⟨36626054453858863822364017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195338957087247273719274757 36626054453858863822364017)
                ·
                  refine ⟨27469540840394147866773013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36626054453858863822364017 27469540840394147866773013)
                  ·
                    refine ⟨1287634726893475681254985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27469540840394147866773013 1287634726893475681254985)
                    ·
                      rfl

theorem cell23_7522979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 6].length) (baseStart_7522979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522979 prefixEnd_7522979 := by exact prefixLift 7522979
  have htrace : WordTrace (prefixWord ++ tailWord_7522979) baseStart_7522979 baseEnd_7522979 := by
    simpa [prefixWord, tailWord_7522979, baseEnd_7522979] using wordTrace_append hprefix tailTrace_7522979
  have hstable : (prefixWord ++ tailWord_7522979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522979).length < 2 ^ (prefixWord ++ tailWord_7522979).sum := by decide
  have hdescent : baseEnd_7522979 < baseStart_7522979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7522997 : List Nat := [1, 3, 3, 3, 1, 1, 4, 1, 2, 1, 3]
def baseStart_7522997 : Nat := 118140960795 + 7522997 * 2 ^ 59
def prefixEnd_7522997 : Nat := 4983230072969 + 3 ^ 40 * 7522997 * 2
def baseEnd_7522997 : Nat := 3862913423332207973339873

theorem tailTrace_7522997 : CollatzResearch.WordTrace tailWord_7522997 prefixEnd_7522997 3862913423332207973339873 := by
  unfold tailWord_7522997
  simp only [CollatzResearch.WordTrace]
  refine ⟨274386242326474169442519245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182924161550982779628346163 274386242326474169442519245)
  ·
    refine ⟨102894840872427813540944717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274386242326474169442519245 102894840872427813540944717)
    ·
      refine ⟨38585565327160430077854269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102894840872427813540944717 38585565327160430077854269)
      ·
        refine ⟨14469586997685161279195351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38585565327160430077854269 14469586997685161279195351)
        ·
          refine ⟨21704380496527741918793027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14469586997685161279195351 21704380496527741918793027)
          ·
            refine ⟨32556570744791612878189541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21704380496527741918793027 32556570744791612878189541)
            ·
              refine ⟨6104357014648427414660539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32556570744791612878189541 6104357014648427414660539)
              ·
                refine ⟨9156535521972641121990809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6104357014648427414660539 9156535521972641121990809)
                ·
                  refine ⟨6867401641479480841493107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9156535521972641121990809 6867401641479480841493107)
                  ·
                    refine ⟨10301102462219221262239661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6867401641479480841493107 10301102462219221262239661)
                    ·
                      refine ⟨3862913423332207973339873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10301102462219221262239661 3862913423332207973339873)
                      ·
                        rfl

theorem cell23_7522997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_7522997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7522997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7522997 prefixEnd_7522997 := by exact prefixLift 7522997
  have htrace : WordTrace (prefixWord ++ tailWord_7522997) baseStart_7522997 baseEnd_7522997 := by
    simpa [prefixWord, tailWord_7522997, baseEnd_7522997] using wordTrace_append hprefix tailTrace_7522997
  have hstable : (prefixWord ++ tailWord_7522997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7522997).length < 2 ^ (prefixWord ++ tailWord_7522997).sum := by decide
  have hdescent : baseEnd_7522997 < baseStart_7522997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7522997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523006 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_7523006 : Nat := 118140960795 + 7523006 * 2 ^ 59
def prefixEnd_7523006 : Nat := 4983230072969 + 3 ^ 40 * 7523006 * 2
def baseEnd_7523006 : Nat := 3862918044658098438127331

theorem tailTrace_7523006 : CollatzResearch.WordTrace tailWord_7523006 prefixEnd_7523006 3862918044658098438127331 := by
  unfold tailWord_7523006
  simp only [CollatzResearch.WordTrace]
  refine ⟨34298321322930195497449609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182924380388961042653064581 34298321322930195497449609)
  ·
    refine ⟨25723740992197646623087207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34298321322930195497449609 25723740992197646623087207)
    ·
      refine ⟨38585611488296469934630811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25723740992197646623087207 38585611488296469934630811)
      ·
        refine ⟨57878417232444704901946217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38585611488296469934630811 57878417232444704901946217)
        ·
          refine ⟨43408812924333528676459663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57878417232444704901946217 43408812924333528676459663)
          ·
            refine ⟨65113219386500293014689495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43408812924333528676459663 65113219386500293014689495)
            ·
              refine ⟨97669829079750439522034243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65113219386500293014689495 97669829079750439522034243)
              ·
                refine ⟨146504743619625659283051365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97669829079750439522034243 146504743619625659283051365)
                ·
                  refine ⟨27469639428679811115572131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146504743619625659283051365 27469639428679811115572131)
                  ·
                    refine ⟨41204459143019716673358197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27469639428679811115572131 41204459143019716673358197)
                    ·
                      refine ⟨3862918044658098438127331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41204459143019716673358197 3862918044658098438127331)
                      ·
                        rfl

theorem cell23_7523006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_7523006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523006 prefixEnd_7523006 := by exact prefixLift 7523006
  have htrace : WordTrace (prefixWord ++ tailWord_7523006) baseStart_7523006 baseEnd_7523006 := by
    simpa [prefixWord, tailWord_7523006, baseEnd_7523006] using wordTrace_append hprefix tailTrace_7523006
  have hstable : (prefixWord ++ tailWord_7523006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523006).length < 2 ^ (prefixWord ++ tailWord_7523006).sum := by decide
  have hdescent : baseEnd_7523006 < baseStart_7523006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523020 : List Nat := [2, 2, 1, 5, 1, 2, 1, 2, 1, 4, 2]
def baseStart_7523020 : Nat := 118140960795 + 7523020 * 2 ^ 59
def prefixEnd_7523020 : Nat := 4983230072969 + 3 ^ 40 * 7523020 * 2
def baseEnd_7523020 : Nat := 3862925233387261383352267

theorem tailTrace_7523020 : CollatzResearch.WordTrace tailWord_7523020 prefixEnd_7523020 3862925233387261383352267 := by
  unfold tailWord_7523020
  simp only [CollatzResearch.WordTrace]
  refine ⟨137193540602695422185303257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182924720803593896247071009 137193540602695422185303257)
  ·
    refine ⟨102895155452021566638977443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137193540602695422185303257 102895155452021566638977443)
    ·
      refine ⟨154342733178032349958466165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102895155452021566638977443 154342733178032349958466165)
      ·
        refine ⟨14469631235440532808606203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154342733178032349958466165 14469631235440532808606203)
        ·
          refine ⟨21704446853160799212909305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14469631235440532808606203 21704446853160799212909305)
          ·
            refine ⟨16278335139870599409681979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21704446853160799212909305 16278335139870599409681979)
            ·
              refine ⟨24417502709805899114522969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16278335139870599409681979 24417502709805899114522969)
              ·
                refine ⟨18313127032354424335892227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24417502709805899114522969 18313127032354424335892227)
                ·
                  refine ⟨27469690548531636503838341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18313127032354424335892227 27469690548531636503838341)
                  ·
                    refine ⟨5150566977849681844469689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27469690548531636503838341 5150566977849681844469689)
                    ·
                      refine ⟨3862925233387261383352267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5150566977849681844469689 3862925233387261383352267)
                      ·
                        rfl

theorem cell23_7523020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_7523020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523020 prefixEnd_7523020 := by exact prefixLift 7523020
  have htrace : WordTrace (prefixWord ++ tailWord_7523020) baseStart_7523020 baseEnd_7523020 := by
    simpa [prefixWord, tailWord_7523020, baseEnd_7523020] using wordTrace_append hprefix tailTrace_7523020
  have hstable : (prefixWord ++ tailWord_7523020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523020).length < 2 ^ (prefixWord ++ tailWord_7523020).sum := by decide
  have hdescent : baseEnd_7523020 < baseStart_7523020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523053 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_7523053 : Nat := 118140960795 + 7523053 * 2 ^ 59
def prefixEnd_7523053 : Nat := 4983230072969 + 3 ^ 40 * 7523053 * 2
def baseEnd_7523053 : Nat := 3862942178248859754239615

theorem tailTrace_7523053 : CollatzResearch.WordTrace tailWord_7523053 prefixEnd_7523053 3862942178248859754239615 := by
  unfold tailWord_7523053
  simp only [CollatzResearch.WordTrace]
  refine ⟨274388284814271291006557813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182925523209514194004371875 274388284814271291006557813)
  ·
    refine ⟨25723901701337933531864795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 274388284814271291006557813 25723901701337933531864795)
    ·
      refine ⟨38585852552006900297797193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25723901701337933531864795 38585852552006900297797193)
      ·
        refine ⟨28939389414005175223347895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38585852552006900297797193 28939389414005175223347895)
        ·
          refine ⟨43409084121007762835021843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28939389414005175223347895 43409084121007762835021843)
          ·
            refine ⟨65113626181511644252532765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43409084121007762835021843 65113626181511644252532765)
            ·
              refine ⟨24417609818066866594699787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65113626181511644252532765 24417609818066866594699787)
              ·
                refine ⟨36626414727100299892049681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24417609818066866594699787 36626414727100299892049681)
                ·
                  refine ⟨27469811045325224919037261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36626414727100299892049681 27469811045325224919037261)
                  ·
                    refine ⟨10301179141996959344638973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27469811045325224919037261 10301179141996959344638973)
                    ·
                      refine ⟨3862942178248859754239615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10301179141996959344638973 3862942178248859754239615)
                      ·
                        rfl

theorem cell23_7523053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_7523053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523053 prefixEnd_7523053 := by exact prefixLift 7523053
  have htrace : WordTrace (prefixWord ++ tailWord_7523053) baseStart_7523053 baseEnd_7523053 := by
    simpa [prefixWord, tailWord_7523053, baseEnd_7523053] using wordTrace_append hprefix tailTrace_7523053
  have hstable : (prefixWord ++ tailWord_7523053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523053).length < 2 ^ (prefixWord ++ tailWord_7523053).sum := by decide
  have hdescent : baseEnd_7523053 < baseStart_7523053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523093 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 4, 4, 2]
def baseStart_7523093 : Nat := 118140960795 + 7523093 * 2 ^ 59
def prefixEnd_7523093 : Nat := 4983230072969 + 3 ^ 40 * 7523093 * 2
def baseEnd_7523093 : Nat := 3862962717475039597739431

theorem tailTrace_7523093 : CollatzResearch.WordTrace tailWord_7523093 prefixEnd_7523093 3862962717475039597739431 := by
  unfold tailWord_7523093
  simp only [CollatzResearch.WordTrace]
  refine ⟨274389743734126377838013933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182926495822750918558675955 274389743734126377838013933)
  ·
    refine ⟨102896153900297391689255225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274389743734126377838013933 102896153900297391689255225)
    ·
      refine ⟨77172115425223043766941419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102896153900297391689255225 77172115425223043766941419)
      ·
        refine ⟨115758173137834565650412129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77172115425223043766941419 115758173137834565650412129)
        ·
          refine ⟨86818629853375924237809097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115758173137834565650412129 86818629853375924237809097)
          ·
            refine ⟨65113972390031943178356823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86818629853375924237809097 65113972390031943178356823)
            ·
              refine ⟨97670958585047914767535235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65113972390031943178356823 97670958585047914767535235)
              ·
                refine ⟨146506437877571872151302853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97670958585047914767535235 146506437877571872151302853)
                ·
                  refine ⟨27469957102044726028369285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146506437877571872151302853 27469957102044726028369285)
                  ·
                    refine ⟨5150616956633386130319241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27469957102044726028369285 5150616956633386130319241)
                    ·
                      refine ⟨3862962717475039597739431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5150616956633386130319241 3862962717475039597739431)
                      ·
                        rfl

theorem cell23_7523093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_7523093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523093 prefixEnd_7523093 := by exact prefixLift 7523093
  have htrace : WordTrace (prefixWord ++ tailWord_7523093) baseStart_7523093 baseEnd_7523093 := by
    simpa [prefixWord, tailWord_7523093, baseEnd_7523093] using wordTrace_append hprefix tailTrace_7523093
  have hstable : (prefixWord ++ tailWord_7523093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523093).length < 2 ^ (prefixWord ++ tailWord_7523093).sum := by decide
  have hdescent : baseEnd_7523093 < baseStart_7523093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523103 : List Nat := [1, 1, 2, 4, 2, 2, 1, 3, 3, 4]
def baseStart_7523103 : Nat := 118140960795 + 7523103 * 2 ^ 59
def prefixEnd_7523103 : Nat := 4983230072969 + 3 ^ 40 * 7523103 * 2
def baseEnd_7523103 : Nat := 1287655950760528186204795

theorem tailTrace_7523103 : CollatzResearch.WordTrace tailWord_7523103 prefixEnd_7523103 1287655950760528186204795 := by
  unfold tailWord_7523103
  simp only [CollatzResearch.WordTrace]
  refine ⟨274390108464090149545877963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182926738976060099697251975 274390108464090149545877963)
  ·
    refine ⟨411585162696135224318816945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274390108464090149545877963 411585162696135224318816945)
    ·
      refine ⟨308688872022101418239112709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411585162696135224318816945 308688872022101418239112709)
      ·
        refine ⟨57879163504144015919833633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 308688872022101418239112709 57879163504144015919833633)
        ·
          refine ⟨43409372628108011939875225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57879163504144015919833633 43409372628108011939875225)
          ·
            refine ⟨32557029471081008954906419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43409372628108011939875225 32557029471081008954906419)
            ·
              refine ⟨48835544206621513432359629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32557029471081008954906419 48835544206621513432359629)
              ·
                refine ⟨18313329077483067537134861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48835544206621513432359629 18313329077483067537134861)
                ·
                  refine ⟨6867498404056150326425573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18313329077483067537134861 6867498404056150326425573)
                  ·
                    refine ⟨1287655950760528186204795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6867498404056150326425573 1287655950760528186204795)
                    ·
                      rfl

theorem cell23_7523103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 4].length) (baseStart_7523103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523103 prefixEnd_7523103 := by exact prefixLift 7523103
  have htrace : WordTrace (prefixWord ++ tailWord_7523103) baseStart_7523103 baseEnd_7523103 := by
    simpa [prefixWord, tailWord_7523103, baseEnd_7523103] using wordTrace_append hprefix tailTrace_7523103
  have hstable : (prefixWord ++ tailWord_7523103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523103).length < 2 ^ (prefixWord ++ tailWord_7523103).sum := by decide
  have hdescent : baseEnd_7523103 < baseStart_7523103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523183 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 2, 6, 2]
def baseStart_7523183 : Nat := 118140960795 + 7523183 * 2 ^ 59
def prefixEnd_7523183 : Nat := 4983230072969 + 3 ^ 40 * 7523183 * 2
def baseEnd_7523183 : Nat := 3863008930733944245614017

theorem tailTrace_7523183 : CollatzResearch.WordTrace tailWord_7523183 prefixEnd_7523183 3863008930733944245614017 := by
  unfold tailWord_7523183
  simp only [CollatzResearch.WordTrace]
  refine ⟨274393026303800323208790203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182928684202533548805860135 274393026303800323208790203)
  ·
    refine ⟨411589539455700484813185305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274393026303800323208790203 411589539455700484813185305)
    ·
      refine ⟨308692154591775363609888979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411589539455700484813185305 308692154591775363609888979)
      ·
        refine ⟨463038231887663045414833469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308692154591775363609888979 463038231887663045414833469)
        ·
          refine ⟨173639336957873642030562551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 463038231887663045414833469 173639336957873642030562551)
          ·
            refine ⟨260459005436810463045843827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173639336957873642030562551 260459005436810463045843827)
            ·
              refine ⟨390688508155215694568765741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260459005436810463045843827 390688508155215694568765741)
              ·
                refine ⟨146508190558205885463287153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 390688508155215694568765741 146508190558205885463287153)
                ·
                  refine ⟨109881142918654414097465365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146508190558205885463287153 109881142918654414097465365)
                  ·
                    refine ⟨5150678574311925660818689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109881142918654414097465365 5150678574311925660818689)
                    ·
                      refine ⟨3863008930733944245614017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5150678574311925660818689 3863008930733944245614017)
                      ·
                        rfl

theorem cell23_7523183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 6, 2].length) (baseStart_7523183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523183 prefixEnd_7523183 := by exact prefixLift 7523183
  have htrace : WordTrace (prefixWord ++ tailWord_7523183) baseStart_7523183 baseEnd_7523183 := by
    simpa [prefixWord, tailWord_7523183, baseEnd_7523183] using wordTrace_append hprefix tailTrace_7523183
  have hstable : (prefixWord ++ tailWord_7523183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523183).length < 2 ^ (prefixWord ++ tailWord_7523183).sum := by decide
  have hdescent : baseEnd_7523183 < baseStart_7523183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523193 : List Nat := [1, 2, 1, 3, 2, 4, 1, 2, 1, 6]
def baseStart_7523193 : Nat := 118140960795 + 7523193 * 2 ^ 59
def prefixEnd_7523193 : Nat := 4983230072969 + 3 ^ 40 * 7523193 * 2
def baseEnd_7523193 : Nat := 1287671355180163068829657

theorem tailTrace_7523193 : CollatzResearch.WordTrace tailWord_7523193 prefixEnd_7523193 1287671355180163068829657 := by
  unfold tailWord_7523193
  simp only [CollatzResearch.WordTrace]
  refine ⟨274393391033764094916654233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182928927355842729944436155 274393391033764094916654233)
  ·
    refine ⟨205795043275323071187490675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274393391033764094916654233 205795043275323071187490675)
    ·
      refine ⟨308692564912984606781236013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205795043275323071187490675 308692564912984606781236013)
      ·
        refine ⟨115759711842369227542963505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308692564912984606781236013 115759711842369227542963505)
        ·
          refine ⟨86819783881776920657222629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115759711842369227542963505 86819783881776920657222629)
          ·
            refine ⟨16278709477833172623229243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86819783881776920657222629 16278709477833172623229243)
            ·
              refine ⟨24418064216749758934843865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16278709477833172623229243 24418064216749758934843865)
              ·
                refine ⟨18313548162562319201132899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24418064216749758934843865 18313548162562319201132899)
                ·
                  refine ⟨27470322243843478801699349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18313548162562319201132899 27470322243843478801699349)
                  ·
                    refine ⟨1287671355180163068829657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27470322243843478801699349 1287671355180163068829657)
                    ·
                      rfl

theorem cell23_7523193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 6].length) (baseStart_7523193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523193 prefixEnd_7523193 := by exact prefixLift 7523193
  have htrace : WordTrace (prefixWord ++ tailWord_7523193) baseStart_7523193 baseEnd_7523193 := by
    simpa [prefixWord, tailWord_7523193, baseEnd_7523193] using wordTrace_append hprefix tailTrace_7523193
  have hstable : (prefixWord ++ tailWord_7523193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523193).length < 2 ^ (prefixWord ++ tailWord_7523193).sum := by decide
  have hdescent : baseEnd_7523193 < baseStart_7523193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523200 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 7, 2, 2]
def baseStart_7523200 : Nat := 118140960795 + 7523200 * 2 ^ 59
def prefixEnd_7523200 : Nat := 4983230072969 + 3 ^ 40 * 7523200 * 2
def baseEnd_7523200 : Nat := 3863017659905070679101439

theorem tailTrace_7523200 : CollatzResearch.WordTrace tailWord_7523200 prefixEnd_7523200 3863017659905070679101439 := by
  unfold tailWord_7523200
  simp only [CollatzResearch.WordTrace]
  refine ⟨137196823172369367556079527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182929097563159156741439369 137196823172369367556079527)
  ·
    refine ⟨205795234758554051334119291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137196823172369367556079527 205795234758554051334119291)
    ·
      refine ⟨308692852137831077001178937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205795234758554051334119291 308692852137831077001178937)
      ·
        refine ⟨231519639103373307750884203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308692852137831077001178937 231519639103373307750884203)
        ·
          refine ⟨347279458655059961626326305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231519639103373307750884203 347279458655059961626326305)
          ·
            refine ⟨260459593991294971219744729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347279458655059961626326305 260459593991294971219744729)
            ·
              refine ⟨195344695493471228414808547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260459593991294971219744729 195344695493471228414808547)
              ·
                refine ⟨293017043240206842622212821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195344695493471228414808547 293017043240206842622212821)
                ·
                  refine ⟨6867586950942347873958113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 293017043240206842622212821 6867586950942347873958113)
                  ·
                    refine ⟨5150690213206760905468585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6867586950942347873958113 5150690213206760905468585)
                    ·
                      refine ⟨3863017659905070679101439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5150690213206760905468585 3863017659905070679101439)
                      ·
                        rfl

theorem cell23_7523200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 7, 2, 2].length) (baseStart_7523200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523200 prefixEnd_7523200 := by exact prefixLift 7523200
  have htrace : WordTrace (prefixWord ++ tailWord_7523200) baseStart_7523200 baseEnd_7523200 := by
    simpa [prefixWord, tailWord_7523200, baseEnd_7523200] using wordTrace_append hprefix tailTrace_7523200
  have hstable : (prefixWord ++ tailWord_7523200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523200).length < 2 ^ (prefixWord ++ tailWord_7523200).sum := by decide
  have hdescent : baseEnd_7523200 < baseStart_7523200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523220 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_7523220 : Nat := 118140960795 + 7523220 * 2 ^ 59
def prefixEnd_7523220 : Nat := 4983230072969 + 3 ^ 40 * 7523220 * 2
def baseEnd_7523220 : Nat := 3863027929518160600851347

theorem tailTrace_7523220 : CollatzResearch.WordTrace tailWord_7523220 prefixEnd_7523220 3863027929518160600851347 := by
  unfold tailWord_7523220
  simp only [CollatzResearch.WordTrace]
  refine ⟨137197187902333139263943557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182929583869777519018591409 137197187902333139263943557)
  ·
    refine ⟨25724472731687463611989417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137197187902333139263943557 25724472731687463611989417)
    ·
      refine ⟨19293354548765597708992063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25724472731687463611989417 19293354548765597708992063)
      ·
        refine ⟨28940031823148396563488095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19293354548765597708992063 28940031823148396563488095)
        ·
          refine ⟨43410047734722594845232143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28940031823148396563488095 43410047734722594845232143)
          ·
            refine ⟨65115071602083892267848215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43410047734722594845232143 65115071602083892267848215)
            ·
              refine ⟨97672607403125838401772323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65115071602083892267848215 97672607403125838401772323)
              ·
                refine ⟨146508911104688757602658485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97672607403125838401772323 146508911104688757602658485)
                ·
                  refine ⟨13735210416064571025249233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146508911104688757602658485 13735210416064571025249233)
                  ·
                    refine ⟨10301407812048428268936925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13735210416064571025249233 10301407812048428268936925)
                    ·
                      refine ⟨3863027929518160600851347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10301407812048428268936925 3863027929518160600851347)
                      ·
                        rfl

theorem cell23_7523220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_7523220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523220 prefixEnd_7523220 := by exact prefixLift 7523220
  have htrace : WordTrace (prefixWord ++ tailWord_7523220) baseStart_7523220 baseEnd_7523220 := by
    simpa [prefixWord, tailWord_7523220, baseEnd_7523220] using wordTrace_append hprefix tailTrace_7523220
  have hstable : (prefixWord ++ tailWord_7523220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523220).length < 2 ^ (prefixWord ++ tailWord_7523220).sum := by decide
  have hdescent : baseEnd_7523220 < baseStart_7523220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523234 : List Nat := [3, 3, 1, 2, 2, 2, 1, 2, 3, 2, 2]
def baseStart_7523234 : Nat := 118140960795 + 7523234 * 2 ^ 59
def prefixEnd_7523234 : Nat := 4983230072969 + 3 ^ 40 * 7523234 * 2
def baseEnd_7523234 : Nat := 3863035118247323546076283

theorem tailTrace_7523234 : CollatzResearch.WordTrace tailWord_7523234 prefixEnd_7523234 3863035118247323546076283 := by
  unfold tailWord_7523234
  simp only [CollatzResearch.WordTrace]
  refine ⟨68598721606653889729724189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182929924284410372612597837 68598721606653889729724189)
  ·
    refine ⟨25724520602495208648646571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68598721606653889729724189 25724520602495208648646571)
    ·
      refine ⟨38586780903742812972969857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25724520602495208648646571 38586780903742812972969857)
      ·
        refine ⟨28940085677807109729727393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38586780903742812972969857 28940085677807109729727393)
        ·
          refine ⟨21705064258355332297295545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28940085677807109729727393 21705064258355332297295545)
          ·
            refine ⟨16278798193766499222971659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21705064258355332297295545 16278798193766499222971659)
            ·
              refine ⟨24418197290649748834457489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16278798193766499222971659 24418197290649748834457489)
              ·
                refine ⟨18313647967987311625843117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24418197290649748834457489 18313647967987311625843117)
                ·
                  refine ⟨6867617987995241859691169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18313647967987311625843117 6867617987995241859691169)
                  ·
                    refine ⟨5150713490996431394768377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6867617987995241859691169 5150713490996431394768377)
                    ·
                      refine ⟨3863035118247323546076283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5150713490996431394768377 3863035118247323546076283)
                      ·
                        rfl

theorem cell23_7523234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_7523234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523234 prefixEnd_7523234 := by exact prefixLift 7523234
  have htrace : WordTrace (prefixWord ++ tailWord_7523234) baseStart_7523234 baseEnd_7523234 := by
    simpa [prefixWord, tailWord_7523234, baseEnd_7523234] using wordTrace_append hprefix tailTrace_7523234
  have hstable : (prefixWord ++ tailWord_7523234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523234).length < 2 ^ (prefixWord ++ tailWord_7523234).sum := by decide
  have hdescent : baseEnd_7523234 < baseStart_7523234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523383 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 5]
def baseStart_7523383 : Nat := 118140960795 + 7523383 * 2 ^ 59
def prefixEnd_7523383 : Nat := 4983230072969 + 3 ^ 40 * 7523383 * 2
def baseEnd_7523383 : Nat := 3863111626864843463113097

theorem tailTrace_7523383 : CollatzResearch.WordTrace tailWord_7523383 prefixEnd_7523383 3863111626864843463113097 := by
  unfold tailWord_7523383
  simp only [CollatzResearch.WordTrace]
  refine ⟨274400320903075757366070803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182933547268717171577380535 274400320903075757366070803)
  ·
    refine ⟨411600481354613636049106205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274400320903075757366070803 411600481354613636049106205)
    ·
      refine ⟨154350180507980113518414827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411600481354613636049106205 154350180507980113518414827)
      ·
        refine ⟨231525270761970170277622241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154350180507980113518414827 231525270761970170277622241)
        ·
          refine ⟨173643953071477627708216681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231525270761970170277622241 173643953071477627708216681)
          ·
            refine ⟨130232964803608220781162511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173643953071477627708216681 130232964803608220781162511)
            ·
              refine ⟨195349447205412331171743767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130232964803608220781162511 195349447205412331171743767)
              ·
                refine ⟨293024170808118496757615651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195349447205412331171743767 293024170808118496757615651)
                ·
                  refine ⟨439536256212177745136423477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293024170808118496757615651 439536256212177745136423477)
                  ·
                    refine ⟨41206524019891663606539701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 439536256212177745136423477 41206524019891663606539701)
                    ·
                      refine ⟨3863111626864843463113097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41206524019891663606539701 3863111626864843463113097)
                      ·
                        rfl

theorem cell23_7523383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_7523383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523383 prefixEnd_7523383 := by exact prefixLift 7523383
  have htrace : WordTrace (prefixWord ++ tailWord_7523383) baseStart_7523383 baseEnd_7523383 := by
    simpa [prefixWord, tailWord_7523383, baseEnd_7523383] using wordTrace_append hprefix tailTrace_7523383
  have hstable : (prefixWord ++ tailWord_7523383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523383).length < 2 ^ (prefixWord ++ tailWord_7523383).sum := by decide
  have hdescent : baseEnd_7523383 < baseStart_7523383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523400 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 1, 4, 3]
def baseStart_7523400 : Nat := 118140960795 + 7523400 * 2 ^ 59
def prefixEnd_7523400 : Nat := 4983230072969 + 3 ^ 40 * 7523400 * 2
def baseEnd_7523400 : Nat := 3863120356035969896600519

theorem tailTrace_7523400 : CollatzResearch.WordTrace tailWord_7523400 prefixEnd_7523400 3863120356035969896600519 := by
  unfold tailWord_7523400
  simp only [CollatzResearch.WordTrace]
  refine ⟨137200470472007084634719827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182933960629342779512959769 137200470472007084634719827)
  ·
    refine ⟨205800705708010626952079741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137200470472007084634719827 205800705708010626952079741)
    ·
      refine ⟨77175264640503985107029903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205800705708010626952079741 77175264640503985107029903)
      ·
        refine ⟨115762896960755977660544855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77175264640503985107029903 115762896960755977660544855)
        ·
          refine ⟨173644345441133966490817283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115762896960755977660544855 173644345441133966490817283)
          ·
            refine ⟨260466518161700949736225925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173644345441133966490817283 260466518161700949736225925)
            ·
              refine ⟨48837472155318928075542361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260466518161700949736225925 48837472155318928075542361)
              ·
                refine ⟨36628104116489196056656771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48837472155318928075542361 36628104116489196056656771)
                ·
                  refine ⟨54942156174733794084985157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36628104116489196056656771 54942156174733794084985157)
                  ·
                    refine ⟨10301654282762586390934717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54942156174733794084985157 10301654282762586390934717)
                    ·
                      refine ⟨3863120356035969896600519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10301654282762586390934717 3863120356035969896600519)
                      ·
                        rfl

theorem cell23_7523400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_7523400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523400 prefixEnd_7523400 := by exact prefixLift 7523400
  have htrace : WordTrace (prefixWord ++ tailWord_7523400) baseStart_7523400 baseEnd_7523400 := by
    simpa [prefixWord, tailWord_7523400, baseEnd_7523400] using wordTrace_append hprefix tailTrace_7523400
  have hstable : (prefixWord ++ tailWord_7523400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523400).length < 2 ^ (prefixWord ++ tailWord_7523400).sum := by decide
  have hdescent : baseEnd_7523400 < baseStart_7523400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523420 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 8]
def baseStart_7523420 : Nat := 118140960795 + 7523420 * 2 ^ 59
def prefixEnd_7523420 : Nat := 4983230072969 + 3 ^ 40 * 7523420 * 2
def baseEnd_7523420 : Nat := 429236736183228868705603

theorem tailTrace_7523420 : CollatzResearch.WordTrace tailWord_7523420 prefixEnd_7523420 429236736183228868705603 := by
  unfold tailWord_7523420
  simp only [CollatzResearch.WordTrace]
  refine ⟨137200835201970856342583857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182934446935961141790111809 137200835201970856342583857)
  ·
    refine ⟨102900626401478142256937893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137200835201970856342583857 102900626401478142256937893)
    ·
      refine ⟨19293867450277151673175855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102900626401478142256937893 19293867450277151673175855)
      ·
        refine ⟨28940801175415727509763783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19293867450277151673175855 28940801175415727509763783)
        ·
          refine ⟨43411201763123591264645675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28940801175415727509763783 43411201763123591264645675)
          ·
            refine ⟨65116802644685386896968513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43411201763123591264645675 65116802644685386896968513)
            ·
              refine ⟨48837601983514040172726385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65116802644685386896968513 48837601983514040172726385)
              ·
                refine ⟨36628201487635530129544789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48837601983514040172726385 36628201487635530129544789)
                ·
                  refine ⟨429236736183228868705603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36628201487635530129544789 429236736183228868705603)
                  ·
                    rfl

theorem cell23_7523420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 8].length) (baseStart_7523420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523420 prefixEnd_7523420 := by exact prefixLift 7523420
  have htrace : WordTrace (prefixWord ++ tailWord_7523420) baseStart_7523420 baseEnd_7523420 := by
    simpa [prefixWord, tailWord_7523420, baseEnd_7523420] using wordTrace_append hprefix tailTrace_7523420
  have hstable : (prefixWord ++ tailWord_7523420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523420).length < 2 ^ (prefixWord ++ tailWord_7523420).sum := by decide
  have hdescent : baseEnd_7523420 < baseStart_7523420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523424 : List Nat := [2, 1, 1, 3, 2, 2, 4, 3, 1, 4]
def baseStart_7523424 : Nat := 118140960795 + 7523424 * 2 ^ 59
def prefixEnd_7523424 : Nat := 4983230072969 + 3 ^ 40 * 7523424 * 2
def baseEnd_7523424 : Nat := 1287710893190559267566803

theorem tailTrace_7523424 : CollatzResearch.WordTrace tailWord_7523424 prefixEnd_7523424 1287710893190559267566803 := by
  unfold tailWord_7523424
  simp only [CollatzResearch.WordTrace]
  refine ⟨137200908147963610684156663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182934544197284814245542217 137200908147963610684156663)
  ·
    refine ⟨205801362221945416026234995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137200908147963610684156663 205801362221945416026234995)
    ·
      refine ⟨308702043332918124039352493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205801362221945416026234995 308702043332918124039352493)
      ·
        refine ⟨115763266249844296514757185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308702043332918124039352493 115763266249844296514757185)
        ·
          refine ⟨86822449687383222386067889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115763266249844296514757185 86822449687383222386067889)
          ·
            refine ⟨65116837265537416789550917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86822449687383222386067889 65116837265537416789550917)
            ·
              refine ⟨12209406987288265648040797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65116837265537416789550917 12209406987288265648040797)
              ·
                refine ⟨4578527620233099618015299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12209406987288265648040797 4578527620233099618015299)
                ·
                  refine ⟨6867791430349649427022949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4578527620233099618015299 6867791430349649427022949)
                  ·
                    refine ⟨1287710893190559267566803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6867791430349649427022949 1287710893190559267566803)
                    ·
                      rfl

theorem cell23_7523424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 1, 4].length) (baseStart_7523424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523424 prefixEnd_7523424 := by exact prefixLift 7523424
  have htrace : WordTrace (prefixWord ++ tailWord_7523424) baseStart_7523424 baseEnd_7523424 := by
    simpa [prefixWord, tailWord_7523424, baseEnd_7523424] using wordTrace_append hprefix tailTrace_7523424
  have hstable : (prefixWord ++ tailWord_7523424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523424).length < 2 ^ (prefixWord ++ tailWord_7523424).sum := by decide
  have hdescent : baseEnd_7523424 < baseStart_7523424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523437 : List Nat := [1, 5, 1, 1, 2, 2, 3, 2, 6]
def baseStart_7523437 : Nat := 118140960795 + 7523437 * 2 ^ 59
def prefixEnd_7523437 : Nat := 4983230072969 + 3 ^ 40 * 7523437 * 2
def baseEnd_7523437 : Nat := 429237706091131805759761

theorem tailTrace_7523437 : CollatzResearch.WordTrace tailWord_7523437 prefixEnd_7523437 429237706091131805759761 := by
  unfold tailWord_7523437
  simp only [CollatzResearch.WordTrace]
  refine ⟨274402290444880124588536565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182934860296586749725691043 274402290444880124588536565)
  ·
    refine ⟨25725214729207511680175303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 274402290444880124588536565 25725214729207511680175303)
    ·
      refine ⟨38587822093811267520262955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25725214729207511680175303 38587822093811267520262955)
      ·
        refine ⟨57881733140716901280394433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38587822093811267520262955 57881733140716901280394433)
        ·
          refine ⟨43411299855537675960295825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57881733140716901280394433 43411299855537675960295825)
          ·
            refine ⟨32558474891653256970221869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43411299855537675960295825 32558474891653256970221869)
            ·
              refine ⟨12209428084369971363833201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32558474891653256970221869 12209428084369971363833201)
              ·
                refine ⟨9157071063277478522874901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12209428084369971363833201 9157071063277478522874901)
                ·
                  refine ⟨429237706091131805759761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9157071063277478522874901 429237706091131805759761)
                  ·
                    rfl

theorem cell23_7523437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_7523437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523437 prefixEnd_7523437 := by exact prefixLift 7523437
  have htrace : WordTrace (prefixWord ++ tailWord_7523437) baseStart_7523437 baseEnd_7523437 := by
    simpa [prefixWord, tailWord_7523437, baseEnd_7523437] using wordTrace_append hprefix tailTrace_7523437
  have hstable : (prefixWord ++ tailWord_7523437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523437).length < 2 ^ (prefixWord ++ tailWord_7523437).sum := by decide
  have hdescent : baseEnd_7523437 < baseStart_7523437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523474 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_7523474 : Nat := 118140960795 + 7523474 * 2 ^ 59
def prefixEnd_7523474 : Nat := 4983230072969 + 3 ^ 40 * 7523474 * 2
def baseEnd_7523474 : Nat := 3863158353604402607075179

theorem tailTrace_7523474 : CollatzResearch.WordTrace tailWord_7523474 prefixEnd_7523474 3863158353604402607075179 := by
  unfold tailWord_7523474
  simp only [CollatzResearch.WordTrace]
  refine ⟨68600909986436519976908369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182935759963830719938422317 68600909986436519976908369)
  ·
    refine ⟨51450682489827389982681277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68600909986436519976908369 51450682489827389982681277)
    ·
      refine ⟨19294005933685271243505479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51450682489827389982681277 19294005933685271243505479)
      ·
        refine ⟨28941008900527906865258219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19294005933685271243505479 28941008900527906865258219)
        ·
          refine ⟨43411513350791860297887329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28941008900527906865258219 43411513350791860297887329)
          ·
            refine ⟨32558635013093895223415497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43411513350791860297887329 32558635013093895223415497)
            ·
              refine ⟨24418976259820421417561623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32558635013093895223415497 24418976259820421417561623)
              ·
                refine ⟨36628464389730632126342435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24418976259820421417561623 36628464389730632126342435)
                ·
                  refine ⟨54942696584595948189513653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36628464389730632126342435 54942696584595948189513653)
                  ·
                    refine ⟨5150877804805870142766905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54942696584595948189513653 5150877804805870142766905)
                    ·
                      refine ⟨3863158353604402607075179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5150877804805870142766905 3863158353604402607075179)
                      ·
                        rfl

theorem cell23_7523474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_7523474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523474 prefixEnd_7523474 := by exact prefixLift 7523474
  have htrace : WordTrace (prefixWord ++ tailWord_7523474) baseStart_7523474 baseEnd_7523474 := by
    simpa [prefixWord, tailWord_7523474, baseEnd_7523474] using wordTrace_append hprefix tailTrace_7523474
  have hstable : (prefixWord ++ tailWord_7523474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523474).length < 2 ^ (prefixWord ++ tailWord_7523474).sum := by decide
  have hdescent : baseEnd_7523474 < baseStart_7523474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523498 : List Nat := [3, 1, 5, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_7523498 : Nat := 118140960795 + 7523498 * 2 ^ 59
def prefixEnd_7523498 : Nat := 4983230072969 + 3 ^ 40 * 7523498 * 2
def baseEnd_7523498 : Nat := 3863170677140110513175069

theorem tailTrace_7523498 : CollatzResearch.WordTrace tailWord_7523498 prefixEnd_7523498 3863170677140110513175069 := by
  unfold tailWord_7523498
  simp only [CollatzResearch.WordTrace]
  refine ⟨68601128824414783001626787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182936343531772754671004765 68601128824414783001626787)
  ·
    refine ⟨102901693236622174502440181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68601128824414783001626787 102901693236622174502440181)
    ·
      refine ⟨9647033740933328859603767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102901693236622174502440181 9647033740933328859603767)
      ·
        refine ⟨14470550611399993289405651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9647033740933328859603767 14470550611399993289405651)
        ·
          refine ⟨21705825917099989934108477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14470550611399993289405651 21705825917099989934108477)
          ·
            refine ⟨8139684718912496225290679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21705825917099989934108477 8139684718912496225290679)
            ·
              refine ⟨12209527078368744337936019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8139684718912496225290679 12209527078368744337936019)
              ·
                refine ⟨18314290617553116506904029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12209527078368744337936019 18314290617553116506904029)
                ·
                  refine ⟨6867858981582418690089011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18314290617553116506904029 6867858981582418690089011)
                  ·
                    refine ⟨10301788472373628035133517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6867858981582418690089011 10301788472373628035133517)
                    ·
                      refine ⟨3863170677140110513175069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10301788472373628035133517 3863170677140110513175069)
                      ·
                        rfl

theorem cell23_7523498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_7523498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523498 prefixEnd_7523498 := by exact prefixLift 7523498
  have htrace : WordTrace (prefixWord ++ tailWord_7523498) baseStart_7523498 baseEnd_7523498 := by
    simpa [prefixWord, tailWord_7523498, baseEnd_7523498] using wordTrace_append hprefix tailTrace_7523498
  have hstable : (prefixWord ++ tailWord_7523498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523498).length < 2 ^ (prefixWord ++ tailWord_7523498).sum := by decide
  have hdescent : baseEnd_7523498 < baseStart_7523498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523500 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 4]
def baseStart_7523500 : Nat := 118140960795 + 7523500 * 2 ^ 59
def prefixEnd_7523500 : Nat := 4983230072969 + 3 ^ 40 * 7523500 * 2
def baseEnd_7523500 : Nat := 3863171704101419505350059

theorem tailTrace_7523500 : CollatzResearch.WordTrace tailWord_7523500 prefixEnd_7523500 3863171704101419505350059 := by
  unfold tailWord_7523500
  simp only [CollatzResearch.WordTrace]
  refine ⟨137202294121825943174039977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182936392162434590898719969 137202294121825943174039977)
  ·
    refine ⟨102901720591369457380529983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137202294121825943174039977 102901720591369457380529983)
    ·
      refine ⟨154352580887054186070794975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102901720591369457380529983 154352580887054186070794975)
      ·
        refine ⟨231528871330581279106192463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154352580887054186070794975 231528871330581279106192463)
        ·
          refine ⟨347293306995871918659288695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231528871330581279106192463 347293306995871918659288695)
          ·
            refine ⟨520939960493807877988933043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347293306995871918659288695 520939960493807877988933043)
            ·
              refine ⟨781409940740711816983399565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520939960493807877988933043 781409940740711816983399565)
              ·
                refine ⟨293028727777766931368774837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 781409940740711816983399565 293028727777766931368774837)
                ·
                  refine ⟨27471443229165649815822641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 293028727777766931368774837 27471443229165649815822641)
                  ·
                    refine ⟨20603582421874237361866981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27471443229165649815822641 20603582421874237361866981)
                    ·
                      refine ⟨3863171704101419505350059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20603582421874237361866981 3863171704101419505350059)
                      ·
                        rfl

theorem cell23_7523500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_7523500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523500 prefixEnd_7523500 := by exact prefixLift 7523500
  have htrace : WordTrace (prefixWord ++ tailWord_7523500) baseStart_7523500 baseEnd_7523500 := by
    simpa [prefixWord, tailWord_7523500, baseEnd_7523500] using wordTrace_append hprefix tailTrace_7523500
  have hstable : (prefixWord ++ tailWord_7523500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523500).length < 2 ^ (prefixWord ++ tailWord_7523500).sum := by decide
  have hdescent : baseEnd_7523500 < baseStart_7523500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523521 : List Nat := [1, 2, 6, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_7523521 : Nat := 118140960795 + 7523521 * 2 ^ 59
def prefixEnd_7523521 : Nat := 4983230072969 + 3 ^ 40 * 7523521 * 2
def baseEnd_7523521 : Nat := 3863182487195163923187463

theorem tailTrace_7523521 : CollatzResearch.WordTrace tailWord_7523521 prefixEnd_7523521 3863182487195163923187463 := by
  unfold tailWord_7523521
  simp only [CollatzResearch.WordTrace]
  refine ⟨274405354176575806934594417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182936902784383871289729611 274405354176575806934594417)
  ·
    refine ⟨205804015632431855200945813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274405354176575806934594417 205804015632431855200945813)
    ·
      refine ⟨9647063232770243212544335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 205804015632431855200945813 9647063232770243212544335)
      ·
        refine ⟨14470594849155364818816503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9647063232770243212544335 14470594849155364818816503)
        ·
          refine ⟨21705892273733047228224755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14470594849155364818816503 21705892273733047228224755)
          ·
            refine ⟨32558838410599570842337133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21705892273733047228224755 32558838410599570842337133)
            ·
              refine ⟨12209564403974839065876425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32558838410599570842337133 12209564403974839065876425)
              ·
                refine ⟨9157173302981129299407319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12209564403974839065876425 9157173302981129299407319)
                ·
                  refine ⟨13735759954471693949110979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9157173302981129299407319 13735759954471693949110979)
                  ·
                    refine ⟨20603639931707540923666469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13735759954471693949110979 20603639931707540923666469)
                    ·
                      refine ⟨3863182487195163923187463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20603639931707540923666469 3863182487195163923187463)
                      ·
                        rfl

theorem cell23_7523521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_7523521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523521 prefixEnd_7523521 := by exact prefixLift 7523521
  have htrace : WordTrace (prefixWord ++ tailWord_7523521) baseStart_7523521 baseEnd_7523521 := by
    simpa [prefixWord, tailWord_7523521, baseEnd_7523521] using wordTrace_append hprefix tailTrace_7523521
  have hstable : (prefixWord ++ tailWord_7523521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523521).length < 2 ^ (prefixWord ++ tailWord_7523521).sum := by decide
  have hdescent : baseEnd_7523521 < baseStart_7523521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523534 : List Nat := [4, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4]
def baseStart_7523534 : Nat := 118140960795 + 7523534 * 2 ^ 59
def prefixEnd_7523534 : Nat := 4983230072969 + 3 ^ 40 * 7523534 * 2
def baseEnd_7523534 : Nat := 3863189162443672372324903

theorem tailTrace_7523534 : CollatzResearch.WordTrace tailWord_7523534 prefixEnd_7523534 3863189162443672372324903 := by
  unfold tailWord_7523534
  simp only [CollatzResearch.WordTrace]
  refine ⟨34300728540691088769352207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182937218883685806769878437 34300728540691088769352207)
  ·
    refine ⟨51451092811036633154028311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34300728540691088769352207 51451092811036633154028311)
    ·
      refine ⟨77176639216554949731042467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51451092811036633154028311 77176639216554949731042467)
      ·
        refine ⟨115764958824832424596563701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77176639216554949731042467 115764958824832424596563701)
        ·
          refine ⟨10852964889828039805927847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115764958824832424596563701 10852964889828039805927847)
          ·
            refine ⟨16279447334742059708891771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10852964889828039805927847 16279447334742059708891771)
            ·
              refine ⟨24419171002113089563337657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16279447334742059708891771 24419171002113089563337657)
              ·
                refine ⟨18314378251584817172503243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24419171002113089563337657 18314378251584817172503243)
                ·
                  refine ⟨27471567377377225758754865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18314378251584817172503243 27471567377377225758754865)
                  ·
                    refine ⟨20603675533032919319066149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27471567377377225758754865 20603675533032919319066149)
                    ·
                      refine ⟨3863189162443672372324903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20603675533032919319066149 3863189162443672372324903)
                      ·
                        rfl

theorem cell23_7523534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_7523534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523534 prefixEnd_7523534 := by exact prefixLift 7523534
  have htrace : WordTrace (prefixWord ++ tailWord_7523534) baseStart_7523534 baseEnd_7523534 := by
    simpa [prefixWord, tailWord_7523534, baseEnd_7523534] using wordTrace_append hprefix tailTrace_7523534
  have hstable : (prefixWord ++ tailWord_7523534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523534).length < 2 ^ (prefixWord ++ tailWord_7523534).sum := by decide
  have hdescent : baseEnd_7523534 < baseStart_7523534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523538 : List Nat := [3, 2, 2, 2, 1, 1, 2, 5, 1, 2, 2]
def baseStart_7523538 : Nat := 118140960795 + 7523538 * 2 ^ 59
def prefixEnd_7523538 : Nat := 4983230072969 + 3 ^ 40 * 7523538 * 2
def baseEnd_7523538 : Nat := 3863191216366290356674885

theorem tailTrace_7523538 : CollatzResearch.WordTrace tailWord_7523538 prefixEnd_7523538 3863191216366290356674885 := by
  unfold tailWord_7523538
  simp only [CollatzResearch.WordTrace]
  refine ⟨68601493554378554709490817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182937316145009479225308845 68601493554378554709490817)
  ·
    refine ⟨51451120165783916032118113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68601493554378554709490817 51451120165783916032118113)
    ·
      refine ⟨38588340124337937024088585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51451120165783916032118113 38588340124337937024088585)
      ·
        refine ⟨28941255093253452768066439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38588340124337937024088585 28941255093253452768066439)
        ·
          refine ⟨43411882639880179152099659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28941255093253452768066439 43411882639880179152099659)
          ·
            refine ⟨65117823959820268728149489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43411882639880179152099659 65117823959820268728149489)
            ·
              refine ⟨48838367969865201546112117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65117823959820268728149489 48838367969865201546112117)
              ·
                refine ⟨4578596997174862644948011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48838367969865201546112117 4578596997174862644948011)
                ·
                  refine ⟨6867895495762293967422017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4578596997174862644948011 6867895495762293967422017)
                  ·
                    refine ⟨5150921621821720475566513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6867895495762293967422017 5150921621821720475566513)
                    ·
                      refine ⟨3863191216366290356674885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5150921621821720475566513 3863191216366290356674885)
                      ·
                        rfl

theorem cell23_7523538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_7523538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523538 prefixEnd_7523538 := by exact prefixLift 7523538
  have htrace : WordTrace (prefixWord ++ tailWord_7523538) baseStart_7523538 baseEnd_7523538 := by
    simpa [prefixWord, tailWord_7523538, baseEnd_7523538] using wordTrace_append hprefix tailTrace_7523538
  have hstable : (prefixWord ++ tailWord_7523538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523538).length < 2 ^ (prefixWord ++ tailWord_7523538).sum := by decide
  have hdescent : baseEnd_7523538 < baseStart_7523538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523564 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 3, 3, 2]
def baseStart_7523564 : Nat := 118140960795 + 7523564 * 2 ^ 59
def prefixEnd_7523564 : Nat := 4983230072969 + 3 ^ 40 * 7523564 * 2
def baseEnd_7523564 : Nat := 3863204566863307254949765

theorem tailTrace_7523564 : CollatzResearch.WordTrace tailWord_7523564 prefixEnd_7523564 3863204566863307254949765 := by
  unfold tailWord_7523564
  simp only [CollatzResearch.WordTrace]
  refine ⟨137203461257710012639204873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182937948343613350185606497 137203461257710012639204873)
  ·
    refine ⟨102902595943282509479403655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137203461257710012639204873 102902595943282509479403655)
    ·
      refine ⟨154353893914923764219105483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102902595943282509479403655 154353893914923764219105483)
      ·
        refine ⟨231530840872385646328658225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154353893914923764219105483 231530840872385646328658225)
        ·
          refine ⟨173648130654289234746493669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231530840872385646328658225 173648130654289234746493669)
          ·
            refine ⟨32559024497679231514967563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173648130654289234746493669 32559024497679231514967563)
            ·
              refine ⟨48838536746518847272451345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32559024497679231514967563 48838536746518847272451345)
              ·
                refine ⟨36628902559889135454338509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48838536746518847272451345 36628902559889135454338509)
                ·
                  refine ⟨13735838459958425795376941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36628902559889135454338509 13735838459958425795376941)
                  ·
                    refine ⟨5150939422484409673266353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13735838459958425795376941 5150939422484409673266353)
                    ·
                      refine ⟨3863204566863307254949765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5150939422484409673266353 3863204566863307254949765)
                      ·
                        rfl

theorem cell23_7523564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 3, 2].length) (baseStart_7523564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523564 prefixEnd_7523564 := by exact prefixLift 7523564
  have htrace : WordTrace (prefixWord ++ tailWord_7523564) baseStart_7523564 baseEnd_7523564 := by
    simpa [prefixWord, tailWord_7523564, baseEnd_7523564] using wordTrace_append hprefix tailTrace_7523564
  have hstable : (prefixWord ++ tailWord_7523564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523564).length < 2 ^ (prefixWord ++ tailWord_7523564).sum := by decide
  have hdescent : baseEnd_7523564 < baseStart_7523564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523572 : List Nat := [2, 6, 1, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_7523572 : Nat := 118140960795 + 7523572 * 2 ^ 59
def prefixEnd_7523572 : Nat := 4983230072969 + 3 ^ 40 * 7523572 * 2
def baseEnd_7523572 : Nat := 3863208674708543223649729

theorem tailTrace_7523572 : CollatzResearch.WordTrace tailWord_7523572 prefixEnd_7523572 3863208674708543223649729 := by
  unfold tailWord_7523572
  simp only [CollatzResearch.WordTrace]
  refine ⟨137203607149695521322350485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182938142866260695096467313 137203607149695521322350485)
  ·
    refine ⟨6431419085141977561985179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 137203607149695521322350485 6431419085141977561985179)
    ·
      refine ⟨9647128627712966342977769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6431419085141977561985179 9647128627712966342977769)
      ·
        refine ⟨7235346470784724757233327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9647128627712966342977769 7235346470784724757233327)
        ·
          refine ⟨10853019706177087135849991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7235346470784724757233327 10853019706177087135849991)
          ·
            refine ⟨16279529559265630703774987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10853019706177087135849991 16279529559265630703774987)
            ·
              refine ⟨24419294338898446055662481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16279529559265630703774987 24419294338898446055662481)
              ·
                refine ⟨18314470754173834541746861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24419294338898446055662481 18314470754173834541746861)
                ·
                  refine ⟨6867926532815187953155073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18314470754173834541746861 6867926532815187953155073)
                  ·
                    refine ⟨5150944899611390964866305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6867926532815187953155073 5150944899611390964866305)
                    ·
                      refine ⟨3863208674708543223649729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5150944899611390964866305 3863208674708543223649729)
                      ·
                        rfl

theorem cell23_7523572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_7523572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523572 prefixEnd_7523572 := by exact prefixLift 7523572
  have htrace : WordTrace (prefixWord ++ tailWord_7523572) baseStart_7523572 baseEnd_7523572 := by
    simpa [prefixWord, tailWord_7523572, baseEnd_7523572] using wordTrace_append hprefix tailTrace_7523572
  have hstable : (prefixWord ++ tailWord_7523572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523572).length < 2 ^ (prefixWord ++ tailWord_7523572).sum := by decide
  have hdescent : baseEnd_7523572 < baseStart_7523572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523598 : List Nat := [4, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2]
def baseStart_7523598 : Nat := 118140960795 + 7523598 * 2 ^ 59
def prefixEnd_7523598 : Nat := 4983230072969 + 3 ^ 40 * 7523598 * 2
def baseEnd_7523598 : Nat := 3863222025205560121924609

theorem tailTrace_7523598 : CollatzResearch.WordTrace tailWord_7523598 prefixEnd_7523598 3863222025205560121924609 := by
  unfold tailWord_7523598
  simp only [CollatzResearch.WordTrace]
  refine ⟨34301020324662106135643431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182938775064864566056764965 34301020324662106135643431)
  ·
    refine ⟨51451530486993159203465147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34301020324662106135643431 51451530486993159203465147)
    ·
      refine ⟨77177295730489738805197721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51451530486993159203465147 77177295730489738805197721)
      ·
        refine ⟨57882971797867304103898291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77177295730489738805197721 57882971797867304103898291)
        ·
          refine ⟨86824457696800956155847437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57882971797867304103898291 86824457696800956155847437)
          ·
            refine ⟨32559171636300358558442789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86824457696800956155847437 32559171636300358558442789)
            ·
              refine ⟨6104844681806317229708023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32559171636300358558442789 6104844681806317229708023)
              ·
                refine ⟨9157267022709475844562035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6104844681806317229708023 9157267022709475844562035)
                ·
                  refine ⟨13735900534064213766843053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9157267022709475844562035 13735900534064213766843053)
                  ·
                    refine ⟨5150962700274080162566145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13735900534064213766843053 5150962700274080162566145)
                    ·
                      refine ⟨3863222025205560121924609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5150962700274080162566145 3863222025205560121924609)
                      ·
                        rfl

theorem cell23_7523598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_7523598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523598 prefixEnd_7523598 := by exact prefixLift 7523598
  have htrace : WordTrace (prefixWord ++ tailWord_7523598) baseStart_7523598 baseEnd_7523598 := by
    simpa [prefixWord, tailWord_7523598, baseEnd_7523598] using wordTrace_append hprefix tailTrace_7523598
  have hstable : (prefixWord ++ tailWord_7523598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523598).length < 2 ^ (prefixWord ++ tailWord_7523598).sum := by decide
  have hdescent : baseEnd_7523598 < baseStart_7523598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523607 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 4]
def baseStart_7523607 : Nat := 118140960795 + 7523607 * 2 ^ 59
def prefixEnd_7523607 : Nat := 4983230072969 + 3 ^ 40 * 7523607 * 2
def baseEnd_7523607 : Nat := 3863226646531450586712067

theorem tailTrace_7523607 : CollatzResearch.WordTrace tailWord_7523607 prefixEnd_7523607 3863226646531450586712067 := by
  unfold tailWord_7523607
  simp only [CollatzResearch.WordTrace]
  refine ⟨274408490854264243622225075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182938993902842829081483383 274408490854264243622225075)
  ·
    refine ⟨411612736281396365433337613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274408490854264243622225075 411612736281396365433337613)
    ·
      refine ⟨154354776105523637037501605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411612736281396365433337613 154354776105523637037501605)
      ·
        refine ⟨28941520519785681944531551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154354776105523637037501605 28941520519785681944531551)
        ·
          refine ⟨43412280779678522916797327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28941520519785681944531551 43412280779678522916797327)
          ·
            refine ⟨65118421169517784375195991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43412280779678522916797327 65118421169517784375195991)
            ·
              refine ⟨97677631754276676562793987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65118421169517784375195991 97677631754276676562793987)
              ·
                refine ⟨146516447631415014844190981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97677631754276676562793987 146516447631415014844190981)
                ·
                  refine ⟨27471833930890315283285809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146516447631415014844190981 27471833930890315283285809)
                  ·
                    refine ⟨20603875448167736462464357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27471833930890315283285809 20603875448167736462464357)
                    ·
                      refine ⟨3863226646531450586712067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20603875448167736462464357 3863226646531450586712067)
                      ·
                        rfl

theorem cell23_7523607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_7523607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523607 prefixEnd_7523607 := by exact prefixLift 7523607
  have htrace : WordTrace (prefixWord ++ tailWord_7523607) baseStart_7523607 baseEnd_7523607 := by
    simpa [prefixWord, tailWord_7523607, baseEnd_7523607] using wordTrace_append hprefix tailTrace_7523607
  have hstable : (prefixWord ++ tailWord_7523607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523607).length < 2 ^ (prefixWord ++ tailWord_7523607).sum := by decide
  have hdescent : baseEnd_7523607 < baseStart_7523607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523624 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_7523624 : Nat := 118140960795 + 7523624 * 2 ^ 59
def prefixEnd_7523624 : Nat := 4983230072969 + 3 ^ 40 * 7523624 * 2
def baseEnd_7523624 : Nat := 3863235375702577020199489

theorem tailTrace_7523624 : CollatzResearch.WordTrace tailWord_7523624 prefixEnd_7523624 3863235375702577020199489 := by
  unfold tailWord_7523624
  simp only [CollatzResearch.WordTrace]
  refine ⟨137204555447601327762796963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182939407263468437017062617 137204555447601327762796963)
  ·
    refine ⟨205806833171401991644195445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137204555447601327762796963 205806833171401991644195445)
    ·
      refine ⟨19294390609818936716643323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205806833171401991644195445 19294390609818936716643323)
      ·
        refine ⟨28941585914728405074964985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19294390609818936716643323 28941585914728405074964985)
        ·
          refine ⟨21706189436046303806223739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28941585914728405074964985 21706189436046303806223739)
          ·
            refine ⟨32559284154069455709335609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21706189436046303806223739 32559284154069455709335609)
            ·
              refine ⟨24419463115552091782001707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32559284154069455709335609 24419463115552091782001707)
              ·
                refine ⟨36629194673328137673002561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24419463115552091782001707 36629194673328137673002561)
                ·
                  refine ⟨27471896004996103254751921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36629194673328137673002561 27471896004996103254751921)
                  ·
                    refine ⟨20603922003747077441063941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27471896004996103254751921 20603922003747077441063941)
                    ·
                      refine ⟨3863235375702577020199489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20603922003747077441063941 3863235375702577020199489)
                      ·
                        rfl

theorem cell23_7523624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_7523624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523624 prefixEnd_7523624 := by exact prefixLift 7523624
  have htrace : WordTrace (prefixWord ++ tailWord_7523624) baseStart_7523624 baseEnd_7523624 := by
    simpa [prefixWord, tailWord_7523624, baseEnd_7523624] using wordTrace_append hprefix tailTrace_7523624
  have hstable : (prefixWord ++ tailWord_7523624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523624).length < 2 ^ (prefixWord ++ tailWord_7523624).sum := by decide
  have hdescent : baseEnd_7523624 < baseStart_7523624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523647 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 1, 7]
def baseStart_7523647 : Nat := 118140960795 + 7523647 * 2 ^ 59
def prefixEnd_7523647 : Nat := 4983230072969 + 3 ^ 40 * 7523647 * 2
def baseEnd_7523647 : Nat := 1287749061919210143403961

theorem tailTrace_7523647 : CollatzResearch.WordTrace tailWord_7523647 prefixEnd_7523647 1287749061919210143403961 := by
  unfold tailWord_7523647
  simp only [CollatzResearch.WordTrace]
  refine ⟨274409949774119330453681195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182939966516079553635787463 274409949774119330453681195)
  ·
    refine ⟨411614924661178995680521793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274409949774119330453681195 411614924661178995680521793)
    ·
      refine ⟨308711193495884246760391345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411614924661178995680521793 308711193495884246760391345)
      ·
        refine ⟨231533395121913185070293509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308711193495884246760391345 231533395121913185070293509)
        ·
          refine ⟨43412511585358722200680033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231533395121913185070293509 43412511585358722200680033)
          ·
            refine ⟨32559383689019041650510025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43412511585358722200680033 32559383689019041650510025)
            ·
              refine ⟨24419537766764281237882519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32559383689019041650510025 24419537766764281237882519)
              ·
                refine ⟨36629306650146421856823779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24419537766764281237882519 36629306650146421856823779)
                ·
                  refine ⟨54943959975219632785235669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36629306650146421856823779 54943959975219632785235669)
                  ·
                    refine ⟨1287749061919210143403961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54943959975219632785235669 1287749061919210143403961)
                    ·
                      rfl

theorem cell23_7523647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 7].length) (baseStart_7523647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523647 prefixEnd_7523647 := by exact prefixLift 7523647
  have htrace : WordTrace (prefixWord ++ tailWord_7523647) baseStart_7523647 baseEnd_7523647 := by
    simpa [prefixWord, tailWord_7523647, baseEnd_7523647] using wordTrace_append hprefix tailTrace_7523647
  have hstable : (prefixWord ++ tailWord_7523647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523647).length < 2 ^ (prefixWord ++ tailWord_7523647).sum := by decide
  have hdescent : baseEnd_7523647 < baseStart_7523647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523697 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 2, 4, 4]
def baseStart_7523697 : Nat := 118140960795 + 7523697 * 2 ^ 59
def prefixEnd_7523697 : Nat := 4983230072969 + 3 ^ 40 * 7523697 * 2
def baseEnd_7523697 : Nat := 3863272859790355234586653

theorem tailTrace_7523697 : CollatzResearch.WordTrace tailWord_7523697 prefixEnd_7523697 3863272859790355234586653 := by
  unfold tailWord_7523697
  simp only [CollatzResearch.WordTrace]
  refine ⟨274411773423938188993001345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182941182282625459328667563 274411773423938188993001345)
  ·
    refine ⟨205808830067953641744751009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274411773423938188993001345 205808830067953641744751009)
    ·
      refine ⟨154356622550965231308563257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205808830067953641744751009 154356622550965231308563257)
      ·
        refine ⟨115767466913223923481422443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154356622550965231308563257 115767466913223923481422443)
        ·
          refine ⟨173651200369835885222133665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115767466913223923481422443 173651200369835885222133665)
          ·
            refine ⟨130238400277376913916600249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173651200369835885222133665 130238400277376913916600249)
            ·
              refine ⟨97678800208032685437450187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130238400277376913916600249 97678800208032685437450187)
              ·
                refine ⟨146518200312049028156175281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97678800208032685437450187 146518200312049028156175281)
                ·
                  refine ⟨109888650234036771117131461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146518200312049028156175281 109888650234036771117131461)
                  ·
                    refine ⟨20604121918881894584462149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109888650234036771117131461 20604121918881894584462149)
                    ·
                      refine ⟨3863272859790355234586653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20604121918881894584462149 3863272859790355234586653)
                      ·
                        rfl

theorem cell23_7523697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_7523697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523697 prefixEnd_7523697 := by exact prefixLift 7523697
  have htrace : WordTrace (prefixWord ++ tailWord_7523697) baseStart_7523697 baseEnd_7523697 := by
    simpa [prefixWord, tailWord_7523697, baseEnd_7523697] using wordTrace_append hprefix tailTrace_7523697
  have hstable : (prefixWord ++ tailWord_7523697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523697).length < 2 ^ (prefixWord ++ tailWord_7523697).sum := by decide
  have hdescent : baseEnd_7523697 < baseStart_7523697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523724 : List Nat := [2, 2, 1, 2, 1, 3, 4, 2, 6]
def baseStart_7523724 : Nat := 118140960795 + 7523724 * 2 ^ 59
def prefixEnd_7523724 : Nat := 4983230072969 + 3 ^ 40 * 7523724 * 2
def baseEnd_7523724 : Nat := 429254080418669625438781

theorem tailTrace_7523724 : CollatzResearch.WordTrace tailWord_7523724 prefixEnd_7523724 429254080418669625438781 := by
  unfold tailWord_7523724
  simp only [CollatzResearch.WordTrace]
  refine ⟨137206379097420186302117113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182941838796560248402822817 137206379097420186302117113)
  ·
    refine ⟨102904784323065139726587835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137206379097420186302117113 102904784323065139726587835)
    ·
      refine ⟨154357176484597709589881753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102904784323065139726587835 154357176484597709589881753)
      ·
        refine ⟨115767882363448282192411315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154357176484597709589881753 115767882363448282192411315)
        ·
          refine ⟨173651823545172423288616973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115767882363448282192411315 173651823545172423288616973)
          ·
            refine ⟨65119433829439658733231365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173651823545172423288616973 65119433829439658733231365)
            ·
              refine ⟨12209893843019936012480881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65119433829439658733231365 12209893843019936012480881)
              ·
                refine ⟨9157420382264952009360661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12209893843019936012480881 9157420382264952009360661)
                ·
                  refine ⟨429254080418669625438781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9157420382264952009360661 429254080418669625438781)
                  ·
                    rfl

theorem cell23_7523724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 6].length) (baseStart_7523724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523724 prefixEnd_7523724 := by exact prefixLift 7523724
  have htrace : WordTrace (prefixWord ++ tailWord_7523724) baseStart_7523724 baseEnd_7523724 := by
    simpa [prefixWord, tailWord_7523724, baseEnd_7523724] using wordTrace_append hprefix tailTrace_7523724
  have hstable : (prefixWord ++ tailWord_7523724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523724).length < 2 ^ (prefixWord ++ tailWord_7523724).sum := by decide
  have hdescent : baseEnd_7523724 < baseStart_7523724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523747 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 7]
def baseStart_7523747 : Nat := 118140960795 + 7523747 * 2 ^ 59
def prefixEnd_7523747 : Nat := 4983230072969 + 3 ^ 40 * 7523747 * 2
def baseEnd_7523747 : Nat := 3863298533823080038961423

theorem tailTrace_7523747 : CollatzResearch.WordTrace tailWord_7523747 prefixEnd_7523747 3863298533823080038961423 := by
  unfold tailWord_7523747
  simp only [CollatzResearch.WordTrace]
  refine ⟨274413597073757047532321495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182942398049171365021547663 274413597073757047532321495)
  ·
    refine ⟨411620395610635571298482243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274413597073757047532321495 411620395610635571298482243)
    ·
      refine ⟨617430593415953356947723365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411620395610635571298482243 617430593415953356947723365)
      ·
        refine ⟨115768236265491254427698131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 617430593415953356947723365 115768236265491254427698131)
        ·
          refine ⟨173652354398236881641547197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115768236265491254427698131 173652354398236881641547197)
          ·
            refine ⟨65119632899338830615580199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173652354398236881641547197 65119632899338830615580199)
            ·
              refine ⟨97679449349008245923370299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65119632899338830615580199 97679449349008245923370299)
              ·
                refine ⟨146519174023512368885055449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97679449349008245923370299 146519174023512368885055449)
                ·
                  refine ⟨109889380517634276663791587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146519174023512368885055449 109889380517634276663791587)
                  ·
                    refine ⟨164834070776451414995687381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109889380517634276663791587 164834070776451414995687381)
                    ·
                      refine ⟨3863298533823080038961423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164834070776451414995687381 3863298533823080038961423)
                      ·
                        rfl

theorem cell23_7523747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_7523747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523747 prefixEnd_7523747 := by exact prefixLift 7523747
  have htrace : WordTrace (prefixWord ++ tailWord_7523747) baseStart_7523747 baseEnd_7523747 := by
    simpa [prefixWord, tailWord_7523747, baseEnd_7523747] using wordTrace_append hprefix tailTrace_7523747
  have hstable : (prefixWord ++ tailWord_7523747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523747).length < 2 ^ (prefixWord ++ tailWord_7523747).sum := by decide
  have hdescent : baseEnd_7523747 < baseStart_7523747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523761 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 1, 5, 2]
def baseStart_7523761 : Nat := 118140960795 + 7523761 * 2 ^ 59
def prefixEnd_7523761 : Nat := 4983230072969 + 3 ^ 40 * 7523761 * 2
def baseEnd_7523761 : Nat := 3863305722552242984186359

theorem tailTrace_7523761 : CollatzResearch.WordTrace tailWord_7523761 prefixEnd_7523761 3863305722552242984186359 := by
  unfold tailWord_7523761
  simp only [CollatzResearch.WordTrace]
  refine ⟨274414107695706327923331137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182942738463804218615554091 274414107695706327923331137)
  ·
    refine ⟨205810580771779745942498353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274414107695706327923331137 205810580771779745942498353)
    ·
      refine ⟨154357935578834809456873765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205810580771779745942498353 154357935578834809456873765)
      ·
        refine ⟨28942112921031526773163831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154357935578834809456873765 28942112921031526773163831)
        ·
          refine ⟨43413169381547290159745747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28942112921031526773163831 43413169381547290159745747)
          ·
            refine ⟨65119754072320935239618621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43413169381547290159745747 65119754072320935239618621)
            ·
              refine ⟨24419907777120350714856983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65119754072320935239618621 24419907777120350714856983)
              ·
                refine ⟨36629861665680526072285475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24419907777120350714856983 36629861665680526072285475)
                ·
                  refine ⟨54944792498520789108428213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36629861665680526072285475 54944792498520789108428213)
                  ·
                    refine ⟨5151074296736323978915145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54944792498520789108428213 5151074296736323978915145)
                    ·
                      refine ⟨3863305722552242984186359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5151074296736323978915145 3863305722552242984186359)
                      ·
                        rfl

theorem cell23_7523761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_7523761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523761 prefixEnd_7523761 := by exact prefixLift 7523761
  have htrace : WordTrace (prefixWord ++ tailWord_7523761) baseStart_7523761 baseEnd_7523761 := by
    simpa [prefixWord, tailWord_7523761, baseEnd_7523761] using wordTrace_append hprefix tailTrace_7523761
  have hstable : (prefixWord ++ tailWord_7523761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523761).length < 2 ^ (prefixWord ++ tailWord_7523761).sum := by decide
  have hdescent : baseEnd_7523761 < baseStart_7523761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523768 : List Nat := [2, 1, 2, 1, 2, 2, 3, 5, 1, 1, 3]
def baseStart_7523768 : Nat := 118140960795 + 7523768 * 2 ^ 59
def prefixEnd_7523768 : Nat := 4983230072969 + 3 ^ 40 * 7523768 * 2
def baseEnd_7523768 : Nat := 3863309316916824456798827

theorem tailTrace_7523768 : CollatzResearch.WordTrace tailWord_7523768 prefixEnd_7523768 3863309316916824456798827 := by
  unfold tailWord_7523768
  simp only [CollatzResearch.WordTrace]
  refine ⟨137207181503340484059417979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182942908671120645412557305 137207181503340484059417979)
  ·
    refine ⟨205810772255010726089126969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137207181503340484059417979 205810772255010726089126969)
    ·
      refine ⟨154358079191258044566845227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205810772255010726089126969 154358079191258044566845227)
      ·
        refine ⟨231537118786887066850267841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154358079191258044566845227 231537118786887066850267841)
        ·
          refine ⟨173652839090165300137700881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231537118786887066850267841 173652839090165300137700881)
          ·
            refine ⟨130239629317623975103275661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173652839090165300137700881 130239629317623975103275661)
            ·
              refine ⟨48839860994108990663728373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130239629317623975103275661 48839860994108990663728373)
              ·
                refine ⟨4578736968197717874724535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48839860994108990663728373 4578736968197717874724535)
                ·
                  refine ⟨6868105452296576812086803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4578736968197717874724535 6868105452296576812086803)
                  ·
                    refine ⟨10302158178444865218130205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6868105452296576812086803 10302158178444865218130205)
                    ·
                      refine ⟨3863309316916824456798827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10302158178444865218130205 3863309316916824456798827)
                      ·
                        rfl

theorem cell23_7523768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 1, 1, 3].length) (baseStart_7523768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523768 prefixEnd_7523768 := by exact prefixLift 7523768
  have htrace : WordTrace (prefixWord ++ tailWord_7523768) baseStart_7523768 baseEnd_7523768 := by
    simpa [prefixWord, tailWord_7523768, baseEnd_7523768] using wordTrace_append hprefix tailTrace_7523768
  have hstable : (prefixWord ++ tailWord_7523768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523768).length < 2 ^ (prefixWord ++ tailWord_7523768).sum := by decide
  have hdescent : baseEnd_7523768 < baseStart_7523768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523801 : List Nat := [1, 2, 1, 2, 4, 4, 1, 1, 1, 6]
def baseStart_7523801 : Nat := 118140960795 + 7523801 * 2 ^ 59
def prefixEnd_7523801 : Nat := 4983230072969 + 3 ^ 40 * 7523801 * 2
def baseEnd_7523801 : Nat := 1287775420592807609228725

theorem tailTrace_7523801 : CollatzResearch.WordTrace tailWord_7523801 prefixEnd_7523801 1287775420592807609228725 := by
  unfold tailWord_7523801
  simp only [CollatzResearch.WordTrace]
  refine ⟨274415566615561414754787257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182943711077040943169858171 274415566615561414754787257)
  ·
    refine ⟨205811674961671061066090443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274415566615561414754787257 205811674961671061066090443)
    ·
      refine ⟨308717512442506591599135665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205811674961671061066090443 308717512442506591599135665)
      ·
        refine ⟨231538134331879943699351749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308717512442506591599135665 231538134331879943699351749)
        ·
          refine ⟨43413400187227489443628453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231538134331879943699351749 43413400187227489443628453)
          ·
            refine ⟨8140012535105154270680335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43413400187227489443628453 8140012535105154270680335)
            ·
              refine ⟨12210018802657731406020503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8140012535105154270680335 12210018802657731406020503)
              ·
                refine ⟨18315028203986597109030755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12210018802657731406020503 18315028203986597109030755)
                ·
                  refine ⟨27472542305979895663546133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18315028203986597109030755 27472542305979895663546133)
                  ·
                    refine ⟨1287775420592807609228725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27472542305979895663546133 1287775420592807609228725)
                    ·
                      rfl

theorem cell23_7523801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 6].length) (baseStart_7523801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523801 prefixEnd_7523801 := by exact prefixLift 7523801
  have htrace : WordTrace (prefixWord ++ tailWord_7523801) baseStart_7523801 baseEnd_7523801 := by
    simpa [prefixWord, tailWord_7523801, baseEnd_7523801] using wordTrace_append hprefix tailTrace_7523801
  have hstable : (prefixWord ++ tailWord_7523801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523801).length < 2 ^ (prefixWord ++ tailWord_7523801).sum := by decide
  have hdescent : baseEnd_7523801 < baseStart_7523801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523842 : List Nat := [3, 4, 1, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_7523842 : Nat := 118140960795 + 7523842 * 2 ^ 59
def prefixEnd_7523842 : Nat := 4983230072969 + 3 ^ 40 * 7523842 * 2
def baseEnd_7523842 : Nat := 3863347314485257167273487

theorem tailTrace_7523842 : CollatzResearch.WordTrace tailWord_7523842 prefixEnd_7523842 3863347314485257167273487 := by
  unfold tailWord_7523842
  simp only [CollatzResearch.WordTrace]
  refine ⟨68604265502103219689257445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182944708005608585838019853 68604265502103219689257445)
  ·
    refine ⟨12863299781644353691735771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68604265502103219689257445 12863299781644353691735771)
    ·
      refine ⟨19294949672466530537603657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12863299781644353691735771 19294949672466530537603657)
      ·
        refine ⟨14471212254349897903202743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19294949672466530537603657 14471212254349897903202743)
        ·
          refine ⟨21706818381524846854804115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14471212254349897903202743 21706818381524846854804115)
          ·
            refine ⟨32560227572287270282206173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21706818381524846854804115 32560227572287270282206173)
            ·
              refine ⟨12210085339607726355827315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32560227572287270282206173 12210085339607726355827315)
              ·
                refine ⟨18315128009411589533740973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12210085339607726355827315 18315128009411589533740973)
                ·
                  refine ⟨6868173003529346075152865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18315128009411589533740973 6868173003529346075152865)
                  ·
                    refine ⟨5151129752647009556364649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6868173003529346075152865 5151129752647009556364649)
                    ·
                      refine ⟨3863347314485257167273487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5151129752647009556364649 3863347314485257167273487)
                      ·
                        rfl

theorem cell23_7523842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_7523842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523842 prefixEnd_7523842 := by exact prefixLift 7523842
  have htrace : WordTrace (prefixWord ++ tailWord_7523842) baseStart_7523842 baseEnd_7523842 := by
    simpa [prefixWord, tailWord_7523842, baseEnd_7523842] using wordTrace_append hprefix tailTrace_7523842
  have hstable : (prefixWord ++ tailWord_7523842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523842).length < 2 ^ (prefixWord ++ tailWord_7523842).sum := by decide
  have hdescent : baseEnd_7523842 < baseStart_7523842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523852 : List Nat := [2, 2, 1, 2, 6, 1, 2, 1, 2, 4]
def baseStart_7523852 : Nat := 118140960795 + 7523852 * 2 ^ 59
def prefixEnd_7523852 : Nat := 4983230072969 + 3 ^ 40 * 7523852 * 2
def baseEnd_7523852 : Nat := 1287784149763934042716147

theorem tailTrace_7523852 : CollatzResearch.WordTrace tailWord_7523852 prefixEnd_7523852 1287784149763934042716147 := by
  unfold tailWord_7523852
  simp only [CollatzResearch.WordTrace]
  refine ⟨137208713369188325232446905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182944951158917766976595873 137208713369188325232446905)
  ·
    refine ⟨102906535026891243924335179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137208713369188325232446905 102906535026891243924335179)
    ·
      refine ⟨154359802540336865886502769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102906535026891243924335179 154359802540336865886502769)
      ·
        refine ⟨115769851905252649414877077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154359802540336865886502769 115769851905252649414877077)
        ·
          refine ⟨5426711808058717941322363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115769851905252649414877077 5426711808058717941322363)
          ·
            refine ⟨8140067712088076911983545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5426711808058717941322363 8140067712088076911983545)
            ·
              refine ⟨6105050784066057683987659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8140067712088076911983545 6105050784066057683987659)
              ·
                refine ⟨9157576176099086525981489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6105050784066057683987659 9157576176099086525981489)
                ·
                  refine ⟨6868182132074314894486117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9157576176099086525981489 6868182132074314894486117)
                  ·
                    refine ⟨1287784149763934042716147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6868182132074314894486117 1287784149763934042716147)
                    ·
                      rfl

theorem cell23_7523852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 2, 4].length) (baseStart_7523852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523852 prefixEnd_7523852 := by exact prefixLift 7523852
  have htrace : WordTrace (prefixWord ++ tailWord_7523852) baseStart_7523852 baseEnd_7523852 := by
    simpa [prefixWord, tailWord_7523852, baseEnd_7523852] using wordTrace_append hprefix tailTrace_7523852
  have hstable : (prefixWord ++ tailWord_7523852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523852).length < 2 ^ (prefixWord ++ tailWord_7523852).sum := by decide
  have hdescent : baseEnd_7523852 < baseStart_7523852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523868 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 3, 3, 2]
def baseStart_7523868 : Nat := 118140960795 + 7523868 * 2 ^ 59
def prefixEnd_7523868 : Nat := 4983230072969 + 3 ^ 40 * 7523868 * 2
def baseEnd_7523868 : Nat := 3863360664982274065548367

theorem tailTrace_7523868 : CollatzResearch.WordTrace tailWord_7523868 prefixEnd_7523868 3863360664982274065548367 := by
  unfold tailWord_7523868
  simp only [CollatzResearch.WordTrace]
  refine ⟨137209005153159342598738129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182945340204212456798317505 137209005153159342598738129)
  ·
    refine ⟨102906753864869506949053597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137209005153159342598738129 102906753864869506949053597)
    ·
      refine ⟨38590032699326065105895099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102906753864869506949053597 38590032699326065105895099)
      ·
        refine ⟨57885049048989097658842649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38590032699326065105895099 57885049048989097658842649)
        ·
          refine ⟨43413786786741823244131987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57885049048989097658842649 43413786786741823244131987)
          ·
            refine ⟨65120680180112734866197981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43413786786741823244131987 65120680180112734866197981)
            ·
              refine ⟨24420255067542275574824243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65120680180112734866197981 24420255067542275574824243)
              ·
                refine ⟨36630382601313413362236365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24420255067542275574824243 36630382601313413362236365)
                ·
                  refine ⟨13736393475492530010838637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36630382601313413362236365 13736393475492530010838637)
                  ·
                    refine ⟨5151147553309698754064489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13736393475492530010838637 5151147553309698754064489)
                    ·
                      refine ⟨3863360664982274065548367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5151147553309698754064489 3863360664982274065548367)
                      ·
                        rfl

theorem cell23_7523868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_7523868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523868 prefixEnd_7523868 := by exact prefixLift 7523868
  have htrace : WordTrace (prefixWord ++ tailWord_7523868) baseStart_7523868 baseEnd_7523868 := by
    simpa [prefixWord, tailWord_7523868, baseEnd_7523868] using wordTrace_append hprefix tailTrace_7523868
  have hstable : (prefixWord ++ tailWord_7523868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523868).length < 2 ^ (prefixWord ++ tailWord_7523868).sum := by decide
  have hdescent : baseEnd_7523868 < baseStart_7523868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523904 : List Nat := [2, 1, 1, 2, 2, 2, 1, 5, 7]
def baseStart_7523904 : Nat := 118140960795 + 7523904 * 2 ^ 59
def prefixEnd_7523904 : Nat := 4983230072969 + 3 ^ 40 * 7523904 * 2
def baseEnd_7523904 : Nat := 429264350031759547188689

theorem tailTrace_7523904 : CollatzResearch.WordTrace tailWord_7523904 prefixEnd_7523904 429264350031759547188689 := by
  unfold tailWord_7523904
  simp only [CollatzResearch.WordTrace]
  refine ⟨137209661667094131672893383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182946215556125508897191177 137209661667094131672893383)
  ·
    refine ⟨205814492500641197509340075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137209661667094131672893383 205814492500641197509340075)
    ·
      refine ⟨308721738750961796264010113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205814492500641197509340075 308721738750961796264010113)
      ·
        refine ⟨231541304063221347198007585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308721738750961796264010113 231541304063221347198007585)
        ·
          refine ⟨173655978047416010398505689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231541304063221347198007585 173655978047416010398505689)
          ·
            refine ⟨130241983535562007798879267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173655978047416010398505689 130241983535562007798879267)
            ·
              refine ⟨195362975303343011698318901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130241983535562007798879267 195362975303343011698318901)
              ·
                refine ⟨18315278934688407346717397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 195362975303343011698318901 18315278934688407346717397)
                ·
                  refine ⟨429264350031759547188689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18315278934688407346717397 429264350031759547188689)
                  ·
                    rfl

theorem cell23_7523904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 7].length) (baseStart_7523904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523904 prefixEnd_7523904 := by exact prefixLift 7523904
  have htrace : WordTrace (prefixWord ++ tailWord_7523904) baseStart_7523904 baseEnd_7523904 := by
    simpa [prefixWord, tailWord_7523904, baseEnd_7523904] using wordTrace_append hprefix tailTrace_7523904
  have hstable : (prefixWord ++ tailWord_7523904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523904).length < 2 ^ (prefixWord ++ tailWord_7523904).sum := by decide
  have hdescent : baseEnd_7523904 < baseStart_7523904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7523949 : List Nat := [1, 5, 1, 1, 4, 2, 1, 2, 2, 2, 2]
def baseStart_7523949 : Nat := 118140960795 + 7523949 * 2 ^ 59
def prefixEnd_7523949 : Nat := 4983230072969 + 3 ^ 40 * 7523949 * 2
def baseEnd_7523949 : Nat := 3863402256915288248635495

theorem tailTrace_7523949 : CollatzResearch.WordTrace tailWord_7523949 prefixEnd_7523949 3863402256915288248635495 := by
  unfold tailWord_7523949
  simp only [CollatzResearch.WordTrace]
  refine ⟨274420964619025236031174901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182947309746016824020783267 274420964619025236031174901)
  ·
    refine ⟨25726965433033615877922647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 274420964619025236031174901 25726965433033615877922647)
    ·
      refine ⟨38590448149550423816883971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25726965433033615877922647 38590448149550423816883971)
      ·
        refine ⟨57885672224325635725325957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38590448149550423816883971 57885672224325635725325957)
        ·
          refine ⟨10853563542061056698498617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57885672224325635725325957 10853563542061056698498617)
          ·
            refine ⟨8140172656545792523873963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10853563542061056698498617 8140172656545792523873963)
            ·
              refine ⟨12210258984818688785810945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8140172656545792523873963 12210258984818688785810945)
              ·
                refine ⟨9157694238614016589358209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12210258984818688785810945 9157694238614016589358209)
                ·
                  refine ⟨6868270678960512442018657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9157694238614016589358209 6868270678960512442018657)
                  ·
                    refine ⟨5151203009220384331513993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6868270678960512442018657 5151203009220384331513993)
                    ·
                      refine ⟨3863402256915288248635495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5151203009220384331513993 3863402256915288248635495)
                      ·
                        rfl

theorem cell23_7523949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_7523949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7523949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7523949 prefixEnd_7523949 := by exact prefixLift 7523949
  have htrace : WordTrace (prefixWord ++ tailWord_7523949) baseStart_7523949 baseEnd_7523949 := by
    simpa [prefixWord, tailWord_7523949, baseEnd_7523949] using wordTrace_append hprefix tailTrace_7523949
  have hstable : (prefixWord ++ tailWord_7523949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7523949).length < 2 ^ (prefixWord ++ tailWord_7523949).sum := by decide
  have hdescent : baseEnd_7523949 < baseStart_7523949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7523949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524028 : List Nat := [2, 2, 2, 3, 1, 3, 1, 3, 6]
def baseStart_7524028 : Nat := 118140960795 + 7524028 * 2 ^ 59
def prefixEnd_7524028 : Nat := 4983230072969 + 3 ^ 40 * 7524028 * 2
def baseEnd_7524028 : Nat := 429271424654110382171959

theorem tailTrace_7524028 : CollatzResearch.WordTrace tailWord_7524028 prefixEnd_7524028 429271424654110382171959 := by
  unfold tailWord_7524028
  simp only [CollatzResearch.WordTrace]
  refine ⟨137211922992869516261650369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182949230657159355015533825 137211922992869516261650369)
  ·
    refine ⟨102908942244652137196237777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137211922992869516261650369 102908942244652137196237777)
    ·
      refine ⟨77181706683489102897178333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102908942244652137196237777 77181706683489102897178333)
      ·
        refine ⟨28943140006308413586441875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77181706683489102897178333 28943140006308413586441875)
        ·
          refine ⟨43414710009462620379662813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28943140006308413586441875 43414710009462620379662813)
          ·
            refine ⟨16280516253548482642373555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43414710009462620379662813 16280516253548482642373555)
            ·
              refine ⟨24420774380322723963560333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16280516253548482642373555 24420774380322723963560333)
              ·
                refine ⟨9157790392621021486335125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24420774380322723963560333 9157790392621021486335125)
                ·
                  refine ⟨429271424654110382171959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9157790392621021486335125 429271424654110382171959)
                  ·
                    rfl

theorem cell23_7524028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 6].length) (baseStart_7524028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524028 prefixEnd_7524028 := by exact prefixLift 7524028
  have htrace : WordTrace (prefixWord ++ tailWord_7524028) baseStart_7524028 baseEnd_7524028 := by
    simpa [prefixWord, tailWord_7524028, baseEnd_7524028] using wordTrace_append hprefix tailTrace_7524028
  have hstable : (prefixWord ++ tailWord_7524028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524028).length < 2 ^ (prefixWord ++ tailWord_7524028).sum := by decide
  have hdescent : baseEnd_7524028 < baseStart_7524028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524078 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_7524078 : Nat := 118140960795 + 7524078 * 2 ^ 59
def prefixEnd_7524078 : Nat := 4983230072969 + 3 ^ 40 * 7524078 * 2
def baseEnd_7524078 : Nat := 3863468495919718243922401

theorem tailTrace_7524078 : CollatzResearch.WordTrace tailWord_7524078 prefixEnd_7524078 3863468495919718243922401 := by
  unfold tailWord_7524078
  simp only [CollatzResearch.WordTrace]
  refine ⟨34303208704444736382827611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182950446423705260708413925 34303208704444736382827611)
  ·
    refine ⟨51454813056667104574241417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34303208704444736382827611 51454813056667104574241417)
    ·
      refine ⟨38591109792500328430681063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51454813056667104574241417 38591109792500328430681063)
      ·
        refine ⟨57886664688750492646021595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38591109792500328430681063 57886664688750492646021595)
        ·
          refine ⟨86829997033125738969032393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57886664688750492646021595 86829997033125738969032393)
          ·
            refine ⟨65122497774844304226774295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86829997033125738969032393 65122497774844304226774295)
            ·
              refine ⟨97683746662266456340161443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65122497774844304226774295 97683746662266456340161443)
              ·
                refine ⟨146525619993399684510242165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97683746662266456340161443 146525619993399684510242165)
                ·
                  refine ⟨13736776874381220422835203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146525619993399684510242165 13736776874381220422835203)
                  ·
                    refine ⟨20605165311571830634252805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13736776874381220422835203 20605165311571830634252805)
                    ·
                      refine ⟨3863468495919718243922401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20605165311571830634252805 3863468495919718243922401)
                      ·
                        rfl

theorem cell23_7524078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_7524078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524078 prefixEnd_7524078 := by exact prefixLift 7524078
  have htrace : WordTrace (prefixWord ++ tailWord_7524078) baseStart_7524078 baseEnd_7524078 := by
    simpa [prefixWord, tailWord_7524078, baseEnd_7524078] using wordTrace_append hprefix tailTrace_7524078
  have hstable : (prefixWord ++ tailWord_7524078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524078).length < 2 ^ (prefixWord ++ tailWord_7524078).sum := by decide
  have hdescent : baseEnd_7524078 < baseStart_7524078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524095 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 5, 2, 2]
def baseStart_7524095 : Nat := 118140960795 + 7524095 * 2 ^ 59
def prefixEnd_7524095 : Nat := 4983230072969 + 3 ^ 40 * 7524095 * 2
def baseEnd_7524095 : Nat := 3863477225090844677409823

theorem tailTrace_7524095 : CollatzResearch.WordTrace tailWord_7524095 prefixEnd_7524095 3863477225090844677409823 := by
  unfold tailWord_7524095
  simp only [CollatzResearch.WordTrace]
  refine ⟨274426289676496302965989739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182950859784330868643993159 274426289676496302965989739)
  ·
    refine ⟨411639434514744454448984609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274426289676496302965989739 411639434514744454448984609)
    ·
      refine ⟨308729575886058340836738457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411639434514744454448984609 308729575886058340836738457)
      ·
        refine ⟨231547181914543755627553843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308729575886058340836738457 231547181914543755627553843)
        ·
          refine ⟨347320772871815633441330765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231547181914543755627553843 347320772871815633441330765)
          ·
            refine ⟨130245289826930862540499037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347320772871815633441330765 130245289826930862540499037)
            ·
              refine ⟨48841983685099073452687139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130245289826930862540499037 48841983685099073452687139)
              ·
                refine ⟨73262975527648610179030709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48841983685099073452687139 73262975527648610179030709)
                ·
                  refine ⟨6868403955717057204284129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73262975527648610179030709 6868403955717057204284129)
                  ·
                    refine ⟨5151302966787792903213097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6868403955717057204284129 5151302966787792903213097)
                    ·
                      refine ⟨3863477225090844677409823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5151302966787792903213097 3863477225090844677409823)
                      ·
                        rfl

theorem cell23_7524095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 2, 2].length) (baseStart_7524095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524095 prefixEnd_7524095 := by exact prefixLift 7524095
  have htrace : WordTrace (prefixWord ++ tailWord_7524095) baseStart_7524095 baseEnd_7524095 := by
    simpa [prefixWord, tailWord_7524095, baseEnd_7524095] using wordTrace_append hprefix tailTrace_7524095
  have hstable : (prefixWord ++ tailWord_7524095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524095).length < 2 ^ (prefixWord ++ tailWord_7524095).sum := by decide
  have hdescent : baseEnd_7524095 < baseStart_7524095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
